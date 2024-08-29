use std::{cmp::max, collections::BTreeMap, iter, sync::Arc};

use halo2_curves::ff::PrimeField;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Any, Challenge, Circuit, Column, ConstraintSystem, Error, Expression, FirstPhase,
        Fixed, Instance, SecondPhase, ThirdPhase, VirtualCells,
    },
    poly::Rotation,
};
use powdr_executor::witgen::WitgenCallback;

use powdr_ast::analyzed::{
    AlgebraicBinaryOperation, AlgebraicBinaryOperator, AlgebraicExpression, SelectedExpressions,
};
use powdr_ast::{
    analyzed::{Analyzed, IdentityKind},
    parsed::visitor::ExpressionVisitable,
};
use powdr_number::FieldElement;

const FIRST_STEP_NAME: &str = "__first_step";
const ENABLE_NAME: &str = "__enable";
const INSTANCE_NAME: &str = "__instance";

#[derive(Clone)]
pub(crate) struct PowdrCircuitConfig {
    advice: BTreeMap<String, Column<Advice>>,
    fixed: BTreeMap<String, Column<Fixed>>,
    enable: Column<Fixed>,
    instance: Column<Instance>,
    challenges: BTreeMap<u64, Challenge>,
}

impl PowdrCircuitConfig {
    fn iter_columns(&self) -> impl Iterator<Item = (&str, Column<Any>)> {
        self.advice
            .iter()
            .map(|(name, column)| (name.as_str(), (*column).into()))
            .chain(
                self.fixed
                    .iter()
                    .map(|(name, column)| (name.as_str(), (*column).into())),
            )
            .chain(std::iter::once((ENABLE_NAME, self.enable.into())))
            .chain(std::iter::once((INSTANCE_NAME, self.instance.into())))
    }
}

#[derive(Clone)]
/// Wraps an Analyzed<T>. This is used as the PowdrCircuit::Params type, which required
/// a type that implements Default.
pub(crate) struct AnalyzedWrapper<T: FieldElement>(Arc<Analyzed<T>>);

impl<T> Default for AnalyzedWrapper<T>
where
    T: FieldElement,
{
    fn default() -> Self {
        // Halo2 calls Params::default() in the Circuit::params() default implementation,
        // which we overwrite...
        unreachable!()
    }
}

impl<T: FieldElement> From<Arc<Analyzed<T>>> for AnalyzedWrapper<T> {
    fn from(analyzed: Arc<Analyzed<T>>) -> Self {
        Self(analyzed)
    }
}

#[derive(Clone)]
pub(crate) struct PowdrCircuit<'a, T> {
    /// The analyzed PIL
    analyzed: Arc<Analyzed<T>>,
    /// The value of the fixed columns
    fixed: &'a [(String, Vec<T>)],
    /// The value of the witness columns, if set
    witness: Option<&'a [(String, Vec<T>)]>,
    /// Column name and index of the public cells
    publics: Vec<(String, usize)>,
    /// Callback to augment the witness in the later stages.
    witgen_callback: Option<WitgenCallback<T>>,
}

fn get_publics<T: FieldElement>(analyzed: &Analyzed<T>) -> Vec<(String, usize)> {
    let mut publics = analyzed
        .public_declarations
        .values()
        .map(|public_declaration| {
            let witness_name = public_declaration.referenced_poly_name();
            let witness_offset = public_declaration.index as usize;
            (witness_name, witness_offset)
        })
        .collect::<Vec<_>>();

    // Sort, so that the order is deterministic
    publics.sort();
    publics
}

impl<'a, T: FieldElement> PowdrCircuit<'a, T> {
    pub(crate) fn new(analyzed: Arc<Analyzed<T>>, fixed: &'a [(String, Vec<T>)]) -> Self {
        for (fixed_name, _) in fixed {
            assert!(fixed_name != FIRST_STEP_NAME);
            assert!(fixed_name != ENABLE_NAME);
        }

        let publics = get_publics(&analyzed);

        Self {
            analyzed,
            fixed,
            witness: None,
            publics,
            witgen_callback: None,
        }
    }

    pub(crate) fn with_witness(self, witness: &'a [(String, Vec<T>)]) -> Self {
        Self {
            witness: Some(witness),
            ..self
        }
    }

    pub(crate) fn with_witgen_callback(self, witgen_callback: WitgenCallback<T>) -> Self {
        Self {
            witgen_callback: Some(witgen_callback),
            ..self
        }
    }

    pub(crate) fn has_publics(&self) -> bool {
        !self.publics.is_empty()
    }

    /// Computes the instance column from the witness
    pub(crate) fn instance_column<F: PrimeField<Repr = [u8; 32]>>(&self) -> Vec<F> {
        let witness = self
            .witness
            .as_ref()
            .expect("Witness needs to be set")
            .iter()
            .map(|(name, values)| (name, values))
            .collect::<BTreeMap<_, _>>();

        self.publics
            .iter()
            .map(|(col_name, i)| convert_field(witness.get(col_name).unwrap()[*i]))
            .collect()
    }
}

impl<'a, T: FieldElement, F: PrimeField<Repr = [u8; 32]>> Circuit<F> for PowdrCircuit<'a, T> {
    type Config = PowdrCircuitConfig;

    type FloorPlanner = SimpleFloorPlanner;

    type Params = AnalyzedWrapper<T>;

    // This doesn't seem to be called in practice?
    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {
        unreachable!()
    }

    fn params(&self) -> Self::Params {
        self.analyzed.clone().into()
    }

    fn configure_with_params(meta: &mut ConstraintSystem<F>, params: Self::Params) -> Self::Config {
        let analyzed = params.0;

        // Create columns

        let advice = analyzed
            .committed_polys_in_source_order()
            .iter()
            .flat_map(|(symbol, _)| {
                symbol
                    .array_elements()
                    .map(|(name, _)| (name, symbol.stage))
            })
            .map(|(name, stage)| {
                let stage = stage.unwrap_or(0);
                let col = match stage {
                    0 => meta.advice_column_in(FirstPhase),
                    1 => meta.advice_column_in(SecondPhase),
                    2 => meta.advice_column_in(ThirdPhase),
                    _ => panic!("Stage too large for Halo2 backend: {stage}"),
                };
                (name.clone(), col)
            })
            .collect();

        let first_step = meta.fixed_column();
        let fixed = analyzed
            .constant_polys_in_source_order()
            .iter()
            .flat_map(|(symbol, _)| symbol.array_elements())
            .map(|(name, _)| (name.clone(), meta.fixed_column()))
            .chain(iter::once((FIRST_STEP_NAME.to_string(), first_step)))
            .collect();

        let enable = meta.fixed_column();
        let instance = meta.instance_column();

        // Collect challenges referenced in any identity.
        let mut challenges = BTreeMap::new();
        for identity in analyzed.identities_with_inlined_intermediate_polynomials() {
            identity.pre_visit_expressions(&mut |expr| {
                if let AlgebraicExpression::Challenge(challenge) = expr {
                    challenges
                        .entry(challenge.id)
                        .or_insert_with(|| match &challenge.stage {
                            0 => meta.challenge_usable_after(FirstPhase),
                            1 => meta.challenge_usable_after(SecondPhase),
                            2 => meta.challenge_usable_after(ThirdPhase),
                            _ => panic!("Stage too large for Halo2 backend: {}", challenge.stage),
                        });
                }
            })
        }

        let config = PowdrCircuitConfig {
            advice,
            fixed,
            enable,
            instance,
            challenges,
        };

        // Enable equality for instance column & all witness columns with public cells
        meta.enable_equality(config.instance);
        for (column_name, _) in get_publics(&analyzed) {
            meta.enable_equality(config.advice[&column_name]);
        }

        // Add polynomial identities
        let identities = analyzed
            .identities_with_inlined_intermediate_polynomials()
            .into_iter()
            .filter(|id| id.kind == IdentityKind::Polynomial)
            .collect::<Vec<_>>();
        if !identities.is_empty() {
            meta.create_gate("main", |meta| -> Vec<(String, Expression<F>)> {
                identities
                    .iter()
                    .map(|id| {
                        let expr = id.expression_for_poly_id();
                        let name = id.to_string();
                        let expr = to_halo2_expression(expr, &config, meta);
                        let expr = expr * meta.query_fixed(config.enable, Rotation::cur());
                        (name, expr)
                    })
                    .collect()
            });
        }

        // Add constraints that for all witness columns, cell 0 must equal cell <degree>.
        // This forces the prover to simulate wrapping correctly.
        meta.create_gate("enforce_wrapping", |meta| -> Vec<(String, Expression<F>)> {
            let first_step = meta.query_fixed(config.fixed[FIRST_STEP_NAME], Rotation::cur());
            config
                .advice
                .keys()
                .map(|name| {
                    let first_row = meta.query_advice(config.advice[name], Rotation::cur());
                    let last_row = meta.query_advice(
                        config.advice[name],
                        Rotation(analyzed.degree().try_into().unwrap()),
                    );
                    let expr = first_step.clone() * (first_row - last_row);
                    (format!("enforce wrapping ({name})"), expr)
                })
                .collect()
        });

        // Challenge used to combine the lookup tuple with the selector
        let beta = Expression::Challenge(meta.challenge_usable_after(FirstPhase));

        let to_lookup_tuple = |expr: &SelectedExpressions<AlgebraicExpression<T>>,
                               meta: &mut VirtualCells<'_, F>| {
            let selector = expr
                .selector
                .as_ref()
                .map_or(Expression::Constant(F::from(1)), |selector| {
                    to_halo2_expression(selector, &config, meta)
                });
            let selector = selector * meta.query_fixed(config.enable, Rotation::cur());

            expr.expressions
                .iter()
                .map(|expr| {
                    let expr = to_halo2_expression(expr, &config, meta);
                    // Turns a selected lookup / permutation argument into an unselected lookup / permutation argument,
                    // see Section 3.3, equation (24) of: https://eprint.iacr.org/2023/474.pdf
                    // Note that they use a different transformation for lookups, because this transformation would fail
                    // if the RHS selector was 1 on all rows (and not on the LHS). This is never the case for us though,
                    // because we multiply with the __enable column!
                    selector.clone() * (expr - beta.clone()) + beta.clone()
                })
                .collect::<Vec<_>>()
        };

        for id in analyzed.identities_with_inlined_intermediate_polynomials() {
            match id.kind {
                // Already handled above
                IdentityKind::Polynomial => {}
                IdentityKind::Connect => unimplemented!(),
                IdentityKind::Plookup => {
                    let name = id.to_string();
                    meta.lookup_any(&name, |meta| {
                        to_lookup_tuple(&id.left, meta)
                            .into_iter()
                            .zip(to_lookup_tuple(&id.right, meta))
                            .collect()
                    });
                }
                IdentityKind::Permutation => {
                    let name = id.to_string();
                    meta.shuffle(&name, |meta| {
                        to_lookup_tuple(&id.left, meta)
                            .into_iter()
                            .zip(to_lookup_tuple(&id.right, meta))
                            .collect()
                    });
                }
            }
        }

        config
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // The structure of the table is as following
        //
        // | constant columns | __enable     |  witness columns | \
        // |  c[0]            |    1         |   w[0]           |  |
        // |  c[1]            |    1         |   w[1]           |  |>  N actual circuit rows
        // |  ...             |   ...        |   ...            |  |
        // |  c[N - 2]        |    1         |   w[N - 2]       |  |
        // |  c[N - 1]        |    1         |   w[N - 1]       | /
        // |  c[0]            |    0         |   w[0]           | \  <-- Row 0 is copy-constrained to row N
        // |  None            |    None      |   None           |  |
        // |  ...             |   ...        |   ...            |  |>  2**(ceil(log2(N)) padding rows to fit the halo2 unusable rows
        // |  None            |    None      |   None           |  |
        // |  None            |    None      |   None           |  | <-- Halo2 will put blinding factors in the last few rows
        // |  None            |    None      |   None           | /      of the witness columns.

        // If we're in a later stage, augment the original stage-0 witness by calling the witgen_callback.
        // If we're in stage 0, we already have the full witness and don't do anything.
        let mut new_witness = Vec::new();
        if let Some(witness) = self.witness {
            let mut stage = 1;
            let challenges = config
                .challenges
                .iter()
                .filter_map(|(&challenge_id, challenge)| {
                    let mut challenge_key_value_pair = None;
                    layouter.get_challenge(*challenge).map(|x| {
                        // The current stage is the maximum of all available challenges + 1
                        stage = max(stage, challenge.phase() + 1);
                        // Set the challenge value. We don't return it here, because we'd get
                        // a Value<T> and Halo2 doesn't let us convert it to an Option<T> easily...
                        challenge_key_value_pair =
                            Some((challenge_id, T::from_bytes_le(&x.to_repr())))
                    });
                    challenge_key_value_pair
                })
                .collect::<BTreeMap<u64, T>>();

            // If there are no available challenges, we are in stage 0 and do nothing.
            if !challenges.is_empty() {
                log::info!(
                    "Running witness generation for stage {stage} ({} challenges)!",
                    challenges.len()
                );
                new_witness = self
                    .witgen_callback
                    .as_ref()
                    .expect("Expected witgen callback!")
                    .next_stage_witness(witness, challenges, stage);
            }
        }

        let public_cells = layouter.assign_region(
            || "main",
            |mut region| {
                for (name, column) in config.iter_columns() {
                    region.name_column(|| name, column);
                }

                // Set fixed values
                for (name, values) in self.fixed {
                    let column = *config.fixed.get(name).unwrap();
                    for (i, value) in values.iter().chain(iter::once(&values[0])).enumerate() {
                        region.assign_fixed(
                            || name,
                            column,
                            i,
                            || Value::known(convert_field::<T, F>(*value)),
                        )?;
                    }
                }
                let degree = self.analyzed.degree() as usize;
                for i in 0..(2 * degree) {
                    let value = F::from((i < degree) as u64);
                    region.assign_fixed(
                        || ENABLE_NAME,
                        config.enable,
                        i,
                        || Value::known(value),
                    )?;
                    region.assign_fixed(
                        || FIRST_STEP_NAME,
                        config.fixed[FIRST_STEP_NAME],
                        i,
                        || Value::known(F::from(if i == 0 { 1 } else { 0 })),
                    )?;
                }

                let publics = self
                    .publics
                    .iter()
                    .enumerate()
                    .map(|(i, p)| (p, i))
                    .collect::<BTreeMap<_, _>>();

                // Set witness values
                let mut public_cells = Vec::new();
                let witness: Option<&[(String, Vec<T>)]> = if new_witness.is_empty() {
                    // We're in stage 0, use the original witness
                    self.witness
                } else {
                    Some(&new_witness)
                };
                if let Some(witness) = witness {
                    for (name, values) in witness.iter() {
                        let column = *config.advice.get(name).unwrap();
                        for (i, value) in values.iter().enumerate() {
                            let value = Value::known(convert_field::<T, F>(*value));

                            let assigned_cell =
                                region.assign_advice(|| name, column, i, || value)?;

                            // The first row needs to be copied to row <degree>
                            if i == 0 {
                                region.assign_advice(|| name, column, degree, || value)?;
                            }

                            // Collect public cells, which are later copy-constrained to equal
                            // a cell in the instance column.
                            if let Some(&instance_index) = publics.get(&(name.clone(), i)) {
                                public_cells.push((instance_index, assigned_cell));
                            }
                        }
                    }
                }

                Ok(public_cells)
            },
        )?;

        // Enforce publics by copy-constraining to cells in the instance column.
        // For example, if we have the following public declarations:
        // - public out1 = A(2);
        // - public out2 = B(0);
        // This would lead to the corresponding values being copied into the public
        // column as follows:
        // | Row | A   | B   | public |
        // |-----|-----|-----|--------|
        // |  0  |  0  | *5* |  *2*   |
        // |  1  |  1  |  6  |  *5*   |
        // |  2  | *2* |  7  |        |
        // |  3  |  4  |  8  |        |

        for (i, cell) in public_cells.into_iter() {
            layouter.constrain_instance(cell.cell(), config.instance, i)?;
        }

        Ok(())
    }
}

pub(crate) fn convert_field<T: FieldElement, F: PrimeField<Repr = [u8; 32]>>(x: T) -> F {
    let x = x.to_arbitrary_integer();
    let mut repr: [u8; 32] = [0; 32];
    let f_le = x.to_le_bytes();
    repr[..f_le.len()].clone_from_slice(&f_le);
    F::from_repr_vartime(repr).expect("value in field")
}

fn to_halo2_expression<T: FieldElement, F: PrimeField<Repr = [u8; 32]>>(
    expr: &AlgebraicExpression<T>,
    config: &PowdrCircuitConfig,
    meta: &mut VirtualCells<'_, F>,
) -> Expression<F> {
    match expr {
        AlgebraicExpression::Number(n) => Expression::Constant(convert_field(*n)),
        AlgebraicExpression::Reference(polyref) => {
            let rotation = match polyref.next {
                false => Rotation::cur(),
                true => Rotation::next(),
            };
            if let Some(column) = config.advice.get(&polyref.name) {
                meta.query_advice(*column, rotation)
            } else if let Some(column) = config.fixed.get(&polyref.name) {
                meta.query_fixed(*column, rotation)
            } else {
                panic!("Unknown reference: {}", polyref.name)
            }
        }
        AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation {
            left: lhe,
            op,
            right: powdr_rhe,
        }) => {
            let lhe = to_halo2_expression(lhe, config, meta);
            let rhe = to_halo2_expression(powdr_rhe, config, meta);
            match op {
                AlgebraicBinaryOperator::Add => lhe + rhe,
                AlgebraicBinaryOperator::Sub => lhe - rhe,
                AlgebraicBinaryOperator::Mul => lhe * rhe,
                AlgebraicBinaryOperator::Pow => {
                    let AlgebraicExpression::Number(e) = powdr_rhe.as_ref() else {
                        panic!("Expected number in exponent.")
                    };
                    let e: u32 = e
                        .to_arbitrary_integer()
                        .try_into()
                        .unwrap_or_else(|_| panic!("Exponent has to fit 32 bits."));
                    if e == 0 {
                        Expression::Constant(F::from(1))
                    } else {
                        (0..e).fold(lhe.clone(), |acc, _| acc * lhe.clone())
                    }
                }
            }
        }
        AlgebraicExpression::Challenge(challenge) => {
            config.challenges.get(&challenge.id).unwrap().expr()
        }
        _ => unimplemented!("{:?}", expr),
    }
}

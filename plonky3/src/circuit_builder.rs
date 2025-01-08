//! A plonky3 adapter for powdr
//!
//! Supports public inputs with the use of fixed columns.
//! Namely, given public value pub corresponding to a witness value in row j
//! of witness column x, a corresponding fixed selector column s which is 0
//! everywhere save for at row j is constructed to constrain s * (pub - x) on
//! every row.

use alloc::{
    collections::{btree_map::BTreeMap, btree_set::BTreeSet},
    string::{String, ToString},
    vec,
    vec::Vec,
};
use itertools::Itertools;
use p3_maybe_rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use tracing::info_span;

use crate::{
    params::{Commitment, FieldElementMap, Plonky3Field, ProverData},
    AirStage,
};
use p3_air::{Air, BaseAir, PairBuilder};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use powdr_ast::analyzed::{
    expression_evaluator::{ExpressionEvaluator, TerminalAccess},
    AlgebraicExpression, AlgebraicReference, AlgebraicReferenceThin, Analyzed, Challenge, Identity,
    PolyID, PolynomialType,
};

use crate::{CallbackResult, MultiStageAir, MultistageAirBuilder};
use powdr_ast::parsed::visitor::ExpressionVisitable;

use powdr_executor_utils::WitgenCallback;
use powdr_number::FieldElement;

/// A description of the constraint system.
/// All of the data is derived from the analyzed PIL, but is materialized
/// here for performance reasons.
pub struct ConstraintSystem<T> {
    // for each witness column, the stage and index of this column in this stage
    witness_columns: BTreeMap<PolyID, (usize, usize)>,
    // for each fixed column, the index of this column in the fixed columns
    fixed_columns: BTreeMap<PolyID, usize>,
    // for each intermediate polynomial, the expression
    intermediates: BTreeMap<AlgebraicReferenceThin, AlgebraicExpression<T>>,
    identities: Vec<Identity<T>>,
    // for each stage, for each public input of that stage, the name, the column name, the poly_id, the row index
    pub(crate) publics_by_stage: Vec<Vec<(String, String, PolyID, usize)>>,
    constant_count: usize,
    // for each stage, the number of witness columns. There is always a least one stage, possibly empty
    stage_widths: Vec<usize>,
    challenges_by_stage: Vec<Vec<u64>>,
}

impl<T: FieldElement> From<&Analyzed<T>> for ConstraintSystem<T> {
    fn from(analyzed: &Analyzed<T>) -> Self {
        let identities = analyzed.identities.clone();
        let constant_count = analyzed.constant_count();
        let stage_widths = (0..analyzed.stage_count() as u32)
            .map(|stage| {
                analyzed
                    .definitions_in_source_order(PolynomialType::Committed)
                    .filter_map(|(s, _)| {
                        let symbol_stage = s.stage.unwrap_or_default();
                        (stage == symbol_stage).then(|| s.array_elements().count())
                    })
                    .sum()
            })
            .collect();

        let fixed_columns = analyzed
            .definitions_in_source_order(PolynomialType::Constant)
            .flat_map(|(symbol, _)| symbol.array_elements())
            .enumerate()
            .map(|(index, (_, id))| (id, index))
            .collect();

        let intermediates = analyzed.intermediate_definitions();

        let witness_columns = analyzed
            .definitions_in_source_order(PolynomialType::Committed)
            .into_group_map_by(|(s, _)| s.stage.unwrap_or_default())
            .into_iter()
            .flat_map(|(stage, symbols)| {
                symbols
                    .into_iter()
                    .flat_map(|(s, _)| s.array_elements())
                    .enumerate()
                    .map(move |(index_in_stage, (_, poly_id))| {
                        (poly_id, (stage as usize, index_in_stage))
                    })
            })
            .collect();

        // we use a set to collect all used challenges
        let mut challenges_by_stage = vec![BTreeSet::new(); analyzed.stage_count()];
        for identity in &identities {
            identity.pre_visit_expressions(&mut |expr| {
                if let AlgebraicExpression::Challenge(challenge) = expr {
                    challenges_by_stage[challenge.stage as usize].insert(challenge.id);
                }
            });
        }

        // finally, we convert the set to a vector
        let challenges_by_stage = challenges_by_stage
            .into_iter()
            .map(|set| set.into_iter().collect())
            .collect();

        let publics_by_stage = analyzed.get_publics().into_iter().fold(
            vec![vec![]; analyzed.stage_count()],
            |mut acc, (name, column_name, id, row, stage)| {
                acc[stage as usize].push((name, column_name, id, row));
                acc
            },
        );

        Self {
            identities,
            publics_by_stage,
            constant_count,
            stage_widths,
            witness_columns,
            fixed_columns,
            intermediates,
            challenges_by_stage,
        }
    }
}

pub struct PowdrCircuit<'a, T: FieldElementMap>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    /// The split program
    pub split: &'a BTreeMap<String, (Analyzed<T>, ConstraintSystem<T>)>,
    /// Callback to augment the witness in the later stages
    witgen_callback: Option<WitgenCallback<T>>,
}

impl<'a, T: FieldElementMap> PowdrCircuit<'a, T>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    pub fn new(split: &'a BTreeMap<String, (Analyzed<T>, ConstraintSystem<T>)>) -> Self {
        Self {
            split,
            witgen_callback: None,
        }
    }

    /// Calculates public values from generated witness values.
    /// For stages in which there are no public values, return an empty vector
    pub fn public_values_so_far(
        &self,
        witness_by_machine: &BTreeMap<String, Vec<(String, Vec<T>)>>,
    ) -> BTreeMap<String, Vec<Vec<Option<T>>>> {
        let witness = witness_by_machine
            .values()
            // this map seems redundant but it turns a reference over a tuple into a tuple of references
            .flat_map(|machine_witness| machine_witness.iter().map(|(n, v)| (n, v)))
            .collect::<BTreeMap<_, _>>();

        self.split
            .iter()
            .map(|(name, (_, table))| {
                let res = table
                    .publics_by_stage
                    .iter()
                    .map(|publics| {
                        publics
                            .iter()
                            .map(|(_, name, _, row)| witness.get(name).map(|column| column[*row]))
                            .collect()
                    })
                    .collect();

                (name.clone(), res)
            })
            .collect()
    }

    pub fn with_witgen_callback(self, witgen_callback: WitgenCallback<T>) -> Self {
        Self {
            witgen_callback: Some(witgen_callback),
            ..self
        }
    }
}

pub(crate) struct PowdrTable<'a, T: FieldElementMap>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    /// The constraint system description
    constraint_system: &'a ConstraintSystem<T>,
}

/// Convert a witness for a stage
pub fn generate_matrix<'a, T: FieldElementMap>(
    witness: impl Iterator<Item = (&'a String, &'a [T])> + Clone,
) -> RowMajorMatrix<Plonky3Field<T>>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    let width = witness.clone().count();

    let size = witness.clone().next().map(|(_, values)| values.len());

    let values = size
        .map(|size|
                // for each row, get the value of each column
                (0..size)
                    .flat_map(move |i| {
                        // witness values
                        witness.clone().map(move |(_, v)| v[i])
                    })
                .map(|f| f.into_p3_field())
                .collect())
        .unwrap_or_default();
    RowMajorMatrix::new(values, width)
}

impl<'a, T: FieldElementMap> PowdrTable<'a, T>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    pub(crate) fn new(constraint_system: &'a ConstraintSystem<T>) -> Self {
        Self { constraint_system }
    }
}

/// An extension of [Air] allowing access to the number of fixed columns
impl<T: FieldElementMap> BaseAir<Plonky3Field<T>> for PowdrTable<'_, T>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    fn width(&self) -> usize {
        unimplemented!("use MultiStageAir method instead")
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<Plonky3Field<T>>> {
        unimplemented!()
    }
}

struct Data<'a, T, AB: MultistageAirBuilder> {
    constraint_system: &'a ConstraintSystem<T>,
    traces_by_stage: &'a [AB::M],
    fixed: &'a AB::M,
    publics: &'a BTreeMap<&'a str, <AB as MultistageAirBuilder>::PublicVar>,
    challenges: &'a [BTreeMap<&'a u64, <AB as MultistageAirBuilder>::Challenge>],
}

impl<T, AB: MultistageAirBuilder> TerminalAccess<AB::Expr> for &Data<'_, T, AB> {
    fn get(&self, reference: &AlgebraicReference) -> AB::Expr {
        match reference.poly_id.ptype {
            PolynomialType::Committed => {
                let (stage, index) = self.constraint_system.witness_columns[&reference.poly_id];
                self.traces_by_stage[stage].row_slice(reference.next as usize)[index].into()
            }
            PolynomialType::Constant => {
                // find the index in the fixed columns
                let index = self.constraint_system.fixed_columns[&reference.poly_id];
                self.fixed.row_slice(reference.next as usize)[index].into()
            }
            PolynomialType::Intermediate => unreachable!(),
        }
    }

    fn get_challenge(&self, challenge: &Challenge) -> AB::Expr {
        self.challenges[challenge.stage as usize][&challenge.id]
            .clone()
            .into()
    }

    fn get_public(&self, public: &str) -> AB::Expr {
        (*self
            .publics
            .get(public)
            .expect("Referenced public value does not exist"))
        .into()
    }
}

impl<T: FieldElementMap, AB: PairBuilder + MultistageAirBuilder<F = Plonky3Field<T>>> Air<AB>
    for PowdrTable<'_, T>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    fn eval(&self, builder: &mut AB) {
        let stage_count = <Self as MultiStageAir<AB>>::stage_count(self);
        let traces_by_stage: Vec<AB::M> =
            (0..stage_count).map(|i| builder.stage_trace(i)).collect();
        let fixed = builder.preprocessed();
        let public_input_values_by_stage = (0..stage_count)
            .map(|i| builder.stage_public_values(i))
            .collect_vec();

        // public constraints
        let public_vals_by_name = self
            .constraint_system
            .publics_by_stage
            .iter()
            .zip_eq(public_input_values_by_stage)
            .flat_map(|(publics, values)| publics.iter().zip_eq(values.iter()))
            .map(|((name, _, _, _), pi)| (name.as_str(), *pi))
            .collect::<BTreeMap<&str, <AB as MultistageAirBuilder>::PublicVar>>();

        // for each stage, the values of the challenges drawn at the end of that stage
        let challenges_by_stage: Vec<BTreeMap<&u64, _>> = self
            .constraint_system
            .challenges_by_stage
            .iter()
            .enumerate()
            .map(|(stage, ids)| {
                let stage_challenges = builder.stage_challenges(stage as u8);
                (
                    stage,
                    ids.iter()
                        .zip_eq(stage_challenges.iter().cloned())
                        .collect(),
                )
            })
            .fold(
                vec![BTreeMap::default(); stage_count as usize],
                |mut acc, (stage, challenges)| {
                    acc[stage] = challenges;
                    acc
                },
            );

        let data: Data<T, AB> = Data {
            constraint_system: self.constraint_system,
            traces_by_stage: &traces_by_stage,
            publics: &public_vals_by_name,
            challenges: &challenges_by_stage,
            fixed: &fixed,
        };
        let mut evaluator = ExpressionEvaluator::new_with_custom_expr(
            &data,
            &self.constraint_system.intermediates,
            |value| AB::Expr::from(value.into_p3_field()),
        );

        // constrain public inputs using witness columns in stage 0
        let fixed_local = fixed.row_slice(0);
        let public_offset = self.constraint_system.constant_count;

        self.constraint_system
            .publics_by_stage
            .iter()
            .flatten()
            .enumerate()
            .for_each(|(index, (name, _, poly_id, _))| {
                let selector = fixed_local[public_offset + index];
                let (stage, index) = self.constraint_system.witness_columns[poly_id];
                let witness_col = traces_by_stage[stage].row_slice(0)[index];
                let public_value = public_vals_by_name[name.as_str()];

                // constraining s(i) * (pub[i] - x(i)) = 0
                builder.assert_zero(selector * (public_value.into() - witness_col));
            });

        // circuit constraints
        for identity in &self.constraint_system.identities {
            match identity {
                Identity::Polynomial(identity) => {
                    let e = evaluator.evaluate(&identity.expression);

                    builder.assert_zero(e);
                }
                Identity::Lookup(..) => unimplemented!("Plonky3 does not support plookup"),
                Identity::Permutation(..) => {
                    unimplemented!("Plonky3 does not support permutations")
                }
                Identity::Connect(..) => unimplemented!("Plonky3 does not support connections"),
                Identity::PhantomPermutation(_)
                | Identity::PhantomLookup(_)
                | Identity::PhantomBusInteraction(_) => {
                    // phantom identities are only used in witgen
                }
            }
        }
    }
}

impl<T: FieldElementMap, AB: PairBuilder + MultistageAirBuilder<F = Plonky3Field<T>>>
    MultiStageAir<AB> for PowdrTable<'_, T>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    fn stage_public_count(&self, stage: u8) -> usize {
        self.constraint_system.publics_by_stage[stage as usize].len()
    }

    fn preprocessed_width(&self) -> usize {
        self.constraint_system.constant_count
            + self
                .constraint_system
                .publics_by_stage
                .iter()
                .map(|publics| publics.len())
                .sum::<usize>()
    }

    fn stage_count(&self) -> u8 {
        self.constraint_system.stage_widths.len() as u8
    }

    fn stage_trace_width(&self, stage: u8) -> usize {
        self.constraint_system.stage_widths[stage as usize]
    }

    fn stage_challenge_count(&self, stage: u8) -> usize {
        self.constraint_system.challenges_by_stage[stage as usize].len()
    }
}

impl<T: FieldElementMap> PowdrCircuit<'_, T>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    /// Computes the stage data for stage number `trace_stage` based on `new_challenge_values` drawn at the end of stage `trace_stage - 1`.
    pub fn compute_stage(
        &self,
        trace_stage: u8,
        new_challenge_values: &[Plonky3Field<T>],
        witness_by_machine: &mut BTreeMap<String, Vec<(String, Vec<T>)>>,
    ) -> CallbackResult<Plonky3Field<T>> {
        let previous_stage_challenges: BTreeSet<&u64> = self
            .split
            .values()
            .flat_map(|(_, constraint_system)| {
                &constraint_system.challenges_by_stage[trace_stage as usize - 1]
            })
            .collect();

        assert_eq!(previous_stage_challenges.len(), new_challenge_values.len());
        let challenge_map = previous_stage_challenges
            .into_iter()
            .zip(new_challenge_values)
            .map(|(c, v)| (*c, T::from_p3_field(*v)))
            .collect::<BTreeMap<_, _>>();

        // remember the columns we already know about
        let columns_before: BTreeSet<String> = witness_by_machine
            .iter()
            .flat_map(|(_, cols)| cols.iter().map(|(name, _)| name.clone()))
            .collect();

        // Compute next-stage witness for each machine in parallel.
        *witness_by_machine = info_span!("Witness generation for next stage").in_scope(|| {
            witness_by_machine
                .par_iter()
                .map(|(machine_name, machine_witness)| {
                    let new_witness = self.witgen_callback.as_ref().unwrap().next_stage_witness(
                        &self.split[machine_name].0,
                        machine_witness,
                        challenge_map.clone(),
                        trace_stage,
                    );
                    (machine_name.clone(), new_witness)
                })
                .collect()
        });

        let public_values = self.public_values_so_far(witness_by_machine);

        // generate the next trace in the format p3 expects
        let air_stages = witness_by_machine
            .iter()
            .map(|(table_name, columns)| {
                // since the witgen callback returns the entire witness so far,
                // we filter out the columns we already know about
                let witness = columns
                    .iter()
                    .filter(|(name, _)| !columns_before.contains(name))
                    .map(|(name, values)| (name, values.as_ref()));
                (
                    table_name.to_string(),
                    AirStage {
                        trace: generate_matrix(witness),
                        public_values: public_values[table_name][trace_stage as usize]
                            .iter()
                            .map(|v| v.expect("public value for stage {trace_stage} should be available at this point").into_p3_field())
                            .collect(),
                    },
                )
            })
            .collect();

        // return the next stage for each table
        CallbackResult { air_stages }
    }
}

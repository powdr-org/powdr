use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

use itertools::Itertools;
use machines::MachineParts;
use powdr_ast::analyzed::{
    AlgebraicExpression, AlgebraicReference, Analyzed, DegreeRange, Expression,
    FunctionValueDefinition, PolyID, PolynomialType, SymbolKind, TypedExpression,
};
use powdr_ast::parsed::visitor::ExpressionVisitable;
use powdr_ast::parsed::{FunctionKind, LambdaExpression};
use powdr_number::{DegreeType, FieldElement};

use crate::constant_evaluator::VariablySizedColumn;
use crate::Identity;

use self::data_structures::column_map::{FixedColumnMap, WitnessColumnMap};
pub use self::eval_result::{
    Constraint, Constraints, EvalError, EvalResult, EvalStatus, EvalValue, IncompleteCause,
};
use self::generator::Generator;

use self::global_constraints::GlobalConstraints;
use self::identity_processor::Machines;
use self::machines::machine_extractor::ExtractionOutput;
use self::machines::profiling::{record_end, record_start, reset_and_print_profile_summary};
use self::machines::Machine;

mod affine_expression;
mod block_processor;
mod data_structures;
mod eval_result;
mod expression_evaluator;
pub mod fixed_evaluator;
mod generator;
mod global_constraints;
mod identity_processor;
mod machines;
mod processor;
mod query_processor;
mod range_constraints;
mod rows;
mod sequence_iterator;
pub mod symbolic_evaluator;
mod symbolic_witness_evaluator;
mod util;
mod vm_processor;

static OUTER_CODE_NAME: &str = "witgen (outer code)";

// TODO change this so that it has functions
// input_from_channel, output_to_channel
// instead of processing strings.
// but we can only do that once we have fully removed the old query functions.
pub trait QueryCallback<T>: Fn(&str) -> Result<Option<T>, String> + Send + Sync {}
impl<T, F> QueryCallback<T> for F where F: Fn(&str) -> Result<Option<T>, String> + Send + Sync {}

pub use powdr_number::WitgenCallback;

pub struct WitgenCallbackContext<T> {
    /// TODO: all these fields probably don't need to be Arc anymore, since the
    /// Arc was moved one level up... but I have to investigate this further.
    analyzed: Arc<Analyzed<T>>,
    fixed_col_values: Arc<Vec<(String, VariablySizedColumn<T>)>>,
    query_callback: Arc<dyn QueryCallback<T>>,
}

impl<T: FieldElement> WitgenCallbackContext<T> {
    pub fn new(
        analyzed: Arc<Analyzed<T>>,
        fixed_col_values: Arc<Vec<(String, VariablySizedColumn<T>)>>,
        query_callback: Option<Arc<dyn QueryCallback<T>>>,
    ) -> Self {
        let query_callback = query_callback.unwrap_or_else(|| Arc::new(unused_query_callback()));
        Self {
            analyzed,
            fixed_col_values,
            query_callback,
        }
    }

    /// Computes the next-stage witness, given the current witness and challenges.
    pub fn next_stage_witness(
        &self,
        current_witness: &[(String, Vec<T>)],
        challenges: BTreeMap<u64, T>,
        stage: u8,
    ) -> Vec<(String, Vec<T>)> {
        WitnessGenerator::new(
            &self.analyzed,
            &self.fixed_col_values,
            &*self.query_callback,
        )
        .with_external_witness_values(current_witness)
        .with_challenges(stage, challenges)
        .generate()
    }
}

pub fn chain_callbacks<T: FieldElement>(
    c1: Arc<dyn QueryCallback<T>>,
    c2: Arc<dyn QueryCallback<T>>,
) -> impl QueryCallback<T> {
    move |query| c1(query).or_else(|_| c2(query))
}

/// @returns a query callback that is never expected to be used.
pub fn unused_query_callback<T>() -> impl QueryCallback<T> {
    |_| -> _ { unreachable!() }
}

/// Everything [Generator] needs to mutate in order to compute a new row.
pub struct MutableState<'a, 'b, T: FieldElement, Q: QueryCallback<T>> {
    pub machines: Machines<'a, 'b, T>,
    pub query_callback: &'b mut Q,
}

pub struct WitnessGenerator<'a, 'b, T: FieldElement> {
    analyzed: &'a Analyzed<T>,
    fixed_col_values: &'b Vec<(String, VariablySizedColumn<T>)>,
    query_callback: &'b dyn QueryCallback<T>,
    external_witness_values: &'b [(String, Vec<T>)],
    stage: u8,
    challenges: BTreeMap<u64, T>,
}

impl<'a, 'b, T: FieldElement> WitnessGenerator<'a, 'b, T> {
    pub fn new(
        analyzed: &'a Analyzed<T>,
        fixed_col_values: &'b Vec<(String, VariablySizedColumn<T>)>,
        query_callback: &'b dyn QueryCallback<T>,
    ) -> Self {
        WitnessGenerator {
            analyzed,
            fixed_col_values,
            query_callback,
            external_witness_values: &[],
            stage: 0,
            challenges: BTreeMap::new(),
        }
    }

    pub fn with_external_witness_values(
        self,
        external_witness_values: &'b [(String, Vec<T>)],
    ) -> Self {
        WitnessGenerator {
            external_witness_values,
            ..self
        }
    }

    pub fn with_challenges(self, stage: u8, challenges: BTreeMap<u64, T>) -> Self {
        WitnessGenerator {
            stage,
            challenges,
            ..self
        }
    }

    /// Generates the committed polynomial values
    /// @returns the values (in source order) and the degree of the polynomials.
    pub fn generate(self) -> Vec<(String, Vec<T>)> {
        record_start(OUTER_CODE_NAME);
        let fixed = FixedData::new(
            self.analyzed,
            self.fixed_col_values,
            self.external_witness_values,
            self.challenges,
            self.stage,
        );
        let identities = self
            .analyzed
            .identities_with_inlined_intermediate_polynomials()
            .into_iter()
            .filter(|identity| {
                let discard = identity.expr_any(|expr| {
                    if let AlgebraicExpression::Challenge(challenge) = expr {
                        challenge.stage >= self.stage.into()
                    } else {
                        false
                    }
                });
                if discard {
                    log::debug!(
                        "Skipping identity that references challenge of later stage: {}",
                        identity
                    );
                }
                !discard
            })
            .collect::<Vec<_>>();

        // Removes identities like X * (X - 1) = 0 or [ A ] in [ BYTES ]
        // These are already captured in the range constraints.
        let (fixed, retained_identities) =
            global_constraints::set_global_constraints(fixed, &identities);
        let ExtractionOutput {
            mut machines,
            base_parts,
        } = if self.stage == 0 {
            machines::machine_extractor::split_out_machines(&fixed, retained_identities, self.stage)
        } else {
            // We expect later-stage witness columns to be accumulators for lookup and permutation arguments.
            // These don't behave like normal witness columns (e.g. in a block machine), and they might depend
            // on witness columns of more than one machine.
            // Therefore, we treat everything as one big machine. Also, we remove lookups and permutations,
            // as they are assumed to be handled in stage 0.
            let polynomial_identities = identities
                .iter()
                .filter(|identity| matches!(identity, Identity::Polynomial(_)))
                .collect::<Vec<_>>();
            ExtractionOutput {
                machines: Vec::new(),
                base_parts: MachineParts::new(
                    &fixed,
                    Default::default(),
                    polynomial_identities,
                    fixed.witness_cols.keys().collect::<HashSet<_>>(),
                    fixed.analyzed.prover_functions.iter().collect(),
                ),
            }
        };

        let mut query_callback = self.query_callback;
        let mut mutable_state = MutableState {
            machines: Machines::from(machines.iter_mut()),
            query_callback: &mut query_callback,
        };

        let generator = (!base_parts.witnesses.is_empty()).then(|| {
            let mut generator = Generator::new(
                "Main Machine".to_string(),
                &fixed,
                base_parts,
                // We could set the latch of the main VM here, but then we would have to detect it.
                // Instead, the main VM will be computed in one block, directly continuing into the
                // infinite loop after the first return.
                None,
            );

            generator.run(&mut mutable_state);
            generator
        });

        // Get columns from machines
        let mut columns = mutable_state
            .machines
            .take_witness_col_values(mutable_state.query_callback);
        if let Some(mut generator) = generator {
            columns.extend(generator.take_witness_col_values(&mut mutable_state));
        }

        record_end(OUTER_CODE_NAME);
        reset_and_print_profile_summary();

        // Order columns according to the order of declaration.
        let witness_cols = self
            .analyzed
            .committed_polys_in_source_order()
            .filter(|(symbol, _)| symbol.stage.unwrap_or_default() <= self.stage.into())
            .flat_map(|(p, _)| p.array_elements())
            .map(|(name, _id)| {
                let column = columns.remove(&name).unwrap();
                assert!(!column.is_empty());
                (name, column)
            })
            .collect::<Vec<_>>();

        log::debug!("Publics:");
        for (name, value) in extract_publics(&witness_cols, self.analyzed) {
            log::debug!(
                "  {name:>30}: {}",
                value
                    .map(|value| value.to_string())
                    .unwrap_or_else(|| "Not yet known at this stage".to_string())
            );
        }
        witness_cols
    }
}

pub fn extract_publics<T: FieldElement>(
    witness: &[(String, Vec<T>)],
    pil: &Analyzed<T>,
) -> Vec<(String, Option<T>)> {
    let witness = witness
        .iter()
        .map(|(name, col)| (name.clone(), col))
        .collect::<BTreeMap<_, _>>();
    pil.public_declarations_in_source_order()
        .map(|(name, public_declaration)| {
            let poly_name = &public_declaration.referenced_poly_name();
            let poly_index = public_declaration.index;
            let value = witness
                .get(poly_name)
                .map(|column| column[poly_index as usize]);
            ((*name).clone(), value)
        })
        .collect()
}

/// Data that is fixed for witness generation.
pub struct FixedData<'a, T: FieldElement> {
    analyzed: &'a Analyzed<T>,
    fixed_cols: FixedColumnMap<FixedColumn<'a, T>>,
    witness_cols: WitnessColumnMap<WitnessColumn<'a, T>>,
    column_by_name: HashMap<String, PolyID>,
    challenges: BTreeMap<u64, T>,
    global_range_constraints: GlobalConstraints<T>,
}

impl<'a, T: FieldElement> FixedData<'a, T> {
    /// Returns the common degree of a set or polynomials
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - the degree is not unique
    /// - the set of polynomials is empty
    /// - a declared polynomial does not have an explicit degree
    fn common_degree_range<'b>(&self, ids: impl IntoIterator<Item = &'b PolyID>) -> DegreeRange {
        let ids: HashSet<_> = ids.into_iter().collect();

        self.analyzed
            // get all definitions
            .definitions
            .iter()
            // only keep polynomials
            .filter_map(|(_, (symbol, _))| {
                matches!(symbol.kind, SymbolKind::Poly(_)).then_some(symbol)
            })
            // get all array elements and their degrees
            .flat_map(|symbol| symbol.array_elements().map(|(_, id)| (id, symbol.degree)))
            // only keep the ones matching our set
            .filter_map(|(id, degree)| ids.contains(&id).then_some(degree))
            // get the common degree
            .unique()
            .exactly_one()
            .unwrap_or_else(|_| panic!("expected all polynomials to have the same degree"))
            .unwrap()
    }

    pub fn new(
        analyzed: &'a Analyzed<T>,
        fixed_col_values: &'a [(String, VariablySizedColumn<T>)],
        external_witness_values: &'a [(String, Vec<T>)],
        challenges: BTreeMap<u64, T>,
        stage: u8,
    ) -> Self {
        let mut external_witness_values = external_witness_values
            .iter()
            .map(|(name, values)| (name.clone(), values))
            .collect::<BTreeMap<_, _>>();

        let witness_cols =
            WitnessColumnMap::from(analyzed.committed_polys_in_source_order().flat_map(
                |(poly, value)| {
                    poly.array_elements()
                        .map(|(name, poly_id)| {
                            let external_values = external_witness_values.remove(name.as_str());
                            // Remove any hint for witness columns of a later stage
                            // (because it might reference a challenge that is not available yet)
                            let value = if poly.stage.unwrap_or_default() <= stage.into() {
                                value.as_ref()
                            } else {
                                None
                            };
                            WitnessColumn::new(poly_id.id as usize, &name, value, external_values)
                        })
                        .collect::<Vec<_>>()
                },
            ));

        if !external_witness_values.is_empty() {
            let available_columns = witness_cols
                .iter()
                .map(|(_, witness)| &witness.poly.name)
                .collect::<Vec<_>>();
            panic!(
                "External witness values for non-existent columns: {:?}\nAvailable columns: {:?}",
                external_witness_values.keys(),
                available_columns
            );
        }

        let fixed_cols =
            FixedColumnMap::from(fixed_col_values.iter().map(|(n, v)| FixedColumn::new(n, v)));

        // The global range constraints are not set yet.
        let global_range_constraints = GlobalConstraints {
            witness_constraints: WitnessColumnMap::new(None, witness_cols.len()),
            fixed_constraints: FixedColumnMap::new(None, fixed_cols.len()),
        };

        FixedData {
            analyzed,
            fixed_cols,
            witness_cols,
            column_by_name: analyzed
                .definitions
                .iter()
                .filter(|(_, (symbol, _))| matches!(symbol.kind, SymbolKind::Poly(_)))
                .map(|(name, (symbol, _))| (name.clone(), symbol.into()))
                .collect(),
            challenges,
            global_range_constraints,
        }
    }

    pub fn with_global_range_constraints(
        self,
        global_range_constraints: GlobalConstraints<T>,
    ) -> Self {
        assert!(
            self.global_range_constraints
                .witness_constraints
                .values()
                .chain(self.global_range_constraints.fixed_constraints.values())
                .all(|c| c.is_none()),
            "range constraints already set"
        );

        Self {
            global_range_constraints,
            ..self
        }
    }

    pub fn global_range_constraints(&self) -> &GlobalConstraints<T> {
        &self.global_range_constraints
    }

    fn witness_map_with<V: Clone>(&self, initial_value: V) -> WitnessColumnMap<V> {
        WitnessColumnMap::new(initial_value, self.witness_cols.len())
    }

    fn column_name(&self, poly_id: &PolyID) -> &str {
        match poly_id.ptype {
            PolynomialType::Committed => &self.witness_cols[poly_id].poly.name,
            PolynomialType::Constant => &self.fixed_cols[poly_id].name,
            PolynomialType::Intermediate => unimplemented!(),
        }
    }

    pub fn try_column_by_name(&self, name: &str) -> Option<PolyID> {
        self.column_by_name.get(name).cloned()
    }

    fn external_witness(&self, row: DegreeType, column: &PolyID) -> Option<T> {
        self.witness_cols[column]
            .external_values
            .as_ref()
            .and_then(|v| {
                let row = row % v.len() as u64;
                v.get(row as usize).cloned()
            })
    }
}

pub struct FixedColumn<'a, T> {
    name: String,
    values: &'a VariablySizedColumn<T>,
}

impl<'a, T> FixedColumn<'a, T> {
    pub fn new(name: &'a str, values: &'a VariablySizedColumn<T>) -> FixedColumn<'a, T> {
        let name = name.to_string();
        FixedColumn { name, values }
    }

    pub fn values(&self, size: DegreeType) -> &[T] {
        self.values.get_by_size(size).unwrap()
    }

    pub fn values_max_size(&self) -> &[T] {
        let max_size = self.values.available_sizes().into_iter().max().unwrap() as DegreeType;
        self.values(max_size)
    }
}

#[derive(Debug)]
pub struct WitnessColumn<'a, T> {
    /// A polynomial reference that points to this column in the "current" row
    /// (i.e., the "next" flag is set to false).
    /// This is needed in situations where we want to update a cell when the
    /// update does not come from an identity (which also has an AlgebraicReference).
    poly: AlgebraicReference,
    /// The algebraic expression that points to this column in the current row.
    expr: AlgebraicExpression<T>,
    /// The prover query expression, if any.
    query: Option<&'a Expression>,
    /// A list of externally computed witness values, if any.
    /// The length of this list must be equal to the degree.
    external_values: Option<&'a Vec<T>>,
}

impl<'a, T> WitnessColumn<'a, T> {
    pub fn new(
        id: usize,
        name: &str,
        value: Option<&'a FunctionValueDefinition>,
        external_values: Option<&'a Vec<T>>,
    ) -> WitnessColumn<'a, T> {
        let query = if let Some(FunctionValueDefinition::Expression(TypedExpression {
            e:
                query @ Expression::LambdaExpression(
                    _,
                    LambdaExpression {
                        kind: FunctionKind::Query,
                        ..
                    },
                ),
            ..
        })) = value
        {
            Some(query)
        } else {
            None
        };
        let poly = AlgebraicReference {
            poly_id: PolyID {
                id: id as u64,
                ptype: PolynomialType::Committed,
            },
            name: name.to_string(),
            next: false,
        };
        let expr = AlgebraicExpression::Reference(poly.clone());
        WitnessColumn {
            poly,
            expr,
            query,
            external_values,
        }
    }
}

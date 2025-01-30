use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use bus_accumulator::generate_bus_accumulator_columns;
use data_structures::identity::{convert_identities, BusReceive, Identity};
use itertools::Itertools;
use machines::machine_extractor::MachineExtractor;
use multiplicity_column_generator::MultiplicityColumnGenerator;
use powdr_ast::analyzed::{
    AlgebraicExpression, AlgebraicReference, AlgebraicReferenceThin, Analyzed, DegreeRange,
    Expression, FunctionValueDefinition, Identity as AnalyzedIdentity, PolyID, PolynomialType,
    Symbol, SymbolKind, TypedExpression,
};
use powdr_ast::parsed::visitor::{AllChildren, ExpressionVisitable};
use powdr_ast::parsed::{FunctionKind, LambdaExpression};
use powdr_number::{DegreeType, FieldElement, KnownField};
use std::iter::once;

use crate::constant_evaluator::VariablySizedColumn;
use crate::witgen::data_structures::mutable_state::MutableState;

use self::data_structures::column_map::{FixedColumnMap, WitnessColumnMap};
pub use self::eval_result::{
    Constraint, Constraints, EvalError, EvalResult, EvalStatus, EvalValue, IncompleteCause,
};

use self::global_constraints::GlobalConstraints;
use self::machines::profiling::{record_end, record_start, reset_and_print_profile_summary};

mod affine_expression;
pub(crate) mod analysis;
mod block_processor;
mod bus_accumulator;
mod data_structures;
mod eval_result;
pub mod evaluators;
mod global_constraints;
mod identity_processor;
mod jit;
mod machines;
mod multiplicity_column_generator;
mod processor;
mod query_processor;
mod range_constraints;
mod rows;
mod sequence_iterator;
mod util;
mod vm_processor;

pub use affine_expression::{AffineExpression, AffineResult, AlgebraicVariable};
pub use evaluators::partial_expression_evaluator::{PartialExpressionEvaluator, SymbolicVariables};

static OUTER_CODE_NAME: &str = "witgen (outer code)";

// TODO change this so that it has functions
// input_from_channel, output_to_channel
// instead of processing strings.
// but we can only do that once we have fully removed the old query functions.
pub trait QueryCallback<T>: Fn(&str) -> Result<Option<T>, String> + Send + Sync {}
impl<T, F> QueryCallback<T> for F where F: Fn(&str) -> Result<Option<T>, String> + Send + Sync {}

pub use powdr_executor_utils::{WitgenCallback, WitgenCallbackFn};

pub struct WitgenCallbackContext<T> {
    /// TODO: all these fields probably don't need to be Arc anymore, since the
    /// Arc was moved one level up... but I have to investigate this further.
    fixed_col_values: Arc<Vec<(String, VariablySizedColumn<T>)>>,
    query_callback: Arc<dyn QueryCallback<T>>,
}

impl<T: FieldElement> WitgenCallbackContext<T> {
    pub fn new(
        fixed_col_values: Arc<Vec<(String, VariablySizedColumn<T>)>>,
        query_callback: Option<Arc<dyn QueryCallback<T>>>,
    ) -> Self {
        let query_callback = query_callback.unwrap_or_else(|| Arc::new(unused_query_callback()));
        Self {
            fixed_col_values,
            query_callback,
        }
    }

    pub fn select_fixed_columns(
        &self,
        pil: &Analyzed<T>,
        size: DegreeType,
    ) -> Vec<(String, VariablySizedColumn<T>)> {
        // The provided PIL might only contain a subset of all fixed columns.
        let fixed_column_names = pil
            .constant_polys_in_source_order()
            .flat_map(|(symbol, _)| symbol.array_elements())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        // Select the columns in the current PIL and select the right size.
        self.fixed_col_values
            .iter()
            .filter(|(n, _)| fixed_column_names.contains(n))
            .map(|(n, v)| (n.clone(), v.get_by_size(size).unwrap().to_vec().into()))
            .collect()
    }

    /// Computes the next-stage witness, given the current witness and challenges.
    /// All columns in the provided PIL are expected to have the same size.
    /// Typically, this function should be called once per machine.
    pub fn next_stage_witness(
        &self,
        pil: &Analyzed<T>,
        current_witness: &[(String, Vec<T>)],
        challenges: BTreeMap<u64, T>,
        stage: u8,
    ) -> Vec<(String, Vec<T>)> {
        let has_phantom_bus_sends = pil
            .identities
            .iter()
            .any(|identity| matches!(identity, AnalyzedIdentity::PhantomBusInteraction(_)));

        let supports_field = match T::known_field().unwrap() {
            KnownField::GoldilocksField
            | KnownField::BabyBearField
            | KnownField::KoalaBearField
            | KnownField::Mersenne31Field => true,
            KnownField::Bn254Field => false,
        };

        if has_phantom_bus_sends && supports_field {
            log::debug!("Using hand-written bus witgen.");
            assert_eq!(stage, 1);
            let bus_columns = generate_bus_accumulator_columns(
                pil,
                current_witness,
                &self.fixed_col_values,
                challenges,
            );

            current_witness.iter().cloned().chain(bus_columns).collect()
        } else {
            log::debug!("Using automatic stage-1 witgen.");
            let size = current_witness.iter().next().unwrap().1.len() as DegreeType;
            let fixed_col_values = self.select_fixed_columns(pil, size);
            WitnessGenerator::new(pil, &fixed_col_values, &*self.query_callback)
                .with_external_witness_values(current_witness)
                .with_challenges(stage, challenges)
                .generate()
        }
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
        let fixed = fixed.filter_identities(|fixed, identity| {
            let references_later_stage_challenge = identity.expr_any(|expr| {
                if let AlgebraicExpression::Challenge(challenge) = expr {
                    challenge.stage >= self.stage.into()
                } else {
                    false
                }
            });
            let references_later_stage_witness = fixed
                .polynomial_references(identity)
                .into_iter()
                .any(|poly_id| {
                    (poly_id.ptype == PolynomialType::Committed)
                        && fixed.witness_cols[&poly_id].stage > self.stage as u32
                });

            let discard = references_later_stage_challenge || references_later_stage_witness;

            if discard {
                log::trace!("Skipping identity that references later-stage items: {identity}",);
            }
            !discard
        });

        // Removes identities like X * (X - 1) = 0 or [ A ] in [ BYTES ]
        // These are already captured in the range constraints.
        let fixed = global_constraints::set_global_constraints(fixed);
        let machines = MachineExtractor::new(&fixed).split_out_machines();

        // Run main machine and extract columns from all machines.
        let columns = MutableState::new(machines.into_iter(), &self.query_callback).run();

        let publics = extract_publics(&columns, self.analyzed);
        if !publics.is_empty() {
            log::debug!("Publics:");
        }
        for (name, value) in publics.iter() {
            log::debug!(
                "  {name:>30}: {}",
                value
                    .map(|value| value.to_string())
                    .unwrap_or_else(|| "Not yet known at this stage".to_string())
            );
        }

        let mut columns = if self.stage == 0 {
            // Multiplicities should be computed in the first stage
            MultiplicityColumnGenerator::new(&fixed).generate(columns, publics)
        } else {
            columns
        };

        record_end(OUTER_CODE_NAME);
        reset_and_print_profile_summary();

        // Order columns according to the order of declaration.
        let witness_cols = self
            .analyzed
            .committed_polys_in_source_order()
            .filter(|(symbol, _)| symbol.stage.unwrap_or_default() <= self.stage.into())
            .flat_map(|(p, _)| p.array_elements())
            .map(|(name, _id)| {
                let column = columns
                    .remove(&name)
                    .unwrap_or_else(|| panic!("No machine generated witness for column: {name}"));
                (name, column)
            })
            .collect::<Vec<_>>();
        witness_cols
    }
}

pub fn extract_publics<'a, T, I>(witness: I, pil: &Analyzed<T>) -> BTreeMap<String, Option<T>>
where
    T: FieldElement,
    I: IntoIterator<Item = (&'a String, &'a Vec<T>)>,
{
    let witness = witness
        .into_iter()
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

/// Data that is fixed for witness generation for a certain proof stage
/// (i.e., a call to [WitnessGenerator::generate]).
pub struct FixedData<'a, T: FieldElement> {
    analyzed: &'a Analyzed<T>,
    /// The identities to be processed, not including those that are fully
    /// represented by the global range constraints (e.g. [X] in [BYTE]).
    identities: Vec<Identity<T>>,
    bus_receives: BTreeMap<T, BusReceive<T>>,
    fixed_cols: FixedColumnMap<FixedColumn<'a, T>>,
    witness_cols: WitnessColumnMap<WitnessColumn<'a, T>>,
    column_by_name: HashMap<String, PolyID>,
    challenges: BTreeMap<u64, T>,
    global_range_constraints: GlobalConstraints<T>,
    intermediate_definitions: BTreeMap<AlgebraicReferenceThin, AlgebraicExpression<T>>,
    stage: u8,
}

impl<'a, T: FieldElement> FixedData<'a, T> {
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

        let intermediate_definitions = analyzed.intermediate_definitions();

        let witness_cols =
            WitnessColumnMap::from(analyzed.committed_polys_in_source_order().flat_map(
                |(symbol, value)| {
                    symbol
                        .array_elements()
                        .map(|(name, poly_id)| {
                            let external_values = external_witness_values.remove(name.as_str());
                            // Remove any hint for witness columns of a later stage
                            // (because it might reference a challenge that is not available yet)
                            let col_stage = symbol.stage.unwrap_or_default();
                            let value = if col_stage <= stage.into() {
                                value.as_ref()
                            } else {
                                None
                            };
                            WitnessColumn::new(
                                poly_id.id as usize,
                                &name,
                                value,
                                external_values,
                                col_stage,
                            )
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

        let (mut identities, bus_receives) = convert_identities(analyzed);
        if stage > 0 {
            // Unfortunately, with the composite backend, we won't have the matching
            // receives in other machines, which can lead to panics. Machine calls
            // should not be executed in the second stage anyway.
            // TODO: Probably we can remove this once we handle "dynamic" busses, because
            // we need to deal with the case that sends can't be matched statically anyway.
            identities.retain(|identity| !matches!(identity, Identity::BusSend(_)));
        }

        FixedData {
            analyzed,
            identities,
            bus_receives,
            fixed_cols,
            witness_cols,
            column_by_name: analyzed
                .definitions
                .iter()
                .filter(|(_, (symbol, _))| matches!(symbol.kind, SymbolKind::Poly(_)))
                .flat_map(|(_, (symbol, _))| symbol.array_elements())
                .collect(),
            challenges,
            global_range_constraints,
            intermediate_definitions,
            stage,
        }
    }

    /// Allows the caller to filter out identities based on some criteria.
    /// The callback has access the fixed data and the identity.
    /// Consumes fixed data and returns a new instance.
    pub fn filter_identities(self, f: impl Fn(&FixedData<T>, &Identity<T>) -> bool) -> Self {
        let keep = self
            .identities
            .iter()
            .map(|id| f(&self, id))
            .collect::<Vec<_>>();
        let identities = self
            .identities
            .into_iter()
            .zip_eq(keep)
            .filter(|(_, keep)| *keep)
            .map(|(id, _)| id)
            .collect();
        Self { identities, ..self }
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

    fn all_poly_symbols(&self) -> impl Iterator<Item = &Symbol> {
        self.analyzed
            .definitions
            .iter()
            .filter_map(|(_, (symbol, _))| {
                matches!(symbol.kind, SymbolKind::Poly(_)).then_some(symbol)
            })
    }

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

        // Iterator of (id, Option<DegreeRange>), with only the requested ids.
        let filtered_ids_and_degrees = || {
            self.all_poly_symbols()
                .flat_map(|symbol| symbol.array_elements().map(|(_, id)| (id, symbol.degree)))
                .filter_map(|(id, degree)| ids.contains(&id).then_some((id, degree)))
        };

        filtered_ids_and_degrees()
            .map(|(_, degree_range)| degree_range)
            .unique()
            .exactly_one()
            .unwrap_or_else(|_| {
                log::error!("The following columns have different degree ranges:");
                for (id, degree) in filtered_ids_and_degrees() {
                    log::error!("  {}: {:?}", self.column_name(&id), degree);
                }
                panic!("Expected all columns to have the same degree")
            })
            .unwrap()
    }

    /// Returns whether all columns have the same static degree.
    fn is_monolithic(&self) -> bool {
        match self
            .all_poly_symbols()
            .map(|symbol| symbol.degree.unwrap())
            .unique()
            .exactly_one()
        {
            Ok(degree) => degree.is_unique(),
            _ => false,
        }
    }

    pub fn stage(&self) -> u8 {
        self.stage
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

    fn witnesses_until_current_stage(&self) -> impl Iterator<Item = PolyID> + '_ {
        self.witness_cols
            .iter()
            .filter(|(_, col)| col.stage <= self.stage as u32)
            .map(|(poly_id, _)| poly_id)
    }

    /// Finds all referenced witness or fixed columns,
    /// including those referenced via intermediate columns.
    fn polynomial_references(
        &self,
        expr: &impl AllChildren<AlgebraicExpression<T>>,
    ) -> HashSet<PolyID> {
        polynomial_references(expr, &self.intermediate_definitions)
    }
}

pub struct FixedColumn<'a, T> {
    name: String,
    values: &'a VariablySizedColumn<T>,
}

impl<'a, T: Copy> FixedColumn<'a, T> {
    pub fn new(name: &'a str, values: &'a VariablySizedColumn<T>) -> FixedColumn<'a, T> {
        let name = name.to_string();
        FixedColumn { name, values }
    }

    pub fn values(&self, size: DegreeType) -> &[T] {
        self.values.get_by_size(size).unwrap_or_else(|| {
            panic!(
                "Fixed column {} does not have a value for size {}. Available sizes: {:?}",
                self.name,
                size,
                self.values.available_sizes()
            )
        })
    }

    pub fn values_max_size(&self) -> &[T] {
        let max_size = self.values.available_sizes().into_iter().max().unwrap() as DegreeType;
        self.values(max_size)
    }

    pub fn has_constant_inner_value(&self) -> Option<T> {
        *self.values.has_constant_inner_value()
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
    /// The stage of the column.
    stage: u32,
}

impl<'a, T> WitnessColumn<'a, T> {
    pub fn new(
        id: usize,
        name: &str,
        value: Option<&'a FunctionValueDefinition>,
        external_values: Option<&'a Vec<T>>,
        stage: u32,
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
            stage,
        }
    }
}

/// Finds all referenced witness or fixed columns,
/// including those referenced via intermediate columns.
fn polynomial_references<T>(
    expr: &impl AllChildren<AlgebraicExpression<T>>,
    intermediate_definitions: &BTreeMap<AlgebraicReferenceThin, AlgebraicExpression<T>>,
) -> HashSet<PolyID> {
    let mut cache = BTreeMap::new();
    polynomial_references_with_cache(expr, intermediate_definitions, &mut cache)
}

/// Like [polynomial_references], but with a cache for intermediate results.
/// This avoids visiting the same intermediate column multiple times, which can lead
/// to exponential complexity for some expressions.
fn polynomial_references_with_cache<T>(
    expr: &impl AllChildren<AlgebraicExpression<T>>,
    intermediate_definitions: &BTreeMap<AlgebraicReferenceThin, AlgebraicExpression<T>>,
    intermediates_cache: &mut BTreeMap<AlgebraicReferenceThin, HashSet<PolyID>>,
) -> HashSet<PolyID> {
    expr.all_children()
        .flat_map(|child| {
            if let AlgebraicExpression::Reference(poly_ref) = child {
                match poly_ref.poly_id.ptype {
                    PolynomialType::Committed | PolynomialType::Constant => {
                        once(poly_ref.poly_id).collect()
                    }
                    PolynomialType::Intermediate => {
                        let poly_ref = poly_ref.to_thin();
                        intermediates_cache
                            .get(&poly_ref)
                            .cloned()
                            .unwrap_or_else(|| {
                                let intermediate_expr = &intermediate_definitions[&poly_ref];
                                let refs = polynomial_references_with_cache(
                                    intermediate_expr,
                                    intermediate_definitions,
                                    intermediates_cache,
                                );
                                intermediates_cache.insert(poly_ref, refs.clone());
                                refs
                            })
                    }
                }
            } else {
                HashSet::new()
            }
        })
        .collect()
}

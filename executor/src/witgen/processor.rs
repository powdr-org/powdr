use std::collections::BTreeMap;

use itertools::Itertools;
use powdr_ast::analyzed::PolynomialType;
use powdr_ast::analyzed::{AlgebraicExpression as Expression, AlgebraicReference, PolyID};

use powdr_number::{DegreeType, FieldElement};

use crate::witgen::affine_expression::AlgebraicVariable;
use crate::witgen::data_structures::mutable_state::MutableState;
use crate::witgen::{query_processor::QueryProcessor, util::try_to_simple_poly, Constraint};
use crate::Identity;

use super::machines::{Connection, LookupCell, MachineParts};
use super::{
    affine_expression::AffineExpression,
    data_structures::{
        column_map::WitnessColumnMap, copy_constraints::CopyConstraints,
        finalizable_data::FinalizableData,
    },
    identity_processor::IdentityProcessor,
    rows::{Row, RowIndex, RowPair, RowUpdater, UnknownStrategy},
    Constraints, EvalError, EvalValue, IncompleteCause, QueryCallback,
};
use super::{EvalResult, FixedData};

pub type Left<'a, T> = Vec<AffineExpression<AlgebraicVariable<'a>, T>>;

/// The data mutated by the processor
pub(crate) struct SolverState<'a, T: FieldElement> {
    /// The block of trace cells
    pub block: FinalizableData<T>,
    /// The values of publics
    pub publics: BTreeMap<&'a str, T>,
}

impl<'a, T: FieldElement> SolverState<'a, T> {
    pub fn new(block: FinalizableData<T>, publics: BTreeMap<&'a str, T>) -> Self {
        Self { block, publics }
    }

    pub fn without_publics(block: FinalizableData<T>) -> Self {
        Self {
            block,
            publics: BTreeMap::new(),
        }
    }
}

/// Data needed to handle an outer query.
#[derive(Clone)]
pub struct OuterQuery<'a, 'b, T: FieldElement> {
    /// Rows of the calling machine.
    pub caller_rows: &'b RowPair<'b, 'a, T>,
    /// Connection.
    pub connection: Connection<'a, T>,
    /// The left side of the connection, evaluated.
    pub left: Left<'a, T>,
}

impl<'a, 'b, T: FieldElement> OuterQuery<'a, 'b, T> {
    pub fn new(caller_rows: &'b RowPair<'b, 'a, T>, connection: Connection<'a, T>) -> Self {
        // Evaluate once, for performance reasons.
        let left = connection
            .left
            .expressions
            .iter()
            .map(|e| caller_rows.evaluate(e).unwrap())
            .collect();
        Self {
            caller_rows,
            connection,
            left,
        }
    }

    pub fn is_complete(&self) -> bool {
        self.left.iter().all(|l| l.is_constant())
    }

    /// Helper functon to convert an `OuterQuery` into a list of `LookupCell`s
    /// to be used by `Machine::process_lookup_direct`.
    pub fn prepare_for_direct_lookup<'c>(
        &self,
        input_output_data: &'c mut [T],
    ) -> Vec<LookupCell<'c, T>> {
        self.left
            .iter()
            .zip_eq(input_output_data.iter_mut())
            .map(|(l, d)| {
                if let Some(value) = l.constant_value() {
                    *d = value;
                    LookupCell::Input(d)
                } else {
                    LookupCell::Output(d)
                }
            })
            .collect::<Vec<_>>()
    }

    /// Helper function to turn the result of a direct lookup into an `EvalResult`,
    /// as used by `Machine::process_plookup`.
    ///
    /// Note that this function assumes that the lookup was successful and complete.
    pub fn direct_lookup_to_eval_result(&self, input_output_data: Vec<T>) -> EvalResult<'a, T> {
        let mut result = EvalValue::complete(vec![]);
        for (l, v) in self.left.iter().zip(input_output_data) {
            if !l.is_constant() {
                let evaluated = l.clone() - v.into();
                match evaluated.solve() {
                    Ok(constraints) => {
                        result.combine(constraints);
                    }
                    Err(_) => {
                        // Fail the whole lookup
                        return Err(EvalError::ConstraintUnsatisfiable(format!(
                            "Constraint is invalid ({l} != {v}).",
                        )));
                    }
                }
            }
        }
        Ok(result)
    }
}

pub struct IdentityResult {
    /// Whether any progress was made by processing the identity
    pub progress: bool,
    /// Whether the identity is complete (i.e. all referenced values are known)
    pub is_complete: bool,
}

/// A basic processor that holds a set of rows and knows how to process identities and queries
/// on any given row.
/// The lifetimes mean the following:
/// - `'a`: The duration of the entire witness generation (e.g. references to identities)
/// - `'c`: The duration of this Processor's lifetime (e.g. the reference to the identity processor)
pub struct Processor<'a, 'c, T: FieldElement, Q: QueryCallback<T>> {
    /// The global index of the first row of [Processor::data].
    row_offset: RowIndex,
    /// The rows that are being processed.
    data: FinalizableData<T>,
    /// The values of the publics
    publics: BTreeMap<&'a str, T>,
    /// The mutable state
    mutable_state: &'c MutableState<'a, T, Q>,
    /// The fixed data (containing information about all columns)
    fixed_data: &'a FixedData<'a, T>,
    /// The machine parts (witness columns, identities, fixed data)
    parts: &'c MachineParts<'a, T>,
    /// Whether a given witness column is relevant for this machine (faster than doing a contains check on witness_cols)
    is_relevant_witness: WitnessColumnMap<bool>,
    /// Relevant witness columns that have a prover query function attached.
    prover_query_witnesses: Vec<PolyID>,
    /// Which prover functions were successfully executed on which row.
    processed_prover_functions: ProcessedProverFunctions,
    /// The outer query, if any. If there is none, processing an outer query will fail.
    outer_query: Option<OuterQuery<'a, 'c, T>>,
    inputs: Vec<(PolyID, T)>,
    previously_set_inputs: BTreeMap<PolyID, usize>,
    copy_constraints: CopyConstraints<(PolyID, RowIndex)>,
    size: DegreeType,
}

impl<'a, 'c, T: FieldElement, Q: QueryCallback<T>> Processor<'a, 'c, T, Q> {
    pub fn new(
        row_offset: RowIndex,
        mutable_data: SolverState<'a, T>,
        mutable_state: &'c MutableState<'a, T, Q>,
        fixed_data: &'a FixedData<'a, T>,
        parts: &'c MachineParts<'a, T>,
        size: DegreeType,
    ) -> Self {
        let is_relevant_witness = WitnessColumnMap::from(
            fixed_data
                .witness_cols
                .keys()
                .map(|poly_id| parts.witnesses.contains(&poly_id)),
        );
        let prover_query_witnesses = fixed_data
            .witness_cols
            .iter()
            .filter(|(poly_id, col)| parts.witnesses.contains(poly_id) && col.query.is_some())
            .map(|(poly_id, _)| poly_id)
            .collect();

        Self {
            row_offset,
            data: mutable_data.block,
            publics: mutable_data.publics,
            mutable_state,
            fixed_data,
            parts,
            is_relevant_witness,
            prover_query_witnesses,
            processed_prover_functions: ProcessedProverFunctions::new(parts.prover_functions.len()),
            outer_query: None,
            inputs: Vec::new(),
            previously_set_inputs: BTreeMap::new(),
            // TODO(#1333): Get copy constraints from PIL.
            copy_constraints: Default::default(),
            size,
        }
    }

    pub fn with_outer_query(self, outer_query: OuterQuery<'a, 'c, T>) -> Processor<'a, 'c, T, Q> {
        log::trace!("  Extracting inputs:");
        let mut inputs = vec![];
        for (l, r) in outer_query
            .left
            .iter()
            .zip(&outer_query.connection.right.expressions)
        {
            if let Some(right_poly) = try_to_simple_poly(r).map(|p| p.poly_id) {
                if let Some(l) = l.constant_value() {
                    log::trace!("    {} = {}", r, l);
                    inputs.push((right_poly, l));
                }
            }
        }
        Processor {
            outer_query: Some(outer_query),
            inputs,
            ..self
        }
    }

    pub fn set_size(&mut self, size: DegreeType) {
        self.size = size;
    }

    pub fn finished_outer_query(&self) -> bool {
        self.outer_query
            .as_ref()
            .map(|outer_query| outer_query.is_complete())
            .unwrap_or(true)
    }

    /// Returns the updated data and values for publics
    pub fn finish(self) -> SolverState<'a, T> {
        SolverState {
            block: self.data,
            publics: self.publics,
        }
    }

    pub fn latch_value(&self, row_index: usize) -> Option<bool> {
        let row_pair = RowPair::from_single_row(
            &self.data[row_index],
            self.row_offset + row_index as u64,
            &self.publics,
            self.fixed_data,
            UnknownStrategy::Unknown,
            self.size,
        );
        self.outer_query
            .as_ref()
            .and_then(|outer_query| {
                row_pair
                    .evaluate(&outer_query.connection.right.selector)
                    .ok()
            })
            .and_then(|l| l.constant_value())
            .map(|l| l.is_one())
    }

    pub fn process_queries(&mut self, row_index: usize) -> Result<bool, EvalError<T>> {
        let mut query_processor = QueryProcessor::new(
            self.fixed_data,
            self.mutable_state.query_callback(),
            self.size,
        );

        let global_row_index = self.row_offset + row_index as u64;
        let row_pair = RowPair::new(
            &self.data[row_index],
            &self.data[row_index + 1],
            global_row_index,
            &self.publics,
            self.fixed_data,
            UnknownStrategy::Unknown,
            self.size,
        );
        let mut updates = EvalValue::complete(vec![]);

        for (i, fun) in self.parts.prover_functions.iter().enumerate() {
            if !self.processed_prover_functions.has_run(row_index, i) {
                let r = query_processor.process_prover_function(&row_pair, fun)?;
                if r.is_complete() {
                    updates.combine(r);
                    self.processed_prover_functions.mark_as_run(row_index, i);
                }
            }
        }

        for poly_id in &self.prover_query_witnesses {
            if let Some(r) = query_processor.process_query(&row_pair, poly_id) {
                updates.combine(r?);
            }
        }
        Ok(self.apply_updates(row_index, &updates, || "queries".to_string()))
    }

    /// Given a row and identity index, computes any updates and applies them.
    /// @returns the `IdentityResult`.
    pub fn process_identity(
        &mut self,
        row_index: usize,
        identity: &'a Identity<T>,
        unknown_strategy: UnknownStrategy,
    ) -> Result<IdentityResult, EvalError<T>> {
        // Create row pair
        let global_row_index = self.row_offset + row_index as u64;
        let row_pair = RowPair::new(
            &self.data[row_index],
            &self.data[row_index + 1],
            global_row_index,
            &self.publics,
            self.fixed_data,
            unknown_strategy,
            self.size,
        );

        // Compute updates
        let mut identity_processor = IdentityProcessor::new(self.mutable_state);
        let updates = identity_processor
            .process_identity(identity, &row_pair)
            .map_err(|e| -> EvalError<T> {
                let mut error = format!(
                    r"Error in identity: {identity}
Known values in current row (local: {row_index}, global {global_row_index}):
{}
",
                    self.data[row_index].render_values(false, self.parts)
                );
                if identity.contains_next_ref() {
                    error += &format!(
                        "Known values in next row (local: {}, global {}):\n{}\n",
                        row_index + 1,
                        global_row_index + 1,
                        self.data[row_index + 1].render_values(false, self.parts)
                    );
                }
                error += &format!("   => Error: {e}");
                error.into()
            })?;

        if unknown_strategy == UnknownStrategy::Zero {
            assert!(updates.constraints.is_empty());
            assert!(!updates.side_effect);
            return Ok(IdentityResult {
                progress: false,
                is_complete: false,
            });
        }

        Ok(IdentityResult {
            progress: self.apply_updates(row_index, &updates, || identity.to_string())
                || updates.side_effect,
            is_complete: updates.is_complete(),
        })
    }

    pub fn process_outer_query(
        &mut self,
        row_index: usize,
    ) -> Result<(bool, Constraints<AlgebraicVariable<'a>, T>), EvalError<T>> {
        let mut progress = false;
        let right = self.outer_query.as_ref().unwrap().connection.right;
        progress |= self
            .set_value(row_index, &right.selector, T::one(), || {
                "Set selector to 1".to_string()
            })
            .unwrap_or(false);

        let outer_query = self
            .outer_query
            .as_ref()
            .expect("Asked to process outer query, but it was not set!");

        let row_pair = RowPair::new(
            &self.data[row_index],
            &self.data[row_index + 1],
            self.row_offset + row_index as u64,
            &self.publics,
            self.fixed_data,
            UnknownStrategy::Unknown,
            self.size,
        );

        let mut identity_processor = IdentityProcessor::new(self.mutable_state);
        let updates = identity_processor
            .process_link(outer_query, &row_pair)
            .map_err(|e| {
                log::warn!("Error in outer query: {e}");
                log::warn!("Some of the following entries could not be matched:");
                for (l, r) in outer_query.left.iter().zip(right.expressions.iter()) {
                    if let Ok(r) = row_pair.evaluate(r) {
                        log::warn!("  => {} = {}", l, r);
                    }
                }
                e
            })?;

        progress |= self.apply_updates(row_index, &updates, || "outer query".to_string());

        let outer_assignments = updates
            .constraints
            .into_iter()
            .filter(|(var, update)| match (var, update) {
                (AlgebraicVariable::Column(poly), Constraint::Assignment(_)) => {
                    !self.is_relevant_witness[&poly.poly_id]
                }
                (AlgebraicVariable::Public(_), Constraint::Assignment(_)) => unimplemented!(),
                // Range constraints are currently not communicated between callee and caller.
                (_, Constraint::RangeConstraint(_)) => false,
            })
            .collect::<Vec<_>>();

        Ok((progress, outer_assignments))
    }

    /// Sets the inputs to the values given in [VmProcessor::inputs] if they are not already set.
    /// Typically, inputs will have a constraint of the form: `((1 - instr__jump_to_operation) * (_input' - _input)) = 0;`
    /// So, once the value of `_input` is set, this function will do nothing until the next reset instruction.
    /// However, if `_input` does become unconstrained, we need to undo all changes we've done so far.
    /// For this reason, we keep track of all changes we've done to inputs in [Processor::previously_set_inputs].
    pub fn set_inputs_if_unset(&mut self, row_index: usize) -> bool {
        let mut input_updates = EvalValue::complete(vec![]);
        for (poly_id, value) in self.inputs.iter() {
            if !self.data[row_index].value_is_known(poly_id) {
                input_updates.combine(EvalValue::complete(vec![(
                    AlgebraicVariable::Column(&self.fixed_data.witness_cols[poly_id].poly),
                    Constraint::Assignment(*value),
                )]));
            }
        }

        for (var, _) in &input_updates.constraints {
            let poly = var.try_as_column().expect("Expected column");
            let poly_id = &poly.poly_id;
            if let Some(start_row) = self.previously_set_inputs.remove(poly_id) {
                log::trace!(
                    "    Resetting previously set inputs for column: {}",
                    self.fixed_data.column_name(poly_id)
                );
                for row_index in start_row..row_index {
                    self.data[row_index].set_cell_unknown(poly_id);
                }
            }
        }
        for (var, _) in &input_updates.constraints {
            let poly = var.try_as_column().expect("Expected column");
            self.previously_set_inputs.insert(poly.poly_id, row_index);
        }
        self.apply_updates(row_index, &input_updates, || "inputs".to_string())
    }

    /// Sets the value of a given expression, in a given row.
    pub fn set_value(
        &mut self,
        row_index: usize,
        expression: &'a Expression<T>,
        value: T,
        name: impl Fn() -> String,
    ) -> Result<bool, IncompleteCause<AlgebraicVariable<'a>>> {
        let row_pair = RowPair::new(
            &self.data[row_index],
            &self.data[row_index + 1],
            self.row_offset + row_index as u64,
            &self.publics,
            self.fixed_data,
            UnknownStrategy::Unknown,
            self.size,
        );
        let affine_expression = row_pair.evaluate(expression)?;
        let updates = (affine_expression - value.into())
            .solve_with_range_constraints(&row_pair)
            .unwrap();
        Ok(self.apply_updates(row_index, &updates, name))
    }

    fn apply_updates(
        &mut self,
        row_index: usize,
        updates: &EvalValue<AlgebraicVariable<'a>, T>,
        source_name: impl Fn() -> String,
    ) -> bool {
        if updates.constraints.is_empty() {
            return false;
        }

        log::trace!("    Updates from: {}", source_name());

        let mut progress = false;
        for (var, c) in &updates.constraints {
            match var {
                AlgebraicVariable::Public(name) => {
                    if let Constraint::Assignment(v) = c {
                        // There should be only few publics, so this can be logged with info.
                        log::info!("      => {} (public) = {}", name, v);
                        assert!(
                            self.publics.insert(name, *v).is_none(),
                            "value was already set!"
                        );
                    }
                }
                AlgebraicVariable::Column(poly) => {
                    if self.parts.witnesses.contains(&poly.poly_id) {
                        let (current, next) = self.data.mutable_row_pair(row_index);
                        let mut row_updater =
                            RowUpdater::new(current, next, self.row_offset + row_index as u64);
                        row_updater.apply_update(poly, c);
                        progress = true;
                        self.propagate_along_copy_constraints(row_index, poly, c);
                    } else if let Constraint::Assignment(v) = c {
                        let left = &mut self.outer_query.as_mut().unwrap().left;
                        log::trace!("      => {} (outer) = {}", poly, v);
                        for l in left.iter_mut() {
                            l.assign(*var, *v);
                        }
                        progress = true;
                    };
                }
            }
        }

        progress
    }

    fn propagate_along_copy_constraints(
        &mut self,
        row_index: usize,
        poly: &AlgebraicReference,
        constraint: &Constraint<T>,
    ) {
        if self.copy_constraints.is_empty() {
            return;
        }
        if let Constraint::Assignment(v) = constraint {
            // If we do an assignment, propagate the value to any other cell that is
            // copy-constrained to the current cell.
            let row = self.row_offset + row_index + poly.next as usize;

            // Have to materialize the other cells to please the borrow checker...
            let others = self
                .copy_constraints
                .iter_equivalence_class((poly.poly_id, row))
                .skip(1)
                .collect::<Vec<_>>();
            for (other_poly, other_row) in others {
                if other_poly.ptype != PolynomialType::Committed {
                    unimplemented!(
                        "Copy constraints to fixed columns are not yet supported (#1335)!"
                    );
                }
                let expression = &self.fixed_data.witness_cols[&other_poly].expr;
                let local_index = other_row.to_local(&self.row_offset);
                self.set_value(local_index, expression, *v, || {
                    format!(
                        "Copy constraint: {} (Row {}) -> {} (Row {})",
                        self.fixed_data.column_name(&poly.poly_id),
                        row,
                        self.fixed_data.column_name(&other_poly),
                        other_row
                    )
                })
                .unwrap();
            }
        }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn finalize_range(&mut self, range: std::ops::Range<usize>) {
        assert!(
            self.copy_constraints.is_empty(),
            "Machines with copy constraints should not be finalized while being processed."
        );
        self.data.finalize_range(range);
    }

    pub fn row(&self, i: usize) -> &Row<T> {
        &self.data[i]
    }

    pub fn has_outer_query(&self) -> bool {
        self.outer_query.is_some()
    }

    /// Sets the ith row, extending the data if necessary.
    pub fn set_row(&mut self, i: usize, row: Row<T>) {
        if i < self.data.len() {
            self.data[i] = row;
        } else {
            assert_eq!(i, self.data.len());
            self.data.push(row);
        }
    }

    /// Checks whether a given identity is satisfied on a proposed row.
    pub fn check_row_pair(
        &mut self,
        row_index: usize,
        proposed_row: &Row<T>,
        identity: &'a Identity<T>,
        // This could be computed from the identity, but should be pre-computed for performance reasons.
        has_next_reference: bool,
    ) -> bool {
        let mut identity_processor = IdentityProcessor::new(self.mutable_state);
        let row_pair = match has_next_reference {
            // Check whether identities with a reference to the next row are satisfied
            // when applied to the previous row and the proposed row.
            true => {
                assert!(row_index > 0);
                RowPair::new(
                    &self.data[row_index - 1],
                    proposed_row,
                    self.row_offset + (row_index - 1) as DegreeType,
                    &self.publics,
                    self.fixed_data,
                    UnknownStrategy::Zero,
                    self.size,
                )
            }
            // Check whether identities without a reference to the next row are satisfied
            // when applied to the proposed row.
            // Because we never access the next row, we can use [RowPair::from_single_row] here.
            false => RowPair::from_single_row(
                proposed_row,
                self.row_offset + row_index as DegreeType,
                &self.publics,
                self.fixed_data,
                UnknownStrategy::Zero,
                self.size,
            ),
        };

        if identity_processor
            .process_identity(identity, &row_pair)
            .is_err()
        {
            log::debug!(
                "Previous {}",
                self.data[row_index - 1].render_values(true, self.parts)
            );
            log::debug!(
                "Proposed {:?}",
                proposed_row.render_values(true, self.parts)
            );
            log::debug!("Failed on identity: {}", identity);

            return false;
        }
        true
    }
}

struct ProcessedProverFunctions {
    data: Vec<u8>,
    function_count: usize,
}

impl ProcessedProverFunctions {
    pub fn new(prover_function_count: usize) -> Self {
        Self {
            data: vec![],
            function_count: prover_function_count,
        }
    }

    pub fn has_run(&self, row_index: usize, function_index: usize) -> bool {
        let (el, bit) = self.index_for(row_index, function_index);
        self.data.get(el).is_some_and(|byte| byte & (1 << bit) != 0)
    }

    pub fn mark_as_run(&mut self, row_index: usize, function_index: usize) {
        let (el, bit) = self.index_for(row_index, function_index);
        if el >= self.data.len() {
            self.data.resize(el + 1, 0);
        }
        self.data[el] |= 1 << bit;
    }

    fn index_for(&self, row_index: usize, function_index: usize) -> (usize, usize) {
        let index = row_index * self.function_count + function_index;
        (index / 8, index % 8)
    }
}

use std::collections::{BTreeMap, HashSet};

use powdr_ast::{
    analyzed::{AlgebraicExpression as Expression, AlgebraicReference, Identity, PolyID},
    parsed::SelectedExpressions,
};
use powdr_number::{DegreeType, FieldElement};

use crate::witgen::{query_processor::QueryProcessor, util::try_to_simple_poly, Constraint};

use super::{
    affine_expression::AffineExpression,
    data_structures::{column_map::WitnessColumnMap, finalizable_data::FinalizableData},
    identity_processor::IdentityProcessor,
    rows::{CellValue, Row, RowIndex, RowPair, RowUpdater, UnknownStrategy},
    Constraints, EvalError, EvalValue, FixedData, IncompleteCause, MutableState, QueryCallback,
};

type CellRef = (PolyID, RowIndex);

#[derive(Default)]
pub struct CopyConstraints {
    copy_cycle: BTreeMap<CellRef, CellRef>,
}

impl CopyConstraints {
    pub fn from_fixed_data<T: FieldElement>(
        fixed_data: &FixedData<T>,
        witness_cols: &HashSet<PolyID>,
    ) -> Self {
        let is_example = witness_cols
            .iter()
            .all(|c| fixed_data.column_name(c).starts_with("main_pythagoras."));

        if is_example {
            log::info!("Using hard-coded copy constraints for Pythagoras example");
            // Hard-code copy constraints every 4 rows:
            // - a[0] = a[1]
            // - a[0] = b[1]
            // - b[0] = a[2]
            // - b[0] = b[2]
            // - c[1] = a[3]
            // - c[2] = b[3]
            // - c[0] = c[3]
            let a = fixed_data.try_column_by_name("main_pythagoras.a").unwrap();
            let b = fixed_data.try_column_by_name("main_pythagoras.b").unwrap();
            let c = fixed_data.try_column_by_name("main_pythagoras.c").unwrap();
            let d = fixed_data.degree;
            let index =
                |block_index, local_index| RowIndex::from_degree(block_index * 4 + local_index, d);

            let mut constraints = Vec::new();

            for i in 0..d / 4 {
                constraints.push(((a, index(i, 0)), (a, index(i, 1))));
                constraints.push(((a, index(i, 0)), (b, index(i, 1))));
                constraints.push(((b, index(i, 0)), (a, index(i, 2))));
                constraints.push(((b, index(i, 0)), (b, index(i, 2))));
                constraints.push(((c, index(i, 1)), (a, index(i, 3))));
                constraints.push(((c, index(i, 2)), (b, index(i, 3))));
                constraints.push(((c, index(i, 0)), (c, index(i, 3))));
            }
            CopyConstraints::new(constraints)
        } else {
            CopyConstraints::default()
        }
    }

    pub fn new(constraint_pairs: Vec<((PolyID, RowIndex), (PolyID, RowIndex))>) -> Self {
        let mut copy_cycle = BTreeMap::new();
        let mut back_edges = BTreeMap::new();

        for (a, b) in constraint_pairs {
            // In the general case, a and b will already be in a cycle,
            // where a has a next node n_a and b has a previous node p_b.
            // We want to change the edges such that a -> b and p_b -> n_a.
            // If a node does not have an entry in the edge list, its previous
            // and next nodes are the node itself.
            let n_a = copy_cycle.get(&a).copied().unwrap_or(a);
            let p_b = back_edges.get(&b).copied().unwrap_or(b);
            copy_cycle.insert(a, b);
            back_edges.insert(b, a);
            copy_cycle.insert(p_b, n_a);
            back_edges.insert(n_a, p_b);
        }
        Self { copy_cycle }
    }

    pub fn next(&self, cell_ref: CellRef) -> CellRef {
        self.copy_cycle.get(&cell_ref).copied().unwrap_or(cell_ref)
    }

    pub fn is_empty(&self) -> bool {
        self.copy_cycle.is_empty()
    }
}

type Left<'a, T> = Vec<AffineExpression<&'a AlgebraicReference, T>>;

/// Data needed to handle an outer query.
pub struct OuterQuery<'a, T: FieldElement> {
    /// A local copy of the left-hand side of the outer query.
    /// This will be mutated while processing the block.
    pub left: Left<'a, T>,
    /// The right-hand side of the outer query.
    pub right: &'a SelectedExpressions<Expression<T>>,
}

impl<'a, T: FieldElement> OuterQuery<'a, T> {
    pub fn new(left: Left<'a, T>, right: &'a SelectedExpressions<Expression<T>>) -> Self {
        Self { left, right }
    }

    pub fn is_complete(&self) -> bool {
        self.left.iter().all(|l| l.is_constant())
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
/// - `'b`: The duration of this machine's call (e.g. the mutable references of the other machines)
/// - `'c`: The duration of this Processor's lifetime (e.g. the reference to the identity processor)
pub struct Processor<'a, 'b, 'c, T: FieldElement, Q: QueryCallback<T>> {
    /// The global index of the first row of [Processor::data].
    row_offset: RowIndex,
    /// The rows that are being processed.
    data: FinalizableData<'a, T>,
    /// The mutable state
    mutable_state: &'c mut MutableState<'a, 'b, T, Q>,
    /// The fixed data (containing information about all columns)
    fixed_data: &'a FixedData<'a, T>,
    /// The set of witness columns that are actually part of this machine.
    witness_cols: &'c HashSet<PolyID>,
    /// Whether a given witness column is relevant for this machine (faster than doing a contains check on witness_cols)
    is_relevant_witness: WitnessColumnMap<bool>,
    /// The outer query, if any. If there is none, processing an outer query will fail.
    outer_query: Option<OuterQuery<'a, T>>,
    inputs: Vec<(PolyID, T)>,
    previously_set_inputs: BTreeMap<PolyID, usize>,
    copy_constraints: CopyConstraints,
}

impl<'a, 'b, 'c, T: FieldElement, Q: QueryCallback<T>> Processor<'a, 'b, 'c, T, Q> {
    pub fn new(
        row_offset: RowIndex,
        data: FinalizableData<'a, T>,
        mutable_state: &'c mut MutableState<'a, 'b, T, Q>,
        fixed_data: &'a FixedData<'a, T>,
        witness_cols: &'c HashSet<PolyID>,
    ) -> Self {
        let is_relevant_witness = WitnessColumnMap::from(
            fixed_data
                .witness_cols
                .keys()
                .map(|poly_id| witness_cols.contains(&poly_id)),
        );
        Self {
            row_offset,
            data,
            mutable_state,
            fixed_data,
            witness_cols,
            is_relevant_witness,
            outer_query: None,
            inputs: Vec::new(),
            previously_set_inputs: BTreeMap::new(),
            copy_constraints: CopyConstraints::from_fixed_data(fixed_data, witness_cols),
        }
    }

    pub fn with_outer_query(self, outer_query: OuterQuery<'a, T>) -> Processor<'a, 'b, 'c, T, Q> {
        log::trace!("  Extracting inputs:");
        let mut inputs = vec![];
        for (l, r) in outer_query.left.iter().zip(&outer_query.right.expressions) {
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

    pub fn finished_outer_query(&self) -> bool {
        self.outer_query
            .as_ref()
            .map(|outer_query| outer_query.is_complete())
            .unwrap_or(true)
    }

    pub fn finish(self) -> FinalizableData<'a, T> {
        self.data
    }

    pub fn latch_value(&self, row_index: usize) -> Option<bool> {
        let row_pair = RowPair::from_single_row(
            &self.data[row_index],
            self.row_offset + row_index as u64,
            self.fixed_data,
            UnknownStrategy::Unknown,
        );
        self.outer_query
            .as_ref()
            .and_then(|outer_query| outer_query.right.selector.as_ref())
            .and_then(|latch| row_pair.evaluate(latch).ok())
            .and_then(|l| l.constant_value())
            .map(|l| l.is_one())
    }

    pub fn process_queries(&mut self, row_index: usize) -> Result<bool, EvalError<T>> {
        let mut query_processor =
            QueryProcessor::new(self.fixed_data, self.mutable_state.query_callback);
        let global_row_index = self.row_offset + row_index as u64;
        let row_pair = RowPair::new(
            &self.data[row_index],
            &self.data[row_index + 1],
            global_row_index,
            self.fixed_data,
            UnknownStrategy::Unknown,
        );
        let mut updates = EvalValue::complete(vec![]);
        for poly_id in self.fixed_data.witness_cols.keys() {
            if self.is_relevant_witness[&poly_id] {
                updates.combine(query_processor.process_query(&row_pair, &poly_id)?);
            }
        }
        Ok(self.apply_updates(row_index, &updates, || "queries".to_string()))
    }

    /// Given a row and identity index, computes any updates and applies them.
    /// @returns the `IdentityResult`.
    pub fn process_identity(
        &mut self,
        row_index: usize,
        identity: &'a Identity<Expression<T>>,
        unknown_strategy: UnknownStrategy,
    ) -> Result<IdentityResult, EvalError<T>> {
        // Create row pair
        let global_row_index = self.row_offset + row_index as u64;
        let row_pair = RowPair::new(
            &self.data[row_index],
            &self.data[row_index + 1],
            global_row_index,
            self.fixed_data,
            unknown_strategy,
        );

        // Compute updates
        let mut identity_processor = IdentityProcessor::new(self.fixed_data, self.mutable_state);
        let updates = identity_processor
            .process_identity(identity, &row_pair)
            .map_err(|e| -> EvalError<T> {
                let mut error = format!(
                    r"Error in identity: {identity}
Known values in current row (local: {row_index}, global {global_row_index}):
{}
",
                    self.data[row_index].render_values(false, Some(self.witness_cols))
                );
                if identity.contains_next_ref() {
                    error += &format!(
                        "Known values in next row (local: {}, global {}):\n{}\n",
                        row_index + 1,
                        global_row_index + 1,
                        self.data[row_index + 1].render_values(false, Some(self.witness_cols))
                    );
                }
                error += &format!("   => Error: {e}");
                error.into()
            })?;

        if unknown_strategy == UnknownStrategy::Zero {
            assert!(updates.constraints.is_empty());
            return Ok(IdentityResult {
                progress: false,
                is_complete: false,
            });
        }

        Ok(IdentityResult {
            progress: self.apply_updates(row_index, &updates, || identity.to_string()),
            is_complete: updates.is_complete(),
        })
    }

    pub fn process_outer_query(
        &mut self,
        row_index: usize,
    ) -> Result<(bool, Constraints<&'a AlgebraicReference, T>), EvalError<T>> {
        let mut progress = false;
        if let Some(selector) = self.outer_query.as_ref().unwrap().right.selector.as_ref() {
            progress |= self
                .set_value(row_index, selector, T::one(), "Set selector to 1")
                .unwrap_or(false);
        }

        let OuterQuery { left, right } = self
            .outer_query
            .as_ref()
            .expect("Asked to process outer query, but it was not set!");

        let row_pair = RowPair::new(
            &self.data[row_index],
            &self.data[row_index + 1],
            self.row_offset + row_index as u64,
            self.fixed_data,
            UnknownStrategy::Unknown,
        );

        let mut identity_processor = IdentityProcessor::new(self.fixed_data, self.mutable_state);
        let updates = identity_processor
            .process_link(left, right, &row_pair)
            .map_err(|e| {
                log::warn!("Error in outer query: {e}");
                log::warn!("Some of the following entries could not be matched:");
                for (l, r) in left.iter().zip(right.expressions.iter()) {
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
            .filter(|(poly, update)| match update {
                Constraint::Assignment(_) => !self.is_relevant_witness[&poly.poly_id],
                // Range constraints are currently not communicated between callee and caller.
                Constraint::RangeConstraint(_) => false,
            })
            .collect::<Vec<_>>();

        Ok((progress, outer_assignments))
    }

    /// Sets the inputs to the values given in [VmProcessor::inputs] if they are not already set.
    /// Typically, inputs will have a constraint of the form: `((1 - instr__reset) * (_input' - _input)) = 0;`
    /// So, once the value of `_input` is set, this function will do nothing until the next reset instruction.
    /// However, if `_input` does become unconstrained, we need to undo all changes we've done so far.
    /// For this reason, we keep track of all changes we've done to inputs in [Processor::previously_set_inputs].
    pub fn set_inputs_if_unset(&mut self, row_index: usize) -> bool {
        let mut input_updates = EvalValue::complete(vec![]);
        for (poly_id, value) in self.inputs.iter() {
            match &self.data[row_index][poly_id].value {
                CellValue::Known(_) => {}
                CellValue::RangeConstraint(_) | CellValue::Unknown => {
                    input_updates.combine(EvalValue::complete(vec![(
                        &self.fixed_data.witness_cols[poly_id].poly,
                        Constraint::Assignment(*value),
                    )]));
                }
            };
        }

        for (poly, _) in &input_updates.constraints {
            let poly_id = poly.poly_id;
            if let Some(start_row) = self.previously_set_inputs.remove(&poly_id) {
                log::trace!(
                    "    Resetting previously set inputs for column: {}",
                    self.fixed_data.column_name(&poly_id)
                );
                for row_index in start_row..row_index {
                    self.data[row_index][&poly_id].value = CellValue::Unknown;
                }
            }
        }
        for (poly, _) in &input_updates.constraints {
            self.previously_set_inputs.insert(poly.poly_id, row_index);
        }
        self.apply_updates(row_index, &input_updates, || "inputs".to_string())
    }

    /// Sets the value of a given expression, in a given row.
    pub fn set_value(
        &mut self,
        local_index: usize,
        expression: &'a Expression<T>,
        value: T,
        reason: &str,
    ) -> Result<bool, IncompleteCause<&'a AlgebraicReference>> {
        let row_pair = RowPair::new(
            &self.data[local_index],
            &self.data[local_index + 1],
            self.row_offset + local_index as u64,
            self.fixed_data,
            UnknownStrategy::Unknown,
        );
        let affine_expression = row_pair.evaluate(expression)?;
        let updates = (affine_expression - value.into())
            .solve_with_range_constraints(&row_pair)
            .unwrap();
        Ok(self.apply_updates(local_index, &updates, || {
            format!("Setting value ({})", reason)
        }))
    }

    fn apply_updates(
        &mut self,
        row_index: usize,
        updates: &EvalValue<&'a AlgebraicReference, T>,
        source_name: impl Fn() -> String,
    ) -> bool {
        if updates.constraints.is_empty() {
            return false;
        }

        log::trace!("    Updates from: {}", source_name());

        let mut progress = false;
        for (poly, c) in &updates.constraints {
            if self.witness_cols.contains(&poly.poly_id) {
                // Build RowUpdater
                // (a bit complicated, because we need two mutable
                // references to elements of the same vector)
                let (current, next) = self.data.mutable_row_pair(row_index);
                let mut row_updater =
                    RowUpdater::new(current, next, self.row_offset + row_index as u64);
                row_updater.apply_update(poly, c);
                progress = true;

                if !self.copy_constraints.is_empty() {
                    self.handle_copy_constraints(row_index, poly, c);
                }
            } else if let Constraint::Assignment(v) = c {
                let left = &mut self.outer_query.as_mut().unwrap().left;
                log::trace!("      => {} (outer) = {}", poly, v);
                for l in left.iter_mut() {
                    l.assign(poly, *v);
                }
                progress = true;
            };
        }

        progress
    }

    fn handle_copy_constraints(
        &mut self,
        row_index: usize,
        poly: &AlgebraicReference,
        constraint: &Constraint<T>,
    ) {
        if let Constraint::Assignment(v) = constraint {
            // If we we do an assignment, propagate the value to any other cell that is
            // copy-constrained to the current cell.
            let row = self.row_offset + row_index + poly.next as usize;
            let (mut other_poly, mut other_row) = self.copy_constraints.next((poly.poly_id, row));

            // Traverse the cycle until we reach the starting point.
            while (other_poly, other_row) != (poly.poly_id, row) {
                let expression = &self.fixed_data.witness_cols[&other_poly].expr;
                self.ensure_enough_rows(&other_row);
                let local_index = other_row.to_local(&self.row_offset);
                self.set_value(local_index, expression, *v, "copy constraint")
                    .unwrap();
                (other_poly, other_row) = self.copy_constraints.next((other_poly, other_row));
            }
        }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn finalize_range(&mut self, range: impl Iterator<Item = usize>) {
        // HACK: If there are copy constraints, never finalize,
        // because it is harder to know when a row is final.
        if self.copy_constraints.is_empty() {
            self.data.finalize_range(range)
        }
    }

    pub fn row(&self, i: usize) -> &Row<'a, T> {
        &self.data[i]
    }

    pub fn has_outer_query(&self) -> bool {
        self.outer_query.is_some()
    }

    /// Sets the ith row, extending the data if necessary.
    pub fn set_row(&mut self, i: usize, row: Row<'a, T>) {
        if i < self.data.len() {
            self.data[i] = row;
        } else {
            assert_eq!(i, self.data.len());
            self.data.push(row);
        }
    }

    /// Ensure that we have enough rows to create a RowPair starting from the given global row index.
    /// This means that we need to have the given row and the next!
    fn ensure_enough_rows(&mut self, row_index: &RowIndex) {
        let local_index = row_index.to_local(&self.row_offset);
        while self.data.len() <= local_index + 1 {
            self.data.push(Row::fresh(
                self.fixed_data,
                RowIndex::from_degree(
                    self.data.len() as DegreeType + u64::from(self.row_offset),
                    self.fixed_data.degree,
                ),
            ));
        }
    }

    /// Checks whether a given identity is satisfied on a proposed row.
    pub fn check_row_pair(
        &mut self,
        row_index: usize,
        proposed_row: &Row<'a, T>,
        identity: &'a Identity<Expression<T>>,
        // This could be computed from the identity, but should be pre-computed for performance reasons.
        has_next_reference: bool,
    ) -> bool {
        let mut identity_processor = IdentityProcessor::new(self.fixed_data, self.mutable_state);
        let row_pair = match has_next_reference {
            // Check whether identities with a reference to the next row are satisfied
            // when applied to the previous row and the proposed row.
            true => {
                assert!(row_index > 0);
                RowPair::new(
                    &self.data[row_index - 1],
                    proposed_row,
                    self.row_offset + (row_index - 1) as DegreeType,
                    self.fixed_data,
                    UnknownStrategy::Zero,
                )
            }
            // Check whether identities without a reference to the next row are satisfied
            // when applied to the proposed row.
            // Because we never access the next row, we can use [RowPair::from_single_row] here.
            false => RowPair::from_single_row(
                proposed_row,
                self.row_offset + row_index as DegreeType,
                self.fixed_data,
                UnknownStrategy::Zero,
            ),
        };

        if identity_processor
            .process_identity(identity, &row_pair)
            .is_err()
        {
            log::debug!("Previous {:?}", &self.data[row_index - 1]);
            log::debug!("Proposed {:?}", proposed_row);
            log::debug!("Failed on identity: {}", identity);

            return false;
        }
        true
    }
}

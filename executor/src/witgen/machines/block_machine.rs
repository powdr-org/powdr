use std::collections::{BTreeMap, HashMap};
use std::fmt::Display;
use std::iter::{self};

use super::{
    compute_size_and_log, ConnectionKind, EvalResult, FixedData, LookupCell, MachineParts,
};

use crate::witgen::affine_expression::AlgebraicVariable;
use crate::witgen::analysis::detect_connection_type_and_block_size;
use crate::witgen::block_processor::BlockProcessor;
use crate::witgen::data_structures::caller_data::CallerData;
use crate::witgen::data_structures::finalizable_data::FinalizableData;
use crate::witgen::data_structures::mutable_state::MutableState;
use crate::witgen::jit::function_cache::FunctionCache;
use crate::witgen::jit::witgen_inference::CanProcessCall;
use crate::witgen::processor::{OuterQuery, Processor, SolverState};
use crate::witgen::range_constraints::RangeConstraint;
use crate::witgen::rows::{Row, RowIndex, RowPair};
use crate::witgen::sequence_iterator::{
    DefaultSequenceIterator, ProcessingSequenceCache, ProcessingSequenceIterator,
};
use crate::witgen::util::try_to_simple_poly;
use crate::witgen::{machines::Machine, EvalError, EvalValue, IncompleteCause, QueryCallback};
use bit_vec::BitVec;
use powdr_ast::analyzed::{DegreeRange, PolyID, PolynomialType};
use powdr_number::{DegreeType, FieldElement};

enum ProcessResult<'a, T: FieldElement> {
    Success(SolverState<'a, T>, EvalValue<AlgebraicVariable<'a>, T>),
    Incomplete(EvalValue<AlgebraicVariable<'a>, T>),
}

impl<'a, T: FieldElement> ProcessResult<'a, T> {
    fn new(data: SolverState<'a, T>, updates: EvalValue<AlgebraicVariable<'a>, T>) -> Self {
        match updates.is_complete() {
            true => ProcessResult::Success(data, updates),
            false => ProcessResult::Incomplete(updates),
        }
    }
}

impl<T: FieldElement> Display for BlockMachine<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} (block_size: {}, latch_row: {})",
            self.name, self.block_size, self.latch_row
        )
    }
}

/// A machine that produces multiple rows (one block) per query.
/// TODO we do not actually "detect" the machine yet, we just check if
/// the lookup has a binary selector that is 1 every k rows for some k
pub struct BlockMachine<'a, T: FieldElement> {
    /// The degree range of all columns in this machine
    degree_range: DegreeRange,
    /// The current degree of all columns in this machine
    degree: DegreeType,
    /// Block size, the period of the selector.
    block_size: usize,
    /// The row index (within the block) of the latch row
    latch_row: usize,
    fixed_data: &'a FixedData<'a, T>,
    /// The parts of the machine (identities, witness columns, etc.)
    parts: MachineParts<'a, T>,
    /// The type of constraint used to connect this machine to its caller.
    connection_type: ConnectionKind,
    /// The data of the machine.
    data: FinalizableData<'a, T>,
    publics: BTreeMap<&'a str, T>,
    /// Cache that states the order in which to evaluate identities
    /// to make progress most quickly.
    processing_sequence_cache: ProcessingSequenceCache,
    /// If this block machine can be JITed, we store the witgen functions here.
    function_cache: FunctionCache<'a, T>,
    name: String,
    /// Counts the number of blocks created using the JIT.
    block_count_jit: usize,
    /// Counts the number of blocks created using the runtime solver.
    block_count_runtime: usize,
}

impl<'a, T: FieldElement> BlockMachine<'a, T> {
    pub fn try_new(
        name: String,
        fixed_data: &'a FixedData<'a, T>,
        parts: &MachineParts<'a, T>,
    ) -> Option<Self> {
        let degree_range = parts.common_degree_range();

        // start from the max degree
        let degree = degree_range.max;

        let (is_permutation, block_size, latch_row) =
            detect_connection_type_and_block_size(fixed_data, &parts.connections)?;

        for id in parts.connections.values() {
            for r in id.right.expressions.iter() {
                if let Some(poly) = try_to_simple_poly(r) {
                    if poly.poly_id.ptype == PolynomialType::Constant {
                        // It does not really make sense to have constant polynomials on the RHS
                        // of a block machine lookup, as all constant polynomials are periodic, so
                        // it would always return the same value.
                        return None;
                    }
                }
            }
        }

        assert!(block_size <= degree as usize);
        // Because block shapes are not always rectangular, we add the last block to the data at the
        // beginning. It starts out with unknown values. Should the first block decide to write to
        // rows < 0, they will be written to this block.
        // In `take_witness_col_values()`, this block will be removed and its values will be used to
        // construct the "default" block used to fill up unused rows.
        let start_index = RowIndex::from_i64(-(block_size as i64), degree);
        let data = FinalizableData::with_initial_rows_in_progress(
            &parts.witnesses,
            (0..block_size).map(|i| Row::fresh(fixed_data, start_index + i)),
            fixed_data,
        );
        let layout = data.layout();
        let function_cache = FunctionCache::new(
            fixed_data,
            parts.clone(),
            block_size,
            latch_row,
            layout,
            name.clone(),
        );
        Some(BlockMachine {
            name,
            degree_range,
            degree,
            block_size,
            latch_row,
            fixed_data,
            parts: parts.clone(),
            connection_type: is_permutation,
            data,
            publics: Default::default(),
            processing_sequence_cache: ProcessingSequenceCache::new(
                block_size,
                latch_row,
                parts.identities.len(),
            ),
            function_cache,
            block_count_jit: 0,
            block_count_runtime: 0,
        })
    }

    #[cfg(test)]
    pub fn machine_info(&self) -> (MachineParts<'a, T>, usize, usize) {
        (self.parts.clone(), self.block_size, self.latch_row)
    }
}

impl<'a, T: FieldElement> Machine<'a, T> for BlockMachine<'a, T> {
    fn identity_ids(&self) -> Vec<u64> {
        self.parts.connections.keys().copied().collect()
    }

    fn can_process_call_fully(
        &mut self,
        can_process: impl CanProcessCall<T>,
        identity_id: u64,
        known_arguments: &BitVec,
        range_constraints: &[RangeConstraint<T>],
    ) -> Option<Vec<RangeConstraint<T>>> {
        if self
            .function_cache
            .compile_cached(can_process, identity_id, known_arguments)
            .is_some()
        {
            Some(range_constraints.to_vec())
        } else {
            None
        }
    }

    fn process_lookup_direct<'b, 'c, Q: QueryCallback<T>>(
        &mut self,
        mutable_state: &'b MutableState<'a, T, Q>,
        identity_id: u64,
        values: &mut [LookupCell<'c, T>],
    ) -> Result<bool, EvalError<T>> {
        if self.rows() + self.block_size as DegreeType > self.degree {
            return Err(EvalError::RowsExhausted(self.name.clone()));
        }

        self.data.finalize_all();
        let data = self.data.append_new_finalized_rows(self.block_size);

        let success =
            self.function_cache
                .process_lookup_direct(mutable_state, identity_id, values, data)?;
        assert!(success);
        self.block_count_jit += 1;
        Ok(true)
    }

    fn process_plookup<'b, Q: QueryCallback<T>>(
        &mut self,
        mutable_state: &'b MutableState<'a, T, Q>,
        identity_id: u64,
        caller_rows: &'b RowPair<'b, 'a, T>,
    ) -> EvalResult<'a, T> {
        let previous_len = self.data.len();
        let result = self.process_plookup_internal(mutable_state, identity_id, caller_rows);
        if let Ok(assignments) = &result {
            if !assignments.is_complete() {
                // rollback the changes.
                self.data.truncate(previous_len);
            }
        }
        result
    }

    fn name(&self) -> &str {
        &self.name
    }

    fn take_witness_col_values<'b, Q: QueryCallback<T>>(
        &mut self,
        mutable_state: &'b MutableState<'a, T, Q>,
    ) -> HashMap<String, Vec<T>> {
        if self.data.len() < 2 * self.block_size {
            if self.fixed_data.is_monolithic() {
                log::warn!(
                    "Filling empty blocks with zeros, because the block machine is never used. \
                 This might violate some internal constraints."
                );
            } else {
                log::info!(
                    "Machine {} is never used at runtime, so we remove it.",
                    self.name
                );
                // Return empty columns for all witnesses.
                return self
                    .parts
                    .witnesses
                    .iter()
                    .map(|id| (*id, Vec::new()))
                    .map(|(id, values)| (self.fixed_data.column_name(&id).to_string(), values))
                    .collect();
            }
        } else {
            let total_block_count = self.block_count_jit + self.block_count_runtime;
            log::debug!(
                "{}: {} / {total_block_count} blocks computed via JIT.",
                self.name,
                self.block_count_jit
            );
        }
        self.degree = compute_size_and_log(
            &self.name,
            // At this point, the data still contains the dummy block, which will be removed below.
            // Therefore, we subtract the block size here.
            self.data.len() - self.block_size,
            self.degree_range,
        );

        if matches!(self.connection_type, ConnectionKind::Permutation) {
            // We have to make sure that *all* selectors are 0 in the dummy block,
            // because otherwise this block won't have a matching block on the LHS.

            // Collect dummy block with rows before and after
            let dummy_block = FinalizableData::with_initial_rows_in_progress(
                &self.parts.witnesses,
                iter::once(self.block_size - 1)
                    .chain(0..self.block_size)
                    .chain(iter::once(0))
                    .map(|i| self.data.get_in_progress_row(i)),
                self.fixed_data,
            );

            // Instantiate a processor
            let row_offset = RowIndex::from_i64(-1, self.degree);
            let mut processor = Processor::new(
                row_offset,
                SolverState::new(dummy_block, self.publics.clone()),
                mutable_state,
                self.fixed_data,
                &self.parts,
                self.degree,
            );

            // Set all selectors to 0
            for id in self.parts.connections.values() {
                processor
                    .set_value(self.latch_row + 1, &id.right.selector, T::zero(), || {
                        "Zero selectors".to_string()
                    })
                    .unwrap();
            }

            // Run BlockProcessor (to potentially propagate selector values)
            let mut processor = BlockProcessor::from_processor(processor, &self.parts.identities);
            let mut sequence_iterator = ProcessingSequenceIterator::Default(
                DefaultSequenceIterator::new(self.block_size, self.parts.identities.len(), None),
            );
            processor.solve(&mut sequence_iterator).unwrap();
            let mut dummy_block = processor.finish().block;

            // Replace the dummy block, discarding first and last row
            dummy_block.pop().unwrap();
            for i in (0..self.block_size).rev() {
                self.data.set(i, dummy_block.pop().unwrap());
            }
        }

        let mut data = self
            .data
            .take_transposed()
            .map(|(id, (values, known_cells))| {
                // Materialize column as Vec<Option<T>>
                let mut values = values
                    .into_iter()
                    .zip(known_cells)
                    .map(|(v, known)| known.then_some(v))
                    .collect::<Vec<_>>();

                // Remove the "last" block added to the beginning of self.data.
                // It contains the values the first block wrote to it and otherwise unknown values.
                let dummy_block = values.drain(0..self.block_size).collect::<Vec<_>>();

                // For all constraints to be satisfied, unused cells have to be filled with valid values.
                // We do this, we construct a default block, by repeating the first input to the block machine.
                values.resize(self.degree as usize, None);

                // Use the block as the default block. However, it needs to be merged with the dummy block,
                // to handle blocks of non-rectangular shape.
                // For example, let's say, the situation might look like this (block size = 3 in this example):
                //  Row  Latch   C1  C2  C3
                //  -3     0
                //  -2     0
                //  -1     1             X  <- This value belongs to the first block
                //   0     0     X   X   X
                //   1     0     X   X   X
                //   2     1     X   X   X  <- This value belongs to the second block
                //
                // The following code constructs the default block as follows:
                // - All values will come from rows 0-2, EXCEPT
                // - In the last row, the value of C3 is whatever value was written to the dummy block
                //
                // Constructed like this, we can repeat the default block forever.
                //
                // TODO: Determine the row-extend per column
                let first_block_values = values.iter().take(self.block_size);
                let default_block = dummy_block
                    .into_iter()
                    .zip(first_block_values)
                    .map(|(dummy_block, first_block)| {
                        dummy_block.or(*first_block).unwrap_or_default()
                    })
                    .collect::<Vec<_>>();

                let values = values
                    .into_iter()
                    .enumerate()
                    .map(|(i, v)| v.unwrap_or(default_block[i % self.block_size]))
                    .collect::<Vec<_>>();

                (id, values)
            })
            .collect();
        self.handle_last_row(&mut data);
        data.into_iter()
            .map(|(id, values)| (self.fixed_data.column_name(&id).to_string(), values))
            .collect()
    }
}

impl<'a, T: FieldElement> BlockMachine<'a, T> {
    /// The characteristic of a block machine is that all fixed columns are
    /// periodic. However, there are exceptions to handle wrapping.
    /// This becomes a problem when a witness polynomial depends on a fixed column
    /// that is not periodic, because values of committed polynomials are copy-pasted
    /// from the default block.
    /// This is the case for the _operation_id_no_change column, generated when
    /// compiling a block machine from Powdr ASM and constrained as:
    /// _operation_id_no_change = ((1 - _block_enforcer_last_step) * (1 - <Latch>));
    /// This function fixes this exception by setting _operation_id_no_change to 0.
    fn handle_last_row(&self, data: &mut HashMap<PolyID, Vec<T>>) {
        #[allow(clippy::iter_over_hash_type)]
        // This is deterministic because there is no shared state.
        for (poly_id, col) in data.iter_mut() {
            if self
                .parts
                .fixed_data
                .column_name(poly_id)
                .ends_with("_operation_id_no_change")
            {
                log::trace!("Setting _operation_id_no_change to 0.");
                col[self.degree as usize - 1] = T::zero();
            }
        }
    }

    /// Returns the current number of rows *not counting the dummy block* inserted at the beginning
    /// (with row numbers (-block_size..0)).
    fn rows(&self) -> DegreeType {
        (self.data.len() - self.block_size) as DegreeType
    }

    fn last_row_index(&self) -> RowIndex {
        RowIndex::from_i64(self.rows() as i64 - 1, self.degree)
    }

    fn process_plookup_internal<'b, Q: QueryCallback<T>>(
        &mut self,
        mutable_state: &MutableState<'a, T, Q>,
        identity_id: u64,
        caller_rows: &'b RowPair<'b, 'a, T>,
    ) -> EvalResult<'a, T> {
        let outer_query =
            match OuterQuery::try_new(caller_rows, self.parts.connections[&identity_id]) {
                Ok(outer_query) => outer_query,
                Err(incomplete_cause) => return Ok(EvalValue::incomplete(incomplete_cause)),
            };

        log::trace!("Start processing block machine '{}'", self.name());
        log::trace!("Left values of lookup:");
        if log::log_enabled!(log::Level::Trace) {
            for l in &outer_query.left {
                log::trace!("  {}", l);
            }
        }

        if self.rows() + self.block_size as DegreeType > self.degree {
            return Err(EvalError::RowsExhausted(self.name.clone()));
        }

        let known_inputs = outer_query.left.iter().map(|e| e.is_constant()).collect();
        if self
            .function_cache
            .compile_cached(mutable_state, identity_id, &known_inputs)
            .is_some()
        {
            let updates = self.process_lookup_via_jit(mutable_state, identity_id, outer_query)?;
            assert!(updates.is_complete());
            self.block_count_jit += 1;
            return Ok(updates);
        }

        // TODO this assumes we are always using the same lookup for this machine.
        let mut sequence_iterator = self
            .processing_sequence_cache
            .get_processing_sequence(&outer_query.left);

        if !sequence_iterator.has_steps() {
            // Shortcut, no need to do anything.
            log::trace!(
                "Abort processing block machine '{}' (inputs incomplete according to cache)",
                self.name()
            );
            return Ok(EvalValue::incomplete(
                IncompleteCause::BlockMachineLookupIncomplete,
            ));
        }

        let process_result =
            self.process(mutable_state, &mut sequence_iterator, outer_query.clone())?;

        match process_result {
            ProcessResult::Success(updated_data, updates) => {
                assert!(updates.is_complete());
                self.block_count_runtime += 1;

                log::trace!(
                    "End processing block machine '{}' (successfully)",
                    self.name()
                );
                self.append_block(updated_data.block)?;
                self.publics.extend(updated_data.publics);

                let updates = updates.report_side_effect();

                // We solved the query, so report it to the cache.
                self.processing_sequence_cache
                    .report_processing_sequence(&outer_query.left, sequence_iterator);
                Ok(updates)
            }
            ProcessResult::Incomplete(updates) => {
                log::trace!(
                    "End processing block machine '{}' (incomplete)",
                    self.name()
                );
                self.processing_sequence_cache
                    .report_incomplete(&outer_query.left);
                Ok(updates)
            }
        }
    }

    fn process_lookup_via_jit<'b, Q: QueryCallback<T>>(
        &mut self,
        mutable_state: &MutableState<'a, T, Q>,
        identity_id: u64,
        outer_query: OuterQuery<'a, 'b, T>,
    ) -> EvalResult<'a, T> {
        let mut values = CallerData::from(&outer_query);

        assert!(
            (self.rows() + self.block_size as DegreeType) <= self.degree,
            "Block machine is full (this should have been checked before)"
        );
        self.data.finalize_all();
        let data = self.data.append_new_finalized_rows(self.block_size);

        let success = self.function_cache.process_lookup_direct(
            mutable_state,
            identity_id,
            &mut values.as_lookup_cells(),
            data,
        )?;
        assert!(success);

        values.into()
    }

    fn process<'b, Q: QueryCallback<T>>(
        &self,
        mutable_state: &MutableState<'a, T, Q>,
        sequence_iterator: &mut ProcessingSequenceIterator,
        outer_query: OuterQuery<'a, 'b, T>,
    ) -> Result<ProcessResult<'a, T>, EvalError<T>> {
        // We start at the last row of the previous block.
        let row_offset = self.last_row_index();
        // Make the block two rows larger than the block size, it includes the last row of the previous block
        // and the first row of the next block.
        let block = FinalizableData::with_initial_rows_in_progress(
            &self.parts.witnesses,
            (0..(self.block_size + 2)).map(|i| Row::fresh(self.fixed_data, row_offset + i)),
            self.fixed_data,
        );
        let mut processor = BlockProcessor::new(
            row_offset,
            SolverState::new(block, self.publics.clone()),
            mutable_state,
            self.fixed_data,
            &self.parts,
            self.degree,
        )
        .with_outer_query(outer_query);

        let outer_assignments = processor.solve(sequence_iterator)?;
        let updated_data = processor.finish();

        Ok(ProcessResult::new(updated_data, outer_assignments))
    }

    /// Takes a block of rows, which contains the last row of its previous block
    /// and the first row of its next block. The first row of its next block is ignored,
    /// the last row of its previous block is merged with the one we have already.
    /// This is necessary to handle non-rectangular block machines, which already use
    /// unused cells in the previous block.
    fn append_block(&mut self, mut new_block: FinalizableData<'a, T>) -> Result<(), EvalError<T>> {
        assert!(
            (self.rows() + self.block_size as DegreeType) <= self.degree,
            "Block machine is full (this should have been checked before)"
        );

        assert_eq!(new_block.len(), self.block_size + 2);

        // 1. Ignore the first row of the next block:
        new_block.pop().unwrap();

        // 2. Merge the last row of the previous block
        new_block
            .get_mut(0)
            .unwrap()
            .merge_with_values(self.data.known_values_in_row(self.data.len() - 1))
            .map_err(|_| {
                EvalError::Generic(
                    "Block machine overwrites existing value with different value!".to_string(),
                )
            })?;

        // 3. Remove the last row of the previous block from data
        self.data.truncate(self.data.len() - 1);

        // 4. Finalize everything so far
        self.data.finalize_all();

        // 5. Append the new block (including the merged last row of the previous block)
        self.data.extend(new_block);

        Ok(())
    }
}

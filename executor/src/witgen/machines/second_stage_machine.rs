use itertools::Itertools;
use powdr_number::{DegreeType, FieldElement};
use std::collections::{BTreeMap, HashMap};

use crate::witgen::block_processor::BlockProcessor;
use crate::witgen::data_structures::finalizable_data::FinalizableData;
use crate::witgen::data_structures::identity::Identity;
use crate::witgen::data_structures::mutable_state::MutableState;
use crate::witgen::machines::{Machine, MachineParts};
use crate::witgen::processor::SolverState;
use crate::witgen::rows::{Row, RowIndex, RowPair};
use crate::witgen::sequence_iterator::{DefaultSequenceIterator, ProcessingSequenceIterator};
use crate::witgen::vm_processor::VmProcessor;
use crate::witgen::{EvalError, EvalResult, FixedData, QueryCallback};

use super::LookupCell;

/// A machine responsible for second-phase witness generation.
/// For example, this might generate the witnesses for a bus accumulator or LogUp argument.
pub struct SecondStageMachine<'a, T: FieldElement> {
    fixed_data: &'a FixedData<'a, T>,
    parts: MachineParts<'a, T>,
    data: FinalizableData<'a, T>,
    publics: BTreeMap<&'a str, T>,
    name: String,
    degree: DegreeType,
}

impl<'a, T: FieldElement> Machine<'a, T> for SecondStageMachine<'a, T> {
    fn process_lookup_direct<'b, 'c, Q: QueryCallback<T>>(
        &mut self,
        _mutable_state: &'b MutableState<'a, T, Q>,
        _identity_id: u64,
        _values: &mut [LookupCell<'c, T>],
    ) -> Result<bool, EvalError<T>> {
        unimplemented!("Direct lookup not supported by machine {}.", self.name())
    }

    fn identity_ids(&self) -> Vec<u64> {
        Vec::new()
    }

    fn name(&self) -> &str {
        &self.name
    }

    /// Runs the machine without any arguments from the first row.
    fn run<Q: QueryCallback<T>>(&mut self, mutable_state: &MutableState<'a, T, Q>) {
        assert!(self.data.is_empty());
        let first_row = self.compute_partial_first_row(mutable_state);
        self.data = self.process(first_row, mutable_state);
    }

    fn process_plookup<'b, Q: QueryCallback<T>>(
        &mut self,
        _mutable_state: &MutableState<'a, T, Q>,
        _identity_id: u64,
        _caller_rows: &'b RowPair<'b, 'a, T>,
    ) -> EvalResult<'a, T> {
        panic!("SecondStageMachine can't be called by other machines!")
    }

    fn take_witness_col_values<'b, Q: QueryCallback<T>>(
        &mut self,
        _mutable_state: &'b MutableState<'a, T, Q>,
    ) -> HashMap<String, Vec<T>> {
        log::debug!("Finalizing VM: {}", self.name());

        self.fix_first_row();

        self.data
            .take_transposed()
            .map(|(id, (values, _))| (id, values))
            .map(|(id, values)| (self.fixed_data.column_name(&id).to_string(), values))
            .collect()
    }
}

impl<'a, T: FieldElement> SecondStageMachine<'a, T> {
    pub fn new(name: String, fixed_data: &'a FixedData<'a, T>, parts: MachineParts<'a, T>) -> Self {
        let data = FinalizableData::new(&parts.witnesses, fixed_data);

        // Only keep polynomial identities. We assume other constraints to be handled in stage 0.
        let polynomial_identities = parts
            .identities
            .into_iter()
            .filter(|identity| matches!(identity, Identity::Polynomial(_)))
            .collect::<Vec<_>>();
        let parts = MachineParts::new(
            fixed_data,
            Default::default(),
            polynomial_identities,
            parts.witnesses,
            parts.prover_functions,
        );

        let witness_sizes = fixed_data
            .witness_cols
            .values()
            .filter_map(|w| w.external_values.as_ref())
            .map(|values| values.len())
            .unique()
            .collect::<Vec<_>>();
        let degree = witness_sizes.into_iter().exactly_one().unwrap() as DegreeType;

        Self {
            degree,
            name,
            fixed_data,
            parts,
            data,
            publics: Default::default(),
        }
    }

    /// Runs the solver on the row pair (degree - 1, 0) in order to partially compute the first
    /// row from identities like `pc' = (1 - first_step') * <...>`.
    fn compute_partial_first_row<Q: QueryCallback<T>>(
        &self,
        mutable_state: &MutableState<'a, T, Q>,
    ) -> Row<T> {
        // Use `BlockProcessor` + `DefaultSequenceIterator` using a "block size" of 0. Because `BlockProcessor`
        // expects `data` to include the row before and after the block, this means we'll run the
        // solver on exactly one row pair.
        // Note that using `BlockProcessor` instead of `VmProcessor` is more convenient here because
        // it does not assert that the row is "complete" afterwards (i.e., that all identities
        // are satisfied assuming 0 for unknown values).
        let data = FinalizableData::with_initial_rows_in_progress(
            &self.parts.witnesses,
            [
                Row::fresh(self.fixed_data, RowIndex::from_i64(-1, self.degree)),
                Row::fresh(self.fixed_data, RowIndex::from_i64(0, self.degree)),
            ]
            .into_iter(),
            self.fixed_data,
        );

        // We're only interested in the first row anyway, so identities without a next reference
        // are irrelevant.
        // Also, they can lead to problems in the case where some witness columns are provided
        // externally, e.g. if the last row happens to call into a stateful machine like memory.
        let next_parts = self.parts.restricted_to_identities_with_next_references();
        let mut processor = BlockProcessor::new(
            RowIndex::from_i64(-1, self.degree),
            // Shouldn't need any publics at this point
            SolverState::without_publics(data),
            mutable_state,
            self.fixed_data,
            &next_parts,
            self.degree,
        );
        let mut sequence_iterator = ProcessingSequenceIterator::Default(
            DefaultSequenceIterator::new(0, next_parts.identities.len(), None),
        );
        processor.solve(&mut sequence_iterator).unwrap();

        // Ignore any updates to the publics at this point, as we'll re-visit the last row again.
        let mut block = processor.finish().block;
        assert!(block.len() == 2);
        block.pop().unwrap()
    }

    fn process<Q: QueryCallback<T>>(
        &mut self,
        first_row: Row<T>,
        mutable_state: &MutableState<'a, T, Q>,
    ) -> FinalizableData<'a, T> {
        log::trace!(
            "Running Second-Stage Machine with the following initial values in the first row:\n{}",
            first_row.render_values(false, &self.parts)
        );
        let data = FinalizableData::with_initial_rows_in_progress(
            &self.parts.witnesses,
            [first_row].into_iter(),
            self.fixed_data,
        );

        let mut processor = VmProcessor::new(
            self.name().to_string(),
            RowIndex::from_degree(0, self.degree),
            self.fixed_data,
            &self.parts,
            SolverState::new(data, self.publics.clone()),
            mutable_state,
            self.degree,
            false,
        );
        processor.run(true);
        let (updated_data, degree) = processor.finish();

        // The processor might have detected a loop, in which case the degree has changed
        self.degree = degree;

        updated_data.block
    }

    /// At the end of the solving algorithm, we'll have computed the first row twice
    /// (as row 0 and as row <degree>). This function merges the two versions.
    fn fix_first_row(&mut self) {
        assert_eq!(self.data.len() as DegreeType, self.degree + 1);

        let last_row = self.data.pop().unwrap();
        if self.data[0].merge_with(&last_row).is_err() {
            log::error!("{}", self.data[0].render("First row", false, &self.parts));
            log::error!("{}", last_row.render("Last row", false, &self.parts));
            panic!(
                "Failed to merge the first and last row of the VM '{}'",
                self.name()
            );
        }
    }
}

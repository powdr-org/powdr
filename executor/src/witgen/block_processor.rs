use std::collections::HashSet;

use powdr_ast::analyzed::{AlgebraicReference, PolyID};
use powdr_number::{DegreeType, FieldElement};

use crate::Identity;

use super::{
    data_structures::finalizable_data::FinalizableData,
    processor::{OuterQuery, Processor},
    rows::{RowIndex, UnknownStrategy},
    sequence_iterator::{Action, ProcessingSequenceIterator, SequenceStep},
    EvalError, EvalValue, FixedData, IncompleteCause, MutableState, QueryCallback,
};

/// A basic processor that knows how to determine a unique satisfying witness
/// for a given list of identities.
/// The lifetimes mean the following:
/// - `'a`: The duration of the entire witness generation (e.g. references to identities)
/// - `'b`: The duration of this machine's call (e.g. the mutable references of the other machines)
/// - `'c`: The duration of this Processor's lifetime (e.g. the reference to the identity processor)
pub struct BlockProcessor<'a, 'b, 'c, T: FieldElement, Q: QueryCallback<T>> {
    processor: Processor<'a, 'b, 'c, T, Q>,
    /// The list of identities
    identities: &'c [&'a Identity<T>],
}

impl<'a, 'b, 'c, T: FieldElement, Q: QueryCallback<T>> BlockProcessor<'a, 'b, 'c, T, Q> {
    pub fn new(
        row_offset: RowIndex,
        data: FinalizableData<T>,
        mutable_state: &'c mut MutableState<'a, 'b, T, Q>,
        identities: &'c [&'a Identity<T>],
        fixed_data: &'a FixedData<'a, T>,
        witness_cols: &'c HashSet<PolyID>,
        size: DegreeType,
    ) -> Self {
        let processor = Processor::new(
            row_offset,
            data,
            mutable_state,
            fixed_data,
            witness_cols,
            size,
        );
        Self {
            processor,
            identities,
        }
    }

    pub fn from_processor(
        processor: Processor<'a, 'b, 'c, T, Q>,
        identities: &'c [&'a Identity<T>],
    ) -> Self {
        Self {
            processor,
            identities,
        }
    }

    pub fn with_outer_query(
        self,
        outer_query: OuterQuery<'a, 'b, T>,
    ) -> BlockProcessor<'a, 'b, 'c, T, Q> {
        let processor = self.processor.with_outer_query(outer_query);
        Self { processor, ..self }
    }

    /// Figures out unknown values.
    /// Returns the assignments to outer query columns.
    pub fn solve(
        &mut self,
        sequence_iterator: &mut ProcessingSequenceIterator,
    ) -> Result<EvalValue<&'a AlgebraicReference, T>, EvalError<T>> {
        let mut outer_assignments = vec![];

        let mut is_identity_complete =
            vec![vec![false; self.identities.len()]; self.processor.len()];

        while let Some(SequenceStep { row_delta, action }) = sequence_iterator.next() {
            let row_index = (1 + row_delta) as usize;
            let progress = match action {
                Action::InternalIdentity(identity_index) => {
                    if is_identity_complete[row_index][identity_index] {
                        // The identity has been completed already, there is no point in processing it again.
                        false
                    } else {
                        let res = self.processor.process_identity(
                            row_index,
                            self.identities[identity_index],
                            UnknownStrategy::Unknown,
                        )?;
                        is_identity_complete[row_index][identity_index] = res.is_complete;
                        res.progress
                    }
                }
                Action::OuterQuery => {
                    let (progress, new_outer_assignments) =
                        self.processor.process_outer_query(row_index)?;
                    outer_assignments.extend(new_outer_assignments);
                    progress
                }
                Action::ProverQueries => self.processor.process_queries(row_index)?,
            };
            sequence_iterator.report_progress(progress);
        }

        match self.processor.finished_outer_query() {
            true => Ok(EvalValue::complete(outer_assignments)),
            false => Ok(EvalValue::incomplete_with_constraints(
                outer_assignments,
                IncompleteCause::BlockMachineLookupIncomplete,
            )),
        }
    }

    pub fn finish(self) -> FinalizableData<T> {
        self.processor.finish()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use powdr_ast::analyzed::{PolyID, PolynomialType};
    use powdr_number::{FieldElement, GoldilocksField};
    use powdr_pil_analyzer::analyze_string;

    use crate::{
        constant_evaluator::generate,
        witgen::{
            data_structures::finalizable_data::FinalizableData,
            identity_processor::Machines,
            machines::FixedLookup,
            rows::{Row, RowIndex},
            sequence_iterator::{DefaultSequenceIterator, ProcessingSequenceIterator},
            unused_query_callback, FixedData, MutableState, QueryCallback,
        },
    };

    use super::BlockProcessor;

    fn name_to_poly_id<T: FieldElement>(fixed_data: &FixedData<T>) -> BTreeMap<String, PolyID> {
        let mut name_to_poly_id = BTreeMap::new();
        for (poly_id, col) in fixed_data.witness_cols.iter() {
            name_to_poly_id.insert(col.poly.name.clone(), poly_id);
        }
        for (poly_id, col) in fixed_data.fixed_cols.iter() {
            name_to_poly_id.insert(col.name.clone(), poly_id);
        }
        name_to_poly_id
    }

    /// Constructs a processor for a given PIL, then calls a function on it.
    fn do_with_processor<T: FieldElement, Q: QueryCallback<T>, R>(
        src: &str,
        mut query_callback: Q,
        f: impl Fn(BlockProcessor<T, Q>, BTreeMap<String, PolyID>, u64, usize) -> R,
    ) -> R {
        let analyzed = analyze_string(src);
        let constants = generate(&analyzed);
        let fixed_data = FixedData::new(&analyzed, &constants, &[], Default::default(), 0);

        // No submachines
        let mut fixed_lookup = FixedLookup::new(fixed_data.global_range_constraints().clone());
        let mut machines = [];

        let degree = fixed_data.analyzed.degree();

        let columns = (0..fixed_data.witness_cols.len())
            .map(move |i| PolyID {
                id: i as u64,
                ptype: PolynomialType::Committed,
            })
            .collect();
        let data = FinalizableData::with_initial_rows_in_progress(
            &columns,
            (0..degree).map(|i| Row::fresh(&fixed_data, RowIndex::from_degree(i, degree))),
        );

        let mut mutable_state = MutableState {
            fixed_lookup: &mut fixed_lookup,
            machines: Machines::from(machines.iter_mut()),
            query_callback: &mut query_callback,
        };
        let row_offset = RowIndex::from_degree(0, degree);
        let identities = analyzed.identities.iter().collect::<Vec<_>>();
        let witness_cols = fixed_data.witness_cols.keys().collect();

        let processor = BlockProcessor::new(
            row_offset,
            data,
            &mut mutable_state,
            &identities,
            &fixed_data,
            &witness_cols,
            degree,
        );

        f(
            processor,
            name_to_poly_id(&fixed_data),
            degree,
            identities.len(),
        )
    }

    fn solve_and_assert<T: FieldElement>(src: &str, asserted_values: &[(usize, &str, u64)]) {
        do_with_processor(
            src,
            unused_query_callback(),
            |mut processor, poly_ids, degree, num_identities| {
                let mut sequence_iterator = ProcessingSequenceIterator::Default(
                    DefaultSequenceIterator::new(degree as usize - 2, num_identities, None),
                );
                let outer_updates = processor.solve(&mut sequence_iterator).unwrap();
                assert!(outer_updates.is_complete());
                assert!(outer_updates.is_empty());

                let data = processor.finish();

                for &(i, name, expected) in asserted_values.iter() {
                    let poly_id = poly_ids[name];
                    let actual: T = data[i].value_or_zero(&poly_id);
                    assert_eq!(actual, T::from(expected));
                }
            },
        )
    }

    #[test]
    fn fibonacci() {
        let src = r#"
            let N: int = 8;

            namespace Fibonacci(N);
                col fixed ISFIRST(i) { if i == 0 { 1 } else { 0 } };
                col fixed ISLAST(i) { if i == N - 1 { 1 } else { 0 } };
                col witness x, y;

                // Start with 1, 1
                ISFIRST * (y - 1) = 0;
                ISFIRST * (x - 1) = 0;

                (1-ISLAST) * (x' - y) = 0;
                (1-ISLAST) * (y' - (x + y)) = 0;
        "#;

        solve_and_assert::<GoldilocksField>(src, &[(7, "Fibonacci.y", 34)]);
    }
}

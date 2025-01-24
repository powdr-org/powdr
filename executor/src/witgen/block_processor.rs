use powdr_number::{DegreeType, FieldElement};

use super::{
    affine_expression::AlgebraicVariable,
    data_structures::{identity::Identity, mutable_state::MutableState},
    machines::MachineParts,
    processor::{OuterQuery, Processor, SolverState},
    rows::{RowIndex, UnknownStrategy},
    sequence_iterator::{Action, ProcessingSequenceIterator, SequenceStep},
    EvalError, EvalValue, FixedData, IncompleteCause, QueryCallback,
};

/// A basic processor that knows how to determine a unique satisfying witness
/// for a given list of identities.
/// The lifetimes mean the following:
/// - `'a`: The duration of the entire witness generation (e.g. references to identities)
/// - `'c`: The duration of this Processor's lifetime (e.g. the reference to the identity processor)
pub struct BlockProcessor<'a, 'c, T: FieldElement, Q: QueryCallback<T>> {
    processor: Processor<'a, 'c, T, Q>,
    /// The list of identities
    identities: &'c [&'a Identity<T>],
}

impl<'a, 'c, T: FieldElement, Q: QueryCallback<T>> BlockProcessor<'a, 'c, T, Q> {
    pub fn new(
        row_offset: RowIndex,
        mutable_data: SolverState<'a, T>,
        mutable_state: &'c MutableState<'a, T, Q>,
        fixed_data: &'a FixedData<'a, T>,
        parts: &'c MachineParts<'a, T>,
        size: DegreeType,
    ) -> Self {
        let processor = Processor::new(
            row_offset,
            mutable_data,
            mutable_state,
            fixed_data,
            parts,
            size,
        );
        Self {
            processor,
            identities: &parts.identities,
        }
    }

    pub fn from_processor(
        processor: Processor<'a, 'c, T, Q>,
        identities: &'c [&'a Identity<T>],
    ) -> Self {
        Self {
            processor,
            identities,
        }
    }

    pub fn with_outer_query(
        self,
        outer_query: OuterQuery<'a, 'c, T>,
    ) -> BlockProcessor<'a, 'c, T, Q> {
        let processor = self.processor.with_outer_query(outer_query);
        Self { processor, ..self }
    }

    /// Figures out unknown values.
    /// Returns the assignments to outer query columns.
    pub fn solve(
        &mut self,
        sequence_iterator: &mut ProcessingSequenceIterator,
    ) -> Result<EvalValue<AlgebraicVariable<'a>, T>, EvalError<T>> {
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

    /// Returns the updated data and values for publics
    pub fn finish(self) -> SolverState<'a, T> {
        self.processor.finish()
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, iter};

    use powdr_ast::analyzed::{PolyID, PolynomialType};
    use powdr_number::{FieldElement, GoldilocksField};
    use powdr_pil_analyzer::analyze_string;

    use crate::{
        constant_evaluator::generate,
        witgen::{
            data_structures::finalizable_data::FinalizableData,
            machines::MachineParts,
            processor::SolverState,
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
        query_callback: Q,
        f: impl Fn(BlockProcessor<T, Q>, BTreeMap<String, PolyID>, u64, usize) -> R,
    ) -> R {
        let analyzed = analyze_string(src)
            .map_err(|errors| {
                for e in errors {
                    e.output_to_stderr();
                }
            })
            .expect("Failed to analyze test input.");
        let constants = generate(&analyzed);
        let fixed_data = FixedData::new(&analyzed, &constants, &[], Default::default(), 0);

        let degree = fixed_data.analyzed.degree();

        let columns = (0..fixed_data.witness_cols.len())
            .map(move |i| PolyID {
                id: i as u64,
                ptype: PolynomialType::Committed,
            })
            .collect();
        let data = FinalizableData::with_initial_rows_in_progress(
            &columns,
            (0..degree).map(|i| Row::fresh(&fixed_data, i)),
            &fixed_data,
        );

        let mutable_state = MutableState::new(iter::empty(), &query_callback);

        let row_offset = RowIndex::from_degree(0, degree);
        let machine_parts = MachineParts::new(
            &fixed_data,
            Default::default(),
            fixed_data.identities.iter().collect(),
            fixed_data.witness_cols.keys().collect(),
            Default::default(),
        );

        let processor = BlockProcessor::new(
            row_offset,
            SolverState::without_publics(data),
            &mutable_state,
            &fixed_data,
            &machine_parts,
            degree,
        );

        f(
            processor,
            name_to_poly_id(&fixed_data),
            degree,
            machine_parts.identities.len(),
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

                let data = processor.finish().block;

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
                col fixed ISFIRST = [1] + [0]*;
                col fixed ISLAST = [0]* + [1];
                col witness x, y;

                // Start with 1, 1
                ISFIRST * (y - 1) = 0;
                ISFIRST * (x - 1) = 0;

                (1-ISLAST) * (x' - y) = 0;
                (1-ISLAST) * (y' - (x + y)) = 0;
        "#;

        solve_and_assert::<GoldilocksField>(src, &[(7, "Fibonacci::y", 34)]);
    }
}

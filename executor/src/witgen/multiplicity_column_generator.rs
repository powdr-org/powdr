use std::collections::{BTreeMap, HashMap};

use powdr_ast::{
    analyzed::{AlgebraicExpression, PolynomialType, SelectedExpressions},
    parsed::visitor::AllChildren,
};
use powdr_executor_utils::expression_evaluator::{ExpressionEvaluator, OwnedTerminalValues};
use powdr_number::FieldElement;
use rayon::iter::{IntoParallelIterator, ParallelIterator};

use crate::witgen::{
    data_structures::identity::convert_identities,
    machines::{
        profiling::{record_end, record_start},
        Connection,
    },
};

use super::FixedData;

static MULTIPLICITY_WITGEN_NAME: &str = "multiplicity witgen";

pub struct MultiplicityColumnGenerator<'a, T: FieldElement> {
    fixed: &'a FixedData<'a, T>,
}

impl<'a, T: FieldElement> MultiplicityColumnGenerator<'a, T> {
    pub fn new(fixed: &'a FixedData<'a, T>) -> Self {
        Self { fixed }
    }

    /// Takes a map of witness columns and extends it with the multiplicity columns
    /// reference in the phantom lookups.
    pub fn generate(
        &self,
        witness_columns: HashMap<String, Vec<T>>,
        publics: BTreeMap<String, Option<T>>,
    ) -> HashMap<String, Vec<T>> {
        record_start(MULTIPLICITY_WITGEN_NAME);

        log::trace!("Starting multiplicity witness generation.");
        let start = std::time::Instant::now();

        // Several range constraints might point to the same target
        let mut multiplicity_columns = BTreeMap::new();

        let identities = convert_identities(self.fixed.analyzed);
        let phantom_lookups = identities
            .iter()
            .filter_map(|identity| {
                Connection::try_new(identity, &self.fixed.bus_receives)
                    .and_then(|connection| connection.multiplicity_column.map(|_| connection))
            })
            .collect::<Vec<_>>();

        let all_columns = witness_columns
            .into_iter()
            .map(|(name, col)| {
                let poly_id = self.fixed.try_column_by_name(&name).unwrap();
                (poly_id, col)
            })
            .chain(
                self.fixed
                    .fixed_cols
                    .iter()
                    // TODO: Avoid clone
                    // TODO: Find the actual size
                    .map(|(poly_id, fixed_col)| (poly_id, fixed_col.values_max_size().to_vec())),
            )
            .collect::<BTreeMap<_, _>>();
        let terminal_values = OwnedTerminalValues {
            trace: all_columns,
            public_values: publics
                .into_iter()
                // Publics might be unavailable if they are later-stage publics.
                .filter_map(|(k, v)| v.map(|v| (k, v)))
                .collect(),
            challenge_values: self.fixed.challenges.clone(),
        };

        log::trace!(
            "  Done building trace values, took: {}s",
            start.elapsed().as_secs_f64()
        );

        for lookup in phantom_lookups {
            log::trace!("  Updating multiplicity for phantom lookup: {lookup}");
            let start = std::time::Instant::now();

            let (rhs_machine_size, rhs_tuples) = self.get_tuples(&terminal_values, lookup.right);

            log::trace!(
                "    Done collecting RHS tuples, took {}s",
                start.elapsed().as_secs_f64()
            );
            let start = std::time::Instant::now();

            let index = rhs_tuples
                .iter()
                .map(|(i, tuple)| {
                    // There might be multiple identical rows, but it's fine, we can pick any.
                    (tuple, *i)
                })
                .collect::<HashMap<_, _>>();

            log::trace!(
                "    Done building index, took {}s",
                start.elapsed().as_secs_f64()
            );
            let start = std::time::Instant::now();

            let (_, lhs_tuples) = self.get_tuples(&terminal_values, lookup.left);

            log::trace!(
                "    Done collecting LHS tuples, took: {}s",
                start.elapsed().as_secs_f64()
            );
            let start = std::time::Instant::now();

            let multiplicity_column_id = lookup.multiplicity_column.unwrap();
            let multiplicities = multiplicity_columns
                .entry(multiplicity_column_id)
                .or_insert_with(|| vec![0; rhs_machine_size]);
            assert_eq!(multiplicities.len(), rhs_machine_size);

            // Looking up the index is slow, so we do it in parallel.
            let indices = lhs_tuples
                .into_par_iter()
                .map(|(_, tuple)| index[&tuple])
                .collect::<Vec<_>>();

            for index in indices {
                multiplicities[index] += 1;
            }
            log::trace!(
                "    Done updating multiplicities, took: {}s",
                start.elapsed().as_secs_f64()
            );
        }

        let columns = terminal_values
            .into_trace()
            .into_iter()
            .chain(
                multiplicity_columns
                    .into_iter()
                    .map(|(col, values)| (col, values.into_iter().map(T::from).collect())),
            )
            .map(|(poly_id, values)| (self.fixed.column_name(&poly_id).to_string(), values))
            .collect();

        record_end(MULTIPLICITY_WITGEN_NAME);
        columns
    }

    /// Given the trace, global values and a selected expression, evaluates the expression
    /// on all rows and returns the number of rows and the selected tuples with their original
    /// row index.
    fn get_tuples(
        &self,
        terminal_values: &OwnedTerminalValues<T>,
        selected_expressions: &SelectedExpressions<T>,
    ) -> (usize, Vec<(usize, Vec<T>)>) {
        let machine_size = selected_expressions
            .expressions
            .iter()
            .flat_map(|expr| expr.all_children())
            .filter_map(|expr| match expr {
                AlgebraicExpression::Reference(ref r) => match r.poly_id.ptype {
                    PolynomialType::Committed | PolynomialType::Constant => {
                        Some(terminal_values.column_length(&r.poly_id))
                    }
                    _ => None,
                },
                _ => None,
            })
            // We add fixed columns in their max size, so they might not be equal...
            // But in practice, either the machine has a (smaller) witness column, or
            // it's a fixed lookup, so there is only one size.
            .min()
            .unwrap_or_else(|| panic!("No column references found: {selected_expressions}"));

        let tuples = (0..machine_size)
            .into_par_iter()
            .filter_map(|row| {
                let mut evaluator = ExpressionEvaluator::new(
                    terminal_values.row(row),
                    &self.fixed.intermediate_definitions,
                );
                let result = evaluator.evaluate(&selected_expressions.selector);

                assert!(result.is_zero() || result.is_one(), "Non-binary selector");
                result.is_one().then(|| {
                    (
                        row,
                        selected_expressions
                            .expressions
                            .iter()
                            .map(|expression| evaluator.evaluate(expression))
                            .collect::<Vec<_>>(),
                    )
                })
            })
            .collect::<Vec<_>>();

        (machine_size, tuples)
    }
}

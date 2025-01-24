use std::collections::{BTreeMap, HashMap};

use super::super::affine_expression::AffineExpression;
use super::{Connection, EvalResult, FixedData, LookupCell};
use super::{Machine, MachineParts};
use crate::witgen::affine_expression::AlgebraicVariable;
use crate::witgen::data_structures::identity::Identity;
use crate::witgen::data_structures::mutable_state::MutableState;
use crate::witgen::evaluators::fixed_evaluator::FixedEvaluator;
use crate::witgen::evaluators::partial_expression_evaluator::PartialExpressionEvaluator;
use crate::witgen::evaluators::symbolic_evaluator::SymbolicEvaluator;
use crate::witgen::rows::RowPair;
use crate::witgen::{EvalError, EvalValue, IncompleteCause, QueryCallback};
use itertools::Itertools;
use num_traits::One;
use powdr_ast::analyzed::{AlgebraicExpression as Expression, AlgebraicReference, PolyID};
use powdr_number::{DegreeType, FieldElement};

/// A machine that can support a lookup in a set of columns that are sorted
/// by one specific column and values in that column have to be unique.
/// This means there is a column A and a constraint of the form
/// NOTLAST $ [ A' - A ] in [ POSITIVE ]
/// Where
///  - NOTLAST is zero only on the last row
///  - POSITIVE has all values from 1 to half of the field size.
pub struct SortedWitnesses<'a, T: FieldElement> {
    degree: DegreeType,
    rhs_references: BTreeMap<u64, Vec<&'a AlgebraicReference>>,
    connections: BTreeMap<u64, Connection<'a, T>>,
    key_col: PolyID,
    /// Position of the witness columns in the data.
    witness_positions: HashMap<PolyID, usize>,
    data: BTreeMap<T, Vec<Option<T>>>,
    fixed_data: &'a FixedData<'a, T>,
    name: String,
}

impl<'a, T: FieldElement> SortedWitnesses<'a, T> {
    pub fn try_new(
        name: String,
        fixed_data: &'a FixedData<'a, T>,
        parts: &MachineParts<'a, T>,
    ) -> Option<Self> {
        let mut identities_without_receives = parts
            .identities
            .iter()
            .filter(|i| !matches!(i, Identity::BusReceive(_)));
        let identity = identities_without_receives.next()?;

        if identities_without_receives.next().is_some() {
            // Expecting exactly one identity
            return None;
        }
        if parts.connections.is_empty() {
            return None;
        }

        let degree = parts.common_degree_range().max;

        check_identity(fixed_data, identity, degree).and_then(|key_col| {
            let witness_positions = parts
                .witnesses
                .iter()
                .filter(|&w| *w != key_col)
                .sorted()
                .enumerate()
                .map(|(i, &x)| (x, i))
                .collect();

            let rhs_references = parts
                .connections
                .iter()
                .filter_map(|(id, &identity)| {
                    let rhs_expressions = identity
                        .right
                        .expressions
                        .iter()
                        .map(|expr| match expr {
                            // Expect all RHS expressions to be references without a next operator applied.
                            Expression::Reference(p) => (!p.next).then_some(p),
                            _ => None,
                        })
                        .collect::<Option<Vec<_>>>()?;

                    Some((*id, rhs_expressions))
                })
                .collect::<BTreeMap<_, _>>();

            if rhs_references.len() != parts.connections.len() {
                // Not all connected identities meet the criteria above, so this is not a DoubleSortedWitnesses machine.
                return None;
            }

            if !parts.prover_functions.is_empty() {
                log::warn!(
                    "SortedWitness machine does not support prover functions.\
                    The following prover functions are ignored:\n{}",
                    parts.prover_functions.iter().format("\n")
                );
            }

            Some(SortedWitnesses {
                degree,
                rhs_references,
                connections: parts.connections.clone(),
                name,
                key_col,
                witness_positions,
                data: Default::default(),
                fixed_data,
            })
        })
    }
}

fn check_identity<T: FieldElement>(
    fixed_data: &FixedData<T>,
    id: &Identity<T>,
    degree: DegreeType,
) -> Option<PolyID> {
    // Looking for a lookup
    let send = match id {
        Identity::BusSend(bus_interaction) => bus_interaction,
        _ => return None,
    };
    let receive = send.try_match_static(&fixed_data.bus_receives)?;
    if !receive.has_arbitrary_multiplicity() {
        return None;
    }

    // Looking for NOTLAST $ [ A' - A ] in [ POSITIVE ]
    let left = &send.selected_payload;
    let right = &receive.selected_payload;
    if !right.selector.is_one() || left.expressions.len() != 1 {
        return None;
    }

    // Check for A' - A in the LHS
    let key_column = check_constraint(fixed_data, left.expressions.first().unwrap())?;

    let not_last = &left.selector;
    let positive = right.expressions.first().unwrap();

    // TODO this could be rather slow. We should check the code for identity instead
    // of evaluating it.
    for row in 0..(degree as usize) {
        let fixed_evaluator = FixedEvaluator::new(fixed_data, row, degree);
        let mut ev =
            PartialExpressionEvaluator::new(fixed_evaluator, &fixed_data.intermediate_definitions);
        let degree = degree as usize;
        let nl = ev.evaluate(not_last).ok()?.constant_value()?;
        if (row == degree - 1 && !nl.is_zero()) || (row < degree - 1 && !nl.is_one()) {
            return None;
        }
        let pos = ev.evaluate(positive).ok()?.constant_value()?;
        if pos != (row as u64 + 1).into() {
            return None;
        }
    }
    Some(key_column)
}

/// Checks that the identity has a constraint of the form `a' - a` as the first expression
/// on the left hand side and returns the ID of the witness column.
fn check_constraint<T: FieldElement>(
    fixed: &FixedData<T>,
    constraint: &Expression<T>,
) -> Option<PolyID> {
    let sort_constraint =
        match PartialExpressionEvaluator::new(SymbolicEvaluator, &fixed.intermediate_definitions)
            .evaluate(constraint)
        {
            Ok(c) => c,
            Err(_) => return None,
        };
    let mut coeff = sort_constraint.nonzero_coefficients();
    let first = coeff
        .next()
        .and_then(|(k, v)| k.try_as_column().map(|k| (k, v)))?;
    let second = coeff
        .next()
        .and_then(|(k, v)| k.try_as_column().map(|k| (k, v)))?;
    if coeff.next().is_some() {
        return None;
    }
    let key_column_id = match (first, second) {
        ((key, _), _) | (_, (key, _)) if !key.next => key,
        _ => return None,
    };
    if key_column_id.next || key_column_id.is_fixed() {
        return None;
    }
    let poly_next = AlgebraicReference {
        next: true,
        ..key_column_id.clone()
    };
    let pattern = AffineExpression::from_variable_id(AlgebraicVariable::Column(&poly_next))
        - AffineExpression::from_variable_id(AlgebraicVariable::Column(key_column_id));
    if sort_constraint != pattern {
        return None;
    }

    Some(key_column_id.poly_id)
}

impl<'a, T: FieldElement> Machine<'a, T> for SortedWitnesses<'a, T> {
    fn process_lookup_direct<'b, 'c, Q: QueryCallback<T>>(
        &mut self,
        _mutable_state: &'b MutableState<'a, T, Q>,
        _identity_id: u64,
        _values: &mut [LookupCell<'c, T>],
    ) -> Result<bool, EvalError<T>> {
        unimplemented!("Direct lookup not supported by machine {}.", self.name())
    }

    fn identity_ids(&self) -> Vec<u64> {
        self.rhs_references.keys().cloned().collect()
    }

    fn name(&self) -> &str {
        &self.name
    }

    fn process_plookup<Q: QueryCallback<T>>(
        &mut self,
        _mutable_state: &MutableState<'a, T, Q>,
        identity_id: u64,
        caller_rows: &RowPair<'_, 'a, T>,
    ) -> EvalResult<'a, T> {
        self.process_plookup_internal(identity_id, caller_rows)
    }

    fn take_witness_col_values<'b, Q: QueryCallback<T>>(
        &mut self,
        _mutable_state: &'b MutableState<'a, T, Q>,
    ) -> HashMap<String, Vec<T>> {
        let mut result = HashMap::new();

        let (mut keys, mut values): (Vec<_>, Vec<_>) =
            std::mem::take(&mut self.data).into_iter().unzip();

        let mut last_key = keys.last().cloned().unwrap_or_default();
        while keys.len() < self.degree as usize {
            last_key += 1u64.into();
            keys.push(last_key);
        }
        result.insert(self.fixed_data.column_name(&self.key_col).to_string(), keys);

        #[allow(clippy::iter_over_hash_type)]
        // TODO: Is this deterministic?
        for (col, &i) in &self.witness_positions {
            let mut col_values = values
                .iter_mut()
                .map(|row| std::mem::take(&mut row[i]).unwrap_or_default())
                .collect::<Vec<_>>();
            col_values.resize(self.degree as usize, 0.into());
            result.insert(self.fixed_data.column_name(col).to_string(), col_values);
        }

        result
    }
}

impl<'a, T: FieldElement> SortedWitnesses<'a, T> {
    fn process_plookup_internal(
        &mut self,
        identity_id: u64,
        caller_rows: &RowPair<'_, 'a, T>,
    ) -> EvalResult<'a, T> {
        let left = self.connections[&identity_id]
            .left
            .expressions
            .iter()
            .map(|e| caller_rows.evaluate(e).unwrap())
            .collect::<Vec<_>>();
        let rhs = self.rhs_references.get(&identity_id).unwrap();
        let key_index = rhs.iter().position(|&x| x.poly_id == self.key_col).unwrap();

        let key_value = left[key_index].constant_value().ok_or_else(|| {
            format!(
                "Value of unique key must be known: {} = {}",
                left[key_index], rhs[key_index]
            )
        })?;

        let mut assignments = EvalValue::complete(vec![]);
        let stored_values = self
            .data
            .entry(key_value)
            .or_insert_with(|| vec![None; self.witness_positions.len()]);
        for (l, &r) in left.iter().zip(rhs.iter()).skip(1) {
            let stored_value = &mut stored_values[self.witness_positions[&r.poly_id]];
            match stored_value {
                // There is a stored value
                Some(v) => {
                    match (l.clone() - (*v).into()).solve() {
                        Err(_) => {
                            // The LHS value is known and it is different from the stored one.
                            return Err(format!(
                                "Lookup mismatch: There is already a unique row with {} = \
                            {key_value} and {r} = {v}, but wanted to store {r} = {l}",
                                self.fixed_data.column_name(&self.key_col),
                            )
                            .into());
                        }
                        Ok(ass) => {
                            if !ass.is_empty() {
                                log::trace!(
                                    "Read {} = {key_value} -> {r} = {v}",
                                    self.fixed_data.column_name(&self.key_col)
                                );
                            }
                            assignments.combine(ass);
                        }
                    }
                }
                // There is no value stored yet.
                None => match l.constant_value() {
                    Some(v) => {
                        log::trace!(
                            "Stored {} = {key_value} -> {r} = {v}",
                            self.fixed_data.column_name(&self.key_col)
                        );
                        assignments = assignments.report_side_effect();
                        *stored_value = Some(v);
                    }
                    None => {
                        return Ok(EvalValue::incomplete(IncompleteCause::DataNotYetAvailable));
                    }
                },
            }
        }
        Ok(assignments)
    }
}

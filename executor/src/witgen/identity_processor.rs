use std::{collections::HashMap, sync::Mutex};

use lazy_static::lazy_static;
use powdr_ast::analyzed::{AlgebraicExpression as Expression, PolynomialIdentity};
use powdr_number::FieldElement;

use crate::witgen::data_structures::mutable_state::MutableState;
use crate::witgen::{global_constraints::CombinedRangeConstraintSet, EvalError};

use super::data_structures::identity::Identity;
use super::{
    affine_expression::AlgebraicVariable, processor::OuterQuery, rows::RowPair, EvalResult,
    EvalValue, IncompleteCause, QueryCallback,
};

/// Computes (value or range constraint) updates given a [RowPair] and [Identity].
/// The lifetimes mean the following:
/// - `'a`: The duration of the entire witness generation (e.g. references to identities)
/// - `'c`: The duration of this IdentityProcessor's lifetime (e.g. the reference to the mutable state)
pub struct IdentityProcessor<'a, 'c, T: FieldElement, Q: QueryCallback<T>> {
    mutable_state: &'c MutableState<'a, T, Q>,
}

impl<'a, 'c, T: FieldElement, Q: QueryCallback<T>> IdentityProcessor<'a, 'c, T, Q> {
    pub fn new(mutable_state: &'c MutableState<'a, T, Q>) -> Self {
        Self { mutable_state }
    }

    /// Given an identity and a row pair, tries to figure out additional values / range constraints
    /// for the given cells.
    /// Fails if any constraint was not satisfiable.
    /// Returns the updates.
    pub fn process_identity(
        &mut self,
        identity: &'a Identity<T>,
        rows: &RowPair<'_, 'a, T>,
    ) -> EvalResult<'a, T> {
        let result = match identity {
            Identity::Polynomial(identity) => self.process_polynomial_identity(identity, rows),
            Identity::BusSend(bus_interaction) => self.process_lookup_or_permutation(
                bus_interaction.identity_id,
                &bus_interaction.selected_payload,
                rows,
            ),
            // Bus receives are handled when they are matched with a send.
            Identity::BusReceive(_) => Ok(EvalValue::complete(vec![])),
            Identity::Connect(..) => {
                // TODO this is not the right cause.
                Ok(EvalValue::incomplete(IncompleteCause::SolvingFailed))
                // unimplemented!(
                //     "Identity of kind {kind:?} is not supported by the identity processor."
                // )
            }
        };
        report_identity_solving(identity, &result);
        result
    }

    fn process_polynomial_identity(
        &self,
        identity: &'a PolynomialIdentity<T>,
        rows: &RowPair<'_, 'a, T>,
    ) -> EvalResult<'a, T> {
        match rows.evaluate(&identity.expression) {
            Err(incomplete_cause) => Ok(EvalValue::incomplete(incomplete_cause)),
            Ok(evaluated) => evaluated.solve_with_range_constraints(rows),
        }
    }

    fn process_lookup_or_permutation(
        &mut self,
        id: u64,
        left: &'a powdr_ast::analyzed::SelectedExpressions<T>,
        rows: &RowPair<'_, 'a, T>,
    ) -> EvalResult<'a, T> {
        if let Some(status) = self.handle_left_selector(&left.selector, rows) {
            return Ok(status);
        }

        self.mutable_state.call(id, rows)
    }

    /// Handles the lookup that connects the current machine to the calling machine.
    /// Arguments:
    /// - `left`: The evaluation of the left side of the lookup (symbolic for unknown values).
    /// - `right`: The expressions on the right side of the lookup.
    /// - `current_rows`: The [RowPair] needed to evaluate the right side of the lookup.
    ///
    /// Returns:
    /// - `Ok(updates)`: The updates for the lookup.
    /// - `Err(e)`: If the constraint system is not satisfiable.
    pub fn process_link(
        &mut self,
        outer_query: &OuterQuery<'a, '_, T>,
        current_rows: &RowPair<'_, 'a, T>,
    ) -> EvalResult<'a, T> {
        let right = outer_query.connection.right;
        // sanity check that the right hand side selector is active
        current_rows
            .evaluate(&right.selector)
            .ok()
            .and_then(|affine_expression| affine_expression.constant_value())
            .and_then(|v| v.is_one().then_some(()))
            .ok_or(EvalError::Generic("Selector is not 1!".to_string()))?;

        let range_constraint =
            CombinedRangeConstraintSet::new(outer_query.caller_rows, current_rows);

        let mut updates = EvalValue::complete(vec![]);

        for (l, r) in outer_query.left.iter().zip(right.expressions.iter()) {
            match current_rows.evaluate(r) {
                Ok(r) => {
                    let result = (l.clone() - r).solve_with_range_constraints(&range_constraint)?;
                    updates.combine(result);
                }
                Err(e) => {
                    updates.status = updates.status.combine(e);
                }
            }
        }
        Ok(updates)
    }

    /// Returns updates of the left selector cannot be evaluated to 1, otherwise None.
    fn handle_left_selector(
        &self,
        left_selector: &'a Expression<T>,
        rows: &RowPair<'_, 'a, T>,
    ) -> Option<EvalValue<AlgebraicVariable<'a>, T>> {
        let value = match rows.evaluate(left_selector) {
            Err(incomplete_cause) => return Some(EvalValue::incomplete(incomplete_cause)),
            Ok(value) => value,
        };
        match value.constant_value() {
            Some(v) if v.is_zero() => Some(EvalValue::complete(vec![])),
            Some(v) if v.is_one() => None,
            _ => Some(EvalValue::incomplete(
                IncompleteCause::NonConstantLeftSelector,
            )),
        }
    }
}

pub struct IdentityData {
    pub invocations: u64,
    pub success: u64,
}

type IdentityID = u64;

lazy_static! {
    static ref STATISTICS: Mutex<HashMap<IdentityID, IdentityData>> =
        Mutex::new(Default::default());
}

fn report_identity_solving<T: FieldElement, K>(identity: &Identity<T>, result: &EvalResult<T, K>) {
    let success = result.as_ref().map(|r| r.is_complete()).unwrap_or_default() as u64;
    let mut stat = STATISTICS.lock().unwrap();
    stat.entry(identity.id())
        .and_modify(|s| {
            s.invocations += 1;
            s.success += success;
        })
        .or_insert(IdentityData {
            invocations: 1,
            success,
        });
}

pub fn get_and_reset_solving_statistics() -> HashMap<IdentityID, IdentityData> {
    let mut stat = STATISTICS.lock().unwrap();
    std::mem::take(&mut (*stat))
}

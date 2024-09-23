use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;

use num_traits::Zero;

use powdr_ast::analyzed::{
    AlgebraicBinaryOperation, AlgebraicBinaryOperator, AlgebraicExpression as Expression,
    AlgebraicReference, IdentityKind, PolyID, PolynomialType,
};

use powdr_number::FieldElement;

use crate::witgen::data_structures::column_map::{FixedColumnMap, WitnessColumnMap};
use crate::Identity;

use super::expression_evaluator::ExpressionEvaluator;
use super::range_constraints::RangeConstraint;
use super::symbolic_evaluator::SymbolicEvaluator;
use super::util::try_to_simple_poly;
use super::{Constraint, FixedData};

/// Trait that provides a range constraint on a symbolic variable if given by ID.
pub trait RangeConstraintSet<K, T: FieldElement> {
    fn range_constraint(&self, id: K) -> Option<RangeConstraint<T>>;
}

pub struct SimpleRangeConstraintSet<'a, T: FieldElement> {
    range_constraints: &'a BTreeMap<PolyID, RangeConstraint<T>>,
}

impl<'a, T: FieldElement> RangeConstraintSet<&AlgebraicReference, T>
    for SimpleRangeConstraintSet<'a, T>
{
    fn range_constraint(&self, id: &AlgebraicReference) -> Option<RangeConstraint<T>> {
        assert!(!id.next);
        self.range_constraints.get(&id.poly_id).cloned()
    }
}

/// A range constraint set that combines two other range constraint sets.
pub struct CombinedRangeConstraintSet<'a, R1, R2, K, T>
where
    T: FieldElement,
    R1: RangeConstraintSet<K, T>,
    R2: RangeConstraintSet<K, T>,
{
    range_constraints1: &'a R1,
    range_constraints2: &'a R2,
    _marker_k: PhantomData<K>,
    _marker_t: PhantomData<T>,
}

impl<'a, R1, R2, K, T> CombinedRangeConstraintSet<'a, R1, R2, K, T>
where
    T: FieldElement,
    R1: RangeConstraintSet<K, T>,
    R2: RangeConstraintSet<K, T>,
{
    pub fn new(range_constraints1: &'a R1, range_constraints2: &'a R2) -> Self {
        Self {
            range_constraints1,
            range_constraints2,
            _marker_k: PhantomData,
            _marker_t: PhantomData,
        }
    }
}

impl<'a, R1, R2, K, T> RangeConstraintSet<K, T> for CombinedRangeConstraintSet<'a, R1, R2, K, T>
where
    T: FieldElement,
    K: Copy,
    R1: RangeConstraintSet<K, T>,
    R2: RangeConstraintSet<K, T>,
{
    fn range_constraint(&self, id: K) -> Option<RangeConstraint<T>> {
        match (
            self.range_constraints1.range_constraint(id),
            self.range_constraints2.range_constraint(id),
        ) {
            (Some(c1), Some(c2)) => Some(c1.conjunction(&c2)),
            (Some(c), None) | (None, Some(c)) => Some(c),
            (None, None) => None,
        }
    }
}

#[derive(Clone)]
pub struct GlobalConstraints<T: FieldElement> {
    pub witness_constraints: WitnessColumnMap<Option<RangeConstraint<T>>>,
    pub fixed_constraints: FixedColumnMap<Option<RangeConstraint<T>>>,
}

impl<T: FieldElement> RangeConstraintSet<&AlgebraicReference, T> for GlobalConstraints<T> {
    fn range_constraint(&self, id: &AlgebraicReference) -> Option<RangeConstraint<T>> {
        assert!(!id.next);
        let poly_id = id.poly_id;
        match poly_id.ptype {
            PolynomialType::Constant => self.fixed_constraints[&poly_id].clone(),
            PolynomialType::Committed => self.witness_constraints[&poly_id].clone(),
            PolynomialType::Intermediate => None,
        }
    }
}

/// Determines global constraints on witness and fixed columns.
/// Removes identities that only serve to create range constraints from
/// the identities vector and returns the remaining identities.
/// Returns fixed data with the global constraints & the retained identities.
/// TODO at some point, we should check that they still hold.
pub fn set_global_constraints<'a, T: FieldElement>(
    fixed_data: FixedData<T>,
    identities: impl IntoIterator<Item = &'a Identity<T>>,
) -> (FixedData<T>, Vec<&'a Identity<T>>) {
    let mut known_constraints = BTreeMap::new();
    // For these columns, we know that they are not only constrained to those bits
    // but also have one row for each possible value.
    // It allows us to completely remove some lookups.
    let mut full_span = BTreeSet::new();
    for (poly_id, col) in fixed_data.fixed_cols.iter() {
        if let Some((cons, full)) = process_fixed_column(col.values_max_size()) {
            assert!(known_constraints.insert(poly_id, cons).is_none());
            if full {
                full_span.insert(poly_id);
            }
        }
    }
    let fixed_constraints = FixedColumnMap::from_indexed(
        known_constraints.iter().map(|(p, c)| (*p, Some(c.clone()))),
        fixed_data.fixed_cols.len(),
    );

    let mut retained_identities = vec![];
    let mut removed_identities = vec![];
    for identity in identities.into_iter() {
        let remove;
        (known_constraints, remove) =
            propagate_constraints(known_constraints, identity, &full_span);
        (if remove {
            &mut removed_identities
        } else {
            &mut retained_identities
        })
        .push(identity);
    }

    log::debug!("Determined the following global range constraints:");
    for (poly_id, con) in &known_constraints {
        if poly_id.ptype == PolynomialType::Committed {
            log::debug!("  {}: {con}", fixed_data.column_name(poly_id));
        }
    }

    log::debug!("Determined the following identities to be purely bit/range constraints:");
    for id in removed_identities {
        log::debug!("  {id}");
    }

    let mut witness_constraints: WitnessColumnMap<Option<RangeConstraint<T>>> =
        fixed_data.witness_map_with(None);
    for (poly_id, con) in known_constraints {
        if poly_id.ptype == PolynomialType::Committed {
            // It's theoretically possible to have a constraint for both X and X'.
            // In that case, we take the conjunction.
            let con = witness_constraints[&poly_id]
                .as_ref()
                .map(|existing_con| existing_con.conjunction(&con))
                .unwrap_or(con);
            witness_constraints[&poly_id] = Some(con);
        }
    }

    let global_constraints = GlobalConstraints {
        witness_constraints,
        fixed_constraints,
    };

    (
        fixed_data.with_global_range_constraints(global_constraints),
        retained_identities,
    )
}

/// Analyzes a fixed column and checks if its values correspond exactly
/// to a certain bit pattern.
/// TODO do this on the symbolic definition instead of the values.
fn process_fixed_column<T: FieldElement>(fixed: &[T]) -> Option<(RangeConstraint<T>, bool)> {
    if let Some(bit) = smallest_period_candidate(fixed) {
        let mask = T::Integer::from(((1 << bit) - 1) as u64);
        if fixed
            .iter()
            .enumerate()
            .all(|(i, v)| v.to_integer() == T::Integer::from(i as u64) & mask)
        {
            return Some((RangeConstraint::from_mask(mask), true));
        }
    }
    let mut mask = T::Integer::zero();
    for v in fixed.iter() {
        mask |= v.to_integer();
    }

    Some((RangeConstraint::from_mask(mask), false))
}

/// Deduces new range constraints on witness columns from constraints on fixed columns
/// and identities. Note that these constraints hold globally, i.e. for all rows.
/// If the returned flag is true, the identity can be removed, because it contains
/// no further information than the range constraint.
fn propagate_constraints<T: FieldElement>(
    mut known_constraints: BTreeMap<PolyID, RangeConstraint<T>>,
    identity: &Identity<T>,
    full_span: &BTreeSet<PolyID>,
) -> (BTreeMap<PolyID, RangeConstraint<T>>, bool) {
    let mut remove = false;
    match identity.kind {
        IdentityKind::Polynomial => {
            if let Some((p, constraint)) = is_binary_constraint(identity.expression_for_poly_id()) {
                assert!(known_constraints.insert(p, constraint).is_none());
                remove = true;
            } else {
                for (p, c) in
                    try_transfer_constraints(identity.expression_for_poly_id(), &known_constraints)
                {
                    known_constraints
                        .entry(p)
                        .and_modify(|existing| *existing = existing.conjunction(&c))
                        .or_insert(c);
                }
            }
        }
        IdentityKind::Plookup | IdentityKind::Permutation | IdentityKind::Connect => {
            if identity.left.selector.is_some() || identity.right.selector.is_some() {
                return (known_constraints, false);
            }
            for (left, right) in identity
                .left
                .expressions
                .iter()
                .zip(identity.right.expressions.iter())
            {
                if let (Some(left), Some(right)) =
                    (try_to_simple_poly(left), try_to_simple_poly(right))
                {
                    if let Some(constraint) = known_constraints.get(&right.poly_id).cloned() {
                        known_constraints
                            .entry(left.poly_id)
                            .and_modify(|existing| *existing = existing.conjunction(&constraint))
                            .or_insert(constraint);
                    }
                }
            }
            if identity.kind == IdentityKind::Plookup && identity.right.expressions.len() == 1 {
                // We can only remove the lookup if the RHS is a fixed polynomial that
                // provides all values in the span.
                if let Some(name) = try_to_simple_poly(&identity.right.expressions[0]) {
                    if try_to_simple_poly(&identity.left.expressions[0]).is_some()
                        && full_span.contains(&name.poly_id)
                    {
                        remove = true;
                    }
                }
            }
        }
    }

    (known_constraints, remove)
}

/// Get simple expression roots for a given expression.
///
/// This function recursively evaluates an algebraic expression and attempts
/// to extract roots from it. The roots are returned as a vector of evaluation
/// values containing references to algebraic expressions and field elements.
///
/// # Parameters
///
/// - `expr`: A reference to an `Expression` of type `T`.
///
/// # Returns
///
/// An `Option` containing a vector of `EvalValue<&AlgebraicReference, T>`
/// if the roots can be successfully extracted, otherwise `None`.
pub fn find_roots<T: FieldElement>(
    expr: &Expression<T>,
) -> Option<Vec<crate::witgen::EvalValue<&AlgebraicReference, T>>> {
    match expr {
        Expression::BinaryOperation(AlgebraicBinaryOperation {
            left,
            op: AlgebraicBinaryOperator::Mul,
            right,
        }) => {
            let right_root = find_roots(right)?;
            let mut left_roots = find_roots(left)?;

            if !left_roots.is_empty() && !right_root.is_empty() {
                if let ([(id1, Constraint::Assignment(_))], [(id2, Constraint::Assignment(_))]) = (
                    &left_roots[0].constraints[..],
                    &right_root[0].constraints[..],
                ) {
                    if id1 != id2 {
                        return None;
                    }
                }
            }

            left_roots.extend(right_root);
            Some(left_roots)
        }
        Expression::Number(_) => Some(vec![]),
        _ => {
            let symbolic_ev = SymbolicEvaluator;
            let root = ExpressionEvaluator::new(symbolic_ev)
                .evaluate(expr)
                .ok()
                .and_then(|l| l.solve().ok())?;

            match root.constraints[..] {
                [] => Some(vec![]),
                [(id, Constraint::Assignment(_))] if id.is_witness() => Some(vec![root]),
                _ => None,
            }
        }
    }
}

/// Tries to find "X * (1 - X) = 0"
fn is_binary_constraint<T: FieldElement>(
    expr: &Expression<T>,
) -> Option<(PolyID, RangeConstraint<T>)> {
    // TODO Write a proper pattern matching engine.
    if let Expression::BinaryOperation(AlgebraicBinaryOperation {
        left,
        op: AlgebraicBinaryOperator::Sub,
        right,
    }) = expr
    {
        if let Expression::Number(n) = right.as_ref() {
            if n.is_zero() {
                return is_binary_constraint(left.as_ref());
            }
        }
    } else if let Expression::BinaryOperation(AlgebraicBinaryOperation {
        left: _,
        op: AlgebraicBinaryOperator::Mul,
        right: _,
    }) = expr
    {
        if let Some(roots) = find_roots(expr) {
            // For setting mask range constaints at least two roots is needed.
            if roots.len() > 1 {
                let poly_id = roots[0].constraints[0].0.poly_id;
                let mut root_values: BTreeSet<T> = BTreeSet::new();
                for root in roots {
                    if let (_, Constraint::Assignment(value)) = root.constraints[0] {
                        root_values.insert(value);
                    } else {
                        return None;
                    }
                }

                return Some((poly_id, RangeConstraint::from_set(root_values)?));
            }
        }
    }
    None
}

/// Tries to transfer constraints in a linear expression.
fn try_transfer_constraints<T: FieldElement>(
    expr: &Expression<T>,
    known_constraints: &BTreeMap<PolyID, RangeConstraint<T>>,
) -> Vec<(PolyID, RangeConstraint<T>)> {
    if expr.contains_next_ref() {
        return vec![];
    }

    let symbolic_ev = SymbolicEvaluator;
    let Some(aff_expr) = ExpressionEvaluator::new(symbolic_ev).evaluate(expr).ok() else {
        return vec![];
    };

    let range_constraints = SimpleRangeConstraintSet {
        range_constraints: known_constraints,
    };
    let Some(result) = aff_expr
        .solve_with_range_constraints(&range_constraints)
        .ok()
    else {
        return vec![];
    };
    result
        .constraints
        .into_iter()
        .flat_map(|(poly, cons)| {
            if let Constraint::RangeConstraint(cons) = cons {
                assert!(!poly.next);
                Some((poly.poly_id, cons))
            } else {
                None
            }
        })
        .collect()
}

fn smallest_period_candidate<T: FieldElement>(fixed: &[T]) -> Option<u64> {
    if fixed.first() != Some(&0.into()) {
        return None;
    }
    (1..63).find(|bit| fixed.last() == Some(&((1u64 << bit) - 1).into()))
}

#[cfg(test)]
mod test {
    use std::collections::BTreeMap;

    use itertools::Itertools;
    use powdr_ast::analyzed::{PolyID, PolynomialType};
    use powdr_number::GoldilocksField;
    use pretty_assertions::assert_eq;
    use test_log::test;

    use crate::constant_evaluator::get_uniquely_sized;

    use super::*;

    #[test]
    fn all_zeros() {
        let fixed = [0.into(); 4];
        assert_eq!(
            process_fixed_column::<GoldilocksField>(&fixed),
            Some((RangeConstraint::from_value(0.into()), false))
        );
    }

    #[test]
    fn zero_one() {
        let fixed = [0, 1, 0, 1].map(|v| v.into());
        assert_eq!(
            process_fixed_column::<GoldilocksField>(&fixed),
            Some((RangeConstraint::from_mask(1_u32), true))
        );
    }

    #[test]
    fn zero_one_two_three() {
        let fixed = [0, 1, 2, 3].map(|v| v.into());
        assert_eq!(
            process_fixed_column::<GoldilocksField>(&fixed),
            Some((RangeConstraint::from_mask(3_u32), true))
        );
    }

    #[test]
    fn various_with_bit_mask() {
        let fixed = [0, 6, 0x0100, 0x1100, 2].map(|v| v.into());
        assert_eq!(
            process_fixed_column::<GoldilocksField>(&fixed),
            Some((RangeConstraint::from_mask(0x1106_u32), false))
        );
    }

    fn constant_poly_id(i: u64) -> PolyID {
        PolyID {
            ptype: PolynomialType::Constant,
            id: i,
        }
    }

    fn witness_poly_id(i: u64) -> PolyID {
        PolyID {
            ptype: PolynomialType::Committed,
            id: i,
        }
    }

    #[test]
    fn constraints_propagation() {
        let pil_source = r"
namespace Global(2**20);
    col fixed BYTE(i) { i & 0xff };
    col fixed BYTE2(i) { i & 0xffff };
    col fixed SHIFTED(i) { i & 0xff0 };
    col witness A;
    // A bit more complicated to see that the 'pattern matcher' works properly.
    (1 - A + 0) * (A + 1 - 1) = 0;
    col witness B;
    [ B ] in [ BYTE ];
    col witness C;
    C = A * 512 + B;
    col witness D;
    [ D ] in [ BYTE ];
    [ D ] in [ SHIFTED ];
";
        let analyzed = powdr_pil_analyzer::analyze_string::<GoldilocksField>(pil_source).unwrap();
        let constants = crate::constant_evaluator::generate(&analyzed);
        let constants = get_uniquely_sized(&constants).unwrap();
        let fixed_polys = (0..constants.len())
            .map(|i| constant_poly_id(i as u64))
            .collect::<Vec<_>>();
        let mut known_constraints = fixed_polys
            .iter()
            .zip(&constants)
            .filter_map(|(&poly_id, (_, values))| {
                process_fixed_column(values).map(|(constraint, _full)| (poly_id, constraint))
            })
            .collect::<BTreeMap<_, _>>();
        assert_eq!(
            known_constraints,
            vec![
                // Global.BYTE
                (constant_poly_id(0), RangeConstraint::from_max_bit(7)),
                // Global.BYTE2
                (constant_poly_id(1), RangeConstraint::from_max_bit(15)),
                // Global.SHIFTED
                (constant_poly_id(2), RangeConstraint::from_mask(0xff0_u32)),
            ]
            .into_iter()
            .collect()
        );
        for identity in &analyzed.identities {
            (known_constraints, _) =
                propagate_constraints(known_constraints, identity, &Default::default());
        }
        assert_eq!(
            known_constraints,
            vec![
                // Global.A
                (witness_poly_id(0), RangeConstraint::from_max_bit(0)),
                // Global.B
                (witness_poly_id(1), RangeConstraint::from_max_bit(7)),
                // Global.C
                (witness_poly_id(2), RangeConstraint::from_mask(0x2ff_u32)),
                // Global.D
                (witness_poly_id(3), RangeConstraint::from_mask(0xf0_u32)),
                // Global.BYTE
                (constant_poly_id(0), RangeConstraint::from_max_bit(7)),
                // Global.BYTE2
                (constant_poly_id(1), RangeConstraint::from_max_bit(15)),
                // Global.SHIFTED
                (constant_poly_id(2), RangeConstraint::from_mask(0xff0_u32)),
            ]
            .into_iter()
            .collect::<BTreeMap<_, _>>()
        );
    }

    #[test]
    fn constraints_propagation_2() {
        let pil_source = r"
namespace Global(2**20);
    col witness Y;
    col witness Z;
    Y * (Y - 1) * (Y - 4) * (Y * 3) * (Y - 5) * (Y - 4)  = 0;
    Z * (Z - 2 ** 30) * (Z - 2 ** 31) * (Z - (2 ** 30 + 2 ** 31)) = 0;
";
        let analyzed = powdr_pil_analyzer::analyze_string::<GoldilocksField>(pil_source);
        let mut known_constraints: BTreeMap<PolyID, RangeConstraint<GoldilocksField>> =
            BTreeMap::new();
        for identity in &analyzed.identities {
            (known_constraints, _) =
                propagate_constraints(known_constraints, identity, &Default::default());
        }
        let _known_constraints_vec: Vec<_> = known_constraints.values().collect_vec();

        assert_eq!(
            known_constraints,
            vec![
                // Global.Y
                (witness_poly_id(0), RangeConstraint::from_mask(0x5_u32)),
                // Global.Z
                (
                    witness_poly_id(1),
                    RangeConstraint::from_mask(0xc0000000u32)
                ),
            ]
            .into_iter()
            .collect::<BTreeMap<_, _>>()
        );
    }

    #[test]
    fn no_remove_identity() {
        // There used to be a bug where the lookup would be removed because the code
        // incorrectly determined it to be a pure range constraint, but it would actually not
        // be able to derive the full constraint.
        let pil_source = r"
namespace Global(1024);
    let bytes: col = |i| i % 256;
    let X;
    [ X * 4 ] in [ bytes ];
";
        let analyzed = powdr_pil_analyzer::analyze_string::<GoldilocksField>(pil_source).unwrap();
        let known_constraints = vec![(constant_poly_id(0), RangeConstraint::from_max_bit(7))]
            .into_iter()
            .collect();
        assert_eq!(analyzed.identities.len(), 1);
        let (_, removed) = propagate_constraints(
            known_constraints,
            analyzed.identities.first().unwrap(),
            &Default::default(),
        );
        assert!(!removed);
    }
}

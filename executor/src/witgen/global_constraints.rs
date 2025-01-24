use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;

use num_traits::Zero;

use num_traits::One;
use powdr_ast::analyzed::{
    AlgebraicBinaryOperation, AlgebraicBinaryOperator, AlgebraicExpression as Expression,
    AlgebraicReference, AlgebraicReferenceThin, PolyID, PolynomialType,
};

use powdr_number::FieldElement;

use crate::witgen::data_structures::column_map::{FixedColumnMap, WitnessColumnMap};

use super::affine_expression::AlgebraicVariable;
use super::data_structures::identity::{BusReceive, Identity};
use super::evaluators::partial_expression_evaluator::PartialExpressionEvaluator;
use super::evaluators::symbolic_evaluator::SymbolicEvaluator;
use super::range_constraints::RangeConstraint;
use super::util::try_to_simple_poly;
use super::{Constraint, FixedData};
use powdr_ast::analyzed::AlgebraicExpression;

/// Trait that provides a range constraint on a symbolic variable if given by ID.
pub trait RangeConstraintSet<K, T: FieldElement> {
    fn range_constraint(&self, id: K) -> Option<RangeConstraint<T>>;
}

pub struct SimpleRangeConstraintSet<'a, T: FieldElement> {
    range_constraints: &'a BTreeMap<PolyID, RangeConstraint<T>>,
}

impl<'a, T: FieldElement> RangeConstraintSet<AlgebraicVariable<'a>, T>
    for SimpleRangeConstraintSet<'a, T>
{
    fn range_constraint(&self, id: AlgebraicVariable<'a>) -> Option<RangeConstraint<T>> {
        match id {
            AlgebraicVariable::Column(id) => {
                assert!(!id.next);
                self.range_constraints.get(&id.poly_id).cloned()
            }
            // No range constraints stored for publics.
            AlgebraicVariable::Public(_) => None,
        }
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

impl<R1, R2, K, T> RangeConstraintSet<K, T> for CombinedRangeConstraintSet<'_, R1, R2, K, T>
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
/// fixed data, sets the range constraints and returns the updated fixed data.
/// TODO at some point, we should check that they still hold.
pub fn set_global_constraints<T: FieldElement>(fixed_data: FixedData<T>) -> FixedData<T> {
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
    for identity in fixed_data.identities.iter() {
        let remove = propagate_constraints(
            &fixed_data.intermediate_definitions,
            &mut known_constraints,
            identity,
            &full_span,
            &fixed_data.bus_receives,
        );

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
    for id in &removed_identities {
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

    // Can't have references to fixed_data in the call to filter_identities.
    let retained_identity_ids = retained_identities
        .iter()
        .map(|identity| identity.id())
        .collect::<BTreeSet<_>>();
    fixed_data
        .with_global_range_constraints(global_constraints)
        .filter_identities(|_, identity| retained_identity_ids.contains(&identity.id()))
}

/// Analyzes a fixed column and checks if its values correspond exactly
/// to a certain bit pattern.
/// TODO do this on the symbolic definition instead of the values.
fn process_fixed_column<T: FieldElement>(fixed: &[T]) -> Option<(RangeConstraint<T>, bool)> {
    if let Some(bit) = smallest_period_candidate(fixed) {
        let mask = T::Integer::from((1u64 << bit) - 1);
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

fn add_constraint<T: FieldElement>(
    known_constraints: &mut BTreeMap<PolyID, RangeConstraint<T>>,
    poly_id: PolyID,
    constraint: RangeConstraint<T>,
) {
    known_constraints
        .entry(poly_id)
        .and_modify(|existing| *existing = existing.conjunction(&constraint))
        .or_insert(constraint);
}

/// Deduces new range constraints on witness columns from constraints on fixed columns
/// and identities. Note that these constraints hold globally, i.e. for all rows.
/// If the returned flag is true, the identity can be removed, because it contains
/// no further information than the range constraint.
fn propagate_constraints<T: FieldElement>(
    intermediate_definitions: &BTreeMap<AlgebraicReferenceThin, AlgebraicExpression<T>>,
    known_constraints: &mut BTreeMap<PolyID, RangeConstraint<T>>,
    identity: &Identity<T>,
    full_span: &BTreeSet<PolyID>,
    bus_receives: &BTreeMap<T, BusReceive<T>>,
) -> bool {
    match identity {
        Identity::Polynomial(identity) => {
            if let Some(p) = is_binary_constraint(intermediate_definitions, &identity.expression) {
                add_constraint(known_constraints, p, RangeConstraint::from_max_bit(0));
                true
            } else {
                for (p, c) in try_transfer_constraints(
                    intermediate_definitions,
                    &identity.expression,
                    known_constraints,
                ) {
                    add_constraint(known_constraints, p, c);
                }
                false
            }
        }
        // A bus receive might be part of a range constraint, which is handled in the
        // bus send case. Even then, it is *not* removed, because it might *also* be
        // part of a conditional range constraint.
        Identity::BusReceive(..) => false,
        Identity::BusSend(send) => {
            let receive = send.try_match_static(bus_receives).unwrap();
            if !send.selected_payload.selector.is_one() {
                return false;
            }

            // For lookups of the form [ a, b, ... ] in [ c, d, ... ], where a, b, ... are columns,
            // transfer constraints from the right to the left side.
            // A special case of this would be [ x ] in [ RANGE ], where RANGE is in the full span.
            for (left, right) in send
                .selected_payload
                .expressions
                .iter()
                .zip(receive.selected_payload.expressions.iter())
            {
                if let (Some(left), Some(right)) =
                    (try_to_simple_poly(left), try_to_simple_poly(right))
                {
                    if let Some(constraint) = known_constraints.get(&right.poly_id).cloned() {
                        add_constraint(known_constraints, left.poly_id, constraint);
                    }
                }
            }

            // Detect [ x ] in [ RANGE ], where RANGE is in the full span.
            // In that case, we can remove the bus interaction pair,
            // because its only function is to enforce the range constraint.
            if receive.selected_payload.expressions.len() == 1
                && receive.has_arbitrary_multiplicity()
                && receive.selected_payload.selector.is_one()
            {
                if let (Some(_), Some(right_ref)) = (
                    // The range constraint has been transferred from right to left
                    // by the above code iff. both expressions can be converted to
                    // simple polynomials.
                    try_to_simple_poly(&send.selected_payload.expressions[0]),
                    try_to_simple_poly(&receive.selected_payload.expressions[0]),
                ) {
                    if full_span.contains(&right_ref.poly_id) {
                        return true;
                    }
                }
            }
            false
        }
        Identity::Connect(..) => {
            // we do not handle connect identities yet, so we do nothing
            false
        }
    }
}

/// Tries to find "X * (1 - X) = 0"
fn is_binary_constraint<T: FieldElement>(
    intermediate_definitions: &BTreeMap<AlgebraicReferenceThin, AlgebraicExpression<T>>,
    expr: &Expression<T>,
) -> Option<PolyID> {
    // TODO Write a proper pattern matching engine.
    if let Expression::BinaryOperation(AlgebraicBinaryOperation {
        left,
        op: AlgebraicBinaryOperator::Sub,
        right,
    }) = expr
    {
        if let Expression::Number(n) = right.as_ref() {
            if n.is_zero() {
                return is_binary_constraint(intermediate_definitions, left.as_ref());
            }
        }
    } else if let Expression::BinaryOperation(AlgebraicBinaryOperation {
        left,
        op: AlgebraicBinaryOperator::Mul,
        right,
    }) = expr
    {
        let mut evaluator =
            PartialExpressionEvaluator::new(SymbolicEvaluator, intermediate_definitions);
        let left_root = evaluator.evaluate(left).ok().and_then(|l| l.solve().ok())?;
        let right_root = evaluator
            .evaluate(right)
            .ok()
            .and_then(|r| r.solve().ok())?;
        if let ([(id1, Constraint::Assignment(value1))], [(id2, Constraint::Assignment(value2))]) =
            (&left_root.constraints[..], &right_root.constraints[..])
        {
            // We expect range constraints only on columns, because the verifier could easily
            // check range constraints on publics themselves.
            if let (AlgebraicVariable::Column(id1), AlgebraicVariable::Column(id2)) = (id1, id2) {
                if id1 != id2 || !id2.is_witness() {
                    return None;
                }
                if (value1.is_zero() && value2.is_one()) || (value1.is_one() && value2.is_zero()) {
                    return Some(id1.poly_id);
                }
            }
        }
    }
    None
}

/// Tries to transfer constraints in a linear expression.
fn try_transfer_constraints<T: FieldElement>(
    intermediate_definitions: &BTreeMap<AlgebraicReferenceThin, AlgebraicExpression<T>>,
    expr: &Expression<T>,
    known_constraints: &BTreeMap<PolyID, RangeConstraint<T>>,
) -> Vec<(PolyID, RangeConstraint<T>)> {
    if expr.contains_next_ref() {
        return vec![];
    }

    let Some(aff_expr) =
        PartialExpressionEvaluator::new(SymbolicEvaluator, intermediate_definitions)
            .evaluate(expr)
            .ok()
    else {
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
        .flat_map(|(poly, cons)| match poly {
            AlgebraicVariable::Column(poly) => {
                if let Constraint::RangeConstraint(cons) = cons {
                    assert!(!poly.next);
                    Some((poly.poly_id, cons))
                } else {
                    None
                }
            }
            AlgebraicVariable::Public(_) => unimplemented!(),
        })
        .collect()
}

fn smallest_period_candidate<T: FieldElement>(fixed: &[T]) -> Option<u64> {
    if fixed.first() != Some(&0.into()) {
        return None;
    }
    let max_bits = T::BITS.min(64);
    (1..max_bits as u64).find(|bit| fixed.last() == Some(&((1u64 << bit) - 1).into()))
}

#[cfg(test)]
mod test {
    use std::collections::BTreeMap;

    use powdr_ast::analyzed::{Analyzed, PolyID, PolynomialType};
    use powdr_number::GoldilocksField;
    use pretty_assertions::assert_eq;
    use test_log::test;

    use crate::{
        constant_evaluator::get_uniquely_sized,
        witgen::data_structures::identity::convert_identities,
    };

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

    fn identities_and_receives<T: FieldElement>(
        analyzed: &Analyzed<T>,
    ) -> (Vec<Identity<T>>, BTreeMap<T, BusReceive<T>>) {
        let identities = convert_identities(analyzed);
        let bus_receives = identities
            .iter()
            .filter_map(|identity| match identity {
                Identity::BusReceive(id) => Some((id.bus_id, id.clone())),
                _ => None,
            })
            .collect();
        (identities, bus_receives)
    }

    #[test]
    fn constraints_propagation() {
        let pil_source = r"
namespace std::convert;
    let fe = [];
namespace Global(2**20);
    col fixed BYTE(i) { std::convert::fe(i & 0xff) };
    col fixed BYTE2(i) { std::convert::fe(i & 0xffff) };
    col fixed SHIFTED(i) { std::convert::fe(i & 0xff0) };
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
        let constraints_and_spans = fixed_polys
            .iter()
            .zip(&constants)
            .filter_map(|(&poly_id, (_, values))| {
                process_fixed_column(values).map(|(constraint, full)| (poly_id, (constraint, full)))
            })
            .collect::<BTreeMap<_, _>>();
        let full_span = constraints_and_spans
            .iter()
            .filter_map(|(p, (_, full))| full.then_some(*p))
            .collect();
        let mut known_constraints = constraints_and_spans
            .into_iter()
            .map(|(p, (c, _))| (p, c))
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
        let (identities, receives) = identities_and_receives(&analyzed);
        for identity in &identities {
            propagate_constraints(
                &BTreeMap::new(),
                &mut known_constraints,
                identity,
                &full_span,
                &receives,
            );
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
    fn constraints_propagation_phantom_lookups() {
        // The same test as above, but with a phantom lookups.
        let pil_source = r"
namespace std::convert;
    let fe = [];
namespace Global(2**20);
    // Add multiplicity columns
    col witness byte_multiplicities;
    col witness shifted_multiplicities;

    col fixed BYTE(i) { std::convert::fe(i & 0xff) };
    col fixed BYTE2(i) { std::convert::fe(i & 0xffff) };
    col fixed SHIFTED(i) { std::convert::fe(i & 0xff0) };
    col witness A;
    // A bit more complicated to see that the 'pattern matcher' works properly.
    (1 - A + 0) * (A + 1 - 1) = 0;
    col witness B;
    Constr::PhantomLookup((Option::None, Option::None), [(B, BYTE)], byte_multiplicities);
    col witness C;
    C = A * 512 + B;
    col witness D;
    Constr::PhantomLookup((Option::None, Option::None), [(D, BYTE)], byte_multiplicities);
    Constr::PhantomLookup((Option::None, Option::None), [(D, SHIFTED)], shifted_multiplicities);
";
        let analyzed = powdr_pil_analyzer::analyze_string::<GoldilocksField>(pil_source).unwrap();
        let constants = crate::constant_evaluator::generate(&analyzed);
        let constants = get_uniquely_sized(&constants).unwrap();
        let fixed_polys = (0..constants.len())
            .map(|i| constant_poly_id(i as u64))
            .collect::<Vec<_>>();
        let constraints_and_spans = fixed_polys
            .iter()
            .zip(&constants)
            .filter_map(|(&poly_id, (_, values))| {
                process_fixed_column(values).map(|(constraint, full)| (poly_id, (constraint, full)))
            })
            .collect::<BTreeMap<_, _>>();
        let full_span = constraints_and_spans
            .iter()
            .filter_map(|(p, (_, full))| full.then_some(*p))
            .collect();
        let mut known_constraints = constraints_and_spans
            .into_iter()
            .map(|(p, (c, _))| (p, c))
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
        let (identities, receives) = identities_and_receives(&analyzed);
        for identity in &identities {
            propagate_constraints(
                &BTreeMap::new(),
                &mut known_constraints,
                identity,
                &full_span,
                &receives,
            );
        }
        assert_eq!(
            known_constraints,
            vec![
                // Global.A
                (witness_poly_id(2), RangeConstraint::from_max_bit(0)),
                // Global.B
                (witness_poly_id(3), RangeConstraint::from_max_bit(7)),
                // Global.C
                (witness_poly_id(4), RangeConstraint::from_mask(0x2ff_u32)),
                // Global.D
                (witness_poly_id(5), RangeConstraint::from_mask(0xf0_u32)),
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
    fn no_remove_identity() {
        // There used to be a bug where the lookup would be removed because the code
        // incorrectly determined it to be a pure range constraint, but it would actually not
        // be able to derive the full constraint.
        let pil_source = r"
namespace std::convert;
    let fe = [];
namespace Global(1024);
    let bytes: col = |i| std::convert::fe(i % 256);
    let X;
    [ X * 4 ] in [ bytes ];
";
        let analyzed = powdr_pil_analyzer::analyze_string::<GoldilocksField>(pil_source).unwrap();
        let mut known_constraints = vec![(constant_poly_id(0), RangeConstraint::from_max_bit(7))]
            .into_iter()
            .collect();
        let (identities, receives) = identities_and_receives(&analyzed);
        let removed = propagate_constraints(
            &BTreeMap::new(),
            &mut known_constraints,
            identities.first().unwrap(),
            &Default::default(),
            &receives,
        );
        assert!(!removed);
    }
}

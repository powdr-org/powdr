use core::fmt;
use std::{cmp::max, collections::BTreeMap, ops::RangeFrom};

use itertools::Itertools;
use powdr_ast::{
    analyzed::{
        AlgebraicExpression, AlgebraicUnaryOperator, Analyzed, ConnectIdentity,
        Identity as AnalyzedIdentity, LookupIdentity, PermutationIdentity,
        PhantomBusInteractionIdentity, PhantomLookupIdentity, PhantomPermutationIdentity,
        PolynomialIdentity, SelectedExpressions,
    },
    parsed::visitor::Children,
};
use powdr_number::FieldElement;

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct BusSend<T> {
    /// The identity ID is globally unique among identities.
    pub identity_id: u64,
    /// The ID of the bus this send sends to.
    pub bus_id: AlgebraicExpression<T>,
    /// The payload sent to the bus, with a selector.
    pub selected_payload: SelectedExpressions<T>,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct BusReceive<T> {
    /// The identity ID is globally unique among identities.
    pub identity_id: u64,
    /// The ID of the bus this receive listens on.
    /// There should be exactly one receive for each bus, but there can be
    /// multiple sends.
    pub bus_id: T,
    /// The payload received from the bus, with a selector.
    /// The selector is an expression that might or might not reference
    /// the multiplicity column, but it should always evaluate to a
    /// binary value. If it is zero, the multiplicity must be zero as well.
    /// For example, it could also be a binary fixed column, indicating
    /// where the multiplicity can be non-zero.
    pub selected_payload: SelectedExpressions<T>,
    /// The multiplicity with which the payload is received from the bus.
    /// None if this interaction comes from the RHS of a native lookup,
    /// as native lookup arguments don't require the multiplicity to be
    /// committed.
    /// Note that this is the absolute multiplicity, i.e., the negation has
    /// been removed.
    pub multiplicity: Option<AlgebraicExpression<T>>,
}

impl<T: FieldElement> BusSend<T> {
    /// Tries to find a matching receive by matching the bus ID
    /// if it is statically known. Receives are uniquely identified by
    /// the bus ID. Returns None if the sender's bus ID is not statically known
    /// and panics if there is no matching receive.
    pub fn try_match_static<'a>(
        &self,
        receives: &'a BTreeMap<T, BusReceive<T>>,
    ) -> Option<&'a BusReceive<T>> {
        let bus_id = self.bus_id()?;
        Some(
            receives
                .get(&bus_id)
                .unwrap_or_else(|| panic!("No matching receive found for bus ID {bus_id}.")),
        )
    }

    /// Returns the bus ID if it is a static number.
    /// Sends and receives can be matched by matching the bus ID.
    pub fn bus_id(&self) -> Option<T> {
        match &self.bus_id {
            AlgebraicExpression::Number(id) => Some(*id),
            _ => None,
        }
    }
}

impl<T: FieldElement> BusReceive<T> {
    /// Returns true if the multiplicity of the receive can be an arbitrary value.
    /// This means that an arbitrary number of rows on the sending side with
    /// the same values can match a single row on the receiving end.
    /// Unconstrained receives are equivalent to the RHS of a lookup,
    /// while 0-1-constrained receives are equivalent to the RHS of a permutation.
    pub fn has_arbitrary_multiplicity(&self) -> bool {
        // TODO: This always works in practice, but we should properly check the
        // range constraints on the multiplicity column.
        self.multiplicity.as_ref() != Some(&self.selected_payload.selector)
    }
}

impl<T> Children<AlgebraicExpression<T>> for BusSend<T> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        self.selected_payload.children_mut()
    }
    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        self.selected_payload.children()
    }
}

impl<T> Children<AlgebraicExpression<T>> for BusReceive<T> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        Box::new(
            self.selected_payload
                .children_mut()
                .chain(self.multiplicity.iter_mut()),
        )
    }
    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        Box::new(
            self.selected_payload
                .children()
                .chain(self.multiplicity.iter()),
        )
    }
}

impl<T: fmt::Display> fmt::Display for BusSend<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Send(payload={}, bus_id={}, identity_id={})",
            self.selected_payload, self.bus_id, self.identity_id
        )
    }
}

impl<T: fmt::Display> fmt::Display for BusReceive<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let multiplicity = self
            .multiplicity
            .as_ref()
            .map_or("None".to_string(), ToString::to_string);
        write!(
            f,
            "Receive(payload={}, multiplicity={}, bus_id={}, identity_id={})",
            self.selected_payload, multiplicity, self.bus_id, self.identity_id
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, derive_more::Display)]
/// A constraint in the constraint system.
/// It is similar to [powdr_ast::analyzed::Identity], but abstracts
/// over (phantom) lookups, permutations, and bus interactions.
/// Instead, they are represented as a (pair of) bus send and bus receive.
pub enum Identity<T> {
    Polynomial(PolynomialIdentity<T>),
    Connect(ConnectIdentity<T>),
    BusSend(BusSend<T>),
    BusReceive(BusReceive<T>),
}

impl<T> Children<AlgebraicExpression<T>> for Identity<T> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        match self {
            Identity::Polynomial(i) => i.children_mut(),
            Identity::Connect(i) => i.children_mut(),
            Identity::BusSend(i) => i.children_mut(),
            Identity::BusReceive(i) => i.children_mut(),
        }
    }

    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        match self {
            Identity::Polynomial(i) => i.children(),
            Identity::Connect(i) => i.children(),
            Identity::BusSend(i) => i.children(),
            Identity::BusReceive(i) => i.children(),
        }
    }
}

impl<T> Identity<T> {
    pub fn contains_next_ref(&self) -> bool {
        // TODO: This does not check the definitions of intermediate polynomials!
        self.children().any(|e| e.contains_next_ref())
    }

    pub fn id(&self) -> u64 {
        match self {
            Identity::Polynomial(i) => i.id,
            Identity::Connect(i) => i.id,
            Identity::BusSend(i) => i.identity_id,
            Identity::BusReceive(i) => i.identity_id,
        }
    }
}

/// Converts a list of [powdr_ast::analyzed::Identity] into a list of [Identity].
/// Polynomial and connect identities remain unchanged, phantom bus interactions
/// are converted to either a bus send or bus receive, and permutations and lookups
/// are converted to a pair of bus send and bus receive.
/// Because this function allocates new identities, we receive a reference to [Analyzed],
/// so we can be sure we operate on all identities.
pub fn convert_identities<T: FieldElement>(analyzed: &Analyzed<T>) -> Vec<Identity<T>> {
    let mut id_counter = id_counter(&analyzed.identities);

    let identities = analyzed
        .identities
        .iter()
        .flat_map(|identity| convert_identity(&mut id_counter, identity))
        .collect::<Vec<_>>();

    // We'd expect the interaction to uniquely identify a bus receive.
    let receive_bus_ids = identities
        .iter()
        .filter_map(|id| match id {
            Identity::BusReceive(r) => Some(r.bus_id),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        receive_bus_ids.iter().unique().count() == receive_bus_ids.len(),
        "Expected bus IDs of receives to be unique, but got: {receive_bus_ids:?}"
    );

    identities
}

fn id_counter<T: FieldElement>(identities: &[AnalyzedIdentity<T>]) -> RangeFrom<u64> {
    // We need to allocate new identity and bus IDs. Make sure it doesn't collide.
    let max_identity_id = identities.iter().map(|id| id.id()).max().unwrap_or(0);
    let max_bus_id = identities
        .iter()
        .filter_map(|id| match id {
            AnalyzedIdentity::PhantomBusInteraction(bus_interaction) => {
                match bus_interaction.payload.0[0] {
                    AlgebraicExpression::Number(id) => Some(id),
                    _ => None,
                }
            }
            _ => None,
        })
        .max()
        .unwrap_or(T::zero())
        .to_degree();
    (max(max_identity_id, max_bus_id) + 1)..
}

/// Like [convert_identities], but only converts a single identity.
/// The caller is responsible for providing an ID counter that does not
/// collide with IDs from existing identities.
fn convert_identity<T: FieldElement>(
    id_counter: &mut RangeFrom<u64>,
    identity: &AnalyzedIdentity<T>,
) -> Vec<Identity<T>> {
    match identity {
        AnalyzedIdentity::Polynomial(identity) => {
            vec![Identity::Polynomial(identity.clone())]
        }
        AnalyzedIdentity::Connect(identity) => {
            vec![Identity::Connect(identity.clone())]
        }
        AnalyzedIdentity::PhantomBusInteraction(bus_interaction) => {
            vec![convert_phantom_bus_interaction(bus_interaction)]
        }
        // Permutations have a RHS multiplicity that is equal to the RHS latch.
        AnalyzedIdentity::Permutation(PermutationIdentity {
            id, left, right, ..
        })
        | AnalyzedIdentity::PhantomPermutation(PhantomPermutationIdentity {
            id,
            left,
            right,
            ..
        }) => bus_interaction_pair(*id, id_counter, left, right, Some(right.selector.clone())),
        // Native lookups do not have a multiplicity.
        AnalyzedIdentity::Lookup(LookupIdentity {
            id, left, right, ..
        }) => bus_interaction_pair(*id, id_counter, left, right, None),
        AnalyzedIdentity::PhantomLookup(PhantomLookupIdentity {
            id,
            left,
            right,
            multiplicity,
            ..
        }) => bus_interaction_pair(*id, id_counter, left, right, Some(multiplicity.clone())),
    }
}

fn convert_phantom_bus_interaction<T: FieldElement>(
    bus_interaction: &PhantomBusInteractionIdentity<T>,
) -> Identity<T> {
    // Detect receives by having a unary minus in the multiplicity
    // TODO: We should instead analyze the range constraints of the
    // multiplicity expression.
    let (is_receive, multiplicity) = match &bus_interaction.multiplicity {
        AlgebraicExpression::UnaryOperation(op) => match op.op {
            AlgebraicUnaryOperator::Minus => (true, (*op.expr).clone()),
        },
        _ => (false, bus_interaction.multiplicity.clone()),
    };
    // By convention, we assume that the first payload entry is the bus ID.
    // TODO: Instead, we should have a separate field in the phantom bus interaction type.
    let bus_id = match bus_interaction.payload.0[0] {
        AlgebraicExpression::Number(id) => id,
        // TODO: Relax this for sends when implementing dynamic sends
        _ => panic!("Expected first payload entry to be a static ID"),
    };
    // Remove the bus ID from the list of expressions.
    let expressions = bus_interaction.payload.0.iter().skip(1).cloned().collect();
    let selected_payload = SelectedExpressions {
        selector: bus_interaction.latch.clone(),
        expressions,
    };
    if is_receive {
        Identity::BusReceive(BusReceive {
            identity_id: bus_interaction.id,
            bus_id,
            multiplicity: Some(multiplicity),
            selected_payload,
        })
    } else {
        assert_eq!(multiplicity, bus_interaction.latch);
        Identity::BusSend(BusSend {
            identity_id: bus_interaction.id,
            bus_id: AlgebraicExpression::Number(bus_id),
            selected_payload,
        })
    }
}

fn bus_interaction_pair<T: FieldElement>(
    id: u64,
    id_counter: &mut RangeFrom<u64>,
    left: &SelectedExpressions<T>,
    right: &SelectedExpressions<T>,
    rhs_multiplicity: Option<AlgebraicExpression<T>>,
) -> Vec<Identity<T>> {
    let bus_id: T = id_counter.next().unwrap().into();
    vec![
        Identity::BusSend(BusSend {
            identity_id: id,
            bus_id: AlgebraicExpression::Number(bus_id),
            selected_payload: left.clone(),
        }),
        Identity::BusReceive(BusReceive {
            identity_id: id_counter.next().unwrap(),
            multiplicity: rhs_multiplicity,
            bus_id,
            selected_payload: right.clone(),
        }),
    ]
}

#[cfg(test)]
mod test {
    use std::collections::VecDeque;

    use powdr_number::GoldilocksField;

    use crate::witgen::data_structures::identity::Identity;

    use super::{convert_identities, BusReceive, BusSend};

    fn get_generated_bus_interaction_pair(
        constraint: &str,
    ) -> (BusSend<GoldilocksField>, BusReceive<GoldilocksField>) {
        let pil_source = format!(
            r"
namespace main(4);
    col fixed right_latch = [0, 1]*;
    col witness right_selector, left_latch, a, b, multiplicities;
    {constraint}
    
    // Selectors should be binary
    (left_latch - 1) * left_latch = 0;
    (right_selector - 1) * right_selector = 0;

    // Some other bus interactions to potentially confuse the matching
    right_latch $ [a] in right_latch $ [a];
    left_latch $ [b] in left_latch $ [b];
"
        );
        let analyzed = powdr_pil_analyzer::analyze_string::<GoldilocksField>(&pil_source).unwrap();
        let mut identities = convert_identities(&analyzed)
            .into_iter()
            .collect::<VecDeque<_>>();
        let receives = identities
            .iter()
            .filter_map(|id| match id {
                Identity::BusReceive(r) => Some((r.bus_id, r.clone())),
                _ => None,
            })
            .collect();

        match (
            identities.pop_front().unwrap(),
            identities.pop_front().unwrap(),
        ) {
            (Identity::BusSend(send), Identity::BusReceive(receive)) => {
                assert_eq!(send.try_match_static(&receives).unwrap(), &receive);
                (send, receive)
            }
            _ => panic!(
                "Expected one receive and one send, but got:\n{}\n{}",
                identities[0], identities[1]
            ),
        }
    }

    #[test]
    fn native_lookup() {
        let (send, receive) =
            get_generated_bus_interaction_pair("left_latch $ [a] in right_latch $ [b];");
        assert_eq!(
            send.selected_payload.to_string(),
            "main::left_latch $ [main::a]"
        );
        assert_eq!(
            receive.selected_payload.to_string(),
            "main::right_latch $ [main::b]"
        );
        assert!(receive.has_arbitrary_multiplicity());
    }

    #[test]
    fn phantom_lookup() {
        let (send, receive) = get_generated_bus_interaction_pair(
            "Constr::PhantomLookup((Option::Some(left_latch), Option::Some(right_latch)), [(a, b)], multiplicities);",
        );
        assert_eq!(
            send.selected_payload.to_string(),
            "main::left_latch $ [main::a]"
        );
        assert_eq!(
            receive.selected_payload.to_string(),
            "main::right_latch $ [main::b]"
        );
        assert_eq!(
            receive.multiplicity.as_ref().unwrap().to_string(),
            "main::multiplicities"
        );
        assert!(receive.has_arbitrary_multiplicity());
    }

    #[test]
    fn lookup_bus_interactions() {
        // Phantom bus interactions, as generated by
        // std::protocols::lookup_via_bus::lookup_send and
        // std::protocols::lookup_via_bus::lookup_receive.
        let (send, receive) = get_generated_bus_interaction_pair(
            r"Constr::PhantomBusInteraction(main::left_latch, [42, main::a], main::left_latch);
              Constr::PhantomBusInteraction(-main::multiplicities, [42, main::b], main::right_latch);",
        );
        assert_eq!(
            send.selected_payload.to_string(),
            "main::left_latch $ [main::a]"
        );
        assert_eq!(
            receive.selected_payload.to_string(),
            "main::right_latch $ [main::b]"
        );
        assert_eq!(send.bus_id.to_string(), "42");
        assert_eq!(receive.bus_id, 42.into());
        assert_eq!(
            receive.multiplicity.as_ref().unwrap().to_string(),
            "main::multiplicities"
        );
        assert!(receive.has_arbitrary_multiplicity());
    }

    #[test]
    fn native_permutation() {
        let (send, receive) = get_generated_bus_interaction_pair(
            "left_latch $ [a] is (right_latch * right_selector) $ [b];",
        );
        assert_eq!(
            send.selected_payload.to_string(),
            "main::left_latch $ [main::a]"
        );
        assert_eq!(
            receive.selected_payload.to_string(),
            "main::right_latch * main::right_selector $ [main::b]"
        );
        assert!(!receive.has_arbitrary_multiplicity());
    }

    #[test]
    fn phantom_permutation() {
        let (send, receive) = get_generated_bus_interaction_pair(
            "Constr::PhantomPermutation((Option::Some(left_latch), Option::Some(right_latch * right_selector)), [(a, b)]);");
        assert_eq!(
            send.selected_payload.to_string(),
            "main::left_latch $ [main::a]"
        );
        assert_eq!(
            receive.selected_payload.to_string(),
            "main::right_latch * main::right_selector $ [main::b]"
        );
        assert!(!receive.has_arbitrary_multiplicity());
    }

    #[test]
    fn permutation_bus_interactions() {
        // Phantom bus interactions, as generated by
        // std::protocols::permutation_via_bus::permutation_send and
        // std::protocols::permutation_via_bus::permutation_receive.
        let (send, receive) = get_generated_bus_interaction_pair(
            r"Constr::PhantomBusInteraction(main::left_latch, [42, main::a], main::left_latch);
              Constr::PhantomBusInteraction(-(main::right_latch * main::right_selector), [42, main::b], main::right_latch * main::right_selector);",
        );
        assert_eq!(
            send.selected_payload.to_string(),
            "main::left_latch $ [main::a]"
        );
        assert_eq!(
            receive.selected_payload.to_string(),
            "main::right_latch * main::right_selector $ [main::b]"
        );
        assert_eq!(send.bus_id.to_string(), "42");
        assert_eq!(receive.bus_id, 42.into());
        assert_eq!(
            receive.multiplicity.as_ref().unwrap().to_string(),
            "main::right_latch * main::right_selector"
        );
        assert!(!receive.has_arbitrary_multiplicity());
    }
}

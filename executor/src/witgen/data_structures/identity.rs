use core::fmt;
use std::{collections::BTreeMap, ops::RangeFrom};

use itertools::{Either, Itertools};
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
    /// This value is used to match sends and receives.
    pub bus_id: AlgebraicExpression<T>,
    /// The payload sent to the bus, with a selector.
    pub selected_payload: SelectedExpressions<T>,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct BusReceive<T> {
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
            "Receive(payload={}, multiplicity={}, bus_id={})",
            self.selected_payload, multiplicity, self.bus_id
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
}

impl<T> Children<AlgebraicExpression<T>> for Identity<T> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        match self {
            Identity::Polynomial(i) => i.children_mut(),
            Identity::Connect(i) => i.children_mut(),
            Identity::BusSend(i) => i.children_mut(),
        }
    }

    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        match self {
            Identity::Polynomial(i) => i.children(),
            Identity::Connect(i) => i.children(),
            Identity::BusSend(i) => i.children(),
        }
    }
}

impl<T> Identity<T> {
    pub fn id(&self) -> u64 {
        match self {
            Identity::Polynomial(i) => i.id,
            Identity::Connect(i) => i.id,
            Identity::BusSend(i) => i.identity_id,
        }
    }
}

enum IdentityOrReceive<T> {
    Identity(Identity<T>),
    Receive(BusReceive<T>),
}

/// Converts a list of [powdr_ast::analyzed::Identity] into a list of [Identity]
/// and a map of [BusReceive]s (bus ID -> BusReceive).
/// Polynomial and connect identities remain unchanged, phantom bus interactions
/// are converted to either a bus send or bus receive, and permutations and lookups
/// are converted to a pair of bus send and bus receive.
/// Because this function allocates new bus IDs, we receive a reference to [Analyzed],
/// so we can be sure we operate on all identities.
pub fn convert_identities<T: FieldElement>(
    analyzed: &Analyzed<T>,
) -> (Vec<Identity<T>>, BTreeMap<T, BusReceive<T>>) {
    let mut bus_id_counter = bus_id_counter(&analyzed.identities);

    let (identities, receives): (Vec<_>, Vec<_>) = analyzed
        .identities
        .iter()
        .flat_map(|identity| convert_identity(&mut bus_id_counter, identity))
        .partition_map(|id| match id {
            IdentityOrReceive::Identity(identity) => Either::Left(identity),
            IdentityOrReceive::Receive(bus_receive) => Either::Right(bus_receive),
        });

    // We'd expect the interaction to uniquely identify a bus receive.
    let receive_bus_ids = receives.iter().map(|id| id.bus_id).collect::<Vec<_>>();
    assert!(
        receive_bus_ids.iter().unique().count() == receive_bus_ids.len(),
        "Expected bus IDs of receives to be unique, but got: {receive_bus_ids:?}"
    );

    let receives = receives.into_iter().map(|r| (r.bus_id, r)).collect();
    (identities, receives)
}

fn bus_id_counter<T: FieldElement>(identities: &[AnalyzedIdentity<T>]) -> RangeFrom<u64> {
    // We need to allocate bus IDs. Make sure it doesn't collide.
    let max_bus_id = identities
        .iter()
        .filter_map(|id| match id {
            AnalyzedIdentity::PhantomBusInteraction(bus_interaction) => {
                match bus_interaction.bus_id {
                    AlgebraicExpression::Number(id) => Some(id),
                    _ => None,
                }
            }
            _ => None,
        })
        .max()
        .unwrap_or(T::zero())
        .to_degree();
    (max_bus_id + 1)..
}

/// Like [convert_identities], but only converts a single identity.
/// The caller is responsible for providing an ID counter that does not
/// collide with IDs from existing identities.
fn convert_identity<T: FieldElement>(
    bus_id_counter: &mut RangeFrom<u64>,
    identity: &AnalyzedIdentity<T>,
) -> Vec<IdentityOrReceive<T>> {
    match identity {
        AnalyzedIdentity::Polynomial(identity) => {
            vec![IdentityOrReceive::Identity(Identity::Polynomial(
                identity.clone(),
            ))]
        }
        AnalyzedIdentity::Connect(identity) => {
            vec![IdentityOrReceive::Identity(Identity::Connect(
                identity.clone(),
            ))]
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
        }) => bus_interaction_pair(
            *id,
            bus_id_counter,
            left,
            right,
            Some(right.selector.clone()),
        ),
        // Native lookups do not have a multiplicity.
        AnalyzedIdentity::Lookup(LookupIdentity {
            id, left, right, ..
        }) => bus_interaction_pair(*id, bus_id_counter, left, right, None),
        AnalyzedIdentity::PhantomLookup(PhantomLookupIdentity {
            id,
            left,
            right,
            multiplicity,
            ..
        }) => bus_interaction_pair(*id, bus_id_counter, left, right, Some(multiplicity.clone())),
    }
}

fn convert_phantom_bus_interaction<T: FieldElement>(
    bus_interaction: &PhantomBusInteractionIdentity<T>,
) -> IdentityOrReceive<T> {
    // Detect receives by having a unary minus in the multiplicity
    // TODO: We should instead analyze the range constraints of the
    // multiplicity expression.
    let (is_receive, multiplicity) = match &bus_interaction.multiplicity {
        AlgebraicExpression::UnaryOperation(op) => match op.op {
            AlgebraicUnaryOperator::Minus => (true, (*op.expr).clone()),
        },
        _ => (false, bus_interaction.multiplicity.clone()),
    };
    let bus_id = match bus_interaction.bus_id {
        AlgebraicExpression::Number(id) => id,
        // TODO: Relax this for sends when implementing dynamic sends
        _ => panic!("Expected first payload entry to be a static ID"),
    };
    let selected_payload = SelectedExpressions {
        selector: bus_interaction.latch.clone(),
        expressions: bus_interaction.payload.0.clone(),
    };
    if is_receive {
        IdentityOrReceive::Receive(BusReceive {
            bus_id,
            multiplicity: Some(multiplicity),
            selected_payload,
        })
    } else {
        assert_eq!(multiplicity, bus_interaction.latch);
        IdentityOrReceive::Identity(Identity::BusSend(BusSend {
            identity_id: bus_interaction.id,
            bus_id: AlgebraicExpression::Number(bus_id),
            selected_payload,
        }))
    }
}

fn bus_interaction_pair<T: FieldElement>(
    id: u64,
    bus_id_counter: &mut RangeFrom<u64>,
    left: &SelectedExpressions<T>,
    right: &SelectedExpressions<T>,
    rhs_multiplicity: Option<AlgebraicExpression<T>>,
) -> Vec<IdentityOrReceive<T>> {
    let bus_id: T = bus_id_counter.next().unwrap().into();
    vec![
        IdentityOrReceive::Identity(Identity::BusSend(BusSend {
            identity_id: id,
            bus_id: AlgebraicExpression::Number(bus_id),
            selected_payload: left.clone(),
        })),
        IdentityOrReceive::Receive(BusReceive {
            multiplicity: rhs_multiplicity,
            bus_id,
            selected_payload: right.clone(),
        }),
    ]
}

#[cfg(test)]
mod test {
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
    col witness right_selector, left_latch, a, b, multiplicities, folded, acc;
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
        let (identities, receives) = convert_identities(&analyzed);

        let send = match &identities[0] {
            Identity::BusSend(send) => send,
            _ => panic!("Expected a send, but got:\n{}", identities[0]),
        };
        let receive = send.try_match_static(&receives).unwrap();
        (send.clone(), receive.clone())
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
            // The folded expressions and accumulator is ignored in both the bus send and receive, so we just use the same.
            r"Constr::PhantomBusInteraction(main::left_latch, 42, [main::a], main::left_latch, [main::folded], [main::acc]);
              Constr::PhantomBusInteraction(-main::multiplicities, 42, [main::b], main::right_latch, [main::folded], [main::acc]);",
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
            // The folded expressions and accumulator is ignored in both the bus send and receive, so we just use the same.
            r"Constr::PhantomBusInteraction(main::left_latch, 42, [main::a], main::left_latch, [main::folded], [main::acc]);
              Constr::PhantomBusInteraction(-(main::right_latch * main::right_selector), 42, [main::b], main::right_latch * main::right_selector, [main::folded], [main::acc]);",
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

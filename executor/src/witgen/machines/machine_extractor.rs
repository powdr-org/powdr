use std::collections::{BTreeMap, BTreeSet, HashSet};

use itertools::Itertools;
use powdr_ast::analyzed::LookupIdentity;
use powdr_ast::analyzed::PermutationIdentity;
use powdr_ast::analyzed::PhantomLookupIdentity;
use powdr_ast::analyzed::PhantomPermutationIdentity;

use super::block_machine::BlockMachine;
use super::double_sorted_witness_machine_16::DoubleSortedWitnesses16;
use super::double_sorted_witness_machine_32::DoubleSortedWitnesses32;
use super::fixed_lookup_machine::FixedLookup;
use super::sorted_witness_machine::SortedWitnesses;
use super::FixedData;
use super::KnownMachine;
use super::Machine;
use crate::witgen::machines::dynamic_machine::DynamicMachine;
use crate::witgen::machines::second_stage_machine::SecondStageMachine;
use crate::witgen::machines::Connection;
use crate::witgen::machines::{write_once_memory::WriteOnceMemory, MachineParts};
use crate::Identity;

use powdr_ast::analyzed::{
    self, AlgebraicExpression as Expression, PolyID, PolynomialReference, Reference,
};
use powdr_ast::parsed::{self, visitor::AllChildren};
use powdr_number::FieldElement;

pub struct MachineExtractor<'a, T: FieldElement> {
    fixed: &'a FixedData<'a, T>,
}

impl<'a, T: FieldElement> MachineExtractor<'a, T> {
    pub fn new(fixed: &'a FixedData<'a, T>) -> Self {
        Self { fixed }
    }

    /// Finds machines in the witness columns and identities and returns a list of machines and the identities
    /// that are not "internal" to the machines.
    /// The first returned machine is the "main machine", i.e. a machine that has no incoming connections.
    pub fn split_out_machines(&self, identities: Vec<&'a Identity<T>>) -> Vec<KnownMachine<'a, T>> {
        // Ignore prover functions that reference columns of later stages.
        let all_witnesses = self.fixed.witness_cols.keys().collect::<HashSet<_>>();
        let current_stage_witnesses = self
            .fixed
            .witnesses_until_current_stage()
            .collect::<HashSet<_>>();
        let later_stage_witness_names = all_witnesses
            .difference(&current_stage_witnesses)
            .map(|w| self.fixed.column_name(w))
            .collect::<HashSet<_>>();
        let prover_functions = self
            .fixed
            .analyzed
            .prover_functions
            .iter()
            .filter(|pf| {
                !refs_in_parsed_expression(pf)
                    .unique()
                    .any(|n| later_stage_witness_names.contains(n.as_str()))
            })
            .collect::<Vec<&analyzed::Expression>>();

        if self.fixed.stage() > 0 {
            let machine_parts = MachineParts::new(
                self.fixed,
                Default::default(),
                identities,
                self.fixed.witness_cols.keys().collect::<HashSet<_>>(),
                prover_functions,
            );

            return vec![KnownMachine::SecondStageMachine(SecondStageMachine::new(
                "Bus Machine".to_string(),
                self.fixed,
                machine_parts,
            ))];
        }
        let mut machines: Vec<KnownMachine<T>> = vec![];

        let mut publics = PublicsTracker::default();
        let mut remaining_witnesses = current_stage_witnesses.clone();
        let mut base_identities = identities.clone();
        let mut extracted_prover_functions = HashSet::new();
        let mut id_counter = 0;

        let all_connections = identities
            .iter()
            .filter_map(|i| Connection::try_from(*i).ok())
            .collect::<Vec<_>>();

        let mut fixed_lookup_connections = BTreeMap::new();

        for connection in &all_connections {
            // If the RHS only consists of fixed columns, record the connection and continue.
            if FixedLookup::is_responsible(connection) {
                assert!(fixed_lookup_connections
                    .insert(connection.id, *connection)
                    .is_none());
                if let Some(multiplicity) = connection.multiplicity_column {
                    remaining_witnesses.remove(&multiplicity);
                }
                continue;
            }

            // Extract all witness columns in the RHS of the lookup.
            let lookup_witnesses =
                &self.refs_in_connection_rhs(connection) & (&remaining_witnesses);
            if lookup_witnesses.is_empty() {
                // Skip connections to machines that were already created or point to FixedLookup.
                continue;
            }

            // Recursively extend the set to all witnesses connected through identities that preserve
            // a fixed row relation.
            let machine_witnesses = self.all_row_connected_witnesses(
                lookup_witnesses,
                &remaining_witnesses,
                &identities,
            );

            // Split identities into those that only concern the machine
            // witnesses and those that concern any other witness.
            let (machine_identities, remaining_identities): (Vec<_>, _) =
                base_identities.iter().cloned().partition(|i| {
                    // The identity's left side has at least one machine witness, but
                    // all referenced witnesses are machine witnesses.
                    // For lookups, any lookup calling from the current machine belongs
                    // to the machine; lookups to the machine do not.
                    let all_refs = &self.refs_in_identity_left(i) & (&current_stage_witnesses);
                    !all_refs.is_empty() && all_refs.is_subset(&machine_witnesses)
                });
            base_identities = remaining_identities;
            remaining_witnesses = &remaining_witnesses - &machine_witnesses;

            publics.add_all(machine_identities.as_slice()).unwrap();

            // Connections that call into the current machine
            let machine_connections = all_connections
                .iter()
                .filter_map(|connection| {
                    // check if the identity connects to the current machine
                    self.refs_in_connection_rhs(connection)
                        .intersection(&machine_witnesses)
                        .next()
                        .is_some()
                        .then_some((connection.id, *connection))
                })
                .collect::<BTreeMap<_, _>>();
            assert!(machine_connections.contains_key(&connection.id));

            let prover_functions = prover_functions
                .iter()
                .copied()
                .enumerate()
                .filter(|(_, pf)| {
                    let refs = refs_in_parsed_expression(pf)
                        .unique()
                        .flat_map(|n| {
                            self.fixed.try_column_by_name(n).into_iter().chain(
                                // The reference might be an array, in which case it wouldn't
                                // be in the list of columns. So we try the first element as well.
                                self.fixed
                                    .try_column_by_name(&format!("{n}[0]"))
                                    .into_iter(),
                            )
                        })
                        .collect::<HashSet<_>>();
                    refs.intersection(&machine_witnesses).next().is_some()
                })
                .collect::<Vec<(_, &analyzed::Expression)>>();

            let machine_parts = MachineParts::new(
                self.fixed,
                machine_connections,
                machine_identities,
                machine_witnesses,
                prover_functions.iter().map(|&(_, pf)| pf).collect(),
            );

            for (i, pf) in &prover_functions {
                if !extracted_prover_functions.insert(*i) {
                    log::warn!("Prover function was assigned to multiple machines:\n{pf}");
                }
            }

            let name = suggest_machine_name(&machine_parts);
            let id = id_counter;
            id_counter += 1;
            let name_with_type = |t: &str| format!("Secondary machine {id}: {name} ({t})");

            machines.push(build_machine(self.fixed, machine_parts, name_with_type));
        }
        publics.add_all(base_identities.as_slice()).unwrap();

        // Always add a fixed lookup machine.
        // Note that this machine comes last, because some machines do a fixed lookup
        // in their take_witness_col_values() implementation.
        // TODO: We should also split this up and have several instances instead.
        let fixed_lookup = FixedLookup::new(
            self.fixed.global_range_constraints().clone(),
            self.fixed,
            fixed_lookup_connections,
        );

        machines.push(KnownMachine::FixedLookup(fixed_lookup));

        // Use the remaining prover functions as base prover functions.
        let base_prover_functions = prover_functions
            .iter()
            .enumerate()
            .filter_map(|(i, &pf)| (!extracted_prover_functions.contains(&i)).then_some(pf))
            .collect::<Vec<_>>();

        // In the remaining witness, we might still have some multiplicity columns
        // of fixed lookups, because they are not referenced by any "normal"
        // first-stage identities. As the main machine should not be on the
        // receiving end of a lookup, we remove any multiplicity columns here.
        // Note that we don't use the passed identities, because we want to
        // include removed range constraints.
        let multiplicity_columns = self
            .fixed
            .analyzed
            .identities
            .iter()
            .filter_map(|identity| Connection::try_from(identity).ok()?.multiplicity_column)
            .collect::<HashSet<_>>();
        let main_witnesses = remaining_witnesses
            .difference(&multiplicity_columns)
            .cloned()
            .collect::<HashSet<_>>();

        log::trace!(
            "\nThe base machine contains the following witnesses:\n{}\n identities:\n{}\n and prover functions:\n{}",
            main_witnesses
                .iter()
                .map(|s| self.fixed.column_name(s))
                .sorted()
                .format(", "),
            base_identities.iter().format("\n"),
            base_prover_functions.iter().format("\n")
        );

        let base_parts = MachineParts::new(
            self.fixed,
            Default::default(),
            base_identities,
            main_witnesses,
            base_prover_functions,
        );

        if let Some(main_machine) = build_main_machine(self.fixed, base_parts) {
            std::iter::once(main_machine).chain(machines).collect()
        } else {
            if !machines.is_empty() {
                log::error!("No main machine was extracted, but secondary machines were. Does the system have a cycle?");
            }
            vec![]
        }
    }

    /// Extends a set of witnesses to the full set of row-connected witnesses.
    /// Two witnesses are row-connected if they are part of a polynomial identity
    /// or part of the same side of a lookup.
    fn all_row_connected_witnesses(
        &self,
        mut witnesses: HashSet<PolyID>,
        all_witnesses: &HashSet<PolyID>,
        identities: &[&Identity<T>],
    ) -> HashSet<PolyID> {
        loop {
            let count = witnesses.len();
            for i in identities {
                match i {
                    Identity::Polynomial(i) => {
                        // Any current witness in the identity adds all other witnesses.
                        let in_identity = &self.fixed.polynomial_references(i) & all_witnesses;
                        if in_identity.intersection(&witnesses).next().is_some() {
                            witnesses.extend(in_identity);
                        }
                    }
                    Identity::Lookup(LookupIdentity { left, .. })
                    | Identity::Permutation(PermutationIdentity { left, .. })
                    | Identity::PhantomLookup(PhantomLookupIdentity { left, .. })
                    | Identity::PhantomPermutation(PhantomPermutationIdentity { left, .. }) => {
                        // If we already have witnesses on the LHS, include the LHS,
                        // and vice-versa, but not across the "sides".
                        let in_lhs = &self.fixed.polynomial_references(left) & all_witnesses;
                        let in_rhs = &self
                            .refs_in_connection_rhs(&Connection::try_from(*i).unwrap())
                            & all_witnesses;
                        if in_lhs.intersection(&witnesses).next().is_some() {
                            witnesses.extend(in_lhs);
                        } else if in_rhs.intersection(&witnesses).next().is_some() {
                            witnesses.extend(in_rhs);
                        }
                    }
                    Identity::Connect(..) => {
                        unimplemented!()
                    }
                    // TODO(bus_interaction)
                    Identity::PhantomBusInteraction(..) => {}
                };
            }
            if witnesses.len() == count {
                return witnesses;
            }
        }
    }

    /// Like refs_in_selected_expressions(connection.right), but also includes the multiplicity column.
    fn refs_in_connection_rhs(&self, connection: &Connection<T>) -> HashSet<PolyID> {
        self.fixed
            .polynomial_references(connection.right)
            .into_iter()
            .chain(connection.multiplicity_column)
            .collect()
    }

    /// Extracts all references to names from the "left" side of an identity. This is the left selected expressions for connecting identities, and everything for other identities.
    fn refs_in_identity_left(&self, identity: &Identity<T>) -> HashSet<PolyID> {
        match identity {
            Identity::Lookup(LookupIdentity { left, .. })
            | Identity::PhantomLookup(PhantomLookupIdentity { left, .. })
            | Identity::Permutation(PermutationIdentity { left, .. })
            | Identity::PhantomPermutation(PhantomPermutationIdentity { left, .. }) => {
                self.fixed.polynomial_references(left)
            }
            Identity::Polynomial(i) => self.fixed.polynomial_references(i),
            Identity::Connect(i) => self.fixed.polynomial_references(i),
            Identity::PhantomBusInteraction(i) => self
                .fixed
                .polynomial_references(&i.tuple)
                .into_iter()
                .chain(self.fixed.polynomial_references(&i.multiplicity))
                .collect(),
        }
    }
}

fn extract_namespace(name: &str) -> &str {
    name.split("::").next().unwrap()
}

fn log_extracted_machine<T: FieldElement>(name: &str, parts: &MachineParts<'_, T>) {
    let namespaces = parts
        .witnesses
        .iter()
        .map(|s| extract_namespace(parts.column_name(s)))
        .collect::<BTreeSet<_>>();
    let exactly_one_namespace = namespaces.len() == 1;
    let log_level = if exactly_one_namespace {
        log::Level::Trace
    } else {
        log::Level::Warn
    };
    log::log!(
        log_level,
        "\nExtracted a machine {name} with the following witnesses:\n{}\n identities:\n{}\n connecting identities:\n{}\n and prover functions:\n{}",
        parts.witnesses
            .iter()
            .map(|s|parts.column_name(s))
            .sorted()
            .format(", "),
        parts.identities
            .iter()
            .format("\n"),
        parts.connections
            .values()
            .format("\n"),
        parts.prover_functions
            .iter()
            .format("\n")
    );
    if !exactly_one_namespace {
        log::warn!("The witnesses of the machine are in different namespaces: {namespaces:?}");
        log::warn!("In theory, witgen ignores namespaces, but in practice, this often means that something has gone wrong with the machine extraction.");
    }
}

fn suggest_machine_name<T: FieldElement>(parts: &MachineParts<'_, T>) -> String {
    let first_witness = parts.witnesses.iter().next().unwrap();
    let first_witness_name = parts.column_name(first_witness);
    let namespace = first_witness_name
        .rfind("::")
        .map(|idx| &first_witness_name[..idx]);

    // For machines compiled using Powdr ASM we'll always have a namespace, but as a last
    // resort we'll use the first witness name.
    namespace.unwrap_or(first_witness_name).to_string()
}

#[derive(Default)]
/// Keeps track of the global set of publics that are referenced by the machine's identities.
struct PublicsTracker<'a>(BTreeSet<&'a String>);

impl<'a> PublicsTracker<'a> {
    /// Given a machine's identities, add all publics that are referenced by them.
    /// Panics if a public is referenced by more than one machine.
    fn add_all<T>(
        &mut self,
        identities: &[&'a powdr_ast::analyzed::Identity<T>],
    ) -> Result<(), String> {
        let referenced_publics = identities
            .iter()
            .flat_map(|id| id.all_children())
            .filter_map(|expr| match expr {
                Expression::PublicReference(public_name) => Some(public_name),
                _ => None,
            })
            .collect();
        let intersection = self
            .0
            .intersection(&referenced_publics)
            .collect::<BTreeSet<_>>();
        if !intersection.is_empty() {
            let intersection_list = intersection.iter().format(", ");
            return Err(format!(
                "Publics are referenced by more than one machine: {intersection_list}",
            ));
        }
        self.0.extend(referenced_publics);
        Ok(())
    }
}

fn build_main_machine<'a, T: FieldElement>(
    fixed_data: &'a FixedData<'a, T>,
    machine_parts: MachineParts<'a, T>,
) -> Option<KnownMachine<'a, T>> {
    (!machine_parts.witnesses.is_empty())
        .then(|| build_machine(fixed_data, machine_parts, |t| format!("Main machine ({t})")))
}

fn build_machine<'a, T: FieldElement>(
    fixed_data: &'a FixedData<'a, T>,
    machine_parts: MachineParts<'a, T>,
    name_with_type: impl Fn(&str) -> String,
) -> KnownMachine<'a, T> {
    let machine = if let Some(machine) =
        SortedWitnesses::try_new(name_with_type("SortedWitness"), fixed_data, &machine_parts)
    {
        log::debug!("Detected machine: sorted witnesses / write-once memory");
        KnownMachine::SortedWitnesses(machine)
    } else if let Some(machine) = DoubleSortedWitnesses16::try_new(
        name_with_type("DoubleSortedWitnesses16"),
        fixed_data,
        &machine_parts,
    ) {
        log::debug!("Detected machine: memory16");
        KnownMachine::DoubleSortedWitnesses16(machine)
    } else if let Some(machine) = DoubleSortedWitnesses32::try_new(
        name_with_type("DoubleSortedWitnesses32"),
        fixed_data,
        &machine_parts,
    ) {
        log::debug!("Detected machine: memory32");
        KnownMachine::DoubleSortedWitnesses32(machine)
    } else if let Some(machine) = WriteOnceMemory::try_new(
        name_with_type("WriteOnceMemory"),
        fixed_data,
        &machine_parts,
    ) {
        log::debug!("Detected machine: write-once memory");
        KnownMachine::WriteOnceMemory(machine)
    } else if let Some(machine) =
        BlockMachine::try_new(name_with_type("BlockMachine"), fixed_data, &machine_parts)
    {
        log::debug!("Detected machine: {machine}");
        log_extracted_machine(machine.name(), &machine_parts);
        KnownMachine::BlockMachine(machine)
    } else {
        log::debug!("Detected machine: Dynamic machine.");
        // If there is a connection to this machine, all connections must have the same latch.
        // If there is no connection to this machine, it is the main machine and there is no latch.
        let latch = machine_parts.connections
            .values()
            .fold(None, |existing_latch, identity| {
                let current_latch = &identity
                    .right
                    .selector;
                if let Some(existing_latch) = existing_latch {
                    assert_eq!(
                        &existing_latch, current_latch,
                        "All connecting identities must have the same selector expression on the right hand side"
                    );
                    Some(existing_latch)
                } else {
                    Some(current_latch.clone())
                }
            });
        KnownMachine::DynamicMachine(DynamicMachine::new(
            name_with_type("Dynamic"),
            fixed_data,
            machine_parts.clone(),
            latch,
        ))
    };

    log_extracted_machine(machine.name(), &machine_parts);
    machine
}

// This only discovers direct references in the expression
// and ignores e.g. called functions, but it will work for now.
fn refs_in_parsed_expression(expr: &analyzed::Expression) -> impl Iterator<Item = &String> + '_ {
    expr.all_children().filter_map(|e| match e {
        parsed::Expression::Reference(_, Reference::Poly(PolynomialReference { name, .. })) => {
            Some(name)
        }
        _ => None,
    })
}

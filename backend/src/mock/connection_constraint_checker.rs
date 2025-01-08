use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt;
use std::ops::ControlFlow;

use itertools::Itertools;
use powdr_ast::analyzed::{
    expression_evaluator::{ExpressionEvaluator, TerminalAccess},
    AlgebraicExpression, Analyzed, Identity, LookupIdentity, PermutationIdentity,
    PhantomLookupIdentity, PhantomPermutationIdentity, SelectedExpressions,
};
use powdr_ast::parsed::visitor::ExpressionVisitable;
use powdr_ast::parsed::visitor::VisitOrder;
use powdr_backend_utils::referenced_namespaces_algebraic_expression;
use powdr_number::FieldElement;
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;

use super::machine::Machine;

#[derive(PartialEq, Eq, Debug)]
pub enum ConnectionKind {
    Lookup,
    Permutation,
}

/// A connection between two machines.
pub struct Connection<F> {
    identity: Identity<F>,
    pub left: SelectedExpressions<F>,
    pub right: SelectedExpressions<F>,
    /// For [ConnectionKind::Permutation], rows of `left` are a permutation of rows of `right`. For [ConnectionKind::Lookup], all rows in `left` are in `right`.
    pub kind: ConnectionKind,
}

impl<F: FieldElement> Connection<F> {
    /// Extracts all connections from the global PIL.
    pub fn get_all(
        global_pil: &Analyzed<F>,
        machine_to_pil: &BTreeMap<String, Analyzed<F>>,
    ) -> Vec<Self> {
        global_pil
            .identities
            .iter()
            .filter_map(|identity| Connection::try_new(identity, global_pil, machine_to_pil).ok())
            .collect()
    }

    fn try_new(
        identity: &Identity<F>,
        global_pil: &Analyzed<F>,
        machine_to_pil: &BTreeMap<String, Analyzed<F>>,
    ) -> Result<Self, ()> {
        let (left, right, kind) = match identity {
            Identity::Polynomial(_) => Err(()),
            Identity::Connect(_) => unimplemented!(),
            Identity::Lookup(LookupIdentity { left, right, .. })
            | Identity::PhantomLookup(PhantomLookupIdentity { left, right, .. }) => {
                Ok((left.clone(), right.clone(), ConnectionKind::Lookup))
            }
            Identity::Permutation(PermutationIdentity { left, right, .. })
            | Identity::PhantomPermutation(PhantomPermutationIdentity { left, right, .. }) => {
                Ok((left.clone(), right.clone(), ConnectionKind::Permutation))
            }
            // TODO(bus_interaction)
            Identity::PhantomBusInteraction(_) => Err(()),
        }?;

        // This connection is not localized yet: Its expression's PolyIDs point to the global PIL, not the local PIL.
        let mut connection = Self {
            identity: identity.clone(),
            left,
            right,
            kind,
        };
        if let Some(caller) = connection.caller() {
            connection.left =
                connection.localize(&connection.left, global_pil, &machine_to_pil[&caller]);
        }
        if let Some(callee) = connection.callee() {
            connection.right =
                connection.localize(&connection.right, global_pil, &machine_to_pil[&callee]);
        }

        Ok(connection)
    }

    /// Translates PolyIDs pointing to columns in the global PIL to PolyIDs pointing to columns in the local PIL.
    fn localize(
        &self,
        selected_expressions: &SelectedExpressions<F>,
        global_pil: &Analyzed<F>,
        local_pil: &Analyzed<F>,
    ) -> SelectedExpressions<F> {
        // Build a map (local ID) -> (global ID).
        let name_to_id_local = local_pil.name_to_poly_id();
        let id_map = global_pil
            .name_to_poly_id()
            .into_iter()
            .filter_map(|(name, source_id)| {
                name_to_id_local
                    .get(&name)
                    .map(|target_id| (source_id, *target_id))
            })
            .collect::<BTreeMap<_, _>>();

        // Translate all polynomial references.
        let mut localized = selected_expressions.clone();
        localized.visit_expressions_mut(
            &mut |expr| {
                if let AlgebraicExpression::Reference(reference) = expr {
                    reference.poly_id = id_map[&reference.poly_id];
                }
                ControlFlow::Continue::<()>(())
            },
            VisitOrder::Pre,
        );

        localized
    }
}

fn unique_referenced_namespaces<F: FieldElement>(
    selected_expressions: &SelectedExpressions<F>,
) -> Option<String> {
    let all_namespaces = referenced_namespaces_algebraic_expression(selected_expressions);
    assert!(
        all_namespaces.len() <= 1,
        "Expected at most one namespace, got: {all_namespaces:?}",
    );
    all_namespaces.into_iter().next()
}

/// A connection between two machines.
impl<F: FieldElement> Connection<F> {
    /// The calling machine. None if there are no column references on the LHS.
    pub fn caller(&self) -> Option<String> {
        unique_referenced_namespaces(&self.left)
    }

    /// The called machine. None if there are no column references on the RHS.
    pub fn callee(&self) -> Option<String> {
        unique_referenced_namespaces(&self.right)
    }
}

pub struct ConnectionConstraintChecker<'a, F: FieldElement> {
    connections: &'a [Connection<F>],
    machines: BTreeMap<String, Machine<'a, F>>,
}

impl<'a, F: FieldElement> ConnectionConstraintChecker<'a, F> {
    /// Creates a new connection constraint checker.
    pub fn new(
        connections: &'a [Connection<F>],
        machines: BTreeMap<String, Machine<'a, F>>,
    ) -> Self {
        Self {
            connections,
            machines,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum ConnectionPart {
    Caller,
    Callee,
}

impl<'a, F: FieldElement> ConnectionConstraintChecker<'a, F> {
    /// Checks all connections.
    pub fn check(&self) -> Result<(), FailingConnectionConstraints<'a, F>> {
        let errors = self
            .connections
            .iter()
            .filter_map(|connection| self.check_connection(connection).err())
            .collect::<Vec<_>>();

        (!errors.is_empty())
            .then(|| {
                let error = FailingConnectionConstraints {
                    connection_count: self.connections.len(),
                    errors,
                };
                log::error!("{}", error);
                Err(error)
            })
            .unwrap_or(Ok(()))
    }

    /// Checks a single connection.
    fn check_connection(
        &self,
        connection: &'a Connection<F>,
    ) -> Result<(), FailingConnectionConstraint<'a, F>> {
        let caller_set = self.selected_tuples(connection, ConnectionPart::Caller);
        let callee_set = self.selected_tuples(connection, ConnectionPart::Callee);

        match connection.kind {
            ConnectionKind::Lookup => {
                // Check if $caller \subseteq callee$.
                let caller_set = caller_set.into_iter().collect::<BTreeSet<_>>();
                let callee_set = callee_set.into_iter().collect::<BTreeSet<_>>();
                let not_in_callee = caller_set
                    .difference(&callee_set)
                    .cloned()
                    .collect::<Vec<_>>();
                if !not_in_callee.is_empty() {
                    Err(FailingConnectionConstraint {
                        connection,
                        not_in_callee,
                        not_in_caller: Vec::new(),
                    })
                } else {
                    Ok(())
                }
            }
            ConnectionKind::Permutation => {
                // Check if $caller = callee$ (as multi-set).
                let is_equal = to_multi_set(&caller_set) == to_multi_set(&callee_set);

                // Find the tuples that are in one set, but not in the other.
                // Note that both `not_in_caller` and `not_in_callee` might actually be empty,
                // if `caller_set` and `callee_set` are equal as sets but not as multi-sets.
                let caller_set = caller_set.into_iter().collect::<BTreeSet<_>>();
                let callee_set = callee_set.into_iter().collect::<BTreeSet<_>>();
                let not_in_caller = callee_set.difference(&caller_set).collect::<Vec<_>>();
                let not_in_callee = caller_set.difference(&callee_set).collect::<Vec<_>>();

                if !is_equal {
                    Err(FailingConnectionConstraint {
                        connection,
                        not_in_caller: not_in_caller.into_iter().cloned().collect(),
                        not_in_callee: not_in_callee.into_iter().cloned().collect(),
                    })
                } else {
                    Ok(())
                }
            }
        }
    }

    /// Returns the set of all selected tuples for a given machine.
    fn selected_tuples(
        &self,
        connection: &Connection<F>,
        connection_part: ConnectionPart,
    ) -> Vec<Tuple<F>> {
        let machine_name = match connection_part {
            ConnectionPart::Caller => connection.caller(),
            ConnectionPart::Callee => connection.callee(),
        };
        let selected_expressions = match connection_part {
            ConnectionPart::Caller => &connection.left,
            ConnectionPart::Callee => &connection.right,
        };

        match machine_name {
            Some(machine_name) => match self.machines.get(&machine_name) {
                // The typical case: Find the selected rows and evaluate the tuples.
                Some(machine) => (0..machine.size)
                    .into_par_iter()
                    .filter_map(|row| {
                        let mut evaluator = ExpressionEvaluator::new(
                            machine.values.row(row),
                            &machine.intermediate_definitions,
                        );
                        let result = evaluator.evaluate(&selected_expressions.selector);

                        assert!(result.is_zero() || result.is_one(), "Non-binary selector");
                        result.is_one().then(|| {
                            let values = selected_expressions
                                .expressions
                                .iter()
                                .map(|expression| evaluator.evaluate(expression))
                                .collect::<Vec<_>>();
                            Tuple { values, row }
                        })
                    })
                    .collect(),
                // The machine is empty, so there are no tuples.
                None => Vec::new(),
            },
            // There are no column references in the selected expressions.
            None => {
                let empty_variables = EmptyVariables {};
                let empty_definitions = BTreeMap::new();
                let mut evaluator = ExpressionEvaluator::new(empty_variables, &empty_definitions);
                let selector_value: F = evaluator.evaluate(&selected_expressions.selector);

                match selector_value.to_degree() {
                    // Selected expressions is of the form `0 $ [ <constants> ]`
                    // => The tuples is the empty set.
                    0 => Vec::new(),
                    // This one is tricky, because we don't know the size of the machine.
                    // But for lookups, we can return one tuple, so something like `[ 5 ] in [ BYTES ]`
                    // would still work.
                    1 => {
                        assert_eq!(
                            connection.kind,
                            ConnectionKind::Lookup,
                            "Unexpected connection: {}",
                            connection.identity
                        );
                        if connection_part == ConnectionPart::Callee {
                            // In theory, for lookups we could handle this by repeating the tuple infinitely...
                            unimplemented!("Unexpected connection: {}", connection.identity);
                        }
                        let values = selected_expressions
                            .expressions
                            .iter()
                            .map(|expression| evaluator.evaluate(expression))
                            .collect::<Vec<_>>();
                        vec![Tuple { values, row: 0 }]
                    }
                    _ => unreachable!("Non-binary selector"),
                }
            }
        }
    }
}

struct EmptyVariables;

impl<T: FieldElement> TerminalAccess<T> for EmptyVariables {}

/// Converts a slice to a multi-set, represented as a map from elements to their count.
fn to_multi_set<T: Ord>(a: &[T]) -> BTreeMap<&T, usize> {
    a.iter()
        .sorted()
        .chunk_by(|&t| t)
        .into_iter()
        .map(|(key, group)| (key, group.count()))
        .collect()
}

#[derive(Debug, Clone)]
/// A tuple of field elements.
pub struct Tuple<F> {
    /// The values of the tuple.
    values: Vec<F>,
    /// The row in the machine where this tuple is located.
    /// Note that this value is only informational and is *not* used for equality or ordering.
    row: usize,
}

impl<F: PartialEq> PartialEq for Tuple<F> {
    fn eq(&self, other: &Self) -> bool {
        self.values == other.values
    }
}

impl<F: PartialEq> Eq for Tuple<F> {}

impl<F: PartialOrd> PartialOrd for Tuple<F> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.values.partial_cmp(&other.values)
    }
}

impl<F: Ord> Ord for Tuple<F> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.values.cmp(&other.values)
    }
}

impl<F: fmt::Display> fmt::Display for Tuple<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let values_str = self
            .values
            .iter()
            .map(|value| value.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "Row {}: ({})", self.row, values_str)
    }
}

pub struct FailingConnectionConstraint<'a, F> {
    /// The connection that failed.
    connection: &'a Connection<F>,

    /// Tuples that are in the callee, but not in the caller.
    /// For [ConnectionKind::Lookup], this is irrelevant and we'll store an empty vector here.
    not_in_caller: Vec<Tuple<F>>,

    /// Tuples that are in the caller, but not in the callee.
    not_in_callee: Vec<Tuple<F>>,
}

const MAX_TUPLES: usize = 5;

/// Formats an error, where some tuples in <machine1> are not in <machine2>.
fn fmt_subset_error<F: fmt::Display>(
    f: &mut fmt::Formatter<'_>,
    machine1: &str,
    machine2: &str,
    not_in_machine2: &[Tuple<F>],
) -> fmt::Result {
    writeln!(
        f,
        "  The following tuples appear in {machine1}, but not in {machine2}:"
    )?;
    for tuple in not_in_machine2.iter().take(MAX_TUPLES) {
        writeln!(f, "    {tuple}")?;
    }
    if not_in_machine2.len() > MAX_TUPLES {
        writeln!(f, "    ...")?;
    }
    Ok(())
}

impl<F: FieldElement> fmt::Display for FailingConnectionConstraint<'_, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let caller = self.connection.caller().unwrap_or("???".to_string());
        let callee = self.connection.callee().unwrap_or("???".to_string());

        writeln!(f, "Connection failed between {caller} and {callee}:")?;
        writeln!(f, "    {}", self.connection.identity)?;

        if !self.not_in_callee.is_empty() {
            fmt_subset_error(f, &caller, &callee, &self.not_in_callee)?;
        }
        if !self.not_in_caller.is_empty() {
            fmt_subset_error(f, &callee, &caller, &self.not_in_caller)?;
        }
        Ok(())
    }
}

const MAX_ERRORS: usize = 5;

pub struct FailingConnectionConstraints<'a, F> {
    connection_count: usize,
    errors: Vec<FailingConnectionConstraint<'a, F>>,
}

impl<F: FieldElement> fmt::Display for FailingConnectionConstraints<'_, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Errors in {} / {} connections:",
            self.errors.len(),
            self.connection_count
        )?;
        for error in self.errors.iter().take(MAX_ERRORS) {
            writeln!(f, "{error}")?;
        }
        if self.errors.len() > MAX_ERRORS {
            writeln!(f, "... and {} more errors", self.errors.len() - MAX_ERRORS)?;
        }
        Ok(())
    }
}

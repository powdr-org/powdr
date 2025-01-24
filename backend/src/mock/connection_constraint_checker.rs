use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt;

use std::iter::once;

use derive_more::{Display, From};
use powdr_ast::analyzed::AlgebraicExpression;
use powdr_ast::analyzed::Analyzed;
use powdr_ast::analyzed::{
    Identity, LookupIdentity, PermutationIdentity, PhantomLookupIdentity,
    PhantomPermutationIdentity, SelectedExpressions,
};
use powdr_executor_utils::expression_evaluator::ExpressionEvaluator;
use powdr_executor_utils::expression_evaluator::TerminalAccess;
use powdr_number::FieldElement;
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;

use super::{localize, machine::Machine, unique_referenced_namespaces};

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
    pub multiplicity: Option<AlgebraicExpression<F>>,
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
        let (left, right, kind, multiplicity) = match identity {
            Identity::Polynomial(_) => Err(()),
            Identity::Connect(_) => unimplemented!(),
            Identity::Lookup(LookupIdentity { left, right, .. }) => {
                Ok((left.clone(), right.clone(), ConnectionKind::Lookup, None))
            }
            Identity::PhantomLookup(PhantomLookupIdentity {
                left,
                right,
                multiplicity,
                ..
            }) => Ok((
                left.clone(),
                right.clone(),
                ConnectionKind::Lookup,
                Some(multiplicity.clone()),
            )),
            Identity::Permutation(PermutationIdentity { left, right, .. })
            | Identity::PhantomPermutation(PhantomPermutationIdentity { left, right, .. }) => Ok((
                left.clone(),
                right.clone(),
                ConnectionKind::Permutation,
                None,
            )),
            // Handled by bus constraint checker
            Identity::PhantomBusInteraction(_) => Err(()),
        }?;

        // This connection is not localized yet: Its expression's PolyIDs point to the global PIL, not the local PIL.
        let mut connection = Self {
            identity: identity.clone(),
            left,
            right,
            kind,
            multiplicity,
        };
        if let Some(caller) = connection.caller() {
            connection.left = localize(
                connection.left.clone(),
                global_pil,
                &machine_to_pil[&caller],
            );
        }
        if let Some(callee) = connection.callee() {
            connection.right = localize(
                connection.right.clone(),
                global_pil,
                &machine_to_pil[&callee],
            );
            connection.multiplicity = connection
                .multiplicity
                .clone()
                .map(|multiplicity| localize(multiplicity, global_pil, &machine_to_pil[&callee]));
        }

        Ok(connection)
    }
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

pub struct ConnectionConstraintChecker<'a, F> {
    connections: &'a [Connection<F>],
    machines: &'a BTreeMap<String, Machine<'a, F>>,
}

impl<'a, F: FieldElement> ConnectionConstraintChecker<'a, F> {
    /// Creates a new connection constraint checker.
    pub fn new(
        connections: &'a [Connection<F>],
        machines: &'a BTreeMap<String, Machine<'a, F>>,
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
    pub fn check(&self) -> Result<(), Errors<'a, F>> {
        let errors = self
            .connections
            .iter()
            .filter_map(|connection| self.check_connection(connection).err())
            .flatten()
            .collect::<Vec<_>>();

        (!errors.is_empty())
            .then(|| {
                let error = Errors {
                    connection_count: self.connections.len(),
                    errors,
                };
                log::error!("{}", error);
                Err(error)
            })
            .unwrap_or(Ok(()))
    }

    /// Checks a single connection.
    fn check_connection(&self, connection: &'a Connection<F>) -> Result<(), Vec<Error<'a, F>>> {
        let caller_multi_set = self.selected_tuples(connection, ConnectionPart::Caller);
        let callee_multi_set = self.selected_tuples(connection, ConnectionPart::Callee);

        match connection.kind {
            ConnectionKind::Lookup => {
                // Check if $caller \subseteq callee$.
                let caller_set = caller_multi_set.keys().collect::<BTreeSet<_>>();
                let callee_set = callee_multi_set.keys().collect::<BTreeSet<_>>();
                let not_in_callee = caller_set
                    .difference(&callee_set)
                    .cloned()
                    .collect::<Vec<_>>();
                if !not_in_callee.is_empty() {
                    Err(vec![FailingConnectionConstraint {
                        connection,
                        not_in_callee: not_in_callee.into_iter().cloned().collect(),
                        not_in_caller: Default::default(),
                    }
                    .into()])
                } else if connection.multiplicity.is_some() {
                    // We additionally check that the multiplicities match

                    let errors = caller_multi_set.iter().filter_map(|(tuple, multiplicity)| {
                        let callee_multiplicity = callee_multi_set.get(tuple).unwrap();
                        (multiplicity != callee_multiplicity).then(|| {
                            log::error!("Connection {}: Multiplicities don't match for tuple {}: caller = {:?}, callee = {:?}", connection.identity, tuple, multiplicity, callee_multiplicity);
                            MultiplicityMismatch {
                                connection,
                                tuple: tuple.clone(),
                                caller_multiplicity: *multiplicity,
                                callee_multiplicity: *callee_multiplicity,
                            }.into()
                        })
                    }).collect::<Vec<_>>();
                    if !errors.is_empty() {
                        Err(errors)
                    } else {
                        Ok(())
                    }
                } else {
                    Ok(())
                }
            }
            ConnectionKind::Permutation => {
                // Check if $caller = callee$ (as multi-set).
                let is_equal = caller_multi_set == callee_multi_set;

                // Find the tuples that are in one set, but not in the other.
                // Note that both `not_in_caller` and `not_in_callee` might actually be empty,
                // if `caller_set` and `callee_set` are equal as sets but not as multi-sets.
                let caller_set = caller_multi_set.keys().collect::<BTreeSet<_>>();
                let callee_set = callee_multi_set.keys().collect::<BTreeSet<_>>();
                let not_in_caller = callee_set.difference(&caller_set).collect::<Vec<_>>();
                let not_in_callee = caller_set.difference(&callee_set).collect::<Vec<_>>();

                if !is_equal {
                    Err(vec![FailingConnectionConstraint {
                        connection,
                        not_in_caller: not_in_caller.into_iter().cloned().cloned().collect(),
                        not_in_callee: not_in_callee.into_iter().cloned().cloned().collect(),
                    }
                    .into()])
                } else {
                    Ok(())
                }
            }
        }
    }

    /// Returns the set of all selected tuples for a given machine, with the multiplicity of each tuple.
    /// In the callee:
    /// - In the absence of a multiplicity column, each match has a multiplicity of 1.
    /// - Therefore, in this case, the multiplicity of the caller and callee likely won't match.
    /// - In the presence of a multiplicity column, each match adds the associated multiplicity.
    fn selected_tuples(
        &self,
        connection: &Connection<F>,
        connection_part: ConnectionPart,
    ) -> BTreeMap<Tuple<F>, usize> {
        let machine_name = match connection_part {
            ConnectionPart::Caller => connection.caller(),
            ConnectionPart::Callee => connection.callee(),
        };
        let (selected_expressions, multiplicity) = match connection_part {
            ConnectionPart::Caller => (&connection.left, &None),
            ConnectionPart::Callee => (&connection.right, &connection.multiplicity),
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
                            let absolute_multiplicity = multiplicity
                                .as_ref()
                                .map(|multiplicity| {
                                    i64::try_from(
                                        evaluator.evaluate(multiplicity).to_signed_integer(),
                                    )
                                    .unwrap()
                                    .unsigned_abs() as usize
                                })
                                .unwrap_or(1);
                            (Tuple { values, row }, absolute_multiplicity)
                        })
                    })
                    .fold(BTreeMap::default, |mut tuples, (tuple, multiplicity)| {
                        let entry = tuples.entry(tuple).or_insert(0);
                        *entry += multiplicity;
                        tuples
                    })
                    .reduce(
                        BTreeMap::default, // Create the global accumulator
                        |mut acc, tuples| {
                            for (tuple, count) in tuples {
                                *acc.entry(tuple).or_insert(0) += count;
                            }
                            acc
                        },
                    ),
                // The machine is empty, so there are no tuples.
                None => Default::default(),
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
                    0 => Default::default(),
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
                        once((Tuple { values, row: 0 }, 1)).collect()
                    }
                    _ => unreachable!("Non-binary selector"),
                }
            }
        }
    }
}

struct EmptyVariables;

impl<T: FieldElement> TerminalAccess<T> for EmptyVariables {}

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

#[derive(From, Display)]
pub enum Error<'a, T> {
    MultiplicityMismatch(MultiplicityMismatch<'a, T>),
    FailingConnectionConstraint(FailingConnectionConstraint<'a, T>),
}

pub struct MultiplicityMismatch<'a, F> {
    connection: &'a Connection<F>,
    tuple: Tuple<F>,
    caller_multiplicity: usize,
    callee_multiplicity: usize,
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

impl<F: FieldElement> fmt::Display for MultiplicityMismatch<'_, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Connection {}: Multiplicities don't match for tuple {}: caller = {:?}, callee = {:?}",
            self.connection.identity,
            self.tuple,
            self.caller_multiplicity,
            self.callee_multiplicity
        )
    }
}

const MAX_ERRORS: usize = 5;

pub struct Errors<'a, F> {
    connection_count: usize,
    errors: Vec<Error<'a, F>>,
}

impl<F: FieldElement> fmt::Display for Errors<'_, F> {
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

use std::{
    collections::{BTreeMap, BTreeSet},
    iter,
    ops::ControlFlow,
    str::FromStr,
};

use itertools::Itertools;
use powdr_ast::{
    analyzed::{
        AlgebraicExpression, Analyzed, Identity, LookupIdentity, PermutationIdentity,
        StatementIdentifier, Symbol, SymbolKind,
    },
    parsed::{
        asm::{AbsoluteSymbolPath, SymbolPath},
        visitor::{ExpressionVisitable, VisitOrder},
    },
};
use powdr_number::VariablySizedColumn;
use powdr_number::{DegreeType, FieldElement};

const DUMMY_COLUMN_NAME: &str = "__dummy";

/// Splits a PIL into multiple PILs, one for each "machine".
/// The rough algorithm is as follows:
/// 1. The PIL is split into namespaces
/// 2. Namespaces without any columns are duplicated and merged with the other namespaces
/// 3. Any lookups or permutations that reference multiple namespaces are removed.
pub fn split_pil<F: FieldElement>(pil: &Analyzed<F>) -> BTreeMap<String, Analyzed<F>> {
    let statements_by_namespace = split_by_namespace(pil);
    let statements_by_machine = merge_empty_namespaces(statements_by_namespace, pil);

    statements_by_machine
        .into_iter()
        .map(|(machine_name, statements)| {
            (machine_name, build_machine_pil(pil.clone(), statements))
        })
        .collect()
}

/// Given a set of columns and a PIL describing the machine, returns the witness columns that belong to the machine.
/// Note that this also adds the dummy column.
pub fn machine_witness_columns<F: FieldElement>(
    all_witness_columns: &[(String, Vec<F>)],
    machine_pil: &Analyzed<F>,
    machine_name: &str,
) -> Vec<(String, Vec<F>)> {
    let machine_columns = select_machine_columns(
        all_witness_columns,
        machine_pil.committed_polys_in_source_order(),
    );
    let size = machine_columns
        .iter()
        .map(|(_, column)| column.len())
        .unique()
        .exactly_one()
        .unwrap_or_else(|err| {
            if err.try_len().unwrap() == 0 {
                // No witness column, use degree of provided PIL
                // In practice, we'd at least expect a bus accumulator here, so this should not happen
                // in any sound setup (after #1498)
                machine_pil.degree() as usize
            } else {
                panic!("Machine {machine_name} has witness columns of different sizes")
            }
        });
    let dummy_column_name = format!("{machine_name}::{DUMMY_COLUMN_NAME}");
    let dummy_column = vec![F::zero(); size];
    iter::once((dummy_column_name, dummy_column))
        .chain(machine_columns.into_iter().cloned())
        .collect::<Vec<_>>()
}

/// Given a set of columns and a PIL describing the machine, returns the fixed column that belong to the machine.
pub fn machine_fixed_columns<'a, F: FieldElement>(
    all_fixed_columns: &'a [(String, VariablySizedColumn<F>)],
    machine_pil: &'a Analyzed<F>,
) -> BTreeMap<DegreeType, Vec<(String, &'a [F])>> {
    let machine_columns = select_machine_columns(
        all_fixed_columns,
        machine_pil.constant_polys_in_source_order(),
    );
    let sizes = machine_columns
        .iter()
        .map(|(_, column)| column.available_sizes())
        .collect::<BTreeSet<_>>();

    assert!(
        sizes.len() <= 1,
        "All fixed columns of a machine must have the same sizes"
    );

    let sizes = sizes.into_iter().next().unwrap_or_else(|| {
        let machine_degree_ranges = machine_pil.degree_ranges();
        assert!(
            machine_degree_ranges.len() <= 1,
            "All fixed columns of a machine must have the same size range"
        );
        let range = machine_degree_ranges.iter().next().unwrap();
        range.iter().collect()
    });

    sizes
        .into_iter()
        .map(|size| {
            (
                size,
                machine_columns
                    .iter()
                    .map(|(name, column)| (name.clone(), column.get_by_size(size).unwrap()))
                    .collect::<Vec<_>>(),
            )
        })
        .collect()
}

/// Filter the given columns to only include those that are referenced by the given symbols.
fn select_machine_columns<'a, T: 'a, C>(
    columns: &'a [(String, C)],
    symbols: impl Iterator<Item = &'a (Symbol, T)>,
) -> Vec<&'a (String, C)> {
    let names = symbols
        .flat_map(|(symbol, _)| symbol.array_elements().map(|(name, _)| name))
        .collect::<BTreeSet<_>>();
    columns
        .iter()
        .filter(|(name, _)| names.contains(name))
        .collect::<Vec<_>>()
}

/// From a symbol name, get the namespace of the symbol.
fn extract_namespace(name: &str) -> String {
    let mut namespace = AbsoluteSymbolPath::default().join(SymbolPath::from_str(name).unwrap());
    namespace.pop().unwrap();
    namespace.relative_to(&Default::default()).to_string()
}

/// From an identity, get the namespaces of the symbols it references.
fn referenced_namespaces<F: FieldElement>(
    expression_visitable: &impl ExpressionVisitable<AlgebraicExpression<F>>,
) -> BTreeSet<String> {
    let mut namespaces = BTreeSet::new();
    expression_visitable.visit_expressions(
        &mut (|expr| {
            match expr {
                AlgebraicExpression::Reference(reference) => {
                    namespaces.insert(extract_namespace(&reference.name));
                }
                AlgebraicExpression::PublicReference(_) => unimplemented!(),
                AlgebraicExpression::Challenge(_) => {}
                AlgebraicExpression::Number(_) => {}
                AlgebraicExpression::BinaryOperation(_) => {}
                AlgebraicExpression::UnaryOperation(_) => {}
            }
            ControlFlow::Continue::<()>(())
        }),
        VisitOrder::Pre,
    );

    namespaces
}

/// Organizes the PIL statements by namespace:
/// - Any definition or public declaration belongs to the namespace of the symbol.
/// - Lookups and permutations that reference multiple namespaces removed.
///
/// Returns:
/// - statements_by_namespace: A map from namespace to the statements in that namespace.
fn split_by_namespace<F: FieldElement>(
    pil: &Analyzed<F>,
) -> BTreeMap<String, Vec<StatementIdentifier>> {
    let mut current_namespace = "".to_string();

    pil.source_order
        .iter()
        // split, filtering out some statements
        .filter_map(|statement| match &statement {
            StatementIdentifier::Definition(name)
            | StatementIdentifier::PublicDeclaration(name) => {
                let namespace = extract_namespace(name);
                current_namespace = namespace.clone();
                // add `statement` to `namespace`
                Some((namespace, statement))
            }
            StatementIdentifier::ProofItem(i) => {
                let identity = &pil.identities[*i];
                let namespaces = referenced_namespaces(identity);

                match namespaces.len() {
                    0 => panic!("Identity references no namespace: {identity}"),
                    // add this identity to the only referenced namespace
                    1 => (namespaces.into_iter().next().unwrap() == current_namespace)
                        .then(|| (current_namespace.clone(), statement)),
                    _ => match identity {
                        Identity::Lookup(LookupIdentity { left, right, .. })
                        | Identity::Permutation(PermutationIdentity { left, right, .. }) => {
                            assert_eq!(
                                referenced_namespaces(left).len(),
                                1,
                                "LHS of identity references multiple namespaces: {identity}"
                            );
                            assert_eq!(
                                referenced_namespaces(right).len(),
                                1,
                                "RHS of identity references multiple namespaces: {identity}"
                            );
                            log::debug!("Skipping connecting identity: {identity}");
                            None
                        }
                        _ => {
                            panic!("Identity references multiple namespaces: {identity}");
                        }
                    },
                }
            }
            StatementIdentifier::ProverFunction(_)
            | StatementIdentifier::TraitImplementation(_) => None,
        })
        // collect into a map
        .fold(Default::default(), |mut acc, (namespace, statement)| {
            acc.entry(namespace).or_default().push(statement.clone());
            acc
        })
}

/// Merges namespaces without any polynomials into the other namespaces.
/// For example, a hint might reference a symbol in an std namespace, so we just make
/// those available to all machines.
fn merge_empty_namespaces<F>(
    statements_by_namespace: BTreeMap<String, Vec<StatementIdentifier>>,
    pil: &Analyzed<F>,
) -> BTreeMap<String, Vec<StatementIdentifier>> {
    // Separate out machines without any polynomials
    let (proper_machines, empty_machines) = statements_by_namespace
        .into_iter()
        .partition::<BTreeMap<_, _>, _>(|(_, statements)| {
            statements.iter().any(|statement| match statement {
                StatementIdentifier::Definition(name) => {
                    let symbol = pil
                        .definitions
                        .get(name)
                        .map(|(symbol, _)| symbol)
                        .or(pil.intermediate_columns.get(name).map(|(symbol, _)| symbol))
                        .unwrap();
                    matches!(symbol.kind, SymbolKind::Poly(_))
                }
                _ => false,
            })
        });
    // Merge empty machines into the proper machines
    proper_machines
        .into_iter()
        .map(|(namespace, mut statements)| {
            statements.extend(
                empty_machines
                    .iter()
                    .flat_map(|(_, statements)| statements.clone()),
            );
            (namespace, statements)
        })
        .collect::<BTreeMap<_, _>>()
}

/// Given a PIL and a list of statements, returns a new PIL that only contains the
/// given subset of statements.
fn build_machine_pil<F: FieldElement>(
    pil: Analyzed<F>,
    statements: Vec<StatementIdentifier>,
) -> Analyzed<F> {
    let pil = Analyzed {
        source_order: statements,
        ..pil
    };
    let pil_string = add_dummy_witness_column(&pil.to_string());
    let parsed_string = powdr_parser::parse(None, &pil_string).unwrap();
    powdr_pil_analyzer::analyze_ast(parsed_string).unwrap()
}

/// Insert a dummy witness column and identity into the PIL string, just after the namespace.
/// This ensures that all machine PILs have at least one witness column and identity, which is
/// assumed by most backends.
/// In the future, this will always be the case, as interacting with the bus will require
/// at least one witness column & identity, so this is only necessary for now.
fn add_dummy_witness_column(pil_string: &str) -> String {
    let dummy_column = format!("    col witness {DUMMY_COLUMN_NAME};");
    let dummy_constraint = format!("    {DUMMY_COLUMN_NAME} = {DUMMY_COLUMN_NAME};");
    let mut has_inserted_dummy_lines = false;

    pil_string
        .lines()
        .flat_map(|line| {
            if line.starts_with("namespace") && !has_inserted_dummy_lines {
                // All namespaces except the first are empty and should stay empty
                has_inserted_dummy_lines = true;
                vec![line, &dummy_column, &dummy_constraint]
            } else {
                vec![line]
            }
        })
        .join("\n")
}

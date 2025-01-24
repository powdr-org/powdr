use core::panic;
use std::collections::{HashMap, HashSet};

use std::fs;
use std::iter::once;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::structural_checks::check_structs_fields;
use itertools::Itertools;
use powdr_ast::parsed::asm::{
    parse_absolute_path, AbsoluteSymbolPath, ModuleStatement, SymbolPath,
};
use powdr_ast::parsed::types::Type;
use powdr_ast::parsed::visitor::{AllChildren, Children};
use powdr_ast::parsed::{
    self, Expression as ParsedExpression, FunctionKind, LambdaExpression, PILFile, PilStatement,
    SourceReference, SymbolCategory, TraitImplementation, TypedExpression,
};
use powdr_number::{FieldElement, GoldilocksField};

use powdr_ast::analyzed::{
    type_from_definition, Analyzed, DegreeRange, Expression, FunctionValueDefinition,
    PolynomialType, PublicDeclaration, Reference, SolvedTraitImpls, StatementIdentifier, Symbol,
    SymbolKind,
};
use powdr_parser::{parse, parse_module, parse_type};
use powdr_parser_util::Error;

use crate::traits_resolver::TraitsResolver;
use crate::type_builtins::constr_function_statement_type;
use crate::type_inference::infer_types;
use crate::{side_effect_checker, AnalysisDriver};

use crate::statement_processor::{Counters, PILItem, StatementProcessor};
use crate::{condenser, evaluator, expression_processor::ExpressionProcessor};

pub fn analyze_file<T: FieldElement>(path: &Path) -> Result<Analyzed<T>, Vec<Error>> {
    let files = import_all_dependencies(path);
    analyze(files)
}

pub fn analyze_ast<T: FieldElement>(pil_file: PILFile) -> Result<Analyzed<T>, Vec<Error>> {
    analyze(vec![pil_file])
}

pub fn analyze_string<T: FieldElement>(contents: &str) -> Result<Analyzed<T>, Vec<Error>> {
    let pil_file = powdr_parser::parse(Some("input"), contents).map_err(|e| vec![e])?;
    analyze(vec![pil_file])
}

fn analyze<T: FieldElement>(files: Vec<PILFile>) -> Result<Analyzed<T>, Vec<Error>> {
    let mut analyzer = PILAnalyzer::new();
    analyzer.process(files)?;
    analyzer.side_effect_check()?;
    analyzer.validate_structs()?;
    analyzer.type_check()?;
    let solved_impls = analyzer.resolve_trait_impls()?;
    analyzer.condense(solved_impls)
}

#[derive(Default)]
struct PILAnalyzer {
    /// Known symbols by name and category, determined in the first step.
    known_symbols: HashMap<String, SymbolCategory>,
    current_namespace: AbsoluteSymbolPath,
    polynomial_degree: Option<DegreeRange>,
    /// Map of definitions, gradually being built up here.
    definitions: HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
    public_declarations: HashMap<String, PublicDeclaration>,
    /// The list of proof items, i.e. statements that evaluate to constraints or prover functions.
    proof_items: Vec<Expression>,
    /// The order in which definitions and identities
    /// appear in the source.
    source_order: Vec<StatementIdentifier>,
    symbol_counters: Option<Counters>,
    /// Symbols from the core that were added automatically but will not be printed.
    auto_added_symbols: HashSet<String>,
    /// All trait implementations found, in source order.
    trait_impls: Vec<TraitImplementation<Expression>>,
}

/// Reads and parses the given path and all its imports.
fn import_all_dependencies(path: &Path) -> Vec<PILFile> {
    let mut processed = Default::default();
    import_all_dependencies_internal(path, &mut processed)
}

fn import_all_dependencies_internal(path: &Path, processed: &mut HashSet<PathBuf>) -> Vec<PILFile> {
    let path = path
        .canonicalize()
        .unwrap_or_else(|e| panic!("File {path:?} not found: {e}"));
    if !processed.insert(path.clone()) {
        return vec![];
    }

    let contents = fs::read_to_string(path.clone()).unwrap();

    let ast = powdr_parser::parse(Some(path.to_str().unwrap()), &contents).unwrap_or_else(|err| {
        eprintln!("Error parsing .pil file:");
        err.output_to_stderr();
        panic!();
    });

    // Filter out non-includes and compute the relative paths of includes.
    let (non_includes, includes) = ast.0.into_iter().fold(
        (vec![], vec![]),
        |(mut non_includes, mut included_paths), s| {
            match s {
                PilStatement::Include(_, include) => {
                    included_paths.push(path.parent().unwrap().join(include));
                }
                _ => non_includes.push(s),
            }
            (non_includes, included_paths)
        },
    );
    // Process includes and add the file itself.
    includes
        .into_iter()
        .flat_map(|path| import_all_dependencies_internal(&path, processed))
        .chain(once(PILFile(non_includes)))
        .collect::<Vec<_>>()
}

impl PILAnalyzer {
    pub fn new() -> PILAnalyzer {
        PILAnalyzer {
            symbol_counters: Some(Default::default()),
            ..Default::default()
        }
    }

    pub fn process(&mut self, mut files: Vec<PILFile>) -> Result<(), Vec<Error>> {
        for PILFile(file) in &files {
            self.current_namespace = Default::default();
            for statement in file {
                self.collect_names(statement);
            }
        }

        if let Some(core) = self.core_types_if_not_present() {
            self.current_namespace = Default::default();
            for statement in &core.0 {
                for (name, _) in self.collect_names(statement) {
                    self.auto_added_symbols.insert(name);
                }
            }
            files = once(core).chain(files).collect();
        }

        let mut errors = Vec::new();
        for PILFile(file) in files {
            self.current_namespace = Default::default();
            for statement in file {
                if let Err(e) = self.handle_statement(statement) {
                    errors.push(e);
                }
            }
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Adds core types if they are not present in the input.
    /// These need to be present because the type checker relies on them.
    fn core_types_if_not_present(&self) -> Option<PILFile> {
        // We are extracting some specific symbols from the prelude file.
        let prelude = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../std/prelude.asm"));
        let missing_symbols = [
            "Constr",
            "Option",
            "challenge",
            "set_hint",
            "Query",
            "true",
            "false",
        ]
        .into_iter()
        .filter(|symbol| {
            !self
                .known_symbols
                .contains_key(&format!("std::prelude::{symbol}"))
        })
        .collect::<Vec<_>>();
        (!missing_symbols.is_empty()).then(|| {
            let module = parse_module(None, prelude).unwrap();
            let missing_symbols = module
                .statements
                .into_iter()
                .filter_map(|s| {
                    match &s {
                        ModuleStatement::SymbolDefinition(s) => {
                            missing_symbols.contains(&s.name.as_str())
                        }
                        ModuleStatement::PilStatement(s) => s
                            .symbol_definition_names()
                            .any(|(name, _)| missing_symbols.contains(&name.as_str())),
                    }
                    .then_some(vec![format!("{s}")])
                })
                .flatten()
                .join("\n");
            parse(None, &format!("namespace std::prelude;\n{missing_symbols}")).unwrap()
        })
    }

    /// Check that query and constr functions are used in the correct contexts.
    pub fn side_effect_check(&self) -> Result<(), Vec<Error>> {
        let mut errors = vec![];
        #[allow(clippy::iter_over_hash_type)]
        // TODO: This is not deterministic to the extent that the errors are added in arbitrary order. Source order would be better.
        for (symbol, value) in self.definitions.values() {
            let Some(value) = value else { continue };
            let context = match symbol.kind {
                // Witness column value is query function
                SymbolKind::Poly(PolynomialType::Committed) => FunctionKind::Query,
                // Fixed column value must be pure.
                SymbolKind::Poly(PolynomialType::Constant) => FunctionKind::Pure,
                SymbolKind::Other() => match value {
                    // Otherwise, just take the kind of the lambda expression.
                    FunctionValueDefinition::Expression(TypedExpression { type_scheme: _, e }) => {
                        if let Expression::LambdaExpression(_, LambdaExpression { kind, .. }) = e {
                            *kind
                        } else {
                            FunctionKind::Constr
                        }
                    }
                    _ => FunctionKind::Constr,
                },
                // Default is constr.
                _ => FunctionKind::Constr,
            };
            value
                .children()
                .try_for_each(|e| side_effect_checker::check(&self.definitions, context, e))
                .unwrap_or_else(|err| errors.push(err));
        }

        for i in &self.trait_impls {
            i.children()
                .try_for_each(|e| {
                    side_effect_checker::check(&self.definitions, FunctionKind::Pure, e)
                })
                .unwrap_or_else(|err| errors.push(err));
        }

        // for all proof items, check that they call pure or constr functions
        errors.extend(self.proof_items.iter().filter_map(|e| {
            side_effect_checker::check(&self.definitions, FunctionKind::Constr, e).err()
        }));

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    pub fn validate_structs(&self) -> Result<(), Vec<Error>> {
        let structs_exprs = self
            .all_children()
            .filter(|expr| matches!(expr, Expression::StructExpression(_, _)));

        check_structs_fields(structs_exprs, &self.definitions)
    }

    pub fn type_check(&mut self) -> Result<(), Vec<Error>> {
        let query_type: Type = parse_type("int -> std::prelude::Query").unwrap().into();
        let mut expressions = vec![];
        // Collect all definitions and traits implementations with their types and expressions.
        // We filter out enum type declarations (the constructor functions have been added
        // by the statement processor already).
        // For Arrays, we also collect the inner expressions and expect them to be field elements.

        for trait_impl in self.trait_impls.iter_mut() {
            let (_, def) = self
                .definitions
                .get(&trait_impl.name.to_string())
                .expect("Trait definition not found");
            let Some(FunctionValueDefinition::TraitDeclaration(trait_decl)) = def else {
                unreachable!();
            };

            let specialized_types: Vec<_> = trait_impl
                .functions
                .iter()
                .map(|named_expr| trait_impl.type_of_function(trait_decl, &named_expr.name))
                .collect();

            for (named_expr, specialized_type) in
                trait_impl.functions.iter_mut().zip(specialized_types)
            {
                expressions.push((
                    Arc::get_mut(&mut named_expr.body).unwrap(),
                    specialized_type.into(),
                ));
            }
        }

        let definitions = self
            .definitions
            .iter_mut()
            .filter(|(_name, (_symbol, value))| {
                !matches!(
                    value,
                    Some(FunctionValueDefinition::TypeDeclaration(_))
                        | Some(FunctionValueDefinition::TraitDeclaration(_))
                )
            })
            .flat_map(|(name, (symbol, value))| {
                let (type_scheme, expr) = match (symbol.kind, value) {
                    (SymbolKind::Poly(PolynomialType::Committed), Some(value)) => {
                        // Witness column, move its value (query function) into the expressions to be checked separately.
                        let type_scheme = type_from_definition(symbol, &None);

                        let FunctionValueDefinition::Expression(TypedExpression { e, .. }) = value
                        else {
                            panic!("Invalid value for query function")
                        };

                        expressions.push((e, query_type.clone().into()));

                        (type_scheme, None)
                    }
                    (
                        _,
                        Some(FunctionValueDefinition::Expression(TypedExpression {
                            type_scheme,
                            e,
                        })),
                    ) => (type_scheme.clone(), Some(e)),
                    (_, value) => {
                        let type_scheme = type_from_definition(symbol, value);

                        if let Some(FunctionValueDefinition::Array(items)) = value {
                            // Expect all items in the arrays to be field elements.
                            expressions.extend(items.children_mut().map(|e| (e, Type::Fe.into())));
                        }

                        (type_scheme, None)
                    }
                };
                Some((name.clone(), (type_scheme, expr)))
            })
            .collect();
        for expr in &mut self.proof_items {
            // At statement level, we allow Constr, Constr[], (int -> ()) or ().
            expressions.push((expr, constr_function_statement_type()));
        }

        let inferred_types = infer_types(definitions, &mut expressions)?;
        // Store the inferred types.
        for (name, ty) in inferred_types {
            let Some(FunctionValueDefinition::Expression(TypedExpression {
                type_scheme: ts @ None,
                e: _,
            })) = &mut self.definitions.get_mut(&name).unwrap().1
            else {
                panic!()
            };
            *ts = Some(ty.into());
        }
        Ok(())
    }

    /// Creates and returns a map for every referenced trait function with concrete type to the
    /// corresponding trait implementation function.
    fn resolve_trait_impls(&mut self) -> Result<SolvedTraitImpls, Vec<Error>> {
        let all_traits = self
            .definitions
            .iter()
            .filter_map(|(name, (_, value))| {
                if let Some(FunctionValueDefinition::TraitDeclaration(..)) = value {
                    Some(name.as_str())
                } else {
                    None
                }
            })
            .collect();
        let mut trait_solver = TraitsResolver::new(all_traits, &self.trait_impls);

        // TODO building this impl map should be different from checking that all trait references
        // have an implementation.
        // The reason is that for building the map, we need to unfold all generic functions,
        // which could cause an exponential blow-up. Checking that an implementation exists
        // could maybe already done at the type-checking level.
        // If we do that earlier, then errors here should be panics.
        // Also we should only build the impl map for code that is reachable from entry points.
        let definitions = self
            .definitions
            .values()
            .flat_map(|(_, def)| match def {
                Some(
                    v
                    @ (FunctionValueDefinition::Expression(_) | FunctionValueDefinition::Array(_)),
                ) => Some(v),
                _ => None,
            })
            .flat_map(|d| d.children());
        let proof_items = self.proof_items.iter();
        let trait_impls = self.trait_impls.iter().flat_map(|i| i.children());
        let mut errors = vec![];
        for expr in definitions
            .chain(proof_items)
            .chain(trait_impls)
            .flat_map(|i| i.all_children())
        {
            if let Expression::Reference(source_ref, Reference::Poly(reference)) = expr {
                if reference.type_args.is_some() {
                    if let Err(e) = trait_solver.resolve_trait_function_reference(reference) {
                        errors.push(source_ref.with_error(e));
                    }
                }
            }
        }

        if !errors.is_empty() {
            Err(errors)
        } else {
            Ok(trait_solver.solved_impls())
        }
    }

    pub fn condense<T: FieldElement>(
        self,
        solved_impls: SolvedTraitImpls,
    ) -> Result<Analyzed<T>, Vec<Error>> {
        Ok(condenser::condense(
            self.definitions,
            solved_impls,
            self.public_declarations,
            &self.proof_items,
            self.trait_impls,
            self.source_order,
            self.auto_added_symbols,
        ))
    }

    /// A step to collect all defined names in the statement.
    fn collect_names(&mut self, statement: &PilStatement) -> Vec<(String, SymbolCategory)> {
        match statement {
            PilStatement::Namespace(_, name, _) => {
                self.current_namespace = AbsoluteSymbolPath::default().join(name.clone());
                vec![]
            }
            PilStatement::Include(_, _) => unreachable!(),
            _ => {
                let names = statement
                    .symbol_definition_names_and_contained()
                    .map(|(name, sub_name, symbol_category)| {
                        (
                            match sub_name {
                                None => self.driver().resolve_decl(name),
                                Some(sub_name) => self
                                    .driver()
                                    .resolve_namespaced_decl(&[name, sub_name])
                                    .relative_to(&Default::default())
                                    .to_string(),
                            },
                            symbol_category,
                        )
                    })
                    .collect::<Vec<_>>();
                for (name, symbol_kind) in &names {
                    if self
                        .known_symbols
                        .insert(name.clone(), *symbol_kind)
                        .is_some()
                    {
                        panic!("Duplicate symbol definition: {name}");
                    }
                }
                names
            }
        }
    }

    fn handle_statement(&mut self, statement: PilStatement) -> Result<(), Error> {
        match statement {
            PilStatement::Include(_, _) => unreachable!(),
            PilStatement::Namespace(_, name, degree) => self.handle_namespace(name, degree),
            _ => {
                // We need a mutable reference to the counter, but it is short-lived.
                let mut counters = self.symbol_counters.take().unwrap();
                let items =
                    StatementProcessor::new(self.driver(), &mut counters, self.polynomial_degree)
                        .handle_statement(statement)?;
                self.symbol_counters = Some(counters);
                for item in items {
                    match item {
                        PILItem::Definition(symbol, value) => {
                            let name = symbol.absolute_name.clone();
                            let is_new = self
                                .definitions
                                .insert(name.clone(), (symbol, value))
                                .is_none();
                            assert!(is_new, "{name} already defined.");
                            self.source_order
                                .push(StatementIdentifier::Definition(name));
                        }
                        PILItem::PublicDeclaration(decl) => {
                            let name = decl.name.clone();
                            let is_new = self
                                .public_declarations
                                .insert(name.clone(), decl)
                                .is_none();
                            assert!(is_new, "Public '{name}' already declared.");
                            self.source_order
                                .push(StatementIdentifier::PublicDeclaration(name));
                        }
                        PILItem::ProofItem(item) => {
                            let index = self.proof_items.len();
                            self.source_order
                                .push(StatementIdentifier::ProofItem(index));
                            self.proof_items.push(item)
                        }
                        PILItem::TraitImplementation(trait_impl) => {
                            let index = self.trait_impls.len();
                            self.source_order
                                .push(StatementIdentifier::TraitImplementation(index));
                            self.trait_impls.push(trait_impl)
                        }
                    }
                }
                Ok(())
            }
        }
    }
    fn handle_namespace(
        &mut self,
        name: SymbolPath,
        degree: Option<parsed::NamespaceDegree>,
    ) -> Result<(), Error> {
        let evaluate_degree_bound = |e: ParsedExpression| -> Result<u64, Error> {
            let source = e.source_reference().clone();
            let e = ExpressionProcessor::new(self.driver(), &Default::default())
                .process_expression(e)
                .map_err(|err| {
                    err.extend_message(|m| format!("Failed to evaluate degree bound: {m}"))
                })?;

            let value = evaluator::evaluate_expression::<GoldilocksField>(
                &e,
                &self.definitions,
                &Default::default(),
            )
            .unwrap()
            .try_to_integer()
            .map_err(|err| source.with_error(err.to_string()))?;

            u64::try_from(value)
                .map_err(|_| source.with_error("Degree bound too large".to_string()))
        };

        self.polynomial_degree = degree
            .map(|degree| -> Result<_, Error> {
                Ok(DegreeRange {
                    min: evaluate_degree_bound(degree.min)?,
                    max: evaluate_degree_bound(degree.max)?,
                })
            })
            .transpose()?;

        self.current_namespace = AbsoluteSymbolPath::default().join(name);

        Ok(())
    }
    fn driver(&self) -> Driver {
        Driver(self)
    }
}

impl Children<Expression> for PILAnalyzer {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        Box::new(
            self.definitions
                .values()
                .filter_map(|(_, def)| def.as_ref())
                // Since TraitFunction definition is already included in the declaration itself, we filter TraitFunctions to avoid duplicates
                .filter(|def| !matches!(def, FunctionValueDefinition::TraitFunction(_, _)))
                .flat_map(|def| def.children())
                .chain(self.trait_impls.iter().flat_map(|impl_| impl_.children()))
                .chain(self.proof_items.iter()),
        )
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        Box::new(
            self.definitions
                .values_mut()
                .filter_map(|(_, def)| def.as_mut())
                // Since TraitFunction definition is already included in the declaration itself, we filter TraitFunctions to avoid duplicates
                .filter(|def| !matches!(def, FunctionValueDefinition::TraitFunction(_, _)))
                .flat_map(|def| def.children_mut())
                .chain(
                    self.trait_impls
                        .iter_mut()
                        .flat_map(|impl_| impl_.children_mut()),
                )
                .chain(self.proof_items.iter_mut()),
        )
    }
}

#[derive(Clone, Copy)]
struct Driver<'a>(&'a PILAnalyzer);

impl AnalysisDriver for Driver<'_> {
    fn resolve_namespaced_decl(&self, path: &[&String]) -> AbsoluteSymbolPath {
        path.iter()
            .fold(self.0.current_namespace.clone(), |path, part| {
                path.with_part(part)
            })
    }

    fn try_resolve_ref(&self, path: &SymbolPath) -> Option<(String, SymbolCategory)> {
        // Try to resolve the name starting at the current namespace and then
        // go up level by level until the root.
        // If this does not work, try resolving inside std::prelude.

        self.0
            .current_namespace
            .iter_to_root()
            .chain(once(parse_absolute_path("::std::prelude")))
            .find_map(|prefix| {
                let path = prefix
                    .join(path.clone())
                    .relative_to(&Default::default())
                    .to_string();
                self.0.known_symbols.get(&path).map(|cat| (path, *cat))
            })
    }

    fn definitions(&self) -> &HashMap<String, (Symbol, Option<FunctionValueDefinition>)> {
        &self.0.definitions
    }
}

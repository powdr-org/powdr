//! Formatting functions for analyzed PIL files.
//!
//! These are not meant to be 1-1 reproductions, they will have errors.
//! Do not use this to re-generate PIL files!

use std::{
    fmt::{Display, Formatter, Result},
    str::FromStr,
};

use itertools::Itertools;
use parsed::{display::format_type_args, LambdaExpression, TypeDeclaration, TypedExpression};

use crate::{parsed::FunctionKind, writeln_indented};

use self::parsed::{
    asm::{AbsoluteSymbolPath, SymbolPath},
    display::format_type_scheme_around_name,
};

use super::*;

impl Display for DegreeRange {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match (self.min, self.max) {
            (min, max) if min == max => write!(f, "{min}"),
            (min, max) => write!(f, "{min}..{max}"),
        }
    }
}

impl<T: Display> Display for Analyzed<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        // Compute map from namespace name to its degree (if not None).
        let namespace_degrees = self
            .definitions
            .values()
            .filter_map(|(symbol, _)| {
                symbol.degree.map(|degree| {
                    let (namespace, _) = split_into_namespace_and_name(&symbol.absolute_name);
                    (namespace, degree)
                })
            })
            .unique()
            .fold(BTreeMap::default(), |mut degrees, (namespace, degree)| {
                let is_new = degrees.insert(namespace.clone(), degree).is_none();
                assert!(
                    is_new,
                    "Found symbols with different degrees in namespace {namespace}"
                );
                degrees
            });
        let mut current_namespace = AbsoluteSymbolPath::default();
        // Helper function to emit a `namespace` statement if the namespace changes.
        let mut update_namespace = |name: &str, f: &mut Formatter<'_>| {
            let (namespace, name) = split_into_namespace_and_name(name);
            if namespace != current_namespace {
                current_namespace = namespace;
                let degree = namespace_degrees
                    .get(&current_namespace)
                    .map(|d| format!("({d})"))
                    .unwrap_or_default();
                writeln!(
                    f,
                    "namespace {}{degree};",
                    current_namespace.relative_to(&Default::default()),
                )?;
            };
            Ok(name)
        };

        for statement in &self.source_order {
            match statement {
                StatementIdentifier::Definition(name) => {
                    if self.auto_added_symbols.contains(name) {
                        // Core symbol added automatically, no need to print.
                        continue;
                    }
                    if let Some((symbol, definition)) = self.definitions.get(name) {
                        if matches!(
                            definition,
                            Some(FunctionValueDefinition::TypeConstructor(_, _))
                                | Some(FunctionValueDefinition::TraitFunction(_, _))
                        ) {
                            // These are printed as part of the enum / trait.
                            continue;
                        }
                        let name = update_namespace(name, f)?;
                        match symbol.kind {
                            SymbolKind::Poly(PolynomialType::Constant) => {
                                writeln_indented(f, format_fixed_column(&name, symbol, definition))?
                            }
                            SymbolKind::Poly(PolynomialType::Committed) => writeln_indented(
                                f,
                                format_witness_column(&name, symbol, definition),
                            )?,
                            SymbolKind::Poly(PolynomialType::Intermediate) => unreachable!(),
                            SymbolKind::Other() => {
                                assert!(symbol.stage.is_none());
                                match definition {
                                    Some(FunctionValueDefinition::Expression(
                                        TypedExpression { e, type_scheme },
                                    )) => {
                                        writeln_indented(
                                            f,
                                            format!(
                                                "let{} = {e};",
                                                format_type_scheme_around_name(&name, type_scheme)
                                            ),
                                        )?;
                                    }
                                    Some(FunctionValueDefinition::TypeDeclaration(
                                        TypeDeclaration::Enum(enum_declaration),
                                    )) => {
                                        writeln_indented(
                                            f,
                                            enum_declaration.to_string_with_name(&name),
                                        )?;
                                    }
                                    Some(FunctionValueDefinition::TypeDeclaration(
                                        TypeDeclaration::Struct(struct_declaration),
                                    )) => {
                                        writeln_indented(
                                            f,
                                            struct_declaration.to_string_with_name(&name),
                                        )?;
                                    }
                                    Some(FunctionValueDefinition::TraitDeclaration(
                                        trait_declaration,
                                    )) => {
                                        writeln_indented(
                                            f,
                                            trait_declaration.to_string_with_name(&name),
                                        )?;
                                    }
                                    _ => {
                                        unreachable!("Invalid definition for symbol: {}", name)
                                    }
                                }
                            }
                        }
                    } else if let Some((symbol, definition)) = self.intermediate_columns.get(name) {
                        assert!(symbol.stage.is_none());
                        let name = update_namespace(name, f)?;
                        assert_eq!(symbol.kind, SymbolKind::Poly(PolynomialType::Intermediate));
                        if let Some(length) = symbol.length {
                            writeln_indented(
                                f,
                                format!(
                                    "col {name}[{length}] = [{}];",
                                    definition.iter().format(", ")
                                ),
                            )?;
                        } else {
                            assert_eq!(definition.len(), 1);
                            writeln_indented(f, format!("col {name} = {};", definition[0]))?;
                        }
                    } else {
                        panic!()
                    }
                }
                StatementIdentifier::PublicDeclaration(name) => {
                    let decl = &self.public_declarations[name];
                    let name = update_namespace(&decl.name, f)?;
                    writeln_indented(f, format_public_declaration(&name, decl))?;
                }
                StatementIdentifier::ProofItem(i) => {
                    writeln_indented(f, &self.identities[*i])?;
                }
                StatementIdentifier::ProverFunction(i) => {
                    writeln_indented(f, format!("{};", &self.prover_functions[*i]))?;
                }
                StatementIdentifier::TraitImplementation(i) => {
                    writeln_indented(f, format!("{}", self.trait_impls[*i]))?;
                }
            }
        }

        Ok(())
    }
}

fn split_into_namespace_and_name(name: &str) -> (AbsoluteSymbolPath, String) {
    let mut path = AbsoluteSymbolPath::default().join(SymbolPath::from_str(name).unwrap());
    let name = path.pop().unwrap();
    (path, name)
}

fn format_fixed_column(
    name: &str,
    symbol: &Symbol,
    definition: &Option<FunctionValueDefinition>,
) -> String {
    assert_eq!(symbol.kind, SymbolKind::Poly(PolynomialType::Constant));
    assert!(symbol.stage.is_none());
    if let Some(TypedExpression { type_scheme, e }) = try_to_simple_expression(definition) {
        if symbol.length.is_some() {
            assert!(matches!(
                type_scheme,
                Some(TypeScheme {
                    vars: _,
                    ty: Type::Array(_)
                })
            ));
        }
        format!(
            "let{} = {e};",
            format_type_scheme_around_name(&name, type_scheme)
        )
    } else {
        assert!(symbol.length.is_none());
        let value = definition
            .as_ref()
            .map(ToString::to_string)
            .unwrap_or_default();
        format!("col fixed {name}{value};",)
    }
}

fn format_witness_column(
    name: &str,
    symbol: &Symbol,
    definition: &Option<FunctionValueDefinition>,
) -> String {
    assert_eq!(symbol.kind, SymbolKind::Poly(PolynomialType::Committed));
    let stage = symbol
        .stage
        .and_then(|s| (s > 0).then(|| format!("stage({s}) ")))
        .unwrap_or_default();
    let length = symbol
        .length
        .map(|length| format!("[{length}]"))
        .unwrap_or_default();
    let mut result = format!("col witness {stage}{name}{length};");
    if let Some(value) = definition {
        assert!(symbol.length.is_none());
        let FunctionValueDefinition::Expression(TypedExpression { e, .. }) = value else {
            panic!()
        };
        result += &format!("\nstd::prelude::set_hint({}, {e});", symbol.absolute_name);
    }
    result
}

fn format_public_declaration(name: &str, decl: &PublicDeclaration) -> String {
    format!(
        "public {name} = {}{}({});",
        decl.polynomial,
        decl.array_index
            .map(|i| format!("[{i}]"))
            .unwrap_or_default(),
        decl.index
    )
}

impl Display for FunctionValueDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            FunctionValueDefinition::Array(e) => {
                write!(f, " = {e}")
            }
            FunctionValueDefinition::Expression(TypedExpression {
                e,
                type_scheme: None,
            }) => format_outer_function(e, f),
            FunctionValueDefinition::Expression(TypedExpression {
                e,
                type_scheme: Some(ty),
            }) if *ty == Type::Col.into() => format_outer_function(e, f),
            FunctionValueDefinition::Expression(TypedExpression {
                e,
                type_scheme: Some(ts),
            }) => {
                assert!(ts.vars.is_empty(), "Should not have called this display function, since we cannot properly format the type vars.");
                write!(f, ": {} = {e}", ts.ty)
            }
            FunctionValueDefinition::TypeDeclaration(_)
            | FunctionValueDefinition::TypeConstructor(_, _)
            | FunctionValueDefinition::TraitDeclaration(_)
            | FunctionValueDefinition::TraitFunction(_, _) => {
                panic!("Should not use this formatting function.")
            }
        }
    }
}

fn try_to_simple_expression(
    definition: &Option<FunctionValueDefinition>,
) -> Option<&TypedExpression<Reference, u64>> {
    match definition.as_ref()? {
        FunctionValueDefinition::Array(_) => None,
        FunctionValueDefinition::Expression(TypedExpression {
            e: Expression::LambdaExpression(_, LambdaExpression { params, .. }),
            type_scheme,
        }) if params.len() == 1
            && type_scheme
                .as_ref()
                .map(|ts| *ts == Type::Col.into())
                .unwrap_or(true) =>
        {
            None
        }
        FunctionValueDefinition::Expression(e) => Some(e),
        _ => unreachable!(),
    }
}

fn format_outer_function(e: &Expression, f: &mut Formatter<'_>) -> Result {
    match e {
        parsed::Expression::LambdaExpression(_, lambda) if lambda.params.len() == 1 => {
            let body = if lambda.kind == FunctionKind::Pure
                && !matches!(lambda.body.as_ref(), Expression::BlockExpression(_, _))
            {
                format!("{{ {} }}", lambda.body)
            } else {
                format!("{}", lambda.body)
            };
            write!(
                f,
                "({}) {}{body}",
                lambda.params.iter().format(", "),
                match lambda.kind {
                    FunctionKind::Pure => "".into(),
                    _ => format!("{} ", &lambda.kind),
                },
            )
        }
        _ => write!(f, " = {e}"),
    }
}

impl<T: Display> Display for SelectedExpressions<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}[{}]",
            {
                // we only print the selector if it is not 1. The comparison is string-based to avoid introducing invasive type bounds on T.
                let s = self.selector.to_string();
                match s.as_str() {
                    "1" => "".to_string(),
                    s => format!("{s} $ "),
                }
            },
            self.expressions.iter().format(", ")
        )
    }
}

impl<T: Display> Display for PolynomialIdentity<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match &self.expression {
            AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation {
                left,
                op: AlgebraicBinaryOperator::Sub,
                right,
            }) => {
                write!(f, "{left} = {right};")
            }
            e => write!(f, "{e} = 0;"),
        }
    }
}

impl<T: Display> Display for LookupIdentity<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{} in {};", self.left, self.right)
    }
}

fn format_selector<T: Display>(selector: &AlgebraicExpression<T>) -> String {
    match selector.to_string().as_str() {
        "1" => "Option::None".to_string(),
        s => format!("Option::Some({s})"),
    }
}

impl<T: Display> Display for PhantomLookupIdentity<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "Constr::PhantomLookup(({}, {}), [{}], {});",
            format_selector(&self.left.selector),
            format_selector(&self.right.selector),
            self.left
                .expressions
                .iter()
                .zip_eq(&self.right.expressions)
                .map(|(left, right)| format!("({left}, {right})"))
                .format(", "),
            self.multiplicity
        )
    }
}

impl<T: Display> Display for PermutationIdentity<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{} is {};", self.left, self.right)
    }
}

impl<T: Display> Display for PhantomPermutationIdentity<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "Constr::PhantomPermutation(({}, {}), [{}]);",
            format_selector(&self.left.selector),
            format_selector(&self.right.selector),
            self.left
                .expressions
                .iter()
                .zip_eq(&self.right.expressions)
                .map(|(left, right)| format!("({left}, {right})"))
                .format(", ")
        )
    }
}

impl<T: Display> Display for ConnectIdentity<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "[{}] connect [{}];",
            self.left.iter().format(", "),
            self.right.iter().format(", ")
        )
    }
}

impl<T: Display> Display for PhantomBusInteractionIdentity<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "Constr::PhantomBusInteraction({}, {}, [{}], {}, [{}], [{}]);",
            self.multiplicity,
            self.bus_id,
            self.payload.0.iter().map(ToString::to_string).format(", "),
            self.latch,
            self.folded_expressions
                .0
                .iter()
                .map(ToString::to_string)
                .format(", "),
            self.accumulator_columns
                .iter()
                .map(ToString::to_string)
                .format(", "),
        )
    }
}

impl Display for Reference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Reference::LocalVar(_index, name) => {
                write!(f, "{name}")
            }
            Reference::Poly(r) => write!(f, "{r}"),
        }
    }
}

impl<T: Display> Display for AlgebraicExpression<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            AlgebraicExpression::Reference(reference) => write!(f, "{reference}"),
            AlgebraicExpression::PublicReference(name) => write!(f, ":{name}"),
            AlgebraicExpression::Challenge(challenge) => {
                write!(
                    f,
                    "std::prelude::challenge({}, {})",
                    challenge.stage, challenge.id,
                )
            }
            AlgebraicExpression::Number(value) => write!(f, "{value}"),
            AlgebraicExpression::BinaryOperation(o) => {
                write!(f, "{o}")
            }
            AlgebraicExpression::UnaryOperation(o) => write!(f, "{o}"),
        }
    }
}

impl<T: Display> Display for AlgebraicBinaryOperation<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let force_parentheses = matches!(self.op, AlgebraicBinaryOperator::Pow);

        let op_precedence = self.op.precedence().unwrap();
        let use_left_parentheses = match self.left.precedence() {
            Some(left_precedence) => {
                force_parentheses
                    || left_precedence > op_precedence
                    || (left_precedence == op_precedence
                        && self.op.associativity() != AlgebraicBinaryOperatorAssociativity::Left)
            }
            None => false,
        };

        let use_right_parentheses = match self.right.precedence() {
            Some(right_precedence) => {
                force_parentheses
                    || right_precedence > op_precedence
                    || (right_precedence == op_precedence
                        && self.op.associativity() != AlgebraicBinaryOperatorAssociativity::Right)
            }
            None => false,
        };

        let left_string = if use_left_parentheses {
            format!("({})", self.left)
        } else {
            format!("{}", self.left)
        };
        let right_string = if use_right_parentheses {
            format!("({})", self.right)
        } else {
            format!("{}", self.right)
        };

        write!(f, "{left_string} {} {right_string}", self.op)
    }
}

impl<T: Display> Display for AlgebraicUnaryOperation<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let exp_string = match (self.op.precedence(), self.expr.precedence()) {
            (Some(precedence), Some(inner_precedence)) if precedence < inner_precedence => {
                format!("({})", self.expr)
            }
            _ => {
                format!("{}", self.expr)
            }
        };

        if self.op.is_prefix() {
            write!(f, "{}{exp_string}", self.op)
        } else {
            write!(f, "{exp_string}{}", self.op)
        }
    }
}

impl Display for AlgebraicUnaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        UnaryOperator::from(*self).fmt(f)
    }
}

impl Display for AlgebraicBinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        BinaryOperator::from(*self).fmt(f)
    }
}

impl Display for AlgebraicReference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.name, if self.next { "'" } else { "" },)
    }
}

impl Display for PolynomialReference {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.name)?;
        if let Some(type_args) = &self.type_args {
            if !type_args.is_empty() {
                write!(f, "::{}", format_type_args(type_args))?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::iter::once;

    use powdr_number::GoldilocksField;
    use powdr_pil_analyzer::analyze_string;
    use pretty_assertions::assert_eq;
    use test_log::test;

    use super::{AlgebraicBinaryOperator, AlgebraicExpression};

    type TestCase<'a> = (&'a str, &'a str);

    fn test_paren(to_declare: &[&str], (input, expected): &TestCase) {
        // Display on `Analysis` pads each line by 4 spaces
        let padding: String = " ".repeat(4);

        // Introduce witness columns for the referenced variables
        let declarations = to_declare
            .iter()
            .map(|to_declare| format!("col witness {to_declare};"));

        // Wrap the expression we're testing in a polynomial identity
        let wrap = |e| {
            declarations
                .clone()
                .chain(once(format!("{e} = 0;")))
                .collect::<Vec<_>>()
                .join(&format!("\n{padding}"))
        };

        let (input, expected) = &(&wrap(input), &wrap(expected));
        let analyzed = analyze_string::<GoldilocksField>(input).unwrap();
        let printed = analyzed.to_string();

        assert_eq!(expected.trim(), printed.trim());
    }

    #[test]
    fn exp_assoc() {
        // We test this separately from other expressions, since although `x ** y ** z` is allowed in
        // `AlgebraicExpression`, it is not produced by the analyzer due to type system restrictions

        let x = AlgebraicExpression::Reference(super::AlgebraicReference {
            name: "x".into(),
            poly_id: super::PolyID {
                id: 0,
                ptype: super::PolynomialType::Committed,
            },
            next: false,
        });
        let y = AlgebraicExpression::Reference(super::AlgebraicReference {
            name: "y".into(),
            poly_id: super::PolyID {
                id: 1,
                ptype: super::PolynomialType::Committed,
            },
            next: false,
        });
        let z = AlgebraicExpression::Reference(super::AlgebraicReference {
            name: "z".into(),
            poly_id: super::PolyID {
                id: 2,
                ptype: super::PolynomialType::Committed,
            },
            next: false,
        });

        // define `x ** (y ** z)`
        let x_yz: AlgebraicExpression<GoldilocksField> = AlgebraicExpression::new_binary(
            x.clone(),
            AlgebraicBinaryOperator::Pow,
            AlgebraicExpression::new_binary(y.clone(), AlgebraicBinaryOperator::Pow, z.clone()),
        );
        // In principle, no parentheses needed as `**` is right-associative. However, we keep parentheses to match behavior of the parsed AST.
        assert_eq!(x_yz.to_string(), "x ** (y ** z)");

        // define `(x ** y) ** z`
        let xy_z = AlgebraicExpression::new_binary(
            AlgebraicExpression::new_binary(x.clone(), AlgebraicBinaryOperator::Pow, y.clone()),
            AlgebraicBinaryOperator::Pow,
            z.clone(),
        );
        // parentheses needed because `**` is right-associative
        assert_eq!(xy_z.to_string(), "(x ** y) ** z");
    }

    #[test]
    fn binary_op() {
        let test_cases: Vec<TestCase> = vec![
            // Don't add extra
            ("x + y + z", "x + y + z"),
            ("x * y * z", "x * y * z"),
            ("x ** 2", "x ** 2"),
            ("x ** 2 * y", "x ** 2 * y"),
            ("x * y ** 2", "x * y ** 2"),
            // Remove unneeded
            ("(-x) + y * (z)", "-x + y * z"),
            ("(x * y) * z", "x * y * z"),
            ("(x - (y + z))", "x - (y + z)"),
            ("(x ** 2)", "x ** 2"),
            ("(x ** 2) * y", "x ** 2 * y"),
            ("x * (y ** 2)", "x * y ** 2"),
            // Observe associativity
            ("x * (y * z)", "x * (y * z)"),
            ("x + (y + z)", "x + (y + z)"),
            // Don't remove needed
            ("(x + y) * z", "(x + y) * z"),
            ("((x + y) * z)", "(x + y) * z"),
            ("-(x + y)", "-(x + y)"),
            ("(x + y) ** 2", "(x + y) ** 2"),
        ];

        for test_case in test_cases {
            test_paren(&["x", "y", "z"], &test_case);
        }
    }

    #[test]
    fn access() {
        let array_test_cases: Vec<TestCase> = vec![
            ("-x[2]", "-x[2]"),
            ("-(x[2])", "-x[2]"),
            ("1 + x[2]", "1 + x[2]"),
        ];

        for test_case in array_test_cases {
            test_paren(&["x[42]"], &test_case);
        }
    }
}

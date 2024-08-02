use std::str::FromStr;

use powdr_ast::parsed::{
    asm::SymbolPath, sugar::ArrayExpression, ArrayLiteral, BlockExpression, Expression,
    FunctionCall, FunctionKind, LambdaExpression, NamespacedPolynomialReference, Pattern,
    SourceReference,
};
use powdr_parser_util::SourceRef;

const ONCE: &str = "std::expand_fixed::once";
const REPEAT: &str = "std::expand_fixed::repeat";
const EXPAND: &str = "std::expand_fixed::expand_unwrapped";
const DEGREE: &str = "std::prover::degree";
const ARGUMENT_NAME: &str = "i";

pub fn desugar_array_literal_expression(array_expression: ArrayExpression) -> Expression {
    desugar_array_literal_expression_with_sourceref(SourceRef::unknown(), array_expression)
}

/// Turn an [ArrayExpression] into calls to stdlib
pub fn desugar_array_literal_expression_with_sourceref(
    source_ref: SourceRef,
    array_expression: ArrayExpression,
) -> Expression {
    // turn the expression into a series of calls to `once` and `repeat`
    let terms = array_expression
        .into_terms()
        .map(|term| match term {
            ArrayExpression::Value(a) => (ONCE, a),
            ArrayExpression::RepeatedValue(a) => (REPEAT, a),
            ArrayExpression::Concat(..) => unreachable!(),
        })
        .map(|(function_path, items)| {
            Expression::FunctionCall(
                source_ref.clone(),
                FunctionCall {
                    function: Box::new(Expression::Reference(
                        source_ref.clone(),
                        NamespacedPolynomialReference {
                            path: SymbolPath::from_str(function_path).unwrap(),
                            type_args: None,
                        },
                    )),
                    arguments: vec![Expression::ArrayLiteral(
                        source_ref.clone(),
                        ArrayLiteral { items },
                    )],
                },
            )
        })
        .collect();

    // prepare the arguments to `expand`
    let arguments = vec![
        // the terms
        Expression::ArrayLiteral(source_ref.clone(), ArrayLiteral { items: terms }),
        // the degree
        Expression::Reference(
            source_ref.clone(),
            NamespacedPolynomialReference {
                path: SymbolPath::from_str(DEGREE).unwrap(),
                type_args: None,
            },
        ),
    ];

    wrap_in_lambda(Expression::FunctionCall(
        source_ref.clone(),
        FunctionCall {
            function: Box::new(Expression::Reference(
                source_ref.clone(),
                NamespacedPolynomialReference {
                    path: SymbolPath::from_str(EXPAND).unwrap(),
                    type_args: None,
                },
            )),
            arguments,
        },
    ))
}

/// Given `f`, returns (|i| { f(i) })
/// This is required since `pol constant foo` only accepts lambdas which return a [BlockExpression] in the parser
fn wrap_in_lambda(e: Expression) -> Expression {
    let source_ref = e.source_reference().clone();

    Expression::LambdaExpression(
        source_ref.clone(),
        LambdaExpression {
            kind: FunctionKind::Pure,
            params: vec![Pattern::Enum(
                source_ref.clone(),
                SymbolPath::from_identifier(ARGUMENT_NAME.into()),
                None,
            )],
            body: Box::new(Expression::BlockExpression(
                source_ref.clone(),
                BlockExpression {
                    statements: vec![],
                    expr: Some(Box::new(Expression::FunctionCall(
                        source_ref.clone(),
                        FunctionCall {
                            function: Box::new(e),
                            arguments: vec![Expression::Reference(
                                source_ref.clone(),
                                NamespacedPolynomialReference::from_identifier(
                                    ARGUMENT_NAME.into(),
                                ),
                            )],
                        },
                    ))),
                },
            )),
            outer_var_references: Default::default(),
        },
    )
}

#[cfg(test)]
mod tests {
    use crate::{powdr::ArrayLiteralExpressionParser, ParserContext};

    use super::*;

    #[test]
    fn desugar() {
        let context = ParserContext::new(None, "");
        let array_expression: ArrayExpression = ArrayLiteralExpressionParser::new()
            .parse(&context, "[1, 2]* + [1] + [1, 2, 3]")
            .unwrap();
        assert_eq!(
            desugar_array_literal_expression(array_expression).to_string(),
            "(|i| { std::expand_fixed::expand_unwrapped([std::expand_fixed::repeat([1, 2]), std::expand_fixed::once([1]), std::expand_fixed::once([1, 2, 3])], std::prover::degree)(i) })"
        );
    }
}

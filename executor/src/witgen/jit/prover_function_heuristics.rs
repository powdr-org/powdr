#![allow(unused)]
use powdr_ast::{
    analyzed::{Expression, PolynomialReference, Reference},
    parsed::{FunctionCall, FunctionKind, LambdaExpression, Number},
};
use powdr_number::{BigUint, FieldElement};

use crate::witgen::machines::MachineParts;

/// Decodes simple prover functions of the kind
/// "query |i| std::prover::provide_if_unknown(X, i, || <value>)"
/// as `(X, <value>)` pairs.
pub fn decode_simple_prover_functions<T: FieldElement>(
    machine_parts: &MachineParts<T>,
) -> Vec<(String, T)> {
    machine_parts
        .prover_functions
        .iter()
        .filter_map(|f| decode_simple_prover_function(f))
        .collect()
}

fn decode_simple_prover_function<T: FieldElement>(function: &Expression) -> Option<(String, T)> {
    let body = try_as_lambda_expression(function, Some(FunctionKind::Query))?;
    let Expression::FunctionCall(
        _,
        FunctionCall {
            function,
            arguments,
        },
    ) = body
    else {
        return None;
    };
    if !is_reference_to(function, "std::prover::provide_if_unknown") {
        return None;
    }
    let [arg_column, arg_row, arg_value] = arguments.as_slice() else {
        return None;
    };
    let assigned_column = extract_reference(arg_column)?;
    if !matches!(arg_row, Expression::Reference(_, Reference::LocalVar(0, _))) {
        return None;
    }
    let value = try_as_number(try_as_lambda_expression(arg_value, None)?)?;
    Some((assigned_column.to_string(), T::from(value.clone())))
}

fn is_reference_to(e: &Expression, name: &str) -> bool {
    extract_reference(e).map(|r| r == name).unwrap_or(false)
}

fn extract_reference(e: &Expression) -> Option<&str> {
    match e {
        Expression::Reference(_, Reference::Poly(PolynomialReference { name, .. })) => Some(name),
        _ => None,
    }
}

fn try_as_number(e: &Expression) -> Option<&BigUint> {
    match e {
        Expression::Number(_, Number { value, .. }) => Some(value),
        _ => None,
    }
}

/// Returns the body of a lambda expression if it is a lambda expression with the given kind
/// (unless None is requested).
/// Note that this ignores the parameters.
fn try_as_lambda_expression(
    e: &Expression,
    requested_kind: Option<FunctionKind>,
) -> Option<&Expression> {
    match e {
        Expression::LambdaExpression(_, LambdaExpression { kind, body, .. })
            if requested_kind.map(|k| k == *kind).unwrap_or(true) =>
        {
            Some(body)
        }
        _ => None,
    }
}

#[cfg(test)]
mod test {
    use powdr_number::GoldilocksField;

    use crate::witgen::jit::test_util::read_pil;

    use super::*;

    #[test]
    fn decode_simple() {
        let input = "
    namespace std::prover;
        let provide_if_unknown: expr, int, (-> fe) -> () = |column, row, f| ();
    namespace main;
        let X;
        query |i| std::prover::provide_if_unknown(X, i, || 11);
        ";
        let (analyzed, _) = read_pil::<GoldilocksField>(input);
        assert_eq!(analyzed.prover_functions.len(), 1);
        let (name, value) =
            decode_simple_prover_function::<GoldilocksField>(&analyzed.prover_functions[0])
                .unwrap();
        assert_eq!(name, "main::X");
        assert_eq!(value, 11.into());
    }
}

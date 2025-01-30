use powdr_ast::{
    analyzed::{AlgebraicReference, Analyzed, Expression, PolyID, PolynomialReference, Reference},
    parsed::{
        ArrayLiteral, BlockExpression, FunctionCall, FunctionKind, LambdaExpression, Number,
        UnaryOperation, UnaryOperator,
    },
};
use powdr_number::{BigUint, FieldElement};

use crate::witgen::{machines::MachineParts, FixedData};

pub trait TryColumnByName: Copy {
    fn try_column_by_name(&self, name: &str) -> Option<PolyID>;
}

#[allow(unused)]
#[derive(Clone)]
pub struct ProverFunctionComputeFrom<'a> {
    pub index: usize,
    pub target_column: AlgebraicReference,
    pub input_columns: Vec<AlgebraicReference>,
    pub computation: &'a Expression,
}

#[allow(unused)]
#[derive(Clone)]
pub enum ProverFunction<'a, T> {
    /// query |i| std::prover::provide_if_unknown(Y, i, || <value>)
    ProvideIfUnknown(usize, AlgebraicReference, T),
    /// query |i| std::prover::compute_from(Y, i, [X, ...], f)
    ComputeFrom(ProverFunctionComputeFrom<'a>),
}

/// Tries to decode the prover functions.
/// Supported are the following forms:
/// - query |i| std::prover::provide_if_unknown(Y, i, || <value>)
/// - query |i| std::prover::compute_from(Y, i, [X, ...], f)
pub fn decode_prover_functions<'a, T: FieldElement>(
    machine_parts: &'a MachineParts<T>,
    try_column_by_name: impl TryColumnByName,
) -> Result<Vec<ProverFunction<'a, T>>, String> {
    machine_parts
        .prover_functions
        .iter()
        .enumerate()
        .map(|(index, f)| decode_prover_function(index, f, try_column_by_name))
        .collect()
}

fn decode_prover_function<T: FieldElement>(
    index: usize,
    function: &Expression,
    try_column_by_name: impl TryColumnByName,
) -> Result<ProverFunction<'_, T>, String> {
    if let Some((name, value)) = try_decode_provide_if_unknown(function, try_column_by_name) {
        Ok(ProverFunction::ProvideIfUnknown(index, name, value))
    } else if let Some(compute_from) = try_decode_compute_from(index, function, try_column_by_name)
    {
        Ok(ProverFunction::ComputeFrom(compute_from))
    } else {
        Err(format!("Unsupported prover function kind: {function}"))
    }
}

fn try_decode_provide_if_unknown<T: FieldElement>(
    function: &Expression,
    try_column_by_name: impl TryColumnByName,
) -> Option<(AlgebraicReference, T)> {
    let body = try_as_lambda_expression(function, Some(FunctionKind::Query))?;
    let [arg_column, arg_row, arg_value] =
        try_as_function_call_to(body, "std::prover::provide_if_unknown")?
    else {
        return None;
    };
    let assigned_column = try_extract_algebraic_reference(arg_column, try_column_by_name)?;
    if !is_local_var(arg_row, 0) {
        return None;
    }
    let value = try_as_number(try_as_lambda_expression(arg_value, None)?)?;
    Some((assigned_column, T::from(value.clone())))
}

/// Decodes functions of the form `query |i| std::prover::compute_from(Y, i, [X], f)`.
fn try_decode_compute_from(
    index: usize,
    function: &Expression,
    try_column_by_name: impl TryColumnByName,
) -> Option<ProverFunctionComputeFrom> {
    let body = try_as_lambda_expression(function, Some(FunctionKind::Query))?;
    let [target_column, row, input_columns, computation] =
        try_as_function_call_to(body, "std::prover::compute_from")?
    else {
        return None;
    };
    let target_column = try_extract_algebraic_reference(target_column, try_column_by_name)?;
    if target_column.next {
        return None;
    }
    if !is_local_var(row, 0) {
        return None;
    }
    let input_columns = try_as_literal_array(input_columns)?
        .iter()
        .map(|e| try_extract_algebraic_reference(e, try_column_by_name))
        .collect::<Option<Vec<_>>>()?;
    Some(ProverFunctionComputeFrom {
        index,
        target_column,
        input_columns,
        computation,
    })
}

fn is_reference_to(e: &Expression, name: &str) -> bool {
    try_extract_reference(e).map(|r| r == name).unwrap_or(false)
}

fn try_extract_reference(e: &Expression) -> Option<&str> {
    match unpack(e) {
        Expression::Reference(_, Reference::Poly(PolynomialReference { name, .. })) => Some(name),
        _ => None,
    }
}

fn try_extract_algebraic_reference(
    e: &Expression,
    try_column_by_name: impl TryColumnByName,
) -> Option<AlgebraicReference> {
    let (e, next) = match unpack(e) {
        Expression::UnaryOperation(
            _,
            UnaryOperation {
                op: UnaryOperator::Next,
                expr,
            },
        ) => (expr.as_ref(), true),
        _ => (e, false),
    };
    let name = try_extract_reference(e)?.to_string();
    let poly_id = try_column_by_name.try_column_by_name(&name)?;
    Some(AlgebraicReference {
        name,
        poly_id,
        next,
    })
}

fn is_local_var(e: &Expression, index: u64) -> bool {
    matches!(unpack(e), Expression::Reference(_, Reference::LocalVar(i, _)) if *i == index)
}

fn try_as_number(e: &Expression) -> Option<&BigUint> {
    match unpack(e) {
        Expression::Number(_, Number { value, .. }) => Some(value),
        _ => None,
    }
}

fn try_as_function_call(e: &Expression) -> Option<&FunctionCall<Expression>> {
    match unpack(e) {
        Expression::FunctionCall(_, f) => Some(f),
        _ => None,
    }
}

/// Tries to parse `e` as a function call to a function called `name` and returns
/// the arguments in that case.
fn try_as_function_call_to<'a>(e: &'a Expression, name: &str) -> Option<&'a [Expression]> {
    let FunctionCall {
        function,
        arguments,
    } = try_as_function_call(e)?;
    is_reference_to(function, name).then_some(arguments.as_slice())
}

/// Returns the body of a lambda expression if it is a lambda expression with the given kind
/// (unless None is requested).
/// Note that this ignores the parameters.
fn try_as_lambda_expression(
    e: &Expression,
    requested_kind: Option<FunctionKind>,
) -> Option<&Expression> {
    match unpack(e) {
        Expression::LambdaExpression(_, LambdaExpression { kind, body, .. })
            if requested_kind.map(|k| k == *kind).unwrap_or(true) =>
        {
            Some(unpack(body))
        }
        _ => None,
    }
}

fn try_as_literal_array(e: &Expression) -> Option<&[Expression]> {
    match unpack(e) {
        Expression::ArrayLiteral(_, ArrayLiteral { items }) => Some(items.as_slice()),
        _ => None,
    }
}

/// If `e` is a block with just a single expression, returns this inner expression,
/// otherwise returns `e` again.
fn unpack(e: &Expression) -> &Expression {
    match e {
        Expression::BlockExpression(
            _,
            BlockExpression {
                statements,
                expr: Some(expr),
            },
        ) if statements.is_empty() => expr,
        _ => e,
    }
}

impl<T: FieldElement> TryColumnByName for &FixedData<'_, T> {
    fn try_column_by_name(&self, name: &str) -> Option<PolyID> {
        FixedData::try_column_by_name(self, name)
    }
}

impl<T> TryColumnByName for &Analyzed<T> {
    fn try_column_by_name(&self, name: &str) -> Option<PolyID> {
        self.definitions.get(name).map(|d| PolyID::from(&d.0))
    }
}

#[cfg(test)]
mod test {
    use powdr_number::GoldilocksField;

    use crate::witgen::jit::test_util::read_pil;

    use super::*;

    #[test]
    fn provide_if_unknown() {
        let input = "
    namespace std::prover;
        let provide_if_unknown: expr, int, (-> fe) -> () = |column, row, f| ();
    namespace main;
        let X;
        query |i| std::prover::provide_if_unknown(X, i, || 11);
        ";
        let (analyzed, _) = read_pil::<GoldilocksField>(input);
        assert_eq!(analyzed.prover_functions.len(), 1);
        let (name, value) = try_decode_provide_if_unknown::<GoldilocksField>(
            &analyzed.prover_functions[0],
            &analyzed,
        )
        .unwrap();
        assert_eq!(name.name, "main::X");
        assert!(!name.next);
        assert_eq!(value, 11.into());
    }

    #[test]
    fn compute_from() {
        let input = "
    namespace std::prover;
        let compute_from: expr, int, expr[], (fe[] -> fe) -> () = query |dest_col, row, input_cols, f| ();
    namespace main;
        let X;
        let Y;
        let Z;
        query |i| std::prover::compute_from(Y, i, [X, Z'], |values| match values {
            [x, z] => x + z + 10,
            _ => 0,
        });
        ";
        let (analyzed, _) = read_pil::<GoldilocksField>(input);
        assert_eq!(analyzed.prover_functions.len(), 1);
        let ProverFunctionComputeFrom {
            index,
            target_column,
            input_columns,
            computation,
        } = try_decode_compute_from(0, &analyzed.prover_functions[0], &analyzed).unwrap();
        assert_eq!(index, 0);
        assert_eq!(target_column.name, "main::Y");
        assert!(!target_column.next);
        let [in_x, in_z] = input_columns.as_slice() else {
            panic!();
        };
        assert_eq!(in_x.name, "main::X");
        assert!(!in_x.next);
        assert_eq!(in_z.name, "main::Z");
        assert!(in_z.next);
        assert!(matches!(computation, Expression::LambdaExpression(_, _)));
    }
}

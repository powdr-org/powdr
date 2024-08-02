use std::{
    collections::HashMap,
    fmt::{self, Display},
    sync::Arc,
};

use itertools::Itertools;
use num_traits::Signed;

use powdr_ast::{
    analyzed::{
        AlgebraicBinaryOperation, AlgebraicBinaryOperator, AlgebraicExpression, AlgebraicReference,
        AlgebraicUnaryOperation, AlgebraicUnaryOperator, Challenge, Expression,
        FunctionValueDefinition, Reference, Symbol, SymbolKind, TypedExpression,
    },
    parsed::{
        display::quote,
        types::{Type, TypeScheme},
        ArrayLiteral, BinaryOperation, BinaryOperator, BlockExpression, FunctionCall, IfExpression,
        IndexAccess, LambdaExpression, LetStatementInsideBlock, MatchArm, MatchExpression, Number,
        Pattern, StatementInsideBlock, UnaryOperation, UnaryOperator,
    },
};
use powdr_number::{BigInt, BigUint, FieldElement, LargeInt};
use powdr_parser_util::SourceRef;

/// Evaluates an expression given a hash map of definitions.
pub fn evaluate_expression<'a, T: FieldElement>(
    expr: &'a Expression,
    definitions: &'a HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
) -> Result<Arc<Value<'a, T>>, EvalError> {
    evaluate(expr, &mut Definitions(definitions))
}

/// Evaluates an expression given a symbol lookup implementation
pub fn evaluate<'a, T: FieldElement>(
    expr: &'a Expression,
    symbols: &mut impl SymbolLookup<'a, T>,
) -> Result<Arc<Value<'a, T>>, EvalError> {
    evaluate_generic(expr, &Default::default(), symbols)
}

/// Evaluates a generic expression given a symbol lookup implementation
/// and values for the generic type parameters.
pub fn evaluate_generic<'a, 'b, T: FieldElement>(
    expr: &'a Expression,
    type_args: &'b HashMap<String, Type>,
    symbols: &mut impl SymbolLookup<'a, T>,
) -> Result<Arc<Value<'a, T>>, EvalError> {
    Evaluator::evaluate_expression(symbols, expr, type_args.clone())
}

/// Evaluates a function call.
pub fn evaluate_function_call<'a, T: FieldElement>(
    function: Arc<Value<'a, T>>,
    arguments: Vec<Arc<Value<'a, T>>>,
    symbols: &mut impl SymbolLookup<'a, T>,
) -> Result<Arc<Value<'a, T>>, EvalError> {
    Evaluator::evaluate_function_call(symbols, function, arguments, Default::default())
}

/// Turns an optional type scheme and a list of generic type arguments into a mapping
/// from type name to type.
pub fn type_arg_mapping(
    type_scheme: &Option<TypeScheme>,
    args: Option<Vec<Type>>,
) -> HashMap<String, Type> {
    let Some(type_scheme) = type_scheme else {
        return Default::default();
    };
    let Some(args) = args else {
        assert!(
            type_scheme.vars.is_empty(),
            "Tried to call a generic function without properly set type parameters."
        );
        return Default::default();
    };
    assert_eq!(
        type_scheme.vars.len(),
        args.len(),
        "Invalid number of generic arguments:\ngiven: {}\nexpected: {}.\nThis might happen if you call generic functions for array length type expressions.",
        args.iter().format(", "),
        type_scheme.vars.vars().format(", ")
    );
    type_scheme
        .vars
        .vars()
        .cloned()
        .zip(args.iter().cloned())
        .collect()
}

/// Evaluation errors.
/// TODO Most of these errors should be converted to panics as soon as we have a proper type checker.
#[derive(Debug)]
pub enum EvalError {
    /// Type error, for example non-number used as array index.
    TypeError(String),
    /// Fundamentally unsupported operation (regardless of type), e.g. access to public variables.
    Unsupported(String),
    /// Array index access out of bounds.
    OutOfBounds(String),
    /// Unable to match pattern. TODO As soon as we have "Option", patterns should be exhaustive
    /// This error occurs quite often and thus should not require allocation.
    NoMatch(),
    /// Reference to an undefined symbol
    SymbolNotFound(String),
    /// Data not (yet) available
    DataNotAvailable,
    /// Failed assertion, with reason.
    FailedAssertion(String),
}

impl Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::TypeError(msg) => write!(f, "Type error: {msg}"),
            EvalError::Unsupported(msg) => write!(f, "Operation unsupported: {msg}"),
            EvalError::OutOfBounds(msg) => write!(f, "Out of bounds access: {msg}"),
            EvalError::NoMatch() => write!(f, "Unable to match pattern."),
            EvalError::SymbolNotFound(msg) => write!(f, "Symbol not found: {msg}"),
            EvalError::DataNotAvailable => write!(f, "Data not (yet) available."),
            EvalError::FailedAssertion(msg) => write!(f, "Assertion failed: {msg}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Value<'a, T> {
    Bool(bool),
    Integer(BigInt),
    FieldElement(T),
    String(String),
    Tuple(Vec<Arc<Self>>),
    Array(Vec<Arc<Self>>),
    Closure(Closure<'a, T>),
    TypeConstructor(&'a str),
    Enum(&'a str, Option<Vec<Arc<Self>>>),
    BuiltinFunction(BuiltinFunction),
    Expression(AlgebraicExpression<T>),
}

impl<'a, T: FieldElement> From<T> for Value<'a, T> {
    fn from(value: T) -> Self {
        Value::FieldElement(value)
    }
}

impl<'a, T: FieldElement> From<AlgebraicExpression<T>> for Value<'a, T> {
    fn from(value: AlgebraicExpression<T>) -> Self {
        Value::Expression(value)
    }
}

impl<'a, T: FieldElement> Value<'a, T> {
    /// Tries to convert the value to a field element. For integers, this only works
    /// if the integer is non-negative and less than the modulus.
    pub fn try_to_field_element(&self) -> Result<T, EvalError> {
        match self {
            Value::FieldElement(x) => Ok(*x),
            Value::Integer(x) => {
                if let Ok(x) = BigUint::try_from(x.clone()) {
                    if x < T::modulus().to_arbitrary_integer() {
                        Ok(T::from(x))
                    } else {
                        Err(EvalError::TypeError(format!(
                            "Expected field element but got integer outside field range: {x}"
                        )))
                    }
                } else {
                    Err(EvalError::TypeError(format!(
                        "Expected field element but got negative integer: {x}"
                    )))
                }
            }
            v => Err(EvalError::TypeError(format!(
                "Expected field element but got {v}"
            ))),
        }
    }

    /// Tries to convert the result into a integer.
    /// Everything else than Value::Integer results in an error.
    pub fn try_to_integer(&self) -> Result<BigInt, EvalError> {
        match self {
            Value::Integer(x) => Ok(x.clone()),
            Value::FieldElement(x) => Ok(x.to_arbitrary_integer().into()),
            v => Err(EvalError::TypeError(format!(
                "Expected integer but got {v}: {}",
                v.type_formatted()
            ))),
        }
    }

    pub fn type_formatted(&self) -> String {
        match self {
            Value::Bool(_) => "bool".to_string(),
            Value::Integer(_) => "int".to_string(),
            Value::FieldElement(_) => "fe".to_string(),
            Value::String(_) => "string".to_string(),
            Value::Tuple(elements) => {
                format!(
                    "({})",
                    elements.iter().map(|e| e.type_formatted()).format(", ")
                )
            }
            Value::Array(elements) => {
                format!(
                    "[{}]",
                    elements.iter().map(|e| e.type_formatted()).format(", ")
                )
            }
            Value::Closure(c) => c.type_formatted(),
            Value::TypeConstructor(name) => format!("{name}_constructor"),
            Value::Enum(name, _) => name.to_string(),
            Value::BuiltinFunction(b) => format!("builtin_{b:?}"),
            Value::Expression(_) => "expr".to_string(),
        }
    }

    /// Tries to match this value against the given pattern.
    /// Returns local variable bindings on success.
    pub fn try_match_pattern<'b>(
        v: &Arc<Value<'b, T>>,
        pattern: &Pattern,
    ) -> Option<Vec<Arc<Value<'b, T>>>> {
        match pattern {
            Pattern::Ellipsis(_) => unreachable!("Should be handled higher up"),
            Pattern::CatchAll(_) => Some(vec![]),
            Pattern::Number(_, n) => match v.as_ref() {
                Value::Integer(x) if x == n => Some(vec![]),
                Value::FieldElement(x) if BigInt::from(x.to_arbitrary_integer()) == *n => {
                    Some(vec![])
                }
                _ => None,
            },
            Pattern::String(_, s) => match v.as_ref() {
                Value::String(x) if x == s => Some(vec![]),
                _ => None,
            },
            Pattern::Tuple(_, items) => match v.as_ref() {
                Value::Tuple(values) => Value::try_match_pattern_list(values, items),
                _ => unreachable!(),
            },
            Pattern::Array(_, items) => {
                let Value::Array(values) = v.as_ref() else {
                    panic!("Type error")
                };
                // Index of ".."
                let ellipsis_pos = items.iter().position(|i| matches!(i, Pattern::Ellipsis(_)));
                // Check if the value is too short.
                let length_matches = match ellipsis_pos {
                    Some(_) => values.len() >= items.len() - 1,
                    None => values.len() == items.len(),
                };
                if !length_matches {
                    return None;
                }
                // Split value into "left" and "right" part.
                let left_len = ellipsis_pos.unwrap_or(values.len());
                let right_len = ellipsis_pos.map(|p| items.len() - p - 1).unwrap_or(0);
                let left = values.iter().take(left_len);
                let right = values.iter().skip(values.len() - right_len);
                assert_eq!(
                    left.len() + right.len(),
                    items.len() - ellipsis_pos.map(|_| 1).unwrap_or_default()
                );
                left.chain(right)
                    .zip(items.iter().filter(|&i| !matches!(i, Pattern::Ellipsis(_))))
                    .try_fold(vec![], |mut vars, (e, p)| {
                        Value::try_match_pattern(e, p).map(|v| {
                            vars.extend(v);
                            vars
                        })
                    })
            }
            Pattern::Variable(_, _) => Some(vec![v.clone()]),
            Pattern::Enum(_, name, fields_pattern) => {
                let Value::Enum(n, data) = v.as_ref() else {
                    panic!()
                };
                if name.name() != n {
                    return None;
                }
                if let Some(fields) = fields_pattern {
                    Value::try_match_pattern_list(data.as_ref().unwrap(), fields)
                } else {
                    Some(vec![])
                }
            }
        }
    }

    fn try_match_pattern_list<'b>(
        values: &[Arc<Value<'b, T>>],
        patterns: &[Pattern],
    ) -> Option<Vec<Arc<Value<'b, T>>>> {
        assert_eq!(values.len(), patterns.len());
        patterns
            .iter()
            .zip(values.iter())
            .try_fold(vec![], |mut vars, (p, e)| {
                Value::try_match_pattern(e, p).map(|v| {
                    vars.extend(v);
                    vars
                })
            })
    }
}

const BUILTINS: [(&str, BuiltinFunction); 11] = [
    ("std::array::len", BuiltinFunction::ArrayLen),
    ("std::check::panic", BuiltinFunction::Panic),
    ("std::convert::expr", BuiltinFunction::ToExpr),
    ("std::convert::fe", BuiltinFunction::ToFe),
    ("std::convert::int", BuiltinFunction::ToInt),
    ("std::debug::print", BuiltinFunction::Print),
    ("std::field::modulus", BuiltinFunction::Modulus),
    ("std::prelude::challenge", BuiltinFunction::Challenge),
    ("std::prover::set_hint", BuiltinFunction::SetHint),
    ("std::prover::degree", BuiltinFunction::Degree),
    ("std::prover::eval", BuiltinFunction::Eval),
];

#[derive(Clone, Copy, Debug)]
pub enum BuiltinFunction {
    /// std::array::len: _[] -> int, returns the length of an array
    ArrayLen,
    /// std::field::modulus: -> int, returns the field modulus as int
    Modulus,
    /// std::check::panic: string -> !, fails evaluation and uses its parameter for error reporting.
    /// Does not return.
    Panic,
    /// std::debug::print: string -> [], prints its argument on stdout.
    /// Returns an empty array.
    Print,
    /// std::convert::expr: fe/int -> expr, converts fe to expr
    ToExpr,
    /// std::convert::int: fe/int -> int, converts fe to int
    ToInt,
    /// std::convert::fe: int/fe -> fe, converts int to fe
    ToFe,
    /// std::prover::challenge: int, int -> expr, constructs a challenge with a given stage and ID.
    Challenge,
    /// std::prover::set_hint: expr, (int -> std::prover::Query) -> (), adds a hint to a witness column.
    SetHint,
    /// std::prover::degree: -> int, returns the current column length / degree.
    Degree,
    /// std::prover::eval: expr -> fe, evaluates an expression on the current row
    Eval,
}

impl<'a, T: Display> Display for Value<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{b}"),
            Value::Integer(x) => write!(f, "{x}"),
            Value::FieldElement(x) => write!(f, "{x}"),
            Value::String(s) => write!(f, "{}", quote(s)),
            Value::Tuple(items) => write!(f, "({})", items.iter().format(", ")),
            Value::Array(elements) => write!(f, "[{}]", elements.iter().format(", ")),
            Value::Closure(closure) => write!(f, "{closure}"),
            Value::TypeConstructor(name) => write!(f, "{name}_constructor"),
            Value::Enum(name, data) => {
                write!(f, "{name}")?;
                if let Some(data) = data {
                    write!(f, "({})", data.iter().format(", "))?;
                }
                Ok(())
            }
            Value::BuiltinFunction(b) => write!(f, "{b:?}"),
            Value::Expression(e) => write!(f, "{e}"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Closure<'a, T> {
    pub lambda: &'a LambdaExpression<Expression>,
    pub environment: Vec<Arc<Value<'a, T>>>,
    pub type_args: Arc<HashMap<String, Type>>,
}

impl<'a, T: Display> Display for Closure<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.lambda)
    }
}

impl<'a, T> From<Closure<'a, T>> for Value<'a, T> {
    fn from(value: Closure<'a, T>) -> Self {
        Value::Closure(value)
    }
}

impl<'a, T> Closure<'a, T> {
    pub fn type_formatted(&self) -> String {
        // TODO should use proper types as soon as we have them
        "closure".to_string()
    }
}

pub struct Definitions<'a>(pub &'a HashMap<String, (Symbol, Option<FunctionValueDefinition>)>);

impl<'a> Definitions<'a> {
    /// Implementation of `lookup` that allows to provide a different implementation
    /// of SymbolLookup for the recursive call.
    pub fn lookup_with_symbols<T: FieldElement>(
        definitions: &'a HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
        name: &str,
        type_args: &Option<Vec<Type>>,
        symbols: &mut impl SymbolLookup<'a, T>,
    ) -> Result<Arc<Value<'a, T>>, EvalError> {
        let (symbol, value) = definitions
            .get(name)
            .ok_or_else(|| EvalError::SymbolNotFound(format!("Symbol {name} not found.")))?;

        Ok(if matches!(symbol.kind, SymbolKind::Poly(_)) {
            if symbol.is_array() {
                let items = symbol
                    .array_elements()
                    .map(|(name, poly_id)| {
                        Value::from(AlgebraicExpression::Reference(AlgebraicReference {
                            name,
                            poly_id,
                            next: false,
                        }))
                        .into()
                    })
                    .collect();
                Value::Array(items).into()
            } else {
                Value::from(AlgebraicExpression::Reference(AlgebraicReference {
                    name: name.to_string(),
                    poly_id: symbol.into(),
                    next: false,
                }))
                .into()
            }
        } else {
            match value {
                Some(FunctionValueDefinition::Expression(TypedExpression {
                    e: value,
                    type_scheme,
                })) => {
                    let type_args = type_arg_mapping(type_scheme, type_args.clone());
                    evaluate_generic(value, &type_args, symbols)?
                }
                Some(FunctionValueDefinition::TypeConstructor(_type_name, variant)) => {
                    if variant.fields.is_none() {
                        Value::Enum(&variant.name, None).into()
                    } else {
                        Value::TypeConstructor(&variant.name).into()
                    }
                }
                _ => Err(EvalError::Unsupported(
                    "Cannot evaluate arrays and queries.".to_string(),
                ))?,
            }
        })
    }
}

impl<'a, T: FieldElement> SymbolLookup<'a, T> for Definitions<'a> {
    fn lookup(
        &mut self,
        name: &str,
        type_args: Option<Vec<Type>>,
    ) -> Result<Arc<Value<'a, T>>, EvalError> {
        Self::lookup_with_symbols(self.0, name, &type_args, self)
    }

    fn lookup_public_reference(&self, name: &str) -> Result<Arc<Value<'a, T>>, EvalError> {
        Ok(Value::from(AlgebraicExpression::PublicReference(name.to_string())).into())
    }
}

impl<'a> From<&'a HashMap<String, (Symbol, Option<FunctionValueDefinition>)>> for Definitions<'a> {
    fn from(value: &'a HashMap<String, (Symbol, Option<FunctionValueDefinition>)>) -> Self {
        Definitions(value)
    }
}

pub trait SymbolLookup<'a, T: FieldElement> {
    fn lookup(
        &mut self,
        name: &'a str,
        type_args: Option<Vec<Type>>,
    ) -> Result<Arc<Value<'a, T>>, EvalError>;

    fn lookup_public_reference(&self, name: &str) -> Result<Arc<Value<'a, T>>, EvalError> {
        Err(EvalError::Unsupported(format!(
            "Cannot evaluate public reference: {name}"
        )))
    }

    fn eval_expr(&self, expr: &AlgebraicExpression<T>) -> Result<Arc<Value<'a, T>>, EvalError> {
        Ok(match expr {
            AlgebraicExpression::Reference(reference) => self.eval_reference(reference)?,
            AlgebraicExpression::PublicReference(_) => unimplemented!(),
            AlgebraicExpression::Challenge(challenge) => self.eval_challenge(challenge)?,
            AlgebraicExpression::Number(n) => Value::FieldElement(*n).into(),
            AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation { left, op, right }) => {
                let left = self.eval_expr(left)?;
                let right = self.eval_expr(right)?;
                match (left.as_ref(), right.as_ref()) {
                    (Value::FieldElement(left), Value::FieldElement(right)) => {
                        evaluate_binary_operation_field(*left, (*op).into(), *right)?
                    }
                    _ => panic!("Expected field elements"),
                }
            }
            AlgebraicExpression::UnaryOperation(AlgebraicUnaryOperation { op, expr: operand }) => {
                match op {
                    AlgebraicUnaryOperator::Minus => {
                        let operand = self.eval_expr(operand)?;
                        match operand.as_ref() {
                            Value::FieldElement(fe) => Value::FieldElement(-*fe).into(),
                            _ => panic!("Expected field element"),
                        }
                    }
                }
            }
        })
    }

    fn eval_challenge(&self, _challenge: &Challenge) -> Result<Arc<Value<'a, T>>, EvalError> {
        Err(EvalError::DataNotAvailable)
    }

    fn eval_reference(
        &self,
        _reference: &AlgebraicReference,
    ) -> Result<Arc<Value<'a, T>>, EvalError> {
        Err(EvalError::DataNotAvailable)
    }

    fn degree(&self) -> Result<Arc<Value<'a, T>>, EvalError> {
        Err(EvalError::Unsupported(
            "Cannot evaluate degree.".to_string(),
        ))
    }

    fn new_column(
        &mut self,
        name: &str,
        _value: Option<Arc<Value<'a, T>>>,
        _source: SourceRef,
    ) -> Result<Arc<Value<'a, T>>, EvalError> {
        Err(EvalError::Unsupported(format!(
            "Tried to create column outside of statement context: {name}"
        )))
    }

    fn set_hint(
        &mut self,
        _col: Arc<Value<'a, T>>,
        _expr: Arc<Value<'a, T>>,
    ) -> Result<(), EvalError> {
        Err(EvalError::Unsupported(
            "Tried to add hint to column outside of statement context.".to_string(),
        ))
    }

    fn add_constraints(
        &mut self,
        _constraints: Arc<Value<'a, T>>,
        _source: SourceRef,
    ) -> Result<(), EvalError> {
        Err(EvalError::Unsupported(
            "Tried to add constraints outside of statement context.".to_string(),
        ))
    }
}

/// Operations to be performed by the evaluator.
enum Operation<'a, T> {
    /// Expand a complex expression or evaluate a leaf expression.
    Expand(&'a Expression),
    /// Evaluate an expanded non-leaf expression once all its
    /// sub-expressions have been evaluated.
    Combine(&'a Expression),
    /// Truncate the local variables to a given length
    TruncateLocals(usize),
    /// Replace the environment (local variables and type args).
    SetEnvironment(Vec<Arc<Value<'a, T>>>, Arc<HashMap<String, Type>>),
    /// Evaluate a let statement, adding matched pattern variables to the local variables.
    LetStatement(&'a LetStatementInsideBlock<Expression>),
    /// Add a constraint to the constraint set.
    AddConstraint,
}

/// We use a non-recursive algorithm to evaluate potentially recursive expressions.
/// This allows arbitrarily deep recursion in PIL on a physical machine with limited stack.
/// SymbolLookup might still do regular recursive calls into the evaluator,
/// but this is very limited.
struct Evaluator<'a, 'b, T: FieldElement, S: SymbolLookup<'a, T>> {
    symbols: &'b mut S,
    local_vars: Vec<Arc<Value<'a, T>>>,
    type_args: Arc<HashMap<String, Type>>,
    op_stack: Vec<Operation<'a, T>>,
    value_stack: Vec<Arc<Value<'a, T>>>,
}

impl<'a, 'b, T: FieldElement, S: SymbolLookup<'a, T>> Evaluator<'a, 'b, T, S> {
    fn new(symbols: &'b mut S, type_args: HashMap<String, Type>) -> Self {
        Self {
            symbols,
            local_vars: vec![],
            type_args: type_args.into(),
            op_stack: vec![],
            value_stack: vec![],
        }
    }

    pub fn evaluate_expression(
        symbols: &'b mut S,
        expr: &'a Expression,
        type_args: HashMap<String, Type>,
    ) -> Result<Arc<Value<'a, T>>, EvalError> {
        let mut ev = Self::new(symbols, type_args);
        ev.expand(expr)?;
        ev.evaluate()
    }

    pub fn evaluate_function_call(
        symbols: &'b mut S,
        function: Arc<Value<'a, T>>,
        arguments: Vec<Arc<Value<'a, T>>>,
        type_args: HashMap<String, Type>,
    ) -> Result<Arc<Value<'a, T>>, EvalError> {
        let mut ev = Self::new(symbols, type_args);
        ev.combine_function_call(function, arguments)?;
        ev.evaluate()
    }

    /// The main evaluation loop. Repeatedly takes the topmost element from the
    /// operation stack and performs the operation until the operation stack is empty.
    fn evaluate(&mut self) -> Result<Arc<Value<'a, T>>, EvalError> {
        while let Some(op) = self.op_stack.pop() {
            match op {
                Operation::Expand(expr) => self.expand(expr)?,
                Operation::Combine(expr) => self.combine(expr)?,
                Operation::TruncateLocals(len) => self.local_vars.truncate(len),
                Operation::SetEnvironment(new_locals, new_type_args) => {
                    self.local_vars = new_locals;
                    self.type_args = new_type_args;
                }
                Operation::LetStatement(s) => {
                    let value = match (&s.ty, &s.value.as_ref()) {
                        (Some(Type::Col), value) | (None, value @ None) => {
                            let Pattern::Variable(_, name) = &s.pattern else {
                                unreachable!()
                            };
                            self.symbols.new_column(
                                name,
                                value.map(|_| self.value_stack.pop().unwrap()),
                                SourceRef::unknown(),
                            )?
                        }
                        (_, Some(_)) => self.value_stack.pop().unwrap(),
                        _ => unreachable!(),
                    };
                    self.local_vars.extend(
                        Value::try_match_pattern(&value, &s.pattern).unwrap_or_else(|| {
                            panic!("Irrefutable pattern did not match: {} = {value}", s.pattern)
                        }),
                    );
                }
                Operation::AddConstraint => {
                    let result = self.value_stack.pop().unwrap();
                    match result.as_ref() {
                        Value::Tuple(t) if t.is_empty() => {}
                        _ => self.symbols.add_constraints(result, SourceRef::unknown())?,
                    }
                }
            };
        }
        assert_eq!(self.value_stack.len(), 1);
        Ok(self.value_stack.pop().unwrap())
    }

    /// Evaluates a leaf expression or expands a complex expression.
    /// Modifies the operation and value stack.
    fn expand(&mut self, expr: &'a Expression) -> Result<(), EvalError> {
        match expr {
            Expression::Reference(_, reference) => {
                let v = self.evaluate_reference(reference)?;
                self.value_stack.push(v)
            }
            Expression::PublicReference(_, name) => self
                .value_stack
                .push(self.symbols.lookup_public_reference(name)?),
            Expression::Number(
                _,
                Number {
                    value: n,
                    type_: ty,
                },
            ) => self
                .value_stack
                .push(evaluate_literal(n.clone(), ty, &self.type_args)?),
            Expression::String(_, s) => self.value_stack.push(Value::String(s.clone()).into()),
            Expression::Tuple(_, items) => {
                self.op_stack.push(Operation::Combine(expr));
                if !items.is_empty() {
                    self.op_stack
                        .extend(items.iter().skip(1).rev().map(Operation::Expand));
                    self.expand(&items[0])?;
                }
            }
            Expression::ArrayLiteral(_, ArrayLiteral { items }) => {
                self.op_stack.push(Operation::Combine(expr));
                if !items.is_empty() {
                    self.op_stack
                        .extend(items.iter().skip(1).rev().map(Operation::Expand));
                    self.expand(&items[0])?;
                }
            }
            Expression::BinaryOperation(_, BinaryOperation { left, right, .. }) => {
                self.op_stack.push(Operation::Combine(expr));
                self.op_stack.push(Operation::Expand(right));
                self.expand(left)?;
            }
            Expression::UnaryOperation(_, UnaryOperation { expr: inner, .. }) => {
                self.op_stack.push(Operation::Combine(expr));
                self.expand(inner)?;
            }
            Expression::LambdaExpression(_, lambda) => {
                // TODO only copy the part of the environment that is actually referenced?
                self.value_stack.push(
                    Value::from(Closure {
                        lambda,
                        environment: self.local_vars.to_vec(),
                        type_args: self.type_args.clone(),
                    })
                    .into(),
                )
            }
            Expression::IndexAccess(_, IndexAccess { array, index }) => {
                self.op_stack.push(Operation::Combine(expr));
                self.op_stack.push(Operation::Expand(index));
                self.expand(array)?;
            }
            Expression::FunctionCall(
                _,
                FunctionCall {
                    function,
                    arguments,
                },
            ) => {
                self.op_stack.push(Operation::Combine(expr));
                self.op_stack
                    .extend(arguments.iter().rev().map(Operation::Expand));
                self.expand(function)?;
            }
            Expression::MatchExpression(
                _,
                MatchExpression {
                    scrutinee: condition,
                    ..
                },
            )
            | Expression::IfExpression(_, IfExpression { condition, .. }) => {
                // Only handle the scrutinee / condition for now, we do not want to evaluate all arms.
                self.op_stack.push(Operation::Combine(expr));
                self.expand(condition)?;
            }
            Expression::BlockExpression(_, BlockExpression { statements, expr }) => {
                self.op_stack
                    .push(Operation::TruncateLocals(self.local_vars.len()));
                match expr {
                    Some(expr) => self.op_stack.push(Operation::Expand(expr)),
                    None => self.value_stack.push(Value::Tuple(vec![]).into()),
                }
                for s in statements.iter().rev() {
                    match s {
                        StatementInsideBlock::LetStatement(s) => {
                            self.op_stack.push(Operation::LetStatement(s));
                            if let Some(v) = &s.value {
                                self.op_stack.push(Operation::Expand(v));
                            }
                        }
                        StatementInsideBlock::Expression(expr) => {
                            self.op_stack.push(Operation::AddConstraint);
                            self.op_stack.push(Operation::Expand(expr));
                        }
                    }
                }
            }
            Expression::FreeInput(_, _) => Err(EvalError::Unsupported(
                "Cannot evaluate free input.".to_string(),
            ))?,
        };
        Ok(())
    }

    fn evaluate_reference(
        &mut self,
        reference: &'a Reference,
    ) -> Result<Arc<Value<'a, T>>, EvalError> {
        Ok(match reference {
            Reference::LocalVar(i, _name) => self.local_vars[*i as usize].clone(),
            Reference::Poly(poly) => {
                if let Some((_, b)) = BUILTINS.iter().find(|(n, _)| (n == &poly.name)) {
                    Value::BuiltinFunction(*b).into()
                } else {
                    let type_args = poly.type_args.clone().map(|mut ta| {
                        for ty in &mut ta {
                            ty.substitute_type_vars(&self.type_args);
                        }
                        ta
                    });
                    self.symbols.lookup(&poly.name, type_args)?
                }
            }
        })
    }

    /// Evaluate a complex expression given the values for all sub-expressions.
    fn combine(&mut self, expr: &'a Expression) -> Result<(), EvalError> {
        let value = match expr {
            Expression::Tuple(_, items) => {
                let inner_values = self
                    .value_stack
                    .split_off(self.value_stack.len() - items.len());
                Value::Tuple(inner_values).into()
            }
            Expression::ArrayLiteral(_, ArrayLiteral { items }) => {
                let inner_values = self
                    .value_stack
                    .split_off(self.value_stack.len() - items.len());
                Value::Array(inner_values).into()
            }
            Expression::BinaryOperation(_, BinaryOperation { op, .. }) => {
                let right = self.value_stack.pop().unwrap();
                let left = self.value_stack.pop().unwrap();
                evaluate_binary_operation(&left, *op, &right)?
            }
            Expression::UnaryOperation(_, UnaryOperation { op, .. }) => {
                let inner = self.value_stack.pop().unwrap();
                match (op, inner.as_ref()) {
                    (UnaryOperator::Minus, Value::FieldElement(e)) => {
                        Value::FieldElement(-*e).into()
                    }
                    (UnaryOperator::LogicalNot, Value::Bool(b)) => Value::Bool(!b).into(),
                    (UnaryOperator::Minus, Value::Integer(n)) => Value::Integer(-n).into(),
                    (UnaryOperator::Next, Value::Expression(e)) => e
                        .clone()
                        .next()
                        .map(|next| Value::from(next).into())
                        // a reference already had its `next` flag on
                        .map_err(|reference| {
                            EvalError::TypeError(format!(
                                "Double application of \"'\" on: {}",
                                reference.name
                            ))
                        })?,
                    (op, Value::Expression(e)) => Value::from(AlgebraicExpression::new_unary(
                        (*op).try_into().unwrap(),
                        e.clone(),
                    ))
                    .into(),
                    (_, inner) => Err(EvalError::TypeError(format!(
                        "Operator {op} not supported on types: {inner}: {}",
                        inner.type_formatted()
                    )))?,
                }
            }
            Expression::IndexAccess(_, _) => {
                let index = self.value_stack.pop().unwrap();
                let array = self.value_stack.pop().unwrap();
                let Value::Array(elements) = array.as_ref() else {
                    panic!()
                };
                match index.as_ref() {
                    Value::Integer(index)
                        if index.is_negative()
                            || *index >= (elements.len() as u64).into() =>
                    {
                        Err(EvalError::OutOfBounds(format!(
                            "Index access out of bounds: Tried to access element {index} of array of size {} in: {expr}.",
                            elements.len()
                        )))?
                    }
                    Value::Integer(index) => {
                        elements[usize::try_from(index).unwrap()].clone()
                    }
                    index => Err(EvalError::TypeError(format!(
                            "Expected integer for array index access but got {index}: {}",
                            index.type_formatted()
                    )))?,
                }
            }
            Expression::FunctionCall(_, FunctionCall { arguments, .. }) => {
                let arguments = self
                    .value_stack
                    .split_off(self.value_stack.len() - arguments.len());
                let function = self.value_stack.pop().unwrap();
                return self.combine_function_call(function, arguments);
            }
            Expression::MatchExpression(_, MatchExpression { arms, .. }) => {
                let v = self.value_stack.pop().unwrap();
                let (vars, body) = arms
                    .iter()
                    .find_map(|MatchArm { pattern, value }| {
                        Value::try_match_pattern(&v, pattern).map(|vars| (vars, value))
                    })
                    .ok_or_else(EvalError::NoMatch)?;
                if !vars.is_empty() {
                    self.op_stack
                        .push(Operation::TruncateLocals(self.local_vars.len()));
                    self.local_vars.extend(vars);
                }
                return self.expand(body);
            }
            Expression::IfExpression(
                _,
                IfExpression {
                    body, else_body, ..
                },
            ) => {
                let v = self.value_stack.pop().unwrap();
                let condition = match v.as_ref() {
                    Value::Bool(b) => Ok(b),
                    x => Err(EvalError::TypeError(format!(
                        "Expected boolean value but got {x}"
                    ))),
                }?;
                let body = if *condition { body } else { else_body };
                return self.expand(body);
            }

            _ => unreachable!(),
        };
        self.value_stack.push(value);
        Ok(())
    }

    fn combine_function_call(
        &mut self,
        function: Arc<Value<'a, T>>,
        arguments: Vec<Arc<Value<'a, T>>>,
    ) -> Result<(), EvalError> {
        match function.as_ref() {
            Value::BuiltinFunction(b) => {
                self.value_stack
                    .push(evaluate_builtin_function(*b, arguments, self.symbols)?)
            }
            Value::TypeConstructor(name) => self
                .value_stack
                .push(Value::Enum(name, Some(arguments)).into()),
            Value::Closure(Closure {
                lambda,
                environment,
                type_args,
            }) => {
                assert_eq!(lambda.params.len(), arguments.len());
                let matched_arguments =
                    arguments
                        .iter()
                        .zip(&lambda.params)
                        .flat_map(|(arg, pattern)| {
                            Value::try_match_pattern(arg, pattern).unwrap_or_else(|| {
                                panic!("Irrefutable pattern did not match: {pattern} = {arg}")
                            })
                        });

                let local_vars = environment
                    .iter()
                    .cloned()
                    .chain(matched_arguments)
                    .collect::<Vec<_>>();

                self.op_stack.push(Operation::SetEnvironment(
                    std::mem::take(&mut self.local_vars),
                    std::mem::take(&mut self.type_args),
                ));
                self.local_vars = local_vars;
                self.type_args = type_args.clone();
                self.expand(&lambda.body)?;
            }
            e => panic!("Expected function but got {e}"),
        };
        Ok(())
    }
}

fn evaluate_literal<'a, T: FieldElement>(
    n: BigUint,
    ty: &Option<Type<u64>>,
    type_args: &HashMap<String, Type>,
) -> Result<Arc<Value<'a, T>>, EvalError> {
    let ty = if let Some(Type::TypeVar(tv)) = ty {
        match &type_args[tv] {
            Type::Fe => Type::Fe,
            Type::Int => Type::Int,
            Type::Expr => Type::Expr,
            t => Err(EvalError::TypeError(format!(
                "Invalid type name for number literal: {t}"
            )))?,
        }
    } else {
        ty.as_ref().cloned().unwrap_or_else(|| Type::Int)
    };
    if ty == Type::Int {
        return Ok(Value::Integer(n.into()).into());
    }
    let fe = T::checked_from(n.clone()).ok_or_else(|| {
        EvalError::TypeError(format!(
            "Number literal {n} is too large for field element."
        ))
    })?;
    Ok((if ty == Type::Fe {
        Value::FieldElement(fe)
    } else if ty == Type::Expr {
        AlgebraicExpression::Number(fe).into()
    } else {
        unreachable!();
    })
    .into())
}

fn evaluate_binary_operation<'a, T: FieldElement>(
    left: &Value<'a, T>,
    op: BinaryOperator,
    right: &Value<'a, T>,
) -> Result<Arc<Value<'a, T>>, EvalError> {
    Ok(match (left, op, right) {
        (Value::Array(l), BinaryOperator::Add, Value::Array(r)) => {
            Value::Array(l.iter().chain(r).cloned().collect::<Vec<_>>()).into()
        }
        (Value::String(l), BinaryOperator::Add, Value::String(r)) => {
            Value::String(l.clone() + r).into()
        }
        (Value::String(l), BinaryOperator::Equal, Value::String(r)) => Value::Bool(l == r).into(),
        (Value::String(l), BinaryOperator::NotEqual, Value::String(r)) => {
            Value::Bool(l != r).into()
        }
        (Value::Bool(l), BinaryOperator::LogicalOr, Value::Bool(r)) => Value::Bool(*l || *r).into(),
        (Value::Bool(l), BinaryOperator::LogicalAnd, Value::Bool(r)) => {
            Value::Bool(*l && *r).into()
        }
        (Value::Integer(l), _, Value::Integer(r)) => evaluate_binary_operation_integer(l, op, r)?,
        (Value::FieldElement(l), _, Value::FieldElement(r)) => {
            evaluate_binary_operation_field(*l, op, *r)?
        }
        (Value::FieldElement(l), BinaryOperator::Pow, Value::Integer(r)) => {
            let exp: u64 = r
                .clone()
                .try_into()
                .map_err(|_| EvalError::TypeError(format!("Exponent in {l}**{r} is too large.")))?;
            Value::FieldElement(l.pow(exp.into())).into()
        }
        (Value::Expression(l), BinaryOperator::Pow, Value::Integer(r)) => {
            let exp: u64 = r
                .clone()
                .try_into()
                .map_err(|_| EvalError::TypeError(format!("Exponent in {l}**{r} is too large.")))?;
            match l {
                AlgebraicExpression::Number(l) => {
                    Value::Expression(AlgebraicExpression::Number(l.pow(exp.into()))).into()
                }
                l => {
                    assert!(
                        BigUint::from(exp) < T::modulus().to_arbitrary_integer(),
                        "Exponent too large: {exp}"
                    );
                    Value::from(AlgebraicExpression::new_binary(
                        l.clone(),
                        AlgebraicBinaryOperator::Pow,
                        T::from(exp).into(),
                    ))
                    .into()
                }
            }
        }
        (l @ Value::Expression(_), BinaryOperator::Identity, r @ Value::Expression(_)) => {
            Value::Enum("Identity", Some(vec![l.clone().into(), r.clone().into()])).into()
        }
        (Value::Expression(l), op, Value::Expression(r)) => match (l, r) {
            (AlgebraicExpression::Number(l), AlgebraicExpression::Number(r)) => {
                let res = evaluate_binary_operation_field::<'a, T>(*l, op, *r)?;
                let Value::FieldElement(result) = res.as_ref() else {
                    panic!()
                };
                Value::from(AlgebraicExpression::Number(*result)).into()
            }
            (l, r) => Value::from(AlgebraicExpression::new_binary(
                l.clone(),
                op.try_into().unwrap(),
                r.clone(),
            ))
            .into(),
        },
        (l, op, r) => Err(EvalError::TypeError(format!(
            "Operator {op} not supported on types: {l}: {}, {r}: {}",
            l.type_formatted(),
            r.type_formatted()
        )))?,
    })
}

#[allow(clippy::print_stdout)]
fn evaluate_builtin_function<'a, T: FieldElement>(
    b: BuiltinFunction,
    mut arguments: Vec<Arc<Value<'a, T>>>,
    symbols: &mut impl SymbolLookup<'a, T>,
) -> Result<Arc<Value<'a, T>>, EvalError> {
    let params = match b {
        BuiltinFunction::ArrayLen => 1,
        BuiltinFunction::Modulus => 0,
        BuiltinFunction::Panic => 1,
        BuiltinFunction::Print => 1,
        BuiltinFunction::ToExpr => 1,
        BuiltinFunction::ToFe => 1,
        BuiltinFunction::ToInt => 1,
        BuiltinFunction::Challenge => 2,
        BuiltinFunction::SetHint => 2,
        BuiltinFunction::Degree => 0,
        BuiltinFunction::Eval => 1,
    };

    if arguments.len() != params {
        Err(EvalError::TypeError(format!(
                "Invalid function call: Supplied {} arguments to function that takes {params} parameters.",
                arguments.len(),
            )))?
    }
    Ok(match b {
        BuiltinFunction::ArrayLen => match arguments.pop().unwrap().as_ref() {
            Value::Array(arr) => Value::Integer((arr.len() as u64).into()).into(),
            v => panic!(
                "Expected array for std::array::len, but got {v}: {}",
                v.type_formatted()
            ),
        },
        BuiltinFunction::Panic => {
            let msg = match arguments.pop().unwrap().as_ref() {
                Value::String(msg) => msg.clone(),
                v => panic!(
                    "Expected string for std::check::panic, but got {v}: {}",
                    v.type_formatted()
                ),
            };
            Err(EvalError::FailedAssertion(msg))?
        }
        BuiltinFunction::Print => {
            let msg = arguments.pop().unwrap();
            if let Value::String(s) = msg.as_ref() {
                print!("{s}");
            } else {
                print!("{msg}");
            }
            Value::Tuple(vec![]).into()
        }
        BuiltinFunction::ToExpr => {
            let arg = arguments.pop().unwrap();
            Value::from(AlgebraicExpression::Number(arg.try_to_field_element()?)).into()
        }
        BuiltinFunction::ToInt => {
            let arg = arguments.pop().unwrap();
            Value::Integer(arg.try_to_integer()?).into()
        }
        BuiltinFunction::ToFe => {
            let arg = arguments.pop().unwrap();
            Value::FieldElement(arg.try_to_field_element()?).into()
        }
        BuiltinFunction::Modulus => {
            Value::Integer(T::modulus().to_arbitrary_integer().into()).into()
        }
        BuiltinFunction::Challenge => {
            let [stage, index] = &arguments[..] else {
                panic!()
            };
            let Value::Integer(stage) = (**stage).clone() else {
                panic!()
            };
            let Value::Integer(id) = (**index).clone() else {
                panic!()
            };
            Value::Expression(AlgebraicExpression::Challenge(Challenge {
                id: u64::try_from(id).unwrap(),
                stage: u32::try_from(stage).unwrap(),
            }))
            .into()
        }
        BuiltinFunction::SetHint => {
            let expr = arguments.pop().unwrap();
            let col = arguments.pop().unwrap();
            symbols.set_hint(col, expr)?;
            Value::Tuple(vec![]).into()
        }
        BuiltinFunction::Degree => symbols.degree()?,
        BuiltinFunction::Eval => {
            let arg = arguments.pop().unwrap();
            match arg.as_ref() {
                Value::Expression(e) => symbols.eval_expr(e)?,
                v => panic!(
                    "Expected expression for std::prover::eval, but got {v}: {}",
                    v.type_formatted()
                ),
            }
        }
    })
}

pub fn evaluate_binary_operation_field<'a, T: FieldElement>(
    left: T,
    op: BinaryOperator,
    right: T,
) -> Result<Arc<Value<'a, T>>, EvalError> {
    Ok(match op {
        BinaryOperator::Add => Value::FieldElement(left + right),
        BinaryOperator::Sub => Value::FieldElement(left - right),
        BinaryOperator::Mul => Value::FieldElement(left * right),
        BinaryOperator::Equal => Value::Bool(left == right),
        BinaryOperator::NotEqual => Value::Bool(left != right),
        _ => Err(EvalError::TypeError(format!(
            "Invalid operator {op} on field elements: {left} {op} {right}"
        )))?,
    }
    .into())
}

pub fn evaluate_binary_operation_integer<'a, T>(
    left: &BigInt,
    op: BinaryOperator,
    right: &BigInt,
) -> Result<Arc<Value<'a, T>>, EvalError> {
    Ok(match op {
        BinaryOperator::Add => Value::Integer(left + right),
        BinaryOperator::Sub => Value::Integer(left - right),
        BinaryOperator::Mul => Value::Integer(left * right),
        BinaryOperator::Div => Value::Integer(left / right),
        BinaryOperator::Pow => Value::Integer(left.pow(usize::try_from(right).unwrap())),
        BinaryOperator::Mod => Value::Integer(left % right),
        BinaryOperator::BinaryAnd => Value::Integer(left & right),
        BinaryOperator::BinaryXor => Value::Integer(left ^ right),
        BinaryOperator::BinaryOr => Value::Integer(left | right),
        BinaryOperator::ShiftLeft => Value::Integer(left << usize::try_from(right).unwrap()),
        BinaryOperator::ShiftRight => Value::Integer(left >> usize::try_from(right).unwrap()),
        BinaryOperator::Less => Value::Bool(left < right),
        BinaryOperator::LessEqual => Value::Bool(left <= right),
        BinaryOperator::Equal => Value::Bool(left == right),
        BinaryOperator::NotEqual => Value::Bool(left != right),
        BinaryOperator::GreaterEqual => Value::Bool(left >= right),
        BinaryOperator::Greater => Value::Bool(left > right),
        _ => Err(EvalError::TypeError(format!(
            "Invalid operator {op} on integers: {left} {op} {right}"
        )))?,
    }
    .into())
}

#[cfg(test)]
mod test {
    use crate::evaluator;
    use powdr_number::GoldilocksField;
    use pretty_assertions::assert_eq;

    use crate::analyze_string;

    use super::*;

    fn parse_and_evaluate_symbol(input: &str, symbol: &str) -> String {
        let analyzed = analyze_string::<GoldilocksField>(input);
        let Some(FunctionValueDefinition::Expression(TypedExpression {
            e: symbol,
            type_scheme: _,
        })) = &analyzed.definitions[symbol].1
        else {
            panic!()
        };
        evaluate::<GoldilocksField>(symbol, &mut Definitions(&analyzed.definitions))
            .unwrap()
            .to_string()
    }

    pub fn evaluate_function<T: FieldElement>(input: &str, function: &str) -> T {
        let analyzed = analyze_string::<GoldilocksField>(input);
        let mut symbols = evaluator::Definitions(&analyzed.definitions);
        let function = symbols.lookup(function, None).unwrap();
        let result = evaluator::evaluate_function_call(function, vec![], &mut symbols)
            .unwrap()
            .as_ref()
            .clone();
        match result {
            Value::FieldElement(fe) => fe,
            _ => panic!("Expected field element but got {result}"),
        }
    }

    #[test]
    fn trivial() {
        let src = r#"namespace Main(16);
            let x: int = 1 + 20;
        "#;
        let result = parse_and_evaluate_symbol(src, "Main.x");
        assert_eq!(result, r#"21"#);
    }

    #[test]
    fn recursion() {
        let src = r#"namespace Main(16);
            let x: int -> int = |i| match i { 0 => 0, _ => x(i - 1) + 1 };
            let y = x(4);
        "#;
        let result = parse_and_evaluate_symbol(src, "Main.y");
        assert_eq!(result, r#"4"#);
    }

    #[test]
    fn arrays_and_strings() {
        let src = r#"namespace Main(16);
            let words = ["the", "quick", "brown", "fox"];
            let translate = |w| match w {
                "the" => "franz",
                "quick" => "jagt",
                "brown" => "mit",
                "fox" => "dem",
                _ => "?",
            };
            let map_array = |arr, f| [f(arr[0]), f(arr[1]), f(arr[2]), f(arr[3])];
            let translated = map_array(words, translate);
        "#;
        let result = parse_and_evaluate_symbol(src, "Main.translated");
        assert_eq!(result, r#"["franz", "jagt", "mit", "dem"]"#);
    }

    #[test]
    fn fibonacci() {
        let src = r#"namespace Main(16);
            let fib: int -> int = |i| match i {
                0 => 0,
                1 => 1,
                _ => fib(i - 1) + fib(i - 2),
            };
            let result = fib(20);
        "#;
        assert_eq!(
            parse_and_evaluate_symbol(src, "Main.result"),
            "6765".to_string()
        );
    }

    #[test]
    fn capturing() {
        let src = r#"namespace Main(16);
            let f: int, (int -> int) -> (int -> int) = |n, g| match n { 99 => |i| n, 1 => g };
            let result = f(1, f(99, |x| x + 3000))(0);
        "#;
        // If the lambda function returned by the expression f(99, ...) does not
        // properly capture the value of n in a closure, then f(1, ...) would return 1.
        assert_eq!(
            parse_and_evaluate_symbol(src, "Main.result"),
            "99".to_string()
        );
    }

    #[test]
    fn array_len() {
        let src = r#"
            let N: int = 2;
            namespace std::array(N);
            let len = 123;
            namespace F(N);
            let x = std::array::len([1, N, 3]);
            let empty: int[] = [];
            let y = std::array::len(empty);
        "#;
        assert_eq!(parse_and_evaluate_symbol(src, "F.x"), "3".to_string());
        assert_eq!(parse_and_evaluate_symbol(src, "F.y"), "0".to_string());
    }

    #[test]
    #[should_panic = r#"FailedAssertion("this text")"#]
    fn panic_complex() {
        let src = r#"
            let N: int = 2;
            namespace std::check(N);
            let panic = 123;
            namespace F(N);
            let concat = |a, b| a + b;
            let arg: int = 1;
            let x: int[] = (|i| if i == 1 { std::check::panic(concat("this ", "text")) } else { [9] })(arg);
        "#;
        parse_and_evaluate_symbol(src, "F.x");
    }

    #[test]
    #[should_panic = r#"FailedAssertion("text")"#]
    fn panic_string() {
        let src = r#"
            let N: int = 2;
            namespace std::check(N);
            let panic = 123;
            namespace F(N);
            let x: int = std::check::panic("text");
        "#;
        parse_and_evaluate_symbol(src, "F.x");
    }

    #[test]
    fn hex_number_outside_field() {
        // This tests that the parser does not lose precision when parsing large integers.
        let src = r#"
            let N: int = 0x9999999999999999999999999999999;
        "#;
        parse_and_evaluate_symbol(src, "N");
    }

    #[test]
    fn decimal_number_outside_field() {
        // This tests that the parser does not lose precision when parsing large integers.
        let src = r#"
            let N: int = 9999999999999999999999999999999;
        "#;
        parse_and_evaluate_symbol(src, "N");
    }

    #[test]
    #[should_panic = "Number literal 9999999999999999999999999999999 is too large for field element."]
    fn decimal_number_outside_field_for_fe() {
        let src = r#"
            let N: fe = 9999999999999999999999999999999;
        "#;
        parse_and_evaluate_symbol(src, "N");
    }

    #[test]
    fn zero_power_zero() {
        let src = r#"
        let zpz_int: int = 0**0;
        let zpz_fe: fe = 0**0;
        "#;
        assert_eq!(parse_and_evaluate_symbol(src, "zpz_int"), "1".to_string());
        assert_eq!(parse_and_evaluate_symbol(src, "zpz_fe"), "1".to_string());
    }

    #[test]
    fn debug_print() {
        let src = r#"
            namespace std::debug(8);
            let print = 2;
            let N = std::debug::print("test output\n");
        "#;
        parse_and_evaluate_symbol(src, "std::debug::N");
    }

    #[test]
    fn debug_print_complex() {
        let src = r#"
            namespace std::debug(8);
            let print = 2;
            let t: fe = 9;
            let x: int = 2;
            let N = {
                let _ = std::debug::print((t, [x, 3], "test output\n"));
                std::debug::print("\n")
            };
        "#;
        parse_and_evaluate_symbol(src, "std::debug::N");
    }

    #[test]
    fn local_vars() {
        let src = r#"
            let f: int -> int = |i| {
                let x = i + 1;
                let y = x - 1;
                let z = y - i;
                z
            };
            let t = f(8);
        "#;
        assert_eq!(parse_and_evaluate_symbol(src, "t"), "0".to_string());
    }

    #[test]
    fn match_pattern() {
        let src = r#"
            let f: int[] -> int = |arr| match arr {
                [] => 0,
                [x] => x,
                [_, x] => x + 9,
                [_, x, y] => x + y,
                _ => 99,
            };
            let t = [
                f([]), f([1]), f([1, 2]), f([1, 2, 3]), f([1, 2, 3, 4])
            ];
        "#;
        assert_eq!(
            parse_and_evaluate_symbol(src, "t"),
            "[0, 1, 11, 5, 99]".to_string()
        );
    }

    #[test]
    fn match_pattern_complex() {
        let src = r#"
            let f: ((int, int), int[]) -> int = |q| match q {
                ((1, _), [x, 4]) => 1 + x,
                ((1, 2), [y]) => 2 + y,
                ((_, 2), [y, z]) => 3 + y + z,
                ((x, 3), _) => x,
                ((x, -1), _) => x,
                (t, [_, r]) => r
            };
            let res = [
                f(((1, 9), [20, 4])),
                f(((1, 2), [3])),
                f(((9, 2), [300, 4])),
                f(((9, 3), [900, 8])),
                f(((90, 3), [900, 8, 7])),
                f(((99, -1), [900, 8, 7])),
                f(((1, 1), [-3, -1]))
            ];
        "#;
        assert_eq!(
            parse_and_evaluate_symbol(src, "res"),
            "[21, 5, 307, 9, 90, 99, -1]".to_string()
        );
    }

    #[test]
    fn match_skip_array() {
        let src = r#"
            let f: int[] -> int = |arr| match arr {
                [x, .., y] => x + y,
                [] => 19,
                _ => 99,
            };
            let t = [f([]), f([1]), f([1, 2]), f([1, 2, 3]), f([1, 2, 3, 4])];
        "#;
        assert_eq!(
            parse_and_evaluate_symbol(src, "t"),
            "[19, 99, 3, 4, 5]".to_string()
        );
    }

    #[test]
    fn match_skip_array_2() {
        let src = r#"
            let f: int[] -> int = |arr| match arr {
                [.., y] => y,
                _ => 99,
            };
            let t = [f([]), f([1]), f([1, 2]), f([1, 2, 3]), f([1, 2, 3, 4])];
        "#;
        assert_eq!(
            parse_and_evaluate_symbol(src, "t"),
            "[99, 1, 2, 3, 4]".to_string()
        );
    }

    #[test]
    fn match_skip_array_3() {
        let src = r#"
            let f: int[] -> int = |arr| match arr {
                [.., x, y] => x,
                [..] => 99,
            };
            let t = [f([]), f([1]), f([1, 2]), f([1, 2, 3]), f([1, 2, 3, 4])];
        "#;
        assert_eq!(
            parse_and_evaluate_symbol(src, "t"),
            "[99, 99, 1, 2, 3]".to_string()
        );
    }

    #[test]
    fn match_skip_array_4() {
        let src = r#"
            let f: int[] -> int = |arr| match arr {
                [x, y, ..] => y,
                [..] => 99,
            };
            let t = [f([]), f([1]), f([1, 2]), f([1, 2, 3]), f([1, 2, 3, 4])];
        "#;
        assert_eq!(
            parse_and_evaluate_symbol(src, "t"),
            "[99, 99, 2, 2, 2]".to_string()
        );
    }

    #[test]
    fn unpack_fun() {
        let src = r#"
            let t: (int, fe, int), int -> int[] = |(x, _, y), z| [x, y, z];
            let x: int[] = t((1, 2, 3), 4);
        "#;
        assert_eq!(parse_and_evaluate_symbol(src, "x"), "[1, 3, 4]".to_string());
    }

    #[test]
    fn unpack_let() {
        let src = r#"
            let x: int[] = {
                let (a, (_, b), (c, _, _, d, _)) = (1, ((), 3), (4, (), (), 7, ()));
                [a, b, c, d]
            };
        "#;
        assert_eq!(
            parse_and_evaluate_symbol(src, "x"),
            "[1, 3, 4, 7]".to_string()
        );
    }

    #[test]
    pub fn match_enum() {
        let src = r#"
            enum X {
                A,
                B(),
                C(int, int),
                D(int, X)
            }
            let f = |x| match x {
                X::A => 1,
                X::B() => 2,
                X::C(a, b) => a + b,
                X::D(0, X::A) => 10001,
                X::D(c, y) => c + f(y),
            };
            let t = [f(X::A), f(X::B()), f(X::C(3, 4)), f(X::D(0, X::A)), f(X::D(0, X::B())), f(X::D(100, X::C(4, 5)))];
        "#;
        assert_eq!(
            parse_and_evaluate_symbol(src, "t"),
            "[1, 2, 7, 10001, 2, 109]".to_string()
        );
    }

    #[test]
    pub fn gigantic_stack() {
        let src = r#"
            let arr_new: int, (int -> int) -> int[] = |n, f| if n == 0 { [] } else { arr_new(n - 1, f) + [f(n - 1)] };
            let arr_rev: int[], int, int -> int[] = |a, i, n| if i >= n { [] } else { arr_rev(a, i + 1, n) + [a[i]] };
            let l = 10000;
            let t = arr_new(l, |i| i);
            let r = arr_rev(t, 0, l);
            let x = r[7];
        "#;
        assert_eq!(parse_and_evaluate_symbol(src, "x"), "9992".to_string());
    }

    #[test]
    pub fn string_eq() {
        let src = r#"
            let yes = "abc" != "def";
            let no = "abc" == "def";
            let yes2 = "abc" == "abc";
            let no2 = "abc" != "abc";
            let yes3 = "ab" != "abc";
            let no3 = "ab" == "abc";
        "#;
        assert_eq!(parse_and_evaluate_symbol(src, "yes"), "true".to_string());
        assert_eq!(parse_and_evaluate_symbol(src, "yes2"), "true".to_string());
        assert_eq!(parse_and_evaluate_symbol(src, "yes3"), "true".to_string());
        assert_eq!(parse_and_evaluate_symbol(src, "no"), "false".to_string());
        assert_eq!(parse_and_evaluate_symbol(src, "no2"), "false".to_string());
        assert_eq!(parse_and_evaluate_symbol(src, "no3"), "false".to_string());
    }

    #[test]
    pub fn eval_complex_expression() {
        let src = r#"
            namespace std::prover;
                let eval: expr -> fe = [];
            namespace main;
                // Put into query function, so we're allowed to use eval()
                let test = query || std::prover::eval(2 * (1 + 1 + 1) + 1);
        "#;
        assert_eq!(
            evaluate_function::<GoldilocksField>(src, "main.test"),
            7u64.into()
        );
    }

    #[test]
    fn no_stmts_in_block() {
        let input = "
    let f: int -> () = |i| ();
    let g: int -> () = |i| {
        f(1)
    };
    
    let h: () = g(1);
    ";

        assert_eq!(parse_and_evaluate_symbol(input, "h"), "()".to_string());
    }

    #[test]
    fn called_with_empty_block() {
        let input = "
    let<T1, T2: FromLiteral> f: T1 -> T2 = |_| 7;
    let g: int = f({ });
    ";

        assert_eq!(parse_and_evaluate_symbol(input, "g"), "7".to_string());
    }
}

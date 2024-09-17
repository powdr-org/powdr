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
        FunctionValueDefinition, Reference, Symbol, SymbolKind, TypeConstructor, TypedExpression,
    },
    parsed::{
        display::quote,
        types::{ArrayType, Type, TypeScheme},
        ArrayLiteral, BinaryOperation, BinaryOperator, BlockExpression, FieldAccess, FunctionCall,
        IfExpression, IndexAccess, LambdaExpression, LetStatementInsideBlock, MatchArm,
        MatchExpression, NamedExpression, Number, Pattern, StatementInsideBlock, StructExpression,
        UnaryOperation, UnaryOperator,
    },
};
use powdr_number::{BigInt, BigUint, FieldElement, LargeInt};
use powdr_parser_util::SourceRef;

/// Evaluates an expression given a hash map of definitions.
pub fn evaluate_expression<'a, T: FieldElement>(
    expr: &'a Expression,
    definitions: &'a HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
    solved_impls: &'a HashMap<String, HashMap<Vec<Type>, Arc<Expression>>>,
) -> Result<Arc<Value<'a, T>>, EvalError> {
    evaluate(
        expr,
        &mut Definitions {
            definitions,
            solved_impls,
        },
    )
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
    args: &Option<Vec<Type>>,
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
    /// Failure when running a prover function (non-recoverable).
    ProverError(String),
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
            EvalError::ProverError(msg) => write!(f, "Error executing prover function: {msg}"),
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
    Struct(&'a str, Vec<(&'a str, Arc<Self>)>),
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
            Value::Enum(name, _) | Value::Struct(name, _) => name.to_string(),
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

const BUILTINS: [(&str, BuiltinFunction); 20] = [
    ("std::array::len", BuiltinFunction::ArrayLen),
    ("std::check::panic", BuiltinFunction::Panic),
    ("std::convert::expr", BuiltinFunction::ToExpr),
    ("std::convert::fe", BuiltinFunction::ToFe),
    ("std::convert::int", BuiltinFunction::ToInt),
    ("std::debug::print", BuiltinFunction::Print),
    ("std::field::modulus", BuiltinFunction::Modulus),
    ("std::prelude::challenge", BuiltinFunction::Challenge),
    (
        "std::prover::new_witness_col_at_stage",
        BuiltinFunction::NewWitAtStage,
    ),
    ("std::prover::provide_value", BuiltinFunction::ProvideValue),
    ("std::prelude::set_hint", BuiltinFunction::SetHint),
    ("std::prover::min_degree", BuiltinFunction::MinDegree),
    ("std::prover::max_degree", BuiltinFunction::MaxDegree),
    ("std::prover::degree", BuiltinFunction::Degree),
    ("std::prover::eval", BuiltinFunction::Eval),
    ("std::prover::try_eval", BuiltinFunction::TryEval),
    ("std::prover::try_eval", BuiltinFunction::TryEval),
    ("std::prover::get_input", BuiltinFunction::GetInput),
    (
        "std::prover::get_input_from_channel",
        BuiltinFunction::GetInputFromChannel,
    ),
    ("std::prover::output_byte", BuiltinFunction::OutputByte),
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
    /// std::prover::new_witness_col_at_stage: string, int -> expr, creates a new witness column at a certain proof stage.
    NewWitAtStage,
    /// std::prover::provide_value: expr, int, fe -> (), provides a value for a witness column at a given row.
    ProvideValue,
    /// std::prelude::set_hint: expr, (int -> std::prelude::Query) -> (), adds a hint to a witness column.
    SetHint,
    /// std::prover::min_degree: -> int, returns the minimum column length / degree.
    MinDegree,
    /// std::prover::max_degree: -> int, returns the maximum column length / degree.
    MaxDegree,
    /// std::prover::degree: -> int, returns the column length / degree, if the minimum and maximum are equal.
    Degree,
    /// std::prover::eval: expr -> fe, evaluates an expression on the current row
    Eval,
    /// std::prover::try_eval: expr -> std::prelude::Option<fe>, evaluates an expression on the current row
    TryEval,
    /// std::prover::get_input: int -> fe, returns the value of a prover-provided and uncommitted input
    GetInput,
    /// std::prover::get_input_from_channel: int, int -> fe, returns the value of a prover-provided and uncommitted input from a certain channel
    GetInputFromChannel,
    /// std::prover::output_byte: int, int -> (), outputs a byte to a file descriptor
    OutputByte,
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
            Value::Struct(name, data) => {
                write!(f, "{name} {{")?;
                for (field, value) in data {
                    write!(f, "{field}: {value}, ")?;
                }
                write!(f, "}}")
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
    pub type_args: HashMap<String, Type>,
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

pub struct Definitions<'a> {
    pub definitions: &'a HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
    pub solved_impls: &'a HashMap<String, HashMap<Vec<Type>, Arc<Expression>>>,
}

impl<'a> Definitions<'a> {
    /// Implementation of `lookup` that allows to provide a different implementation
    /// of SymbolLookup for the recursive call.
    pub fn lookup_with_symbols<T: FieldElement>(
        definitions: &'a HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
        solved_impls: &'a HashMap<String, HashMap<Vec<Type>, Arc<Expression>>>,
        name: &str,
        type_args: &Option<Vec<Type>>,
        symbols: &mut impl SymbolLookup<'a, T>,
    ) -> Result<Arc<Value<'a, T>>, EvalError> {
        let name = name.to_string();
        let (symbol, value) = definitions
            .get(&name)
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
                    name,
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
                    let type_args = type_arg_mapping(type_scheme, type_args);
                    evaluate_generic(value, &type_args, symbols)?
                }
                Some(FunctionValueDefinition::TypeConstructor(TypeConstructor::Enum(
                    _type_name,
                    variant,
                ))) => {
                    if variant.fields.is_none() {
                        Value::Enum(&variant.name, None).into()
                    } else {
                        Value::TypeConstructor(&variant.name).into()
                    }
                }
                Some(FunctionValueDefinition::TypeConstructor(TypeConstructor::Struct(
                    struct_decl,
                    _fields,
                ))) => Value::TypeConstructor(&struct_decl.name).into(),
                Some(FunctionValueDefinition::TraitFunction(_, _)) => {
                    let type_arg = type_args.as_ref().unwrap();
                    let Expression::LambdaExpression(_, lambda) =
                        solved_impls[&name][type_arg].as_ref()
                    else {
                        unreachable!()
                    };
                    let closure = Closure {
                        lambda,
                        environment: vec![],
                        type_args: HashMap::new(),
                    };
                    Value::Closure(closure).into()
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
        type_args: &Option<Vec<Type>>,
    ) -> Result<Arc<Value<'a, T>>, EvalError> {
        Self::lookup_with_symbols(self.definitions, self.solved_impls, name, type_args, self)
    }

    fn lookup_public_reference(&self, name: &str) -> Result<Arc<Value<'a, T>>, EvalError> {
        Ok(Value::from(AlgebraicExpression::PublicReference(name.to_string())).into())
    }
}

pub trait SymbolLookup<'a, T: FieldElement> {
    fn lookup(
        &mut self,
        name: &'a str,
        type_args: &Option<Vec<Type>>,
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

    fn min_degree(&self) -> Result<Arc<Value<'a, T>>, EvalError> {
        Err(EvalError::Unsupported(
            "Cannot evaluate min degree.".to_string(),
        ))
    }

    fn max_degree(&self) -> Result<Arc<Value<'a, T>>, EvalError> {
        Err(EvalError::Unsupported(
            "Cannot evaluate max degree.".to_string(),
        ))
    }

    fn degree(&self) -> Result<Arc<Value<'a, T>>, EvalError> {
        Err(EvalError::Unsupported(
            "Cannot evaluate degree.".to_string(),
        ))
    }

    fn new_column(
        &mut self,
        name: &str,
        _type: Option<&Type>,
        _stage: Option<u32>,
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

    fn provide_value(
        &mut self,
        _col: Arc<Value<'a, T>>,
        _row: Arc<Value<'a, T>>,
        _value: Arc<Value<'a, T>>,
    ) -> Result<(), EvalError> {
        Err(EvalError::Unsupported(
            "Tried to provide value outside of prover function.".to_string(),
        ))
    }

    fn get_input(&mut self, _index: usize) -> Result<Arc<Value<'a, T>>, EvalError> {
        Err(EvalError::Unsupported(
            "Tried to get input outside of prover function.".to_string(),
        ))
    }

    fn get_input_from_channel(
        &mut self,
        _channel: u32,
        _index: usize,
    ) -> Result<Arc<Value<'a, T>>, EvalError> {
        Err(EvalError::Unsupported(
            "Tried to get input from channel outside of prover function.".to_string(),
        ))
    }

    fn output_byte(&mut self, _fd: u32, _byte: u8) -> Result<(), EvalError> {
        Err(EvalError::Unsupported(
            "Tried to output byte outside of prover function.".to_string(),
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
    SetEnvironment(Vec<Arc<Value<'a, T>>>, HashMap<String, Type>),
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
    type_args: HashMap<String, Type>,
    op_stack: Vec<Operation<'a, T>>,
    value_stack: Vec<Arc<Value<'a, T>>>,
}

impl<'a, 'b, T: FieldElement, S: SymbolLookup<'a, T>> Evaluator<'a, 'b, T, S> {
    fn new(symbols: &'b mut S, type_args: HashMap<String, Type>) -> Self {
        Self {
            symbols,
            local_vars: vec![],
            type_args,
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
                Operation::LetStatement(s) => self.evaluate_let_statement(s)?,
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
            Expression::FieldAccess(_, FieldAccess { object, field: _ }) => {
                self.op_stack.push(Operation::Combine(expr));
                self.op_stack.push(Operation::Expand(object));
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
            Expression::StructExpression(_, StructExpression { name, fields }) => {
                let mut exp_fields = Vec::new();
                for NamedExpression { name, body } in fields.iter() {
                    self.expand(body)?;

                    let value = self.value_stack.pop().ok_or(EvalError::SymbolNotFound(
                        "Symbol {name} not found".to_string(),
                    ))?;

                    exp_fields.push((name.as_str(), value));
                }

                self.value_stack
                    .push(Value::Struct(name, exp_fields).into());
            }
        };
        Ok(())
    }

    fn evaluate_let_statement(
        &mut self,
        s: &'a LetStatementInsideBlock<Expression>,
    ) -> Result<(), EvalError> {
        let value = if s.value.is_none()
            || matches!(&s.ty, Some(Type::Col) | Some(Type::Inter))
            || matches!(&s.ty, Some(Type::Array(ArrayType { base, .. })) if matches!(base.as_ref(), Type::Col | Type::Inter))
        {
            // Dynamic column creation
            let Pattern::Variable(_, name) = &s.pattern else {
                unreachable!()
            };
            let value = s.value.as_ref().map(|_| self.value_stack.pop().unwrap());
            self.symbols
                .new_column(name, s.ty.as_ref(), None, value, SourceRef::unknown())?
        } else {
            // Regular local variable declaration.
            self.value_stack.pop().unwrap()
        };
        self.local_vars.extend(
            Value::try_match_pattern(&value, &s.pattern).unwrap_or_else(|| {
                panic!("Irrefutable pattern did not match: {} = {value}", s.pattern)
            }),
        );
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
                    self.symbols.lookup(&poly.name, &type_args)?
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
                evaluate_binary_operation(left, *op, right)?
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
                        "Operator \"{op}\" not supported on types: {inner}: {}",
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
            Expression::FieldAccess(_, FieldAccess { object: _, field }) => {
                let object = self.value_stack.pop().unwrap();
                match object.as_ref() {
                    Value::Struct(_, fields) => fields
                        .iter()
                        .find_map(|(name, value)| {
                            if name == field {
                                Some(value.clone())
                            } else {
                                None
                            }
                        })
                        .ok_or_else(|| {
                            EvalError::SymbolNotFound(format!(
                                "Field {field} not found in {object}"
                            ))
                        })?,
                    _ => Err(EvalError::TypeError(format!(
                        "Expected struct for field access but got {object}: {}",
                        object.type_formatted()
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
            Expression::StructExpression(_, StructExpression { name: _, fields: _ }) => {
                return self.expand(expr);
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
    left: Arc<Value<'a, T>>,
    op: BinaryOperator,
    right: Arc<Value<'a, T>>,
) -> Result<Arc<Value<'a, T>>, EvalError> {
    Ok(match (left.as_ref(), op, right.as_ref()) {
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
        (Value::Expression(_), BinaryOperator::Select, Value::Array(_)) => {
            Value::Enum("SelectedExprs", Some(vec![left, right])).into()
        }
        (_, BinaryOperator::In | BinaryOperator::Is, _) => {
            let (left_sel, left_exprs) = to_selected_exprs_expanded(&left);
            let (right_sel, right_exprs) = to_selected_exprs_expanded(&right);
            let name = match op {
                BinaryOperator::In => "Lookup",
                BinaryOperator::Is => "Permutation",
                _ => unreachable!(),
            };
            let selectors = Value::Tuple(vec![left_sel, right_sel]).into();
            let expr_pairs = zip_expressions_for_op(op, left_exprs, right_exprs)?;
            Value::Enum(name, Some(vec![selectors, expr_pairs])).into()
        }
        (Value::Array(left), BinaryOperator::Connect, Value::Array(right)) => {
            let expr_pairs = zip_expressions_for_op(op, left, right)?;
            Value::Enum("Connection", Some(vec![expr_pairs])).into()
        }
        (l, op, r) => Err(EvalError::TypeError(format!(
            "Operator \"{op}\" not supported on types: {l}: {}, {r}: {}",
            l.type_formatted(),
            r.type_formatted()
        )))?,
    })
}

fn zip_expressions_for_op<'a, T>(
    op: BinaryOperator,
    left: &[Arc<Value<'a, T>>],
    right: &[Arc<Value<'a, T>>],
) -> Result<Arc<Value<'a, T>>, EvalError> {
    if left.len() != right.len() {
        Err(EvalError::TypeError(format!(
            "Tried to use \"{op}\" operator on arrays of different lengths: {} and {}",
            left.len(),
            right.len()
        )))?
    }
    Ok(Value::Array(
        left.iter()
            .zip(right)
            .map(|(l, r)| Value::Tuple(vec![l.clone(), r.clone()]).into())
            .collect(),
    )
    .into())
}

/// Turns a value that can be interpreted as a seleceted expressions (either "a $ [b, c]" or "[b, c]")
/// into the selector and the exprs. The selector is already wrappend into a std::prelude::Option.
fn to_selected_exprs_expanded<'a, 'b, T>(
    selected_exprs: &'a Value<'b, T>,
) -> (Arc<Value<'b, T>>, &'a Vec<Arc<Value<'b, T>>>) {
    match selected_exprs {
        // An array of expressions or a selected expressions without selector.
        Value::Array(items) | Value::Enum("JustExprs", Some(items)) => {
            (Value::Enum("None", None).into(), &items)
        }
        // A selected expressions
        Value::Enum("SelectedExprs", Some(items)) => {
            let [sel, exprs] = &items[..] else { panic!() };
            let selector = Value::Enum("Some", Some(vec![sel.clone()])).into();
            let Value::Array(exprs) = exprs.as_ref() else {
                panic!();
            };
            (selector, exprs)
        }
        _ => panic!(),
    }
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
        BuiltinFunction::NewWitAtStage => 2,
        BuiltinFunction::ProvideValue => 3,
        BuiltinFunction::SetHint => 2,
        BuiltinFunction::MinDegree => 0,
        BuiltinFunction::MaxDegree => 0,
        BuiltinFunction::Degree => 0,
        BuiltinFunction::Eval => 1,
        BuiltinFunction::TryEval => 1,
        BuiltinFunction::GetInput => 1,
        BuiltinFunction::GetInputFromChannel => 2,
        BuiltinFunction::OutputByte => 2,
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
        BuiltinFunction::NewWitAtStage => {
            let [name, stage] = &arguments[..] else {
                panic!()
            };
            let Value::String(name) = name.as_ref() else {
                panic!()
            };
            let Value::Integer(stage) = (**stage).clone() else {
                panic!()
            };
            let stage = Some(u32::try_from(stage).unwrap());
            symbols.new_column(name, Some(&Type::Col), stage, None, SourceRef::unknown())?
        }
        BuiltinFunction::ProvideValue => {
            let value = arguments.pop().unwrap();
            let row = arguments.pop().unwrap();
            let col = arguments.pop().unwrap();
            symbols.provide_value(col, row, value)?;
            Value::Tuple(vec![]).into()
        }
        BuiltinFunction::GetInput => {
            let index = arguments.pop().unwrap();
            let Value::Integer(index) = index.as_ref() else {
                panic!()
            };
            symbols.get_input(usize::try_from(index).unwrap())?
        }
        BuiltinFunction::GetInputFromChannel => {
            let index = arguments.pop().unwrap();
            let channel = arguments.pop().unwrap();
            let Value::Integer(index) = index.as_ref() else {
                panic!()
            };
            let Value::Integer(channel) = channel.as_ref() else {
                panic!()
            };
            symbols.get_input_from_channel(
                u32::try_from(channel).unwrap(),
                usize::try_from(index).unwrap(),
            )?
        }
        BuiltinFunction::OutputByte => {
            let byte = arguments.pop().unwrap();
            let fd = arguments.pop().unwrap();
            let (Value::Integer(fd), Value::Integer(byte)) = (fd.as_ref(), byte.as_ref()) else {
                panic!()
            };
            symbols.output_byte(u32::try_from(fd).unwrap(), u8::try_from(byte).unwrap())?;
            Value::Tuple(vec![]).into()
        }
        BuiltinFunction::SetHint => {
            let expr = arguments.pop().unwrap();
            let col = arguments.pop().unwrap();
            symbols.set_hint(col, expr)?;
            Value::Tuple(vec![]).into()
        }
        BuiltinFunction::MaxDegree => symbols.max_degree()?,
        BuiltinFunction::MinDegree => symbols.min_degree()?,
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
        BuiltinFunction::TryEval => {
            let arg = arguments.pop().unwrap();
            let result = match arg.as_ref() {
                Value::Expression(e) => symbols.eval_expr(e),
                v => panic!(
                    "Expected expression for std::prover::eval, but got {v}: {}",
                    v.type_formatted()
                ),
            };
            match result {
                Ok(v) => Value::Enum("Some", Some(vec![v])),
                Err(EvalError::DataNotAvailable) => Value::Enum("None", None),
                Err(e) => return Err(e),
            }
            .into()
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
            "Invalid operator \"{op}\" on field elements: {left} {op} {right}"
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
            "Invalid operator \"{op}\" on integers: {left} {op} {right}"
        )))?,
    }
    .into())
}

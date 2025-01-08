use core::ops::{Add, Mul, Sub};
use std::collections::BTreeMap;
use std::ops::Neg;

use crate::analyzed::{
    AlgebraicBinaryOperation, AlgebraicBinaryOperator, AlgebraicExpression as Expression,
    AlgebraicReference, AlgebraicReferenceThin, AlgebraicUnaryOperation, AlgebraicUnaryOperator,
    Analyzed, Challenge, PolyID, PolynomialType,
};
use powdr_number::FieldElement;
use powdr_number::LargeInt;

/// Accessor for terminal symbols.
pub trait TerminalAccess<T> {
    fn get(&self, _poly_ref: &AlgebraicReference) -> T {
        unimplemented!();
    }
    fn get_public(&self, _public: &str) -> T {
        unimplemented!();
    }
    fn get_challenge(&self, _challenge: &Challenge) -> T {
        unimplemented!();
    }
}

/// A simple container for trace values.
pub struct OwnedTerminalValues<F> {
    pub trace: BTreeMap<PolyID, Vec<F>>,
    pub public_values: BTreeMap<String, F>,
    pub challenge_values: BTreeMap<u64, F>,
}

/// A view into the trace values for a single row.
pub struct RowValues<'a, F> {
    values: &'a OwnedTerminalValues<F>,
    row: usize,
}

impl<F> OwnedTerminalValues<F> {
    pub fn new(
        pil: &Analyzed<F>,
        witness_columns: Vec<(String, Vec<F>)>,
        fixed_columns: Vec<(String, Vec<F>)>,
    ) -> Self {
        let mut columns_by_name = witness_columns
            .into_iter()
            .chain(fixed_columns)
            .collect::<BTreeMap<_, _>>();
        let trace = pil
            .committed_polys_in_source_order()
            .chain(pil.constant_polys_in_source_order())
            .flat_map(|(symbol, _)| symbol.array_elements())
            .filter_map(|(name, poly_id)| {
                columns_by_name
                    .remove(&name)
                    .map(|column| (poly_id, column))
            })
            .collect();
        Self {
            trace,
            public_values: Default::default(),
            challenge_values: Default::default(),
        }
    }

    pub fn with_publics(mut self, publics: Vec<(String, F)>) -> Self {
        self.public_values = publics.into_iter().collect();
        self
    }

    pub fn with_challenges(mut self, challenges: BTreeMap<u64, F>) -> Self {
        self.challenge_values = challenges;
        self
    }

    pub fn height(&self) -> usize {
        self.trace.values().next().map(|v| v.len()).unwrap()
    }

    pub fn row(&self, row: usize) -> RowValues<F> {
        RowValues { values: self, row }
    }
}

impl<F: FieldElement, T: From<F>> TerminalAccess<T> for RowValues<'_, F> {
    fn get(&self, column: &AlgebraicReference) -> T {
        match column.poly_id.ptype {
            PolynomialType::Committed | PolynomialType::Constant => {
                let column_values = self.values.trace.get(&column.poly_id).unwrap();
                let row = (self.row + column.next as usize) % column_values.len();
                column_values[row].into()
            }
            PolynomialType::Intermediate => unreachable!(
                "Intermediate polynomials should have been handled by ExpressionEvaluator"
            ),
        }
    }

    fn get_public(&self, public: &str) -> T {
        self.values.public_values[public].into()
    }

    fn get_challenge(&self, challenge: &Challenge) -> T {
        self.values.challenge_values[&challenge.id].into()
    }
}

pub trait ExpressionWalkerCallback<F, T> {
    fn handle_binary_operation(
        &self,
        left: T,
        op: &AlgebraicBinaryOperator,
        right: T,
        right_expr: &Expression<F>,
    ) -> T;
    fn handle_unary_operation(&self, op: &AlgebraicUnaryOperator, arg: T) -> T;
    fn handle_number(&self, fe: &F) -> T;
}

/// Evaluates an algebraic expression to a value.
pub struct ExpressionWalker<'a, T, Expr, TA, C> {
    terminal_access: TA,
    intermediate_definitions: &'a BTreeMap<AlgebraicReferenceThin, Expression<T>>,
    /// Maps intermediate reference to their evaluation. Updated throughout the lifetime of the
    /// ExpressionEvaluator.
    intermediates_cache: BTreeMap<AlgebraicReferenceThin, Expr>,
    callback: C,
}

impl<'a, T, Expr: Clone, TA, C> ExpressionWalker<'a, T, Expr, TA, C>
where
    TA: TerminalAccess<Expr>,
    C: ExpressionWalkerCallback<T, Expr>,
{
    /// Create a new expression evaluator with custom expression converters.
    pub fn new(
        terminal_access: TA,
        intermediate_definitions: &'a BTreeMap<AlgebraicReferenceThin, Expression<T>>,
        callback: C,
    ) -> Self {
        Self {
            terminal_access,
            intermediate_definitions,
            intermediates_cache: Default::default(),
            callback,
        }
    }

    pub fn evaluate(&mut self, expr: &'a Expression<T>) -> Expr {
        match expr {
            Expression::Reference(reference) => match reference.poly_id.ptype {
                PolynomialType::Committed => self.terminal_access.get(reference),
                PolynomialType::Constant => self.terminal_access.get(reference),
                PolynomialType::Intermediate => {
                    let reference = reference.to_thin();
                    let value = self.intermediates_cache.get(&reference).cloned();
                    match value {
                        Some(v) => v,
                        None => {
                            let definition = self.intermediate_definitions.get(&reference).unwrap();
                            let result = self.evaluate(definition);
                            self.intermediates_cache.insert(reference, result.clone());
                            result
                        }
                    }
                }
            },
            Expression::PublicReference(public) => self.terminal_access.get_public(public),
            Expression::Challenge(challenge) => self.terminal_access.get_challenge(challenge),
            Expression::Number(n) => self.callback.handle_number(n),
            Expression::BinaryOperation(AlgebraicBinaryOperation { left, op, right }) => {
                let left_value = self.evaluate(left);
                let right_value = self.evaluate(right);
                self.callback
                    .handle_binary_operation(left_value, op, right_value, right)
            }
            Expression::UnaryOperation(AlgebraicUnaryOperation { op, expr }) => {
                let arg = self.evaluate(expr);
                self.callback.handle_unary_operation(op, arg)
            }
        }
    }
}

struct EvaluatorCallback<F, T> {
    to_expr: fn(&F) -> T,
}

impl<F, Expr> ExpressionWalkerCallback<F, Expr> for EvaluatorCallback<F, Expr>
where
    Expr: Clone + Add<Output = Expr> + Sub<Output = Expr> + Mul<Output = Expr> + Neg<Output = Expr>,
    F: FieldElement,
{
    fn handle_binary_operation(
        &self,
        left: Expr,
        op: &AlgebraicBinaryOperator,
        right: Expr,
        right_expr: &Expression<F>,
    ) -> Expr {
        match op {
            AlgebraicBinaryOperator::Add => left + right,
            AlgebraicBinaryOperator::Sub => left - right,
            AlgebraicBinaryOperator::Mul => left * right,
            AlgebraicBinaryOperator::Pow => match right_expr {
                Expression::Number(n) => (0u32..n.to_integer().try_into_u32().unwrap())
                    .fold((self.to_expr)(&F::one()), |acc, _| acc * left.clone()),
                _ => unimplemented!("pow with non-constant exponent"),
            },
        }
    }

    fn handle_unary_operation(&self, op: &AlgebraicUnaryOperator, arg: Expr) -> Expr {
        match op {
            AlgebraicUnaryOperator::Minus => -arg,
        }
    }

    fn handle_number(&self, fe: &F) -> Expr {
        (self.to_expr)(fe)
    }
}

/// Evaluates an algebraic expression to a value.
pub struct ExpressionEvaluator<'a, T, Expr, TA> {
    expression_walker: ExpressionWalker<'a, T, Expr, TA, EvaluatorCallback<T, Expr>>,
}

impl<'a, T, TA> ExpressionEvaluator<'a, T, T, TA>
where
    TA: TerminalAccess<T>,
    T: FieldElement,
{
    /// Create a new expression evaluator (for the case where Expr = T).
    pub fn new(
        terminal_access: TA,
        intermediate_definitions: &'a BTreeMap<AlgebraicReferenceThin, Expression<T>>,
    ) -> Self {
        Self::new_with_custom_expr(terminal_access, intermediate_definitions, |x| *x)
    }
}

impl<'a, T, Expr, TA> ExpressionEvaluator<'a, T, Expr, TA>
where
    TA: TerminalAccess<Expr>,
    Expr: Clone + Add<Output = Expr> + Sub<Output = Expr> + Mul<Output = Expr> + Neg<Output = Expr>,
    T: FieldElement,
{
    /// Create a new expression evaluator with custom expression converters.
    pub fn new_with_custom_expr(
        terminal_access: TA,
        intermediate_definitions: &'a BTreeMap<AlgebraicReferenceThin, Expression<T>>,
        to_expr: fn(&T) -> Expr,
    ) -> Self {
        let callback = EvaluatorCallback { to_expr };
        let expression_walker =
            ExpressionWalker::new(terminal_access, intermediate_definitions, callback);
        Self { expression_walker }
    }

    pub fn evaluate(&mut self, expr: &'a Expression<T>) -> Expr {
        self.expression_walker.evaluate(expr)
    }
}

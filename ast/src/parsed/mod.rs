pub mod asm;
pub mod build;
pub mod display;
pub mod folder;
pub mod sugar;
pub mod types;
pub mod visitor;

use std::{
    collections::BTreeSet,
    iter::{empty, once},
    ops,
    str::FromStr,
};

use auto_enums::auto_enum;
use derive_more::Display;
use powdr_number::{BigInt, BigUint};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use powdr_parser_util::SourceRef;

use self::{
    asm::{Part, SymbolPath},
    types::{FunctionType, Type, TypeBounds, TypeScheme},
    visitor::{Children, ExpressionVisitable},
};

#[derive(Display, Clone, Copy, PartialEq, Eq)]
pub enum SymbolCategory {
    /// A value, which has a type and can be referenced in expressions (a variable, function, constant, ...).
    Value,
    /// A type, for example the name of an enum or other user-defined type.
    Type,
    /// A type constructor, i.e. an enum variant, which can be used as a function or constant inside an expression
    /// or to deconstruct a value in a pattern.
    TypeConstructor,
    /// A trait declaration, which can be used as a type.
    TraitDeclaration,
}
impl SymbolCategory {
    /// Returns if a symbol of a given category can satisfy a request for a certain category.
    pub fn compatible_with_request(&self, request: SymbolCategory) -> bool {
        match self {
            SymbolCategory::Value => request == SymbolCategory::Value,
            SymbolCategory::Type => request == SymbolCategory::Type,
            SymbolCategory::TypeConstructor => {
                // Type constructors can also satisfy requests for values.
                request == SymbolCategory::TypeConstructor || request == SymbolCategory::Value
            }
            SymbolCategory::TraitDeclaration => request == SymbolCategory::TraitDeclaration,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct PILFile(pub Vec<PilStatement>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum PilStatement {
    /// File name
    Include(SourceRef, String),
    /// Name of namespace and optional polynomial degree (constant)
    Namespace(SourceRef, SymbolPath, Option<Expression>),
    LetStatement(
        SourceRef,
        String,
        Option<TypeScheme<Expression>>,
        Option<Expression>,
    ),
    PolynomialDefinition(SourceRef, String, Expression),
    PublicDeclaration(
        SourceRef,
        /// The name of the public value.
        String,
        /// The polynomial/column that contains the public value.
        NamespacedPolynomialReference,
        /// If the polynomial is an array, this is the array element index.
        Option<Expression>,
        /// The row number of the public value.
        Expression,
    ),
    PolynomialConstantDeclaration(SourceRef, Vec<PolynomialName>),
    PolynomialConstantDefinition(SourceRef, String, FunctionDefinition),
    PolynomialCommitDeclaration(
        SourceRef,
        // Stage
        Option<u32>,
        // Names
        Vec<PolynomialName>,
        // Value (prover query / hint)
        Option<FunctionDefinition>,
    ),
    PlookupIdentity(
        SourceRef,
        SelectedExpressions<Expression>,
        SelectedExpressions<Expression>,
    ),
    PermutationIdentity(
        SourceRef,
        SelectedExpressions<Expression>,
        SelectedExpressions<Expression>,
    ),
    ConnectIdentity(SourceRef, Vec<Expression>, Vec<Expression>),
    EnumDeclaration(SourceRef, EnumDeclaration<Expression>),
    TraitImplementation(SourceRef, TraitImplementation<Expression>),
    TraitDeclaration(SourceRef, TraitDeclaration<Expression>),
    Expression(SourceRef, Expression),
}

impl PilStatement {
    /// If the statement is a symbol definition, returns all (local) names of defined symbols
    /// and their category.
    /// Note it does not return nested definitions (for an enum for example).
    pub fn symbol_definition_names(&self) -> impl Iterator<Item = (&String, SymbolCategory)> + '_ {
        self.symbol_definition_names_and_contained()
            .filter_map(|(name, sub_name, category)| match sub_name {
                Some(_) => None,
                None => Some((name, category)),
            })
    }

    /// If the statement is a symbol definition, returns all (local) names of defined symbols
    /// and their category.
    /// For an enum, returns the name of the enum and all the variants, where the first
    /// component is the name of the enum and the second the name of the variant.
    pub fn symbol_definition_names_and_contained(
        &self,
    ) -> Box<dyn Iterator<Item = (&String, Option<&String>, SymbolCategory)> + '_> {
        match self {
            PilStatement::PolynomialDefinition(_, name, _)
            | PilStatement::PolynomialConstantDefinition(_, name, _)
            | PilStatement::PublicDeclaration(_, name, _, _, _)
            | PilStatement::LetStatement(_, name, _, _) => {
                Box::new(once((name, None, SymbolCategory::Value)))
            }
            PilStatement::EnumDeclaration(_, EnumDeclaration { name, variants, .. }) => Box::new(
                once((name, None, SymbolCategory::Type)).chain(
                    variants
                        .iter()
                        .map(move |v| (name, Some(&v.name), SymbolCategory::TypeConstructor)),
                ),
            ),
            PilStatement::TraitDeclaration(
                _,
                TraitDeclaration {
                    name, functions, ..
                },
            ) => Box::new(
                once((name, None, SymbolCategory::TraitDeclaration)).chain(
                    functions
                        .iter()
                        .map(move |f| (name, Some(&f.name), SymbolCategory::Value)),
                ),
            ),
            PilStatement::PolynomialConstantDeclaration(_, polynomials)
            | PilStatement::PolynomialCommitDeclaration(_, _, polynomials, _) => Box::new(
                polynomials
                    .iter()
                    .map(|p| (&p.name, None, SymbolCategory::Value)),
            ),

            PilStatement::Include(_, _)
            | PilStatement::Namespace(_, _, _)
            | PilStatement::PlookupIdentity(_, _, _)
            | PilStatement::PermutationIdentity(_, _, _)
            | PilStatement::ConnectIdentity(_, _, _)
            | PilStatement::Expression(_, _)
            | PilStatement::TraitImplementation(_, _) => Box::new(empty()),
        }
    }
}

impl Children<Expression> for PilStatement {
    /// Returns an iterator over all (top-level) expressions in this statement.
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        match self {
            PilStatement::PlookupIdentity(_, left, right)
            | PilStatement::PermutationIdentity(_, left, right) => {
                Box::new(left.children().chain(right.children()))
            }
            PilStatement::ConnectIdentity(_start, left, right) => {
                Box::new(left.iter().chain(right.iter()))
            }
            PilStatement::Expression(_, e)
            | PilStatement::Namespace(_, _, Some(e))
            | PilStatement::PolynomialDefinition(_, _, e) => Box::new(once(e)),

            PilStatement::EnumDeclaration(_, enum_decl) => enum_decl.children(),
            PilStatement::TraitImplementation(_, trait_impl) => trait_impl.children(),
            PilStatement::TraitDeclaration(_, trait_decl) => trait_decl.children(),

            PilStatement::LetStatement(_, _, type_scheme, value) => Box::new(
                type_scheme
                    .iter()
                    .flat_map(|t| t.ty.children())
                    .chain(value),
            ),

            PilStatement::PublicDeclaration(_, _, _, i, e) => Box::new(i.iter().chain(once(e))),

            PilStatement::PolynomialConstantDefinition(_, _, def)
            | PilStatement::PolynomialCommitDeclaration(_, _, _, Some(def)) => def.children(),
            PilStatement::PolynomialCommitDeclaration(_, _, _, None)
            | PilStatement::Include(_, _)
            | PilStatement::Namespace(_, _, None)
            | PilStatement::PolynomialConstantDeclaration(_, _) => Box::new(empty()),
        }
    }

    /// Returns an iterator over all (top-level) expressions in this statement.
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        match self {
            PilStatement::PlookupIdentity(_, left, right)
            | PilStatement::PermutationIdentity(_, left, right) => {
                Box::new(left.children_mut().chain(right.children_mut()))
            }
            PilStatement::ConnectIdentity(_start, left, right) => {
                Box::new(left.iter_mut().chain(right.iter_mut()))
            }
            PilStatement::Expression(_, e)
            | PilStatement::Namespace(_, _, Some(e))
            | PilStatement::PolynomialDefinition(_, _, e) => Box::new(once(e)),

            PilStatement::EnumDeclaration(_, enum_decl) => enum_decl.children_mut(),
            PilStatement::TraitImplementation(_, trait_impl) => trait_impl.children_mut(),
            PilStatement::TraitDeclaration(_, trait_decl) => trait_decl.children_mut(),

            PilStatement::LetStatement(_, _, ty, value) => {
                Box::new(ty.iter_mut().flat_map(|t| t.ty.children_mut()).chain(value))
            }

            PilStatement::PublicDeclaration(_, _, _, i, e) => Box::new(i.iter_mut().chain(once(e))),

            PilStatement::PolynomialConstantDefinition(_, _, def)
            | PilStatement::PolynomialCommitDeclaration(_, _, _, Some(def)) => def.children_mut(),
            PilStatement::PolynomialCommitDeclaration(_, _, _, None)
            | PilStatement::Include(_, _)
            | PilStatement::Namespace(_, _, None)
            | PilStatement::PolynomialConstantDeclaration(_, _) => Box::new(empty()),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct EnumDeclaration<E = u64> {
    pub name: String,
    pub type_vars: TypeBounds,
    pub variants: Vec<EnumVariant<E>>,
}

impl<R> Children<Expression<R>> for EnumDeclaration<u64> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        Box::new(empty())
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        Box::new(empty())
    }
}

impl<R> Children<Expression<R>> for EnumDeclaration<Expression<R>> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        Box::new(self.variants.iter().flat_map(|v| v.children()))
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        Box::new(self.variants.iter_mut().flat_map(|v| v.children_mut()))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct EnumVariant<E = u64> {
    pub name: String,
    pub fields: Option<Vec<Type<E>>>,
}

impl<E: Clone> EnumVariant<E> {
    /// Returns the type of the constructor function for this variant
    /// given the enum type.
    pub fn constructor_type(&self, enum_decl: &EnumDeclaration) -> TypeScheme<E> {
        let name = SymbolPath::from_str(&enum_decl.name).unwrap();
        let vars = enum_decl.type_vars.clone();
        let generic_args =
            (!vars.is_empty()).then(|| vars.vars().cloned().map(Type::TypeVar).collect::<Vec<_>>());

        let named_type = Type::NamedType(name, generic_args);

        let ty = match &self.fields {
            None => named_type,
            Some(fields) => Type::Function(FunctionType {
                params: (*fields).clone(),
                value: named_type.into(),
            }),
        };

        TypeScheme { vars, ty }
    }
}

impl<R> Children<Expression<R>> for EnumVariant<u64> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        Box::new(empty())
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        Box::new(empty())
    }
}

impl<R> Children<Expression<R>> for EnumVariant<Expression<R>> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        Box::new(
            self.fields
                .iter()
                .flat_map(|f| f.iter())
                .flat_map(|f| f.children()),
        )
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        Box::new(
            self.fields
                .iter_mut()
                .flat_map(|f| f.iter_mut())
                .flat_map(|f| f.children_mut()),
        )
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct TraitImplementation<Expr> {
    pub name: SymbolPath,
    pub type_scheme: TypeScheme,
    pub functions: Vec<NamedExpression<Expr>>,
}

impl<R> Children<Expression<R>> for TraitImplementation<Expression<R>> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        Box::new(self.functions.iter().flat_map(|m| m.body.children()))
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        Box::new(
            self.functions
                .iter_mut()
                .flat_map(|m| m.body.children_mut()),
        )
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct NamedExpression<Expr> {
    pub name: String,
    pub body: Box<Expr>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct TraitDeclaration<E = u64> {
    pub name: String,
    pub type_vars: Vec<String>,
    pub functions: Vec<TraitFunction<E>>,
}

impl TraitDeclaration<u64> {
    pub fn function_by_name(&self, name: &str) -> Option<&TraitFunction> {
        self.functions.iter().find(|f| f.name == name)
    }
}

impl<R> Children<Expression<R>> for TraitDeclaration<Expression<R>> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        Box::new(self.functions.iter().flat_map(|f| f.children()))
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        Box::new(self.functions.iter_mut().flat_map(|f| f.children_mut()))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct TraitFunction<E = u64> {
    pub name: String,
    pub ty: Type<E>,
}

impl<R> Children<Expression<R>> for TraitFunction<Expression<R>> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        self.ty.children()
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        self.ty.children_mut()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct SelectedExpressions<E = Expression<NamespacedPolynomialReference>> {
    pub selector: Option<E>,
    pub expressions: Box<E>,
}

impl<T> Default for SelectedExpressions<Expression<T>> {
    fn default() -> Self {
        Self {
            selector: Default::default(),
            expressions: Box::new(ArrayLiteral { items: vec![] }.into()),
        }
    }
}

impl<T> Children<Expression<T>> for SelectedExpressions<Expression<T>> {
    /// Returns an iterator over all (top-level) expressions in this SelectedExpressions.
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<T>> + '_> {
        Box::new(self.selector.iter().chain(self.expressions.children()))
    }

    /// Returns an iterator over all (top-level) expressions in this SelectedExpressions.
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<T>> + '_> {
        Box::new(
            self.selector
                .iter_mut()
                .chain(self.expressions.children_mut()),
        )
    }
}

#[derive(Debug, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub enum Expression<Ref = NamespacedPolynomialReference> {
    Reference(SourceRef, Ref),
    PublicReference(SourceRef, String),
    // A number literal and its type.
    Number(SourceRef, Number),
    String(SourceRef, String),
    Tuple(SourceRef, Vec<Self>),
    LambdaExpression(SourceRef, LambdaExpression<Self>),
    ArrayLiteral(SourceRef, ArrayLiteral<Self>),
    UnaryOperation(SourceRef, UnaryOperation<Self>),
    BinaryOperation(SourceRef, BinaryOperation<Self>),
    IndexAccess(SourceRef, IndexAccess<Self>),
    FunctionCall(SourceRef, FunctionCall<Self>),
    FreeInput(SourceRef, Box<Self>),
    MatchExpression(SourceRef, MatchExpression<Self>),
    IfExpression(SourceRef, IfExpression<Self>),
    BlockExpression(SourceRef, BlockExpression<Self>),
}

/// Comparison function for expressions that ignore source information.
macro_rules! impl_partial_eq_for_expression {
    ($($variant:ident),*) => {
        impl<Ref: PartialEq> PartialEq for Expression<Ref> {
            fn eq(&self, other: &Self) -> bool {
                match (self, other) {
                    $(
                        (Expression::$variant(_, a), Expression::$variant(_, b)) => a == b,
                    )*
                    // This catches the case where variants are different and returns false
                    $(
                        (Expression::$variant(_, _), _) => false,
                    )*
                }
            }
        }
    }
}

impl_partial_eq_for_expression!(
    Reference,
    PublicReference,
    Number,
    String,
    Tuple,
    LambdaExpression,
    ArrayLiteral,
    BinaryOperation,
    UnaryOperation,
    IndexAccess,
    FunctionCall,
    FreeInput,
    MatchExpression,
    IfExpression,
    BlockExpression
);

pub trait SourceReference {
    fn source_reference(&self) -> &SourceRef;
    fn source_reference_mut(&mut self) -> &mut SourceRef;
}

macro_rules! impl_source_reference {
    ($enum:ident, $($variant:ident),*) => {
        impl<E> SourceReference for $enum<E> {
            fn source_reference(&self) -> &SourceRef {
                match self {
                    $( $enum::$variant(src, _) => src, )*
                }
            }

            fn source_reference_mut(&mut self) -> &mut SourceRef {
                match self {
                    $( $enum::$variant(src, _) => src, )*
                }
            }
        }
    }
}

impl_source_reference!(
    Expression,
    Reference,
    PublicReference,
    Number,
    String,
    Tuple,
    LambdaExpression,
    ArrayLiteral,
    BinaryOperation,
    UnaryOperation,
    IndexAccess,
    FunctionCall,
    FreeInput,
    MatchExpression,
    IfExpression,
    BlockExpression
);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct UnaryOperation<E = Expression<NamespacedPolynomialReference>> {
    pub op: UnaryOperator,
    pub expr: Box<E>,
}

impl<Ref> From<UnaryOperation<Expression<Ref>>> for Expression<Ref> {
    fn from(operation: UnaryOperation<Expression<Ref>>) -> Self {
        Expression::UnaryOperation(SourceRef::unknown(), operation)
    }
}

impl<E> Children<E> for UnaryOperation<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(once(self.expr.as_ref()))
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(once(self.expr.as_mut()))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct BinaryOperation<E = Expression<NamespacedPolynomialReference>> {
    pub left: Box<E>,
    pub op: BinaryOperator,
    pub right: Box<E>,
}

impl<Ref> From<BinaryOperation<Expression<Ref>>> for Expression<Ref> {
    fn from(operation: BinaryOperation<Expression<Ref>>) -> Self {
        Expression::BinaryOperation(SourceRef::unknown(), operation)
    }
}

impl<E> Children<E> for BinaryOperation<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new([self.left.as_ref(), self.right.as_ref()].into_iter())
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new([self.left.as_mut(), self.right.as_mut()].into_iter())
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct Number {
    #[schemars(skip)]
    pub value: BigUint,
    pub type_: Option<Type>,
}

impl<Ref> From<Number> for Expression<Ref> {
    fn from(number: Number) -> Self {
        Expression::Number(SourceRef::unknown(), number)
    }
}

impl<Ref> From<BigUint> for Expression<Ref> {
    fn from(value: BigUint) -> Self {
        Number { value, type_: None }.into()
    }
}

impl<Ref> From<u32> for Expression<Ref> {
    fn from(value: u32) -> Self {
        BigUint::from(value).into()
    }
}
pub type ExpressionPrecedence = u64;

impl<Ref> Expression<Ref> {
    pub fn new_binary(left: Self, op: BinaryOperator, right: Self) -> Self {
        Expression::BinaryOperation(
            SourceRef::unknown(),
            BinaryOperation {
                left: Box::new(left),
                op,
                right: Box::new(right),
            },
        )
    }

    /// Visits this expression and all of its sub-expressions and returns true
    /// if `f` returns true on any of them.
    pub fn any(&self, mut f: impl FnMut(&Self) -> bool) -> bool {
        use std::ops::ControlFlow;
        self.pre_visit_expressions_return(&mut |e| {
            if f(e) {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        })
        .is_break()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct MatchExpression<E = Expression<NamespacedPolynomialReference>> {
    pub scrutinee: Box<E>,
    pub arms: Vec<MatchArm<E>>,
}

impl<Ref> From<MatchExpression<Expression<Ref>>> for Expression<Ref> {
    fn from(match_expr: MatchExpression<Expression<Ref>>) -> Self {
        Expression::MatchExpression(SourceRef::unknown(), match_expr)
    }
}

impl<E> Children<E> for MatchExpression<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(
            once(self.scrutinee.as_ref()).chain(self.arms.iter().flat_map(|arm| arm.children())),
        )
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(
            once(self.scrutinee.as_mut())
                .chain(self.arms.iter_mut().flat_map(|arm| arm.children_mut())),
        )
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct BlockExpression<E> {
    pub statements: Vec<StatementInsideBlock<E>>,
    pub expr: Option<Box<E>>,
}

impl<Ref> From<BlockExpression<Expression<Ref>>> for Expression<Ref> {
    fn from(block: BlockExpression<Expression<Ref>>) -> Self {
        Expression::BlockExpression(SourceRef::unknown(), block)
    }
}

impl<E> Children<E> for BlockExpression<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(
            self.statements
                .iter()
                .flat_map(|s| s.children())
                .chain(self.expr.iter().map(|boxed| &**boxed)),
        )
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(
            self.statements
                .iter_mut()
                .flat_map(|s| s.children_mut())
                .chain(self.expr.iter_mut().map(|boxed| &mut **boxed)),
        )
    }
}

impl Expression<NamespacedPolynomialReference> {
    pub fn try_to_identifier(&self) -> Option<&String> {
        if let Expression::Reference(_, r) = self {
            r.try_to_identifier()
        } else {
            None
        }
    }
}

impl<Ref> ops::Add for Expression<Ref> {
    type Output = Expression<Ref>;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new_binary(self, BinaryOperator::Add, rhs)
    }
}

impl<Ref> ops::Sub for Expression<Ref> {
    type Output = Expression<Ref>;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::new_binary(self, BinaryOperator::Sub, rhs)
    }
}
impl<Ref> ops::Mul for Expression<Ref> {
    type Output = Expression<Ref>;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::new_binary(self, BinaryOperator::Mul, rhs)
    }
}

impl<Ref> std::iter::Sum for Expression<Ref> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|a, b| a + b).unwrap_or_else(|| 0u32.into())
    }
}

impl From<NamespacedPolynomialReference> for Expression {
    fn from(value: NamespacedPolynomialReference) -> Self {
        Self::Reference(SourceRef::unknown(), value)
    }
}

impl<R> Expression<R> {
    /// Returns an iterator over all (top-level) expressions in this expression.
    /// This specifically does not implement Children because otherwise it would
    /// have a wrong implementation of ExpressionVisitable (which is implemented
    /// generically for all types that implement Children<Expr>).
    #[auto_enum(Iterator)]
    pub fn children(&self) -> impl Iterator<Item = &Expression<R>> + '_ {
        match self {
            Expression::Reference(_, _)
            | Expression::PublicReference(_, _)
            | Expression::String(_, _) => empty(),
            Expression::Number(_, _) => empty(),
            Expression::Tuple(_, v) => v.iter(),
            Expression::LambdaExpression(_, lambda) => lambda.children(),
            Expression::ArrayLiteral(_, array) => array.children(),
            Expression::BinaryOperation(_, binary_op) => binary_op.children(),
            Expression::UnaryOperation(_, unary_op) => unary_op.children(),
            Expression::IndexAccess(_, index_access) => index_access.children(),
            Expression::FunctionCall(_, function_call) => function_call.children(),
            Expression::FreeInput(_, e) => once(e.as_ref()),
            Expression::MatchExpression(_, match_expr) => match_expr.children(),
            Expression::IfExpression(_, if_expr) => if_expr.children(),
            Expression::BlockExpression(_, block_expr) => block_expr.children(),
        }
    }

    /// Returns an iterator over all (top-level) expressions in this expression.
    /// This specifically does not implement Children because otherwise it would
    /// have a wrong implementation of ExpressionVisitable (which is implemented
    /// generically for all types that implement Children<Expr>).
    #[auto_enum(Iterator)]
    pub fn children_mut(&mut self) -> impl Iterator<Item = &mut Expression<R>> + '_ {
        match self {
            Expression::Reference(_, _)
            | Expression::PublicReference(_, _)
            | Expression::String(_, _) => empty(),
            Expression::Number(_, _) => empty(),
            Expression::Tuple(_, v) => v.iter_mut(),
            Expression::LambdaExpression(_, lambda) => lambda.children_mut(),
            Expression::ArrayLiteral(_, array) => array.children_mut(),
            Expression::BinaryOperation(_, binary_op) => binary_op.children_mut(),
            Expression::UnaryOperation(_, unary_op) => unary_op.children_mut(),
            Expression::IndexAccess(_, index_access) => index_access.children_mut(),
            Expression::FunctionCall(_, function_call) => function_call.children_mut(),
            Expression::FreeInput(_, e) => once(e.as_mut()),
            Expression::MatchExpression(_, match_expr) => match_expr.children_mut(),
            Expression::IfExpression(_, if_expr) => if_expr.children_mut(),
            Expression::BlockExpression(_, block_expr) => block_expr.children_mut(),
        }
    }

    /// Returns true if the expression contains a reference to a next value
    pub fn contains_next_ref(&self) -> bool {
        self.expr_any(|e| {
            matches!(
                e,
                Expression::UnaryOperation(
                    _,
                    UnaryOperation {
                        op: UnaryOperator::Next,
                        ..
                    }
                )
            )
        })
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Default, Clone)]
pub struct PolynomialName {
    pub name: String,
    pub array_size: Option<Expression>,
}

#[derive(Debug, PartialEq, Eq, Default, Clone, PartialOrd, Ord)]
/// A polynomial with an optional namespace
/// This is different from SymbolPath mainly due to different formatting.
pub struct NamespacedPolynomialReference {
    pub path: SymbolPath,
    pub type_args: Option<Vec<Type<Expression>>>,
}

impl From<SymbolPath> for NamespacedPolynomialReference {
    fn from(value: SymbolPath) -> Self {
        Self {
            path: value,
            type_args: Default::default(),
        }
    }
}

impl NamespacedPolynomialReference {
    pub fn from_identifier(name: String) -> Self {
        SymbolPath::from_parts(vec![Part::Named(name)]).into()
    }

    pub fn try_to_identifier(&self) -> Option<&String> {
        if self.type_args.is_none() {
            self.path.try_to_identifier()
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema)]
pub struct LambdaExpression<E = Expression<NamespacedPolynomialReference>> {
    pub kind: FunctionKind,
    pub params: Vec<Pattern>,
    pub body: Box<E>,
    /// The IDs of the variables outside the functions that are referenced,
    /// i.e. the environment that is captured by the closure.
    /// This is filled in by the expression processor.
    #[schemars(skip)]
    pub outer_var_references: BTreeSet<u64>,
}

impl<Ref> From<LambdaExpression<Expression<Ref>>> for Expression<Ref> {
    fn from(lambda: LambdaExpression<Expression<Ref>>) -> Self {
        Expression::LambdaExpression(SourceRef::unknown(), lambda)
    }
}

impl<E> Children<E> for LambdaExpression<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(once(self.body.as_ref()))
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(once(self.body.as_mut()))
    }
}

#[derive(
    Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema,
)]
pub enum FunctionKind {
    Pure,
    Constr,
    Query,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema)]
pub struct ArrayLiteral<E = Expression<NamespacedPolynomialReference>> {
    pub items: Vec<E>,
}

impl<Ref> From<ArrayLiteral<Expression<Ref>>> for Expression<Ref> {
    fn from(array: ArrayLiteral<Expression<Ref>>) -> Self {
        Expression::ArrayLiteral(SourceRef::unknown(), array)
    }
}

impl<E> Children<E> for ArrayLiteral<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(self.items.iter())
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(self.items.iter_mut())
    }
}

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Serialize, Deserialize, JsonSchema,
)]
pub enum UnaryOperator {
    Minus,
    LogicalNot,
    Next,
}

impl UnaryOperator {
    /// Returns true if the operator is a prefix-operator and false if it is a postfix operator.
    pub fn is_prefix(&self) -> bool {
        match self {
            UnaryOperator::Minus | UnaryOperator::LogicalNot => true,
            UnaryOperator::Next => false,
        }
    }
}

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Serialize, Deserialize, JsonSchema,
)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    BinaryAnd,
    BinaryXor,
    BinaryOr,
    ShiftLeft,
    ShiftRight,
    LogicalOr,
    LogicalAnd,
    Less,
    LessEqual,
    Equal,
    Identity,
    NotEqual,
    GreaterEqual,
    Greater,
}

#[derive(Debug, PartialEq, Eq)]
pub enum BinaryOperatorAssociativity {
    Left,
    Right,
    RequireParentheses,
}

trait Precedence {
    fn precedence(&self) -> Option<ExpressionPrecedence>;
}

impl Precedence for UnaryOperator {
    fn precedence(&self) -> Option<ExpressionPrecedence> {
        use UnaryOperator::*;
        let precedence = match self {
            // NOTE: Any modification must be done with care to not overlap with BinaryOperator's precedence
            Next => 1,
            Minus | LogicalNot => 2,
        };

        Some(precedence)
    }
}

impl Precedence for BinaryOperator {
    fn precedence(&self) -> Option<ExpressionPrecedence> {
        use BinaryOperator::*;
        let precedence = match self {
            // NOTE: Any modification must be done with care to not overlap with LambdaExpression's precedence
            // Unary Oprators
            // **
            Pow => 3,
            // * / %
            Mul | Div | Mod => 4,
            // + -
            Add | Sub => 5,
            // << >>
            ShiftLeft | ShiftRight => 6,
            // &
            BinaryAnd => 7,
            // ^
            BinaryXor => 8,
            // |
            BinaryOr => 9,
            // = == != < > <= >=
            Identity | Equal | NotEqual | Less | Greater | LessEqual | GreaterEqual => 10,
            // &&
            LogicalAnd => 11,
            // ||
            LogicalOr => 12,
            // .. ..=
            // ??
        };

        Some(precedence)
    }
}

impl<E> Precedence for Expression<E> {
    fn precedence(&self) -> Option<ExpressionPrecedence> {
        match self {
            Expression::UnaryOperation(_, operation) => operation.op.precedence(),
            Expression::BinaryOperation(_, operation) => operation.op.precedence(),
            _ => None,
        }
    }
}

impl BinaryOperator {
    pub fn associativity(&self) -> BinaryOperatorAssociativity {
        use BinaryOperator::*;
        use BinaryOperatorAssociativity::*;
        match self {
            Identity | Equal | NotEqual | Less | Greater | LessEqual | GreaterEqual => {
                RequireParentheses
            }
            Pow => Right,

            // .. ..= => RequireParentheses,
            _ => Left,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct IndexAccess<E = Expression<NamespacedPolynomialReference>> {
    pub array: Box<E>,
    pub index: Box<E>,
}

impl<Ref> From<IndexAccess<Expression<Ref>>> for Expression<Ref> {
    fn from(ia: IndexAccess<Expression<Ref>>) -> Self {
        Expression::IndexAccess(SourceRef::unknown(), ia)
    }
}

impl<E> Children<E> for IndexAccess<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(once(self.array.as_ref()).chain(once(self.index.as_ref())))
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(once(self.array.as_mut()).chain(once(self.index.as_mut())))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct FunctionCall<E = Expression<NamespacedPolynomialReference>> {
    pub function: Box<E>,
    pub arguments: Vec<E>,
}

impl<Ref> From<FunctionCall<Expression<Ref>>> for Expression<Ref> {
    fn from(call: FunctionCall<Expression<Ref>>) -> Self {
        Expression::FunctionCall(SourceRef::unknown(), call)
    }
}

impl<E> Children<E> for FunctionCall<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(once(self.function.as_ref()).chain(self.arguments.iter()))
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(once(self.function.as_mut()).chain(self.arguments.iter_mut()))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct MatchArm<E = Expression<NamespacedPolynomialReference>> {
    pub pattern: Pattern,
    pub value: E,
}

impl<E> Children<E> for MatchArm<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(once(&self.value))
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(once(&mut self.value))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct IfExpression<E = Expression<NamespacedPolynomialReference>> {
    pub condition: Box<E>,
    pub body: Box<E>,
    pub else_body: Box<E>,
}

impl<Ref> From<IfExpression<Expression<Ref>>> for Expression<Ref> {
    fn from(ifexpr: IfExpression<Expression<Ref>>) -> Self {
        Expression::IfExpression(SourceRef::unknown(), ifexpr)
    }
}

impl<E> Children<E> for IfExpression<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(
            once(&self.condition)
                .chain(once(&self.body))
                .chain(once(&self.else_body))
                .map(|e| e.as_ref()),
        )
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(
            once(&mut self.condition)
                .chain(once(&mut self.body))
                .chain(once(&mut self.else_body))
                .map(|e| e.as_mut()),
        )
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub enum StatementInsideBlock<E = Expression<NamespacedPolynomialReference>> {
    LetStatement(LetStatementInsideBlock<E>),
    Expression(E),
}

impl<E> Children<E> for StatementInsideBlock<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        match self {
            StatementInsideBlock::LetStatement(l) => Box::new(l.children()),
            StatementInsideBlock::Expression(e) => Box::new(once(e)),
        }
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        match self {
            StatementInsideBlock::LetStatement(l) => Box::new(l.children_mut()),
            StatementInsideBlock::Expression(e) => Box::new(once(e)),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct LetStatementInsideBlock<E = Expression<NamespacedPolynomialReference>> {
    pub pattern: Pattern,
    pub ty: Option<Type<u64>>,
    pub value: Option<E>,
}

impl<E> Children<E> for LetStatementInsideBlock<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(self.value.iter())
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(self.value.iter_mut())
    }
}

/// The definition of a function (excluding its name):
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum FunctionDefinition {
    /// Generic expression
    Expression(Expression),
    /// A type declaration.
    TypeDeclaration(EnumDeclaration<Expression>),
    /// A trait declaration.
    TraitDeclaration(TraitDeclaration<Expression>),
}

impl From<Expression> for FunctionDefinition {
    fn from(value: Expression) -> Self {
        Self::Expression(value)
    }
}

impl Children<Expression> for FunctionDefinition {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        match self {
            FunctionDefinition::Expression(e) => Box::new(once(e)),
            FunctionDefinition::TypeDeclaration(_enum_declaration) => todo!(),
            FunctionDefinition::TraitDeclaration(trait_declaration) => trait_declaration.children(),
        }
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        match self {
            FunctionDefinition::Expression(e) => Box::new(once(e)),
            FunctionDefinition::TypeDeclaration(_enum_declaration) => todo!(),
            FunctionDefinition::TraitDeclaration(trait_declaration) => {
                trait_declaration.children_mut()
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub enum Pattern {
    CatchAll(SourceRef), // "_", matches a single value
    Ellipsis(SourceRef), // "..", matches a series of values, only valid inside array patterns
    #[schemars(skip)]
    Number(SourceRef, BigInt),
    String(SourceRef, String),
    Tuple(SourceRef, Vec<Pattern>),
    Array(SourceRef, Vec<Pattern>),
    // A pattern that binds a variable. Variable references are parsed as
    // Enum and are then re-mapped to Variable if they do not reference
    // an enum variant.
    Variable(SourceRef, String),
    Enum(SourceRef, SymbolPath, Option<Vec<Pattern>>),
}

impl Pattern {
    /// Returns an iterator over all variables in this pattern.
    pub fn variables(&self) -> Box<dyn Iterator<Item = &String> + '_> {
        match self {
            Pattern::Variable(_, v) => Box::new(once(v)),
            _ => Box::new(self.children().flat_map(|p| p.variables())),
        }
    }

    /// Return true if the pattern is irrefutable, i.e. matches all possible values of its type.
    pub fn is_irrefutable(&self) -> bool {
        match self {
            Pattern::Ellipsis(_) => unreachable!(),
            Pattern::CatchAll(_) | Pattern::Variable(_, _) => true,
            Pattern::Number(_, _) | Pattern::String(_, _) | Pattern::Enum(_, _, _) => false,
            Pattern::Array(_, items) => {
                // Only "[..]"" is irrefutable
                matches!(&items[..], [Pattern::Ellipsis(_)])
            }
            Pattern::Tuple(_, p) => p.iter().all(|p| p.is_irrefutable()),
        }
    }
}

impl Children<Pattern> for Pattern {
    fn children(&self) -> Box<dyn Iterator<Item = &Pattern> + '_> {
        match self {
            Pattern::CatchAll(_)
            | Pattern::Ellipsis(_)
            | Pattern::Number(_, _)
            | Pattern::String(_, _)
            | Pattern::Variable(_, _) => Box::new(empty()),
            Pattern::Tuple(_, p) | Pattern::Array(_, p) => Box::new(p.iter()),
            Pattern::Enum(_, _, fields) => Box::new(fields.iter().flatten()),
        }
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Pattern> + '_> {
        match self {
            Pattern::CatchAll(_)
            | Pattern::Ellipsis(_)
            | Pattern::Number(_, _)
            | Pattern::String(_, _)
            | Pattern::Variable(_, _) => Box::new(empty()),
            Pattern::Tuple(_, p) | Pattern::Array(_, p) => Box::new(p.iter_mut()),
            Pattern::Enum(_, _, fields) => Box::new(fields.iter_mut().flatten()),
        }
    }
}

impl SourceReference for Pattern {
    fn source_reference(&self) -> &SourceRef {
        match self {
            Pattern::CatchAll(s)
            | Pattern::Ellipsis(s)
            | Pattern::Number(s, _)
            | Pattern::String(s, _)
            | Pattern::Variable(s, _)
            | Pattern::Tuple(s, _)
            | Pattern::Array(s, _)
            | Pattern::Enum(s, _, _) => s,
        }
    }
    fn source_reference_mut(&mut self) -> &mut SourceRef {
        match self {
            Pattern::CatchAll(s)
            | Pattern::Ellipsis(s)
            | Pattern::Number(s, _)
            | Pattern::String(s, _)
            | Pattern::Variable(s, _)
            | Pattern::Tuple(s, _)
            | Pattern::Array(s, _)
            | Pattern::Enum(s, _, _) => s,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct TypedExpression<Ref = NamespacedPolynomialReference, E = Expression<Ref>> {
    pub e: Expression<Ref>,
    pub type_scheme: Option<TypeScheme<E>>,
}

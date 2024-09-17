mod display;
pub mod visitor;

use std::cmp::max;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::iter::{self, empty};
use std::ops::{self, ControlFlow};
use std::sync::Arc;

use itertools::Itertools;
use powdr_number::{DegreeType, FieldElement};
use powdr_parser_util::SourceRef;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::parsed::types::{ArrayType, Type, TypeBounds, TypeScheme};
use crate::parsed::visitor::{Children, ExpressionVisitable};
pub use crate::parsed::BinaryOperator;
pub use crate::parsed::UnaryOperator;
use crate::parsed::{
    self, ArrayExpression, ArrayLiteral, EnumDeclaration, EnumVariant, StructDeclaration,
    TraitDeclaration, TraitFunction,
};

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub enum StatementIdentifier {
    /// Either an intermediate column or a definition.
    Definition(String),
    PublicDeclaration(String),
    /// Index into the vector of identities.
    Identity(usize),
    /// Index into the vector of prover functions.
    ProverFunction(usize),
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, JsonSchema)]
pub struct Analyzed<T> {
    pub definitions: HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
    pub solved_impls: HashMap<String, HashMap<Vec<Type>, Arc<Expression>>>,
    pub public_declarations: HashMap<String, PublicDeclaration>,
    pub intermediate_columns: HashMap<String, (Symbol, Vec<AlgebraicExpression<T>>)>,
    pub identities: Vec<Identity<SelectedExpressions<AlgebraicExpression<T>>>>,
    pub prover_functions: Vec<Expression>,
    /// The order in which definitions and identities
    /// appear in the source.
    pub source_order: Vec<StatementIdentifier>,
    /// Symbols from the core that were added automatically but will not be printed.
    pub auto_added_symbols: HashSet<String>,
}

impl<T> Analyzed<T> {
    /// Returns the degree common among all symbols that have an explicit degree.
    ///
    /// # Panics
    ///
    /// Panics if there is no common degree or if there are no symbols
    pub fn degree(&self) -> DegreeType {
        self.definitions
            .values()
            .filter_map(|(symbol, _)| symbol.degree)
            .unique()
            .exactly_one()
            .unwrap()
            .try_into_unique()
            .unwrap()
    }

    pub fn degree_ranges(&self) -> HashSet<DegreeRange> {
        self.definitions
            .values()
            .filter_map(|(symbol, _)| symbol.degree)
            .collect::<HashSet<_>>()
    }

    /// Returns the set of all explicit degrees in this [`Analyzed<T>`].
    pub fn degrees(&self) -> HashSet<DegreeType> {
        self.definitions
            .values()
            .filter_map(|(symbol, _)| symbol.degree)
            .map(|d| d.try_into_unique().unwrap())
            .collect::<HashSet<_>>()
    }

    /// @returns the number of committed polynomials (with multiplicities for arrays)
    pub fn commitment_count(&self) -> usize {
        self.declaration_type_count(PolynomialType::Committed)
    }
    /// @returns the number of intermediate polynomials (with multiplicities for arrays)
    pub fn intermediate_count(&self) -> usize {
        self.intermediate_columns
            .iter()
            .map(|(_, (sym, _))| sym.length.unwrap_or(1) as usize)
            .sum()
    }
    /// @returns the number of constant polynomials (with multiplicities for arrays)
    pub fn constant_count(&self) -> usize {
        self.declaration_type_count(PolynomialType::Constant)
    }
    /// @returns the number of public inputs
    pub fn publics_count(&self) -> usize {
        self.public_declarations.len()
    }

    pub fn constant_polys_in_source_order(
        &self,
    ) -> Vec<&(Symbol, Option<FunctionValueDefinition>)> {
        self.definitions_in_source_order(PolynomialType::Constant)
    }

    pub fn committed_polys_in_source_order(
        &self,
    ) -> Vec<&(Symbol, Option<FunctionValueDefinition>)> {
        self.definitions_in_source_order(PolynomialType::Committed)
    }

    pub fn intermediate_polys_in_source_order(
        &self,
    ) -> Vec<&(Symbol, Vec<AlgebraicExpression<T>>)> {
        self.source_order
            .iter()
            .filter_map(move |statement| {
                if let StatementIdentifier::Definition(name) = statement {
                    if let Some(definition) = self.intermediate_columns.get(name) {
                        return Some(definition);
                    }
                }
                None
            })
            .collect()
    }

    pub fn definitions_in_source_order(
        &self,
        poly_type: PolynomialType,
    ) -> Vec<&(Symbol, Option<FunctionValueDefinition>)> {
        assert!(
            poly_type != PolynomialType::Intermediate,
            "Use intermediate_polys_in_source_order to get intermediate polys."
        );
        self.source_order
            .iter()
            .filter_map(move |statement| {
                if let StatementIdentifier::Definition(name) = statement {
                    if let Some(definition) = self.definitions.get(name) {
                        match definition.0.kind {
                            SymbolKind::Poly(ptype) if ptype == poly_type => {
                                return Some(definition);
                            }
                            _ => {}
                        }
                    }
                }
                None
            })
            .collect()
    }

    pub fn public_declarations_in_source_order(&self) -> Vec<(&String, &PublicDeclaration)> {
        self.source_order
            .iter()
            .filter_map(move |statement| {
                if let StatementIdentifier::PublicDeclaration(name) = statement {
                    if let Some(public_declaration) = self.public_declarations.get(name) {
                        return Some((name, public_declaration));
                    }
                }
                None
            })
            .collect()
    }

    fn declaration_type_count(&self, poly_type: PolynomialType) -> usize {
        self.definitions
            .iter()
            .filter_map(move |(_name, (symbol, _))| match symbol.kind {
                SymbolKind::Poly(ptype) if ptype == poly_type => {
                    Some(symbol.length.unwrap_or(1) as usize)
                }
                _ => None,
            })
            .sum()
    }

    /// Returns the type (scheme) of a symbol with the given name.
    pub fn type_of_symbol(&self, name: &str) -> TypeScheme {
        let (sym, value) = &self.definitions[name];
        type_from_definition(sym, value).unwrap()
    }

    /// Adds a polynomial identity and returns the ID.
    pub fn append_polynomial_identity(
        &mut self,
        identity: AlgebraicExpression<T>,
        source: SourceRef,
    ) -> u64 {
        let id = self
            .identities
            .iter()
            .map(|identity| identity.id)
            .max()
            .unwrap_or_default()
            + 1;
        self.identities.push(
            Identity::<SelectedExpressions<AlgebraicExpression<T>>>::from_polynomial_identity(
                id, source, identity,
            ),
        );
        self.source_order
            .push(StatementIdentifier::Identity(self.identities.len() - 1));
        id
    }

    /// Remove some identities by their index (not their ID).
    /// Does not re-allocate IDs.
    pub fn remove_identities(&mut self, to_remove: &BTreeSet<usize>) {
        let mut shift = 0;
        self.source_order.retain_mut(|s| {
            if let StatementIdentifier::Identity(index) = s {
                if to_remove.contains(index) {
                    shift += 1;
                    return false;
                }
                *index -= shift;
            }
            true
        });
        let mut index = 0;
        self.identities.retain(|_| {
            let retain = !to_remove.contains(&index);
            index += 1;
            retain
        })
    }

    /// Removes the given definitions and intermediate columns by name. Those must not be referenced
    /// by any remaining definitions, identities or public declarations.
    pub fn remove_definitions(&mut self, to_remove: &BTreeSet<String>) {
        self.definitions.retain(|name, _| !to_remove.contains(name));
        self.intermediate_columns
            .retain(|name, _| !to_remove.contains(name));
        self.source_order.retain_mut(|s| {
            if let StatementIdentifier::Definition(name) = s {
                !to_remove.contains(name)
            } else {
                true
            }
        });

        // Now re-assign the IDs to be contiguous and in source order again.
        let mut replacements: BTreeMap<PolyID, PolyID> = Default::default();

        let mut handle_symbol = |new_id: u64, symbol: &Symbol| -> u64 {
            let length = symbol.length.unwrap_or(1);
            // Empty arrays still need ID replacement
            for i in 0..max(length, 1) {
                let old_poly_id = PolyID {
                    id: symbol.id + i,
                    ..PolyID::from(symbol)
                };
                let new_poly_id = PolyID {
                    id: new_id + i,
                    ..PolyID::from(symbol)
                };
                replacements.insert(old_poly_id, new_poly_id);
            }
            new_id + length
        };

        // Create and update the replacement map for all polys.
        self.committed_polys_in_source_order()
            .iter()
            .fold(0, |new_id, (poly, _def)| handle_symbol(new_id, poly));
        self.constant_polys_in_source_order()
            .iter()
            .fold(0, |new_id, (poly, _def)| handle_symbol(new_id, poly));
        self.intermediate_polys_in_source_order()
            .iter()
            .fold(0, |new_id, (poly, _def)| handle_symbol(new_id, poly));

        self.definitions.values_mut().for_each(|(poly, _def)| {
            if matches!(poly.kind, SymbolKind::Poly(_)) {
                let poly_id = PolyID::from(poly as &Symbol);
                poly.id = replacements[&poly_id].id;
            }
        });
        self.intermediate_columns
            .values_mut()
            .for_each(|(poly, _def)| {
                let poly_id = PolyID::from(poly as &Symbol);
                poly.id = replacements[&poly_id].id;
            });
        let algebraic_visitor = &mut |expr: &mut AlgebraicExpression<_>| {
            if let AlgebraicExpression::Reference(poly) = expr {
                poly.poly_id = replacements[&poly.poly_id];
            }
        };
        self.post_visit_expressions_in_identities_mut(algebraic_visitor);
    }

    pub fn post_visit_expressions_in_identities_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut AlgebraicExpression<T>),
    {
        self.identities
            .iter_mut()
            .for_each(|i| i.post_visit_expressions_mut(f));
        self.intermediate_columns
            .values_mut()
            .for_each(|(_sym, value)| {
                value
                    .iter_mut()
                    .for_each(|v| v.post_visit_expressions_mut(f))
            });
    }

    pub fn post_visit_expressions_in_definitions_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Expression),
    {
        // TODO add public inputs if we change them to expressions at some point.
        self.definitions
            .values_mut()
            .filter_map(|(_poly, definition)| definition.as_mut())
            .for_each(|definition| definition.post_visit_expressions_mut(f))
    }

    /// Retrieves (col_name, col_idx, offset) of each public witness in the trace.
    pub fn get_publics(&self) -> Vec<(String, usize, usize)> {
        let mut publics = self
            .public_declarations
            .values()
            .map(|public_declaration| {
                let column_name = public_declaration.referenced_poly_name();
                let column_idx = {
                    let base = self.definitions[&public_declaration.polynomial.name].0.id;
                    match public_declaration.array_index {
                        Some(array_idx) => base + array_idx as u64,
                        None => base,
                    }
                };
                let row_offset = public_declaration.index as usize;
                (column_name, column_idx as usize, row_offset)
            })
            .collect::<Vec<_>>();

        // Sort, so that the order is deterministic
        publics.sort();
        publics
    }
}

impl<T: FieldElement> Analyzed<T> {
    /// @returns all identities with intermediate polynomials inlined.
    pub fn identities_with_inlined_intermediate_polynomials(
        &self,
    ) -> Vec<Identity<SelectedExpressions<AlgebraicExpression<T>>>> {
        let intermediates = &self
            .intermediate_polys_in_source_order()
            .iter()
            .flat_map(|(symbol, def)| {
                symbol
                    .array_elements()
                    .zip(def)
                    .map(|((_, poly_id), def)| (poly_id, def))
            })
            .collect();

        substitute_intermediate(self.identities.clone(), intermediates)
    }

    pub fn get_struct_schema() -> schemars::schema::RootSchema {
        schemars::schema_for!(Self)
    }

    pub fn serialize(&self) -> Result<Vec<u8>, String> {
        serde_cbor::to_vec(self).map_err(|e| format!("Failed to serialize analyzed: {e}"))
    }

    pub fn deserialize(bytes: &[u8]) -> Result<Self, String> {
        serde_cbor::from_slice(bytes).map_err(|e| format!("Failed to deserialize analyzed: {e}"))
    }
}

/// Takes identities as values and inlines intermediate polynomials everywhere, returning a vector of the updated identities
/// TODO: this could return an iterator
fn substitute_intermediate<T: Copy + Display>(
    identities: impl IntoIterator<Item = Identity<SelectedExpressions<AlgebraicExpression<T>>>>,
    intermediate_polynomials: &HashMap<PolyID, &AlgebraicExpression<T>>,
) -> Vec<Identity<SelectedExpressions<AlgebraicExpression<T>>>> {
    identities
        .into_iter()
        .scan(HashMap::default(), |cache, mut identity| {
            identity.post_visit_expressions_mut(&mut |e| {
                if let AlgebraicExpression::Reference(poly) = e {
                    match poly.poly_id.ptype {
                        PolynomialType::Committed => {}
                        PolynomialType::Constant => {}
                        PolynomialType::Intermediate => {
                            // recursively inline intermediate polynomials, updating the cache
                            *e = inlined_expression_from_intermediate_poly_id(
                                poly.clone(),
                                intermediate_polynomials,
                                cache,
                            );
                        }
                    }
                }
            });
            Some(identity)
        })
        .collect()
}

/// Recursively inlines intermediate polynomials inside an expression and returns the new expression
/// This uses a cache to avoid resolving an intermediate polynomial twice
///
/// poly_to_replace can be a "next" reference, but then its value cannot contain any next references.
fn inlined_expression_from_intermediate_poly_id<T: Copy + Display>(
    poly_to_replace: AlgebraicReference,
    intermediate_polynomials: &HashMap<PolyID, &AlgebraicExpression<T>>,
    cache: &mut HashMap<AlgebraicReference, AlgebraicExpression<T>>,
) -> AlgebraicExpression<T> {
    assert_eq!(poly_to_replace.poly_id.ptype, PolynomialType::Intermediate);
    if let Some(e) = cache.get(&poly_to_replace) {
        return e.clone();
    }
    let mut expr = intermediate_polynomials[&poly_to_replace.poly_id].clone();
    expr.post_visit_expressions_mut(&mut |e| {
        let AlgebraicExpression::Reference(r) = e else { return; };
        // "forward" the next operator from the polynomial to be replaced.
        if poly_to_replace.next && r.next {
            let value = intermediate_polynomials[&poly_to_replace.poly_id];
            panic!(
                "Error inlining intermediate polynomial {poly_to_replace} = ({value})':\nNext operator already applied to {} and then again to {} - cannot apply it twice!",
                r.name,
                poly_to_replace.name
            );
        }
        r.next = r.next || poly_to_replace.next;
        match r.poly_id.ptype {
            PolynomialType::Committed | PolynomialType::Constant => {}
            PolynomialType::Intermediate => {
                *e = inlined_expression_from_intermediate_poly_id(
                    r.clone(),
                    intermediate_polynomials,
                    cache,
                );
            }
        }
    });
    cache.insert(poly_to_replace, expr.clone());
    expr
}

/// Extracts the declared (or implicit) type from a definition.
pub fn type_from_definition(
    symbol: &Symbol,
    value: &Option<FunctionValueDefinition>,
) -> Option<TypeScheme> {
    if let Some(value) = value {
        match value {
            FunctionValueDefinition::Array(_) => Some(Type::Col.into()),
            FunctionValueDefinition::Expression(TypedExpression { e: _, type_scheme }) => {
                type_scheme.clone()
            }
            FunctionValueDefinition::TypeDeclaration(_) => {
                panic!("Requested type of type declaration.")
            }
            FunctionValueDefinition::TypeConstructor(TypeConstructor::Enum(enum_decl, variant)) => {
                Some(variant.constructor_type(enum_decl))
            }
            FunctionValueDefinition::TypeConstructor(TypeConstructor::Struct(
                struct_decl,
                field,
            )) => Some(TypeScheme {
                vars: struct_decl.type_vars.clone(),
                ty: field.1.clone(),
            }),
            FunctionValueDefinition::TraitDeclaration(_) => {
                panic!("Requested type of trait declaration.")
            }
            FunctionValueDefinition::TraitFunction(trait_decl, trait_func) => {
                let vars = trait_decl
                    .type_vars
                    .iter()
                    .map(|var| {
                        let bounds = BTreeSet::new();
                        (var.clone(), bounds)
                    })
                    .collect::<Vec<_>>();

                Some(TypeScheme {
                    vars: TypeBounds::new(vars.into_iter()),
                    ty: trait_func.ty.clone(),
                })
            }
        }
    } else {
        assert!(
            symbol.kind == SymbolKind::Poly(PolynomialType::Committed)
                || symbol.kind == SymbolKind::Poly(PolynomialType::Constant)
        );
        if symbol.length.is_some() {
            Some(
                Type::Array(ArrayType {
                    base: Box::new(Type::Col),
                    length: None,
                })
                .into(),
            )
        } else {
            Some(Type::Col.into())
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Serialize, Deserialize, JsonSchema, Copy)]
pub struct DegreeRange {
    pub min: DegreeType,
    pub max: DegreeType,
}

impl From<DegreeType> for DegreeRange {
    fn from(value: DegreeType) -> Self {
        Self {
            min: value,
            max: value,
        }
    }
}

impl DegreeRange {
    pub fn try_into_unique(self) -> Option<DegreeType> {
        (self.min == self.max).then_some(self.min)
    }

    /// Iterate through powers of two in this range
    pub fn iter(&self) -> impl Iterator<Item = DegreeType> {
        let min_ceil = self.min.next_power_of_two();
        let max_ceil = self.max.next_power_of_two();
        let min_log = usize::BITS - min_ceil.leading_zeros() - 1;
        let max_log = usize::BITS - max_ceil.leading_zeros() - 1;
        (min_log..=max_log).map(|exponent| 1 << exponent)
    }

    /// Fit a degree to this range:
    /// - returns the smallest value in the range which is larger or equal to `new_degree`
    /// - panics if no such value exists
    pub fn fit(&self, new_degree: u64) -> u64 {
        assert!(new_degree <= self.max);
        self.min.max(new_degree)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct Symbol {
    pub id: u64,
    pub source: SourceRef,
    pub absolute_name: String,
    pub stage: Option<u32>,
    pub kind: SymbolKind,
    pub length: Option<u64>,
    pub degree: Option<DegreeRange>,
}

impl Symbol {
    pub fn is_array(&self) -> bool {
        self.length.is_some()
    }
    /// Returns an iterator producing either just the symbol (if it is not an array),
    /// or all the elements of the array with their names in the form `array[index]`.
    pub fn array_elements(&self) -> impl Iterator<Item = (String, PolyID)> + '_ {
        let SymbolKind::Poly(ptype) = self.kind else {
            panic!("Expected polynomial.");
        };
        let length = self.length.unwrap_or(1);
        (0..length).map(move |i| {
            (
                self.array_element_name(i),
                PolyID {
                    id: self.id + i,
                    ptype,
                },
            )
        })
    }

    /// Returns "name[index]" if this is an array or just "name" otherwise.
    /// In the second case, requires index to be zero and otherwise
    /// requires index to be less than length.
    pub fn array_element_name(&self, index: u64) -> String {
        match self.length {
            Some(length) => {
                assert!(index < length);
                format!("{}[{index}]", self.absolute_name)
            }
            None => self.absolute_name.to_string(),
        }
    }

    /// Returns "name[length]" if this is an array or just "name" otherwise.
    pub fn array_name(&self) -> String {
        match self.length {
            Some(length) => {
                format!("{}[{length}]", self.absolute_name)
            }
            None => self.absolute_name.to_string(),
        }
    }
}

/// The "kind" of a symbol. In the future, this will be mostly
/// replaced by its type.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema,
)]
pub enum SymbolKind {
    /// Fixed, witness or intermediate polynomial
    Poly(PolynomialType),
    /// Other symbol, depends on the type.
    /// Examples include functions not of the type "int -> fe".
    Other(),
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub enum FunctionValueDefinition {
    Array(ArrayExpression<Reference>),
    Expression(TypedExpression),
    TypeDeclaration(TypeDeclaration),
    TypeConstructor(TypeConstructor),
    TraitDeclaration(TraitDeclaration),
    TraitFunction(Arc<TraitDeclaration>, TraitFunction),
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub enum TypeDeclaration {
    Enum(EnumDeclaration),
    Struct(StructDeclaration),
}

impl Children<Expression> for TypeDeclaration {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        match self {
            TypeDeclaration::Enum(enum_decl) => enum_decl.children(),
            TypeDeclaration::Struct(struct_decl) => struct_decl.children(),
        }
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        match self {
            TypeDeclaration::Enum(enum_decl) => enum_decl.children_mut(),
            TypeDeclaration::Struct(struct_decl) => struct_decl.children_mut(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub enum TypeConstructor {
    Enum(Arc<EnumDeclaration>, EnumVariant),
    Struct(Arc<StructDeclaration>, (String, Type)),
}

impl Children<Expression> for TypeConstructor {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        match self {
            TypeConstructor::Enum(_, variant) => variant.children(),
            TypeConstructor::Struct(_, _) => Box::new(empty()),
        }
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        match self {
            TypeConstructor::Enum(_, variant) => variant.children_mut(),
            TypeConstructor::Struct(_, _) => Box::new(empty()),
        }
    }
}

impl Children<Expression> for FunctionValueDefinition {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        match self {
            FunctionValueDefinition::Expression(TypedExpression { e, type_scheme: _ }) => {
                Box::new(iter::once(e))
            }
            FunctionValueDefinition::Array(e) => e.children(),
            FunctionValueDefinition::TypeDeclaration(enum_declaration) => {
                enum_declaration.children()
            }
            FunctionValueDefinition::TypeConstructor(type_constructor) => {
                type_constructor.children()
            }
            FunctionValueDefinition::TraitDeclaration(trait_decl) => trait_decl.children(),
            FunctionValueDefinition::TraitFunction(_, trait_func) => trait_func.children(),
        }
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        match self {
            FunctionValueDefinition::Expression(TypedExpression { e, type_scheme: _ }) => {
                Box::new(iter::once(e))
            }
            FunctionValueDefinition::Array(e) => e.children_mut(),
            FunctionValueDefinition::TypeDeclaration(enum_declaration) => {
                enum_declaration.children_mut()
            }
            FunctionValueDefinition::TypeConstructor(type_constructor) => {
                type_constructor.children_mut()
            }
            FunctionValueDefinition::TraitDeclaration(trait_decl) => trait_decl.children_mut(),
            FunctionValueDefinition::TraitFunction(_, trait_func) => trait_func.children_mut(),
        }
    }
}

impl Children<Expression> for TraitDeclaration {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        Box::new(empty())
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        Box::new(empty())
    }
}

impl Children<Expression> for TraitFunction {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        Box::new(empty())
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        Box::new(empty())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct PublicDeclaration {
    pub id: u64,
    pub source: SourceRef,
    pub name: String,
    pub polynomial: PolynomialReference,
    pub array_index: Option<usize>,
    /// The evaluation point of the polynomial, not the array index.
    pub index: DegreeType,
}

impl PublicDeclaration {
    pub fn referenced_poly_name(&self) -> String {
        match self.array_index {
            Some(index) => format!("{}[{}]", self.polynomial.name, index),
            None => self.polynomial.name.clone(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct SelectedExpressions<Expr> {
    pub selector: Option<Expr>,
    pub expressions: Vec<Expr>,
}

impl<Expr> Default for SelectedExpressions<Expr> {
    fn default() -> Self {
        Self {
            selector: Default::default(),
            expressions: vec![],
        }
    }
}

impl<Expr> Children<Expr> for SelectedExpressions<Expr> {
    /// Returns an iterator over all (top-level) expressions in this SelectedExpressions.
    fn children(&self) -> Box<dyn Iterator<Item = &Expr> + '_> {
        Box::new(self.selector.iter().chain(self.expressions.iter()))
    }
    /// Returns an iterator over all (top-level) expressions in this SelectedExpressions.
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expr> + '_> {
        Box::new(self.selector.iter_mut().chain(self.expressions.iter_mut()))
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize, JsonSchema)]
pub struct Identity<SelectedExpressions> {
    /// The ID is globally unique among identities.
    pub id: u64,
    pub kind: IdentityKind,
    pub source: SourceRef,
    /// For a simple polynomial identity, the selector contains
    /// the actual expression (see expression_for_poly_id).
    pub left: SelectedExpressions,
    pub right: SelectedExpressions,
}

impl<T> Identity<SelectedExpressions<AlgebraicExpression<T>>> {
    /// Constructs an Identity from a polynomial identity (expression assumed to be identical zero).
    pub fn from_polynomial_identity(
        id: u64,
        source: SourceRef,
        identity: AlgebraicExpression<T>,
    ) -> Self {
        Identity {
            id,
            kind: IdentityKind::Polynomial,
            source,
            left: SelectedExpressions {
                selector: Some(identity),
                expressions: vec![],
            },
            right: SelectedExpressions {
                selector: Default::default(),
                expressions: vec![],
            },
        }
    }
    /// Returns the expression in case this is a polynomial identity.
    pub fn expression_for_poly_id(&self) -> &AlgebraicExpression<T> {
        assert_eq!(self.kind, IdentityKind::Polynomial);
        self.left.selector.as_ref().unwrap()
    }

    /// Returns the expression in case this is a polynomial identity.
    pub fn expression_for_poly_id_mut(&mut self) -> &mut AlgebraicExpression<T> {
        assert_eq!(self.kind, IdentityKind::Polynomial);
        self.left.selector.as_mut().unwrap()
    }

    pub fn contains_next_ref(&self) -> bool {
        self.left.contains_next_ref() || self.right.contains_next_ref()
    }

    /// Either returns (a, Some(b)) if this is a - b or (a, None)
    /// if it is a polynomial identity of a different structure.
    /// Panics if it is a different kind of constraint.
    pub fn as_polynomial_identity(
        &self,
    ) -> (&AlgebraicExpression<T>, Option<&AlgebraicExpression<T>>) {
        assert_eq!(self.kind, IdentityKind::Polynomial);
        match self.expression_for_poly_id() {
            AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation {
                left: a,
                op: AlgebraicBinaryOperator::Sub,
                right: b,
            }) => (a.as_ref(), Some(b.as_ref())),
            a => (a, None),
        }
    }

    pub fn degree(&self) -> usize {
        self.children().map(|e| e.degree()).max().unwrap_or(0)
    }
}

impl<R> Identity<parsed::SelectedExpressions<parsed::Expression<R>>> {
    /// Constructs an Identity from a polynomial identity (expression assumed to be identical zero).
    pub fn from_polynomial_identity(
        id: u64,
        source: SourceRef,
        identity: parsed::Expression<R>,
    ) -> Self {
        Identity {
            id,
            kind: IdentityKind::Polynomial,
            source,
            left: parsed::SelectedExpressions {
                selector: Some(identity),
                expressions: Box::new(ArrayLiteral { items: vec![] }.into()),
            },
            right: Default::default(),
        }
    }
    /// Returns the expression in case this is a polynomial identity.
    pub fn expression_for_poly_id(&self) -> &parsed::Expression<R> {
        assert_eq!(self.kind, IdentityKind::Polynomial);
        self.left.selector.as_ref().unwrap()
    }

    /// Returns the expression in case this is a polynomial identity.
    pub fn expression_for_poly_id_mut(&mut self) -> &mut parsed::Expression<R> {
        assert_eq!(self.kind, IdentityKind::Polynomial);
        self.left.selector.as_mut().unwrap()
    }
    /// Either returns (a, Some(b)) if this is a - b or (a, None)
    /// if it is a polynomial identity of a different structure.
    /// Panics if it is a different kind of constraint.
    pub fn as_polynomial_identity(
        &self,
    ) -> (&parsed::Expression<R>, Option<&parsed::Expression<R>>) {
        assert_eq!(self.kind, IdentityKind::Polynomial);
        match self.expression_for_poly_id() {
            parsed::Expression::BinaryOperation(
                _,
                parsed::BinaryOperation {
                    left,
                    op: BinaryOperator::Sub,
                    right,
                },
            ) => (left.as_ref(), Some(right.as_ref())),
            a => (a, None),
        }
    }
}

impl<T> Children<AlgebraicExpression<T>> for Identity<SelectedExpressions<AlgebraicExpression<T>>> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        Box::new(self.left.children_mut().chain(self.right.children_mut()))
    }

    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        Box::new(self.left.children().chain(self.right.children()))
    }
}

impl<R> Children<parsed::Expression<R>>
    for Identity<parsed::SelectedExpressions<parsed::Expression<R>>>
{
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut parsed::Expression<R>> + '_> {
        Box::new(self.left.children_mut().chain(self.right.children_mut()))
    }

    fn children(&self) -> Box<dyn Iterator<Item = &parsed::Expression<R>> + '_> {
        Box::new(self.left.children().chain(self.right.children()))
    }
}

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Serialize, Deserialize, JsonSchema,
)]
pub enum IdentityKind {
    Polynomial,
    Plookup,
    Permutation,
    Connect,
}

impl<T> SelectedExpressions<AlgebraicExpression<T>> {
    /// @returns true if the expression contains a reference to a next value of a
    /// (witness or fixed) column
    pub fn contains_next_ref(&self) -> bool {
        self.selector
            .iter()
            .chain(self.expressions.iter())
            .any(|e| e.contains_next_ref())
    }
}

pub type Expression = parsed::Expression<Reference>;
pub type TypedExpression = crate::parsed::TypedExpression<Reference, u64>;

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub enum Reference {
    LocalVar(u64, String),
    Poly(PolynomialReference),
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize, JsonSchema)]
pub struct AlgebraicReference {
    /// Name of the polynomial - just for informational purposes.
    /// Comparisons are based on polynomial ID.
    /// In case of an array element, this ends in `[i]`.
    pub name: String,
    /// Identifier for a polynomial reference, already contains
    /// the element offset in case of an array element.
    pub poly_id: PolyID,
    pub next: bool,
}

impl AlgebraicReference {
    #[inline]
    pub fn is_witness(&self) -> bool {
        self.poly_id.ptype == PolynomialType::Committed
    }
    #[inline]
    pub fn is_fixed(&self) -> bool {
        self.poly_id.ptype == PolynomialType::Constant
    }
}

impl PartialOrd for AlgebraicReference {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AlgebraicReference {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (&self.poly_id, &self.next).cmp(&(&other.poly_id, &other.next))
    }
}

impl PartialEq for AlgebraicReference {
    fn eq(&self, other: &Self) -> bool {
        self.poly_id == other.poly_id && self.next == other.next
    }
}

impl Hash for AlgebraicReference {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.poly_id.hash(state);
        self.next.hash(state);
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub enum AlgebraicExpression<T> {
    Reference(AlgebraicReference),
    PublicReference(String),
    Challenge(Challenge),
    Number(T),
    BinaryOperation(AlgebraicBinaryOperation<T>),
    UnaryOperation(AlgebraicUnaryOperation<T>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct AlgebraicBinaryOperation<T> {
    pub left: Box<AlgebraicExpression<T>>,
    pub op: AlgebraicBinaryOperator,
    pub right: Box<AlgebraicExpression<T>>,
}
impl<T> AlgebraicBinaryOperation<T> {
    fn new(
        left: AlgebraicExpression<T>,
        op: AlgebraicBinaryOperator,
        right: AlgebraicExpression<T>,
    ) -> Self {
        Self {
            left: Box::new(left),
            op,
            right: Box::new(right),
        }
    }
}

impl<T> From<AlgebraicBinaryOperation<T>> for AlgebraicExpression<T> {
    fn from(value: AlgebraicBinaryOperation<T>) -> Self {
        Self::BinaryOperation(value)
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct AlgebraicUnaryOperation<T> {
    pub op: AlgebraicUnaryOperator,
    pub expr: Box<AlgebraicExpression<T>>,
}
impl<T> AlgebraicUnaryOperation<T> {
    fn new(op: AlgebraicUnaryOperator, expr: AlgebraicExpression<T>) -> Self {
        Self {
            op,
            expr: Box::new(expr),
        }
    }
}

impl<T> From<AlgebraicUnaryOperation<T>> for AlgebraicExpression<T> {
    fn from(value: AlgebraicUnaryOperation<T>) -> Self {
        Self::UnaryOperation(value)
    }
}

pub type ExpressionPrecedence = u64;
trait Precedence {
    fn precedence(&self) -> Option<ExpressionPrecedence>;
}

impl Precedence for AlgebraicUnaryOperator {
    fn precedence(&self) -> Option<ExpressionPrecedence> {
        use AlgebraicUnaryOperator::*;
        let precedence = match self {
            // NOTE: Any modification must be done with care to not overlap with BinaryOperator's precedence
            Minus => 1,
        };

        Some(precedence)
    }
}

impl Precedence for AlgebraicBinaryOperator {
    fn precedence(&self) -> Option<ExpressionPrecedence> {
        use AlgebraicBinaryOperator::*;
        let precedence = match self {
            // NOTE: Any modification must be done with care to not overlap with LambdaExpression's precedence
            // Unary Oprators
            // **
            Pow => 2,
            // * / %
            Mul => 3,
            // + -
            Add | Sub => 4,
        };

        Some(precedence)
    }
}

impl<E> Precedence for AlgebraicExpression<E> {
    fn precedence(&self) -> Option<ExpressionPrecedence> {
        match self {
            AlgebraicExpression::UnaryOperation(operation) => operation.op.precedence(),
            AlgebraicExpression::BinaryOperation(operation) => operation.op.precedence(),
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum AlgebraicBinaryOperatorAssociativity {
    Left,
    Right,
    RequireParentheses,
}

impl AlgebraicBinaryOperator {
    pub fn associativity(&self) -> AlgebraicBinaryOperatorAssociativity {
        use AlgebraicBinaryOperator::*;
        use AlgebraicBinaryOperatorAssociativity::*;
        match self {
            Pow => Right,

            // .. ..= => RequireParentheses,
            _ => Left,
        }
    }
}

impl<T> AlgebraicExpression<T> {
    /// Returns an iterator over all (top-level) expressions in this expression.
    /// This specifically does not implement Children because otherwise it would
    /// have a wrong implementation of ExpressionVisitable (which is implemented
    /// generically for all types that implement Children<Expr>).
    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        match self {
            AlgebraicExpression::Reference(_)
            | AlgebraicExpression::PublicReference(_)
            | AlgebraicExpression::Challenge(_)
            | AlgebraicExpression::Number(_) => Box::new(iter::empty()),
            AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation {
                left, right, ..
            }) => Box::new([left.as_ref(), right.as_ref()].into_iter()),
            AlgebraicExpression::UnaryOperation(AlgebraicUnaryOperation { expr: e, .. }) => {
                Box::new([e.as_ref()].into_iter())
            }
        }
    }
    /// Returns an iterator over all (top-level) expressions in this expression.
    /// This specifically does not implement Children because otherwise it would
    /// have a wrong implementation of ExpressionVisitable (which is implemented
    /// generically for all types that implement Children<Expr>).
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        match self {
            AlgebraicExpression::Reference(_)
            | AlgebraicExpression::PublicReference(_)
            | AlgebraicExpression::Challenge(_)
            | AlgebraicExpression::Number(_) => Box::new(iter::empty()),
            AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation {
                left, right, ..
            }) => Box::new([left.as_mut(), right.as_mut()].into_iter()),
            AlgebraicExpression::UnaryOperation(AlgebraicUnaryOperation { expr: e, .. }) => {
                Box::new([e.as_mut()].into_iter())
            }
        }
    }

    /// Apply `'` to the expression, returning a new expression
    /// For example, `x + 1` becomes `x' + 1`
    ///
    /// # Errors
    ///
    /// If the `next` flag is already active on an `AlgebraicReference`, it is returned as an error
    pub fn next(self) -> Result<Self, AlgebraicReference> {
        use AlgebraicExpression::*;

        match self {
            Reference(r) => {
                if r.next {
                    Err(r)
                } else {
                    Ok(Self::Reference(AlgebraicReference { next: true, ..r }))
                }
            }
            e @ PublicReference(..) | e @ Challenge(..) | e @ Number(..) => Ok(e),
            BinaryOperation(AlgebraicBinaryOperation { left, op, right }) => {
                Ok(Self::new_binary(left.next()?, op, right.next()?))
            }
            UnaryOperation(AlgebraicUnaryOperation { op, expr }) => {
                Ok(Self::new_unary(op, expr.next()?))
            }
        }
    }

    /// Returns the degree of the expressions
    pub fn degree(&self) -> usize {
        match self {
            // One for each column
            AlgebraicExpression::Reference(_) => 1,
            // Multiplying two expressions adds their degrees
            AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation {
                op: AlgebraicBinaryOperator::Mul,
                left,
                right,
            }) => left.degree() + right.degree(),
            // In all other cases, we take the maximum of the degrees of the children
            _ => self.children().map(|e| e.degree()).max().unwrap_or(0),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct Challenge {
    /// Challenge ID
    pub id: u64,
    pub stage: u32,
}

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Serialize, Deserialize, JsonSchema,
)]
pub enum AlgebraicBinaryOperator {
    Add,
    Sub,
    Mul,
    /// Exponentiation, but only by constants.
    Pow,
}

impl From<AlgebraicBinaryOperator> for BinaryOperator {
    fn from(op: AlgebraicBinaryOperator) -> BinaryOperator {
        match op {
            AlgebraicBinaryOperator::Add => BinaryOperator::Add,
            AlgebraicBinaryOperator::Sub => BinaryOperator::Sub,
            AlgebraicBinaryOperator::Mul => BinaryOperator::Mul,
            AlgebraicBinaryOperator::Pow => BinaryOperator::Pow,
        }
    }
}

impl TryFrom<BinaryOperator> for AlgebraicBinaryOperator {
    type Error = String;

    fn try_from(op: BinaryOperator) -> Result<Self, Self::Error> {
        match op {
            BinaryOperator::Add => Ok(AlgebraicBinaryOperator::Add),
            BinaryOperator::Sub => Ok(AlgebraicBinaryOperator::Sub),
            BinaryOperator::Mul => Ok(AlgebraicBinaryOperator::Mul),
            BinaryOperator::Pow => Ok(AlgebraicBinaryOperator::Pow),
            _ => Err(format!(
                "Binary operator \"{op}\" not allowed in algebraic expression."
            )),
        }
    }
}

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Serialize, Deserialize, JsonSchema,
)]
pub enum AlgebraicUnaryOperator {
    Minus,
}

impl AlgebraicUnaryOperator {
    /// Returns true if the operator is a prefix-operator and false if it is a postfix operator.
    pub fn is_prefix(&self) -> bool {
        match self {
            AlgebraicUnaryOperator::Minus => true,
        }
    }
}

impl From<AlgebraicUnaryOperator> for UnaryOperator {
    fn from(op: AlgebraicUnaryOperator) -> UnaryOperator {
        match op {
            AlgebraicUnaryOperator::Minus => UnaryOperator::Minus,
        }
    }
}

impl TryFrom<UnaryOperator> for AlgebraicUnaryOperator {
    type Error = String;

    fn try_from(op: UnaryOperator) -> Result<Self, Self::Error> {
        match op {
            UnaryOperator::Minus => Ok(AlgebraicUnaryOperator::Minus),
            _ => Err(format!(
                "Unary operator \"{op}\" not allowed in algebraic expression."
            )),
        }
    }
}

impl<T> AlgebraicExpression<T> {
    pub fn new_binary(left: Self, op: AlgebraicBinaryOperator, right: Self) -> Self {
        AlgebraicBinaryOperation::new(left, op, right).into()
    }

    pub fn new_unary(op: AlgebraicUnaryOperator, expr: Self) -> Self {
        AlgebraicUnaryOperation::new(op, expr).into()
    }

    /// @returns true if the expression contains a reference to a next value of a
    /// (witness or fixed) column
    pub fn contains_next_ref(&self) -> bool {
        self.expr_any(|e| match e {
            AlgebraicExpression::Reference(poly) => poly.next,
            _ => false,
        })
    }

    /// @returns true if the expression contains a reference to a next value of a witness column.
    pub fn contains_next_witness_ref(&self) -> bool {
        self.expr_any(|e| match e {
            AlgebraicExpression::Reference(poly) => poly.next && poly.is_witness(),
            _ => false,
        })
    }

    /// @returns true if the expression contains a reference to a witness column.
    pub fn contains_witness_ref(&self) -> bool {
        self.expr_any(|e| match e {
            AlgebraicExpression::Reference(poly) => poly.is_witness(),
            _ => false,
        })
    }
}

impl<T> ops::Add for AlgebraicExpression<T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new_binary(self, AlgebraicBinaryOperator::Add, rhs)
    }
}

impl<T> ops::Sub for AlgebraicExpression<T> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::new_binary(self, AlgebraicBinaryOperator::Sub, rhs)
    }
}

impl<T> ops::Mul for AlgebraicExpression<T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::new_binary(self, AlgebraicBinaryOperator::Mul, rhs)
    }
}

impl<T> From<T> for AlgebraicExpression<T> {
    fn from(value: T) -> Self {
        AlgebraicExpression::Number(value)
    }
}

/// Reference to a symbol with optional type arguments.
/// Named `PolynomialReference` for historical reasons, it can reference
/// any symbol.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct PolynomialReference {
    /// Absolute name of the symbol.
    pub name: String,
    /// The type arguments if the symbol is generic.
    /// Guaranteed to be Some(_) after type checking is completed.
    pub type_args: Option<Vec<Type>>,
}

#[derive(
    Debug, Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Serialize, Deserialize, JsonSchema,
)]
pub struct PolyID {
    pub id: u64,
    pub ptype: PolynomialType,
}

impl From<&Symbol> for PolyID {
    fn from(symbol: &Symbol) -> Self {
        let SymbolKind::Poly(ptype) = symbol.kind else {
            panic!()
        };
        PolyID {
            id: symbol.id,
            ptype,
        }
    }
}

impl Hash for PolyID {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // single call to hash is faster
        ((self.id << 2) + self.ptype as u64).hash(state);
    }
}

#[derive(
    Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, JsonSchema,
)]
pub enum PolynomialType {
    Committed = 0,
    Constant,
    Intermediate,
}

impl Display for PolynomialType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                PolynomialType::Committed => "witness",
                PolynomialType::Constant => "fixed",
                PolynomialType::Intermediate => "intermediate",
            }
        )
    }
}

#[cfg(test)]
mod tests {
    use powdr_number::DegreeType;
    use powdr_parser_util::SourceRef;

    use crate::analyzed::{AlgebraicReference, DegreeRange, PolyID, PolynomialType};

    use super::{AlgebraicExpression, Analyzed};

    #[test]
    fn insert_remove_identities() {
        let mut pil = Analyzed::default();
        pil.append_polynomial_identity(AlgebraicExpression::Number(0), SourceRef::unknown());
        pil.append_polynomial_identity(AlgebraicExpression::Number(1), SourceRef::unknown());
        pil.append_polynomial_identity(AlgebraicExpression::Number(2), SourceRef::unknown());
        pil.append_polynomial_identity(AlgebraicExpression::Number(3), SourceRef::unknown());
        assert_eq!(pil.identities.len(), 4);
        assert_eq!(pil.source_order.len(), 4);

        let to_remove = [4].into_iter().collect();
        pil.remove_identities(&to_remove);
        assert_eq!(pil.identities.len(), 4);
        assert_eq!(pil.source_order.len(), 4);

        let to_remove = [1, 2].into_iter().collect();
        pil.remove_identities(&to_remove);
        assert_eq!(pil.identities.len(), 2);
        assert_eq!(pil.source_order.len(), 2);

        pil.append_polynomial_identity(AlgebraicExpression::Number(4), SourceRef::unknown());
        pil.append_polynomial_identity(AlgebraicExpression::Number(5), SourceRef::unknown());
        assert_eq!(pil.identities.len(), 4);
        assert_eq!(pil.source_order.len(), 4);

        let to_remove = [1, 2].into_iter().collect();
        pil.remove_identities(&to_remove);
        assert_eq!(pil.identities.len(), 2);
        assert_eq!(pil.source_order.len(), 2);

        let mut pil_result = Analyzed::default();
        pil_result.append_polynomial_identity(AlgebraicExpression::Number(0), SourceRef::unknown());
        pil_result.append_polynomial_identity(AlgebraicExpression::Number(5), SourceRef::unknown());
        pil_result.identities[1].id = 6;
        assert_eq!(pil.identities, pil_result.identities);
        assert_eq!(pil.source_order, pil_result.source_order);
    }

    #[test]
    fn test_degree() {
        let column = AlgebraicExpression::<i32>::Reference(AlgebraicReference {
            name: "column".to_string(),
            poly_id: PolyID {
                id: 0,
                ptype: PolynomialType::Committed,
            },
            next: false,
        });
        let one = AlgebraicExpression::Number(1);

        let expr = one.clone() + one.clone() * one.clone();
        assert_eq!(expr.degree(), 0);

        let expr = column.clone() + one.clone() * one.clone();
        assert_eq!(expr.degree(), 1);

        let expr = column.clone() + one.clone() * column.clone();
        assert_eq!(expr.degree(), 1);

        let expr = column.clone() + column.clone() * column.clone();
        assert_eq!(expr.degree(), 2);

        let expr = column.clone() + column.clone() * (column.clone() + one.clone());
        assert_eq!(expr.degree(), 2);

        let expr = column.clone() * column.clone() * column.clone();
        assert_eq!(expr.degree(), 3);
    }

    #[test]
    fn degree_range() {
        assert_eq!(
            DegreeRange { min: 4, max: 4 }.iter().collect::<Vec<_>>(),
            vec![4]
        );
        assert_eq!(
            DegreeRange { min: 4, max: 16 }.iter().collect::<Vec<_>>(),
            vec![4, 8, 16]
        );
        assert_eq!(
            DegreeRange { min: 3, max: 15 }.iter().collect::<Vec<_>>(),
            vec![4, 8, 16]
        );
        assert_eq!(
            DegreeRange { min: 15, max: 3 }
                .iter()
                .collect::<Vec<DegreeType>>(),
            Vec::<DegreeType>::new()
        );
    }
}

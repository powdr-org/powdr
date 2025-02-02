mod contains_next_ref;
mod display;
pub mod visitor;

use std::cmp::max;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::iter::{self, empty, once};
use std::ops::{self, ControlFlow};
use std::sync::Arc;

use itertools::Itertools;
use num_traits::One;
use powdr_number::{DegreeType, FieldElement};
use powdr_parser_util::SourceRef;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::parsed::types::{ArrayType, Type, TypeBounds, TypeScheme};
use crate::parsed::visitor::{Children, ExpressionVisitable};
pub use crate::parsed::BinaryOperator;
pub use crate::parsed::UnaryOperator;
use crate::parsed::{
    self, ArrayExpression, EnumDeclaration, EnumVariant, NamedType, SourceReference,
    TraitDeclaration, TraitImplementation, TypeDeclaration,
};
pub use contains_next_ref::ContainsNextRef;

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema, PartialEq, Eq, Hash)]
pub enum StatementIdentifier {
    /// Either an intermediate column or a definition.
    Definition(String),
    PublicDeclaration(String),
    /// Index into the vector of proof items / identities.
    ProofItem(usize),
    /// Index into the vector of prover functions.
    ProverFunction(usize),
    /// Index into the vector of trait implementations.
    TraitImplementation(usize),
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, JsonSchema)]
pub struct Analyzed<T> {
    pub definitions: HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
    pub solved_impls: SolvedTraitImpls,
    pub public_declarations: HashMap<String, PublicDeclaration>,
    pub intermediate_columns: HashMap<String, (Symbol, Vec<AlgebraicExpression<T>>)>,
    pub identities: Vec<Identity<T>>,
    pub prover_functions: Vec<Expression>,
    pub trait_impls: Vec<TraitImplementation<Expression>>,
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

    /// Returns the number of stages based on the maximum stage number of all definitions
    pub fn stage_count(&self) -> usize {
        self.definitions
            .iter()
            .map(|(_, (s, _))| s.stage.unwrap_or_default())
            .max()
            .unwrap_or_default() as usize
            + 1
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

    pub fn name_to_poly_id(&self) -> BTreeMap<String, PolyID> {
        self.definitions
            .values()
            .map(|(symbol, _)| symbol)
            .filter(|symbol| matches!(symbol.kind, SymbolKind::Poly(_)))
            .chain(self.intermediate_columns.values().map(|(symbol, _)| symbol))
            .flat_map(|symbol| symbol.array_elements())
            .collect()
    }

    pub fn constant_polys_in_source_order(
        &self,
    ) -> impl Iterator<Item = &(Symbol, Option<FunctionValueDefinition>)> {
        self.definitions_in_source_order(PolynomialType::Constant)
    }

    pub fn committed_polys_in_source_order(
        &self,
    ) -> impl Iterator<Item = &(Symbol, Option<FunctionValueDefinition>)> {
        self.definitions_in_source_order(PolynomialType::Committed)
    }

    pub fn intermediate_polys_in_source_order(
        &self,
    ) -> impl Iterator<Item = &(Symbol, Vec<AlgebraicExpression<T>>)> {
        self.source_order.iter().filter_map(move |statement| {
            if let StatementIdentifier::Definition(name) = statement {
                if let Some(definition) = self.intermediate_columns.get(name) {
                    return Some(definition);
                }
            }
            None
        })
    }

    pub fn definitions_in_source_order(
        &self,
        poly_type: PolynomialType,
    ) -> impl Iterator<Item = &(Symbol, Option<FunctionValueDefinition>)> {
        assert!(
            poly_type != PolynomialType::Intermediate,
            "Use intermediate_polys_in_source_order to get intermediate polys."
        );
        self.source_order.iter().filter_map(move |statement| {
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
    }

    pub fn public_declarations_in_source_order(
        &self,
    ) -> impl Iterator<Item = (&String, &PublicDeclaration)> {
        self.source_order.iter().filter_map(move |statement| {
            if let StatementIdentifier::PublicDeclaration(name) = statement {
                if let Some(public_declaration) = self.public_declarations.get(name) {
                    return Some((name, public_declaration));
                }
            }
            None
        })
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
        expression: AlgebraicExpression<T>,
        source: SourceRef,
    ) -> u64 {
        let id = self
            .identities
            .iter()
            .map(|identity| identity.id())
            .max()
            .unwrap_or_default()
            + 1;
        self.identities.push(
            PolynomialIdentity {
                id,
                source,
                expression,
            }
            .into(),
        );
        self.source_order
            .push(StatementIdentifier::ProofItem(self.identities.len() - 1));
        id
    }

    /// Remove some identities by their index (not their ID).
    /// Does not re-allocate IDs.
    pub fn remove_identities(&mut self, to_remove: &BTreeSet<usize>) {
        let mut shift = 0;
        self.source_order.retain_mut(|s| {
            if let StatementIdentifier::ProofItem(index) = s {
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
            .fold(0, |new_id, (poly, _def)| handle_symbol(new_id, poly));
        self.constant_polys_in_source_order()
            .fold(0, |new_id, (poly, _def)| handle_symbol(new_id, poly));
        self.intermediate_polys_in_source_order()
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

    /// Removes the given set of trait impls, identified by their index
    /// in the list of trait impls.
    pub fn remove_trait_impls(&mut self, to_remove: &BTreeSet<usize>) {
        let to_remove_vec: Vec<usize> = to_remove.iter().copied().collect();

        self.source_order.retain_mut(|s| {
            if let StatementIdentifier::TraitImplementation(index) = s {
                match to_remove_vec.binary_search(index) {
                    Ok(_) => false,
                    Err(insert_pos) => {
                        // `insert_pos` is the number of removed elements before this one.
                        *index -= insert_pos;
                        true
                    }
                }
            } else {
                true
            }
        });
        self.trait_impls = std::mem::take(&mut self.trait_impls)
            .into_iter()
            .enumerate()
            .filter(|(i, _)| !to_remove.contains(i))
            .map(|(_, impl_)| impl_)
            .collect();
        self.solved_impls.remove_trait_impls(&to_remove_vec);
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

    pub fn post_visit_expressions_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Expression),
    {
        // TODO add public inputs if we change them to expressions at some point.
        self.definitions
            .values_mut()
            .filter_map(|(_poly, definition)| definition.as_mut())
            .for_each(|definition| definition.post_visit_expressions_mut(f));
        self.prover_functions
            .iter_mut()
            .for_each(|e| e.post_visit_expressions_mut(f));
    }

    /// Retrieves (name, col_name, poly_id, offset, stage) of each public witness in the trace.
    pub fn get_publics(&self) -> Vec<(String, String, PolyID, usize, u8)> {
        let mut publics = self
            .public_declarations
            .values()
            .map(|public_declaration| {
                let column_name = public_declaration.referenced_poly_name();
                let (poly_id, stage) = {
                    let symbol = &self.definitions[&public_declaration.polynomial.name].0;
                    (
                        symbol
                            .array_elements()
                            .nth(public_declaration.array_index.unwrap_or_default())
                            .unwrap()
                            .1,
                        symbol.stage.unwrap_or_default() as u8,
                    )
                };
                let row_offset = public_declaration.index as usize;
                (
                    public_declaration.name.clone(),
                    column_name,
                    poly_id,
                    row_offset,
                    stage,
                )
            })
            .collect::<Vec<_>>();

        // Sort, so that the order is deterministic
        publics.sort();
        publics
    }
}

impl<T: Clone> Analyzed<T> {
    /// Builds a map from a reference to an intermediate polynomial to the corresponding definition.
    pub fn intermediate_definitions(
        &self,
    ) -> BTreeMap<AlgebraicReferenceThin, AlgebraicExpression<T>> {
        self.intermediate_polys_in_source_order()
            .flat_map(|(symbol, definitions)| symbol.array_elements().zip_eq(definitions))
            .flat_map(|((_, poly_id), def)| {
                // A definition for <intermediate>' only exists if no sub-expression in its definition
                // has the next operator applied to it.
                let next_definition = def.clone().next().ok().map(|def_next| {
                    (
                        AlgebraicReferenceThin {
                            poly_id,
                            next: true,
                        },
                        def_next,
                    )
                });

                next_definition.into_iter().chain(once((
                    AlgebraicReferenceThin {
                        poly_id,
                        next: false,
                    },
                    def.clone(),
                )))
            })
            .collect()
    }
}

impl<T> Children<Expression> for Analyzed<T> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        Box::new(
            self.definitions
                .values()
                .filter_map(|(_, def)| def.as_ref())
                .flat_map(|def| def.children())
                .chain(self.trait_impls.iter().flat_map(|impls| impls.children()))
                .chain(self.prover_functions.iter()),
        )
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        Box::new(
            self.definitions
                .values_mut()
                .filter_map(|(_, def)| def.as_mut())
                .flat_map(|def| def.children_mut())
                .chain(
                    self.trait_impls
                        .iter_mut()
                        .flat_map(|impls| impls.children_mut()),
                )
                .chain(self.prover_functions.iter_mut()),
        )
    }
}

impl<T> Children<AlgebraicExpression<T>> for Analyzed<T> {
    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        Box::new(
            self.intermediate_columns
                .values()
                .flat_map(|(_, exprs)| exprs.iter())
                .chain(self.identities.iter().flat_map(|i| i.children())),
        )
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        Box::new(
            self.intermediate_columns
                .values_mut()
                .flat_map(|(_, exprs)| exprs.iter_mut())
                .chain(self.identities.iter_mut().flat_map(|i| i.children_mut())),
        )
    }
}

impl<T: FieldElement> Analyzed<T> {
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
            FunctionValueDefinition::TypeConstructor(enum_decl, variant) => {
                Some(variant.constructor_type(enum_decl))
            }
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

/// Data structure to help with finding the correct implementation of a trait function
/// given a list of type arguments.
#[derive(Default, Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct SolvedTraitImpls {
    impls: BTreeMap<String, HashMap<Vec<Type>, ImplData>>,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
struct ImplData {
    index: usize,
    function: Arc<Expression>,
}

impl SolvedTraitImpls {
    /// Returns an index into the list of trait implementations such that the corresponding
    /// trait implementation contains the matching function for a given trait function name
    /// and type arguments. It returns an index into the list provided by `Analyzed`.
    pub fn resolve_trait_impl_index(&self, trait_function_name: &str, type_args: &[Type]) -> usize {
        self.impls[trait_function_name][type_args].index
    }

    /// Returns the correct trait impl function for a given trait function name and type arguments,
    /// if it is stored here, otherwise returns None.
    pub fn try_resolve_trait_function(
        &self,
        trait_function_name: &str,
        type_args: &[Type],
    ) -> Option<&Expression> {
        self.impls
            .get(trait_function_name)
            .and_then(|map| map.get(type_args))
            .map(|impl_data| impl_data.function.as_ref())
    }

    /// Returns the correct trait impl function for a given trait function name and type arguments.
    /// It returns just the function of the trait impl.
    pub fn resolve_trait_function(
        &self,
        trait_function_name: &str,
        type_args: &[Type],
    ) -> &Expression {
        self.try_resolve_trait_function(trait_function_name, type_args)
            .unwrap()
    }

    pub fn insert(
        &mut self,
        trait_function_name: String,
        type_args: Vec<Type>,
        index: usize,
        function: Arc<Expression>,
    ) {
        let existing = self
            .impls
            .entry(trait_function_name)
            .or_default()
            .insert(type_args, ImplData { index, function });
        assert!(
            existing.is_none(),
            "Duplicate trait impl for the same type arguments."
        );
    }

    /// Update the data structure after a certain set of trait impls have been removed.
    /// This just updates the `index` fields.
    /// Assumes that `to_remove` is sorted.
    pub fn remove_trait_impls(&mut self, to_remove: &[usize]) {
        for map in self.impls.values_mut() {
            *map = map
                .drain()
                .filter_map(|(type_args, mut impl_data)| {
                    match to_remove.binary_search(&impl_data.index) {
                        Ok(_) => None,
                        Err(index) => {
                            // `index` is the number of removed elements before this one.
                            impl_data.index -= index;
                            Some((type_args, impl_data))
                        }
                    }
                })
                .collect();
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
    pub fn is_unique(&self) -> bool {
        self.min == self.max
    }

    pub fn try_into_unique(self) -> Option<DegreeType> {
        self.is_unique().then_some(self.min)
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

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema, Hash)]
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
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema, Hash,
)]
pub enum SymbolKind {
    /// Fixed, witness or intermediate polynomial
    Poly(PolynomialType),
    /// Other symbol, depends on the type.
    /// Examples include functions not of the type "int -> fe".
    Other(),
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema, PartialEq, Eq, Hash)]
pub enum FunctionValueDefinition {
    Array(ArrayExpression<Reference>),
    Expression(TypedExpression),
    TypeDeclaration(TypeDeclaration),
    TypeConstructor(Arc<EnumDeclaration>, EnumVariant),
    TraitDeclaration(TraitDeclaration),
    TraitFunction(Arc<TraitDeclaration>, NamedType),
}

impl Children<Expression> for FunctionValueDefinition {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        match self {
            FunctionValueDefinition::Expression(TypedExpression { e, type_scheme: _ }) => {
                Box::new(iter::once(e))
            }
            FunctionValueDefinition::Array(e) => e.children(),
            FunctionValueDefinition::TypeDeclaration(type_declaration) => {
                type_declaration.children()
            }
            FunctionValueDefinition::TypeConstructor(_, variant) => variant.children(),
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
            FunctionValueDefinition::TypeDeclaration(type_declaration) => {
                type_declaration.children_mut()
            }
            FunctionValueDefinition::TypeConstructor(_, variant) => variant.children_mut(),
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

impl Children<Expression> for NamedType {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        Box::new(empty())
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        Box::new(empty())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema, Hash)]
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

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema, Hash,
)]
pub struct SelectedExpressions<T> {
    pub selector: AlgebraicExpression<T>,
    pub expressions: Vec<AlgebraicExpression<T>>,
}

impl<T: One> Default for SelectedExpressions<T> {
    fn default() -> Self {
        Self {
            selector: T::one().into(),
            expressions: vec![],
        }
    }
}

impl<T> Children<AlgebraicExpression<T>> for SelectedExpressions<T> {
    /// Returns an iterator over all (top-level) expressions in this SelectedExpressions.
    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        Box::new(once(&self.selector).chain(self.expressions.iter()))
    }
    /// Returns an iterator over all (top-level) expressions in this SelectedExpressions.
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        Box::new(once(&mut self.selector).chain(self.expressions.iter_mut()))
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize, JsonSchema, Hash)]
pub struct PolynomialIdentity<T> {
    // The ID is globally unique among identities.
    pub id: u64,
    pub source: SourceRef,
    pub expression: AlgebraicExpression<T>,
}

impl<T> Children<AlgebraicExpression<T>> for PolynomialIdentity<T> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        Box::new(iter::once(&mut self.expression))
    }
    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        Box::new(iter::once(&self.expression))
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize, JsonSchema, Hash)]
pub struct LookupIdentity<T> {
    // The ID is globally unique among identities.
    pub id: u64,
    pub source: SourceRef,
    pub left: SelectedExpressions<T>,
    pub right: SelectedExpressions<T>,
}

impl<T> Children<AlgebraicExpression<T>> for LookupIdentity<T> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        Box::new(self.left.children_mut().chain(self.right.children_mut()))
    }
    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        Box::new(self.left.children().chain(self.right.children()))
    }
}

/// A witness generation helper for a lookup identity.
///
/// This identity is used as a replacement for a lookup identity which has been turned into challenge-based polynomial identities.
/// This is ignored by the backend.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize, JsonSchema, Hash)]
pub struct PhantomLookupIdentity<T> {
    // The ID is globally unique among identities.
    pub id: u64,
    pub source: SourceRef,
    pub left: SelectedExpressions<T>,
    pub right: SelectedExpressions<T>,
    pub multiplicity: AlgebraicExpression<T>,
}

impl<T> Children<AlgebraicExpression<T>> for PhantomLookupIdentity<T> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        Box::new(
            self.left
                .children_mut()
                .chain(self.right.children_mut())
                .chain(once(&mut self.multiplicity)),
        )
    }
    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        Box::new(
            self.left
                .children()
                .chain(self.right.children())
                .chain(once(&self.multiplicity)),
        )
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize, JsonSchema, Hash)]
pub struct PermutationIdentity<T> {
    // The ID is globally unique among identities.
    pub id: u64,
    pub source: SourceRef,
    pub left: SelectedExpressions<T>,
    pub right: SelectedExpressions<T>,
}

impl<T> Children<AlgebraicExpression<T>> for PermutationIdentity<T> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        Box::new(self.left.children_mut().chain(self.right.children_mut()))
    }
    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        Box::new(self.left.children().chain(self.right.children()))
    }
}

/// A witness generation helper for a permutation identity.
///
/// This identity is used as a replacement for a permutation identity which has been turned into challenge-based polynomial identities.
/// This is ignored by the backend.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize, JsonSchema, Hash)]
pub struct PhantomPermutationIdentity<T> {
    // The ID is globally unique among identities.
    pub id: u64,
    pub source: SourceRef,
    pub left: SelectedExpressions<T>,
    pub right: SelectedExpressions<T>,
}

impl<T> Children<AlgebraicExpression<T>> for PhantomPermutationIdentity<T> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        Box::new(self.left.children_mut().chain(self.right.children_mut()))
    }
    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        Box::new(self.left.children().chain(self.right.children()))
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize, JsonSchema, Hash)]
pub struct ConnectIdentity<T> {
    // The ID is globally unique among identities.
    pub id: u64,
    pub source: SourceRef,
    pub left: Vec<AlgebraicExpression<T>>,
    pub right: Vec<AlgebraicExpression<T>>,
}

impl<T> Children<AlgebraicExpression<T>> for ConnectIdentity<T> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        Box::new(self.left.iter_mut().chain(self.right.iter_mut()))
    }
    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        Box::new(self.left.iter().chain(self.right.iter()))
    }
}

#[derive(
    Debug, PartialEq, Eq, Clone, Serialize, Deserialize, JsonSchema, PartialOrd, Ord, Hash,
)]
pub struct ExpressionList<T>(pub Vec<AlgebraicExpression<T>>);

impl<T> Children<AlgebraicExpression<T>> for ExpressionList<T> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        Box::new(self.0.iter_mut())
    }
    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        Box::new(self.0.iter())
    }
}

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema, Hash,
)]
pub struct PhantomBusInteractionIdentity<T> {
    // The ID is globally unique among identities.
    pub id: u64,
    pub source: SourceRef,
    pub multiplicity: AlgebraicExpression<T>,
    pub bus_id: AlgebraicExpression<T>,
    pub payload: ExpressionList<T>,
    pub latch: AlgebraicExpression<T>,
    pub folded_expressions: ExpressionList<T>,
    pub accumulator_columns: Vec<AlgebraicReference>,
}

impl<T> Children<AlgebraicExpression<T>> for PhantomBusInteractionIdentity<T> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        Box::new(
            once(&mut self.multiplicity)
                .chain(self.payload.children_mut())
                .chain(once(&mut self.latch)),
        )
    }
    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        Box::new(
            once(&self.multiplicity)
                .chain(self.payload.children())
                .chain(once(&self.latch)),
        )
    }
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    Serialize,
    Deserialize,
    JsonSchema,
    Hash,
    derive_more::Display,
    derive_more::From,
    derive_more::TryInto,
)]
pub enum Identity<T> {
    Polynomial(PolynomialIdentity<T>),
    Lookup(LookupIdentity<T>),
    PhantomLookup(PhantomLookupIdentity<T>),
    Permutation(PermutationIdentity<T>),
    PhantomPermutation(PhantomPermutationIdentity<T>),
    Connect(ConnectIdentity<T>),
    PhantomBusInteraction(PhantomBusInteractionIdentity<T>),
}

impl<T> Identity<T> {
    pub fn degree(
        &self,
        intermediate_polynomials: &BTreeMap<AlgebraicReferenceThin, AlgebraicExpression<T>>,
    ) -> usize {
        let mut cache = BTreeMap::new();
        self.children()
            .map(|e| e.degree_with_cache(intermediate_polynomials, &mut cache))
            .max()
            .unwrap_or(0)
    }

    pub fn id(&self) -> u64 {
        match self {
            Identity::Polynomial(i) => i.id,
            Identity::Lookup(i) => i.id,
            Identity::PhantomLookup(i) => i.id,
            Identity::Permutation(i) => i.id,
            Identity::PhantomPermutation(i) => i.id,
            Identity::Connect(i) => i.id,
            Identity::PhantomBusInteraction(i) => i.id,
        }
    }

    pub fn kind(&self) -> IdentityKind {
        match self {
            Identity::Polynomial(_) => IdentityKind::Polynomial,
            Identity::Lookup(_) => IdentityKind::Lookup,
            Identity::PhantomLookup(_) => IdentityKind::PhantomLookup,
            Identity::Permutation(_) => IdentityKind::Permutation,
            Identity::PhantomPermutation(_) => IdentityKind::PhantomPermutation,
            Identity::Connect(_) => IdentityKind::Connect,
            Identity::PhantomBusInteraction(_) => IdentityKind::PhantomBusInteraction,
        }
    }
}

impl<T> SourceReference for Identity<T> {
    fn source_reference(&self) -> &SourceRef {
        match self {
            Identity::Polynomial(i) => &i.source,
            Identity::Lookup(i) => &i.source,
            Identity::PhantomLookup(i) => &i.source,
            Identity::Permutation(i) => &i.source,
            Identity::PhantomPermutation(i) => &i.source,
            Identity::Connect(i) => &i.source,
            Identity::PhantomBusInteraction(i) => &i.source,
        }
    }

    fn source_reference_mut(&mut self) -> &mut SourceRef {
        match self {
            Identity::Polynomial(i) => &mut i.source,
            Identity::Lookup(i) => &mut i.source,
            Identity::PhantomLookup(i) => &mut i.source,
            Identity::Permutation(i) => &mut i.source,
            Identity::PhantomPermutation(i) => &mut i.source,
            Identity::Connect(i) => &mut i.source,
            Identity::PhantomBusInteraction(i) => &mut i.source,
        }
    }
}

impl<T> Children<AlgebraicExpression<T>> for Identity<T> {
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut AlgebraicExpression<T>> + '_> {
        match self {
            Identity::Polynomial(i) => i.children_mut(),
            Identity::Lookup(i) => i.children_mut(),
            Identity::PhantomLookup(i) => i.children_mut(),
            Identity::Permutation(i) => i.children_mut(),
            Identity::PhantomPermutation(i) => i.children_mut(),
            Identity::Connect(i) => i.children_mut(),
            Identity::PhantomBusInteraction(i) => i.children_mut(),
        }
    }

    fn children(&self) -> Box<dyn Iterator<Item = &AlgebraicExpression<T>> + '_> {
        match self {
            Identity::Polynomial(i) => i.children(),
            Identity::Lookup(i) => i.children(),
            Identity::PhantomLookup(i) => i.children(),
            Identity::Permutation(i) => i.children(),
            Identity::PhantomPermutation(i) => i.children(),
            Identity::Connect(i) => i.children(),
            Identity::PhantomBusInteraction(i) => i.children(),
        }
    }
}

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Serialize, Deserialize, JsonSchema,
)]
pub enum IdentityKind {
    Polynomial,
    Lookup,
    PhantomLookup,
    Permutation,
    PhantomPermutation,
    Connect,
    PhantomBusInteraction,
}

pub type Expression = parsed::Expression<Reference>;
pub type TypedExpression = crate::parsed::TypedExpression<Reference, u64>;

#[derive(
    Debug, Clone, Serialize, Deserialize, JsonSchema, PartialEq, Eq, Hash, PartialOrd, Ord,
)]
pub enum Reference {
    LocalVar(u64, String),
    Poly(PolynomialReference),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
/// Like [[AlgebraicReference]], but without the name.
pub struct AlgebraicReferenceThin {
    pub poly_id: PolyID,
    pub next: bool,
}

impl From<&AlgebraicReference> for AlgebraicReferenceThin {
    fn from(value: &AlgebraicReference) -> Self {
        value.to_thin()
    }
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

    pub fn to_thin(&self) -> AlgebraicReferenceThin {
        AlgebraicReferenceThin {
            poly_id: self.poly_id,
            next: self.next,
        }
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

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema, Hash,
)]
pub enum AlgebraicExpression<T> {
    Reference(AlgebraicReference),
    PublicReference(String),
    Challenge(Challenge),
    Number(T),
    BinaryOperation(AlgebraicBinaryOperation<T>),
    UnaryOperation(AlgebraicUnaryOperation<T>),
}

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema, Hash,
)]
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

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema, Hash,
)]
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

impl<T: FieldElement> num_traits::One for AlgebraicExpression<T> {
    fn one() -> Self {
        AlgebraicExpression::Number(T::one())
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
    pub fn degree_with_cache(
        &self,
        intermediate_definitions: &BTreeMap<AlgebraicReferenceThin, AlgebraicExpression<T>>,
        cache: &mut BTreeMap<AlgebraicReferenceThin, usize>,
    ) -> usize {
        match self {
            AlgebraicExpression::Reference(reference) => match reference.poly_id.ptype {
                PolynomialType::Committed | PolynomialType::Constant => 1,
                PolynomialType::Intermediate => {
                    let reference = reference.to_thin();
                    cache.get(&reference).cloned().unwrap_or_else(|| {
                        let def = intermediate_definitions
                            .get(&reference)
                            .expect("Intermediate definition not found.");
                        let result = def.degree_with_cache(intermediate_definitions, cache);
                        cache.insert(reference, result);
                        result
                    })
                }
            },
            // Multiplying two expressions adds their degrees
            AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation {
                op: AlgebraicBinaryOperator::Mul,
                left,
                right,
            }) => {
                left.degree_with_cache(intermediate_definitions, cache)
                    + right.degree_with_cache(intermediate_definitions, cache)
            }
            // In all other cases, we take the maximum of the degrees of the children
            _ => self
                .children()
                .map(|e| e.degree_with_cache(intermediate_definitions, cache))
                .max()
                .unwrap_or(0),
        }
    }
}

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Serialize, Deserialize, JsonSchema, Hash,
)]
pub struct Challenge {
    /// Challenge ID
    pub id: u64,
    pub stage: u32,
}

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Serialize, Deserialize, JsonSchema, Hash,
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
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Serialize, Deserialize, JsonSchema, Hash,
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
#[derive(
    Debug, Clone, Serialize, Deserialize, JsonSchema, PartialEq, Eq, PartialOrd, Ord, Hash,
)]
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

    use crate::analyzed::{
        AlgebraicReference, DegreeRange, Identity, PolyID, PolynomialIdentity, PolynomialType,
    };

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
        if let Identity::Polynomial(PolynomialIdentity { id, .. }) = &mut pil_result.identities[1] {
            *id = 6;
        } else {
            panic!();
        }
        assert_eq!(pil.identities, pil_result.identities);
        assert_eq!(pil.source_order, pil_result.source_order);
    }

    #[test]
    fn test_degree_no_intermediates() {
        let column = AlgebraicExpression::<i32>::Reference(AlgebraicReference {
            name: "column".to_string(),
            poly_id: PolyID {
                id: 0,
                ptype: PolynomialType::Committed,
            },
            next: false,
        });
        let one = AlgebraicExpression::Number(1);

        // No intermediates
        let intermediate_definitions = Default::default();
        let mut cache = Default::default();

        let expr = one.clone() + one.clone() * one.clone();
        let degree = expr.degree_with_cache(&intermediate_definitions, &mut cache);
        assert_eq!(degree, 0);

        let expr = column.clone() + one.clone() * one.clone();
        let degree = expr.degree_with_cache(&intermediate_definitions, &mut cache);
        assert_eq!(degree, 1);

        let expr = column.clone() + one.clone() * column.clone();
        let degree = expr.degree_with_cache(&intermediate_definitions, &mut cache);
        assert_eq!(degree, 1);

        let expr = column.clone() + column.clone() * column.clone();
        let degree = expr.degree_with_cache(&intermediate_definitions, &mut cache);
        assert_eq!(degree, 2);

        let expr = column.clone() + column.clone() * (column.clone() + one.clone());
        let degree = expr.degree_with_cache(&intermediate_definitions, &mut cache);
        assert_eq!(degree, 2);

        let expr = column.clone() * column.clone() * column.clone();
        let degree = expr.degree_with_cache(&intermediate_definitions, &mut cache);
        assert_eq!(degree, 3);

        assert!(cache.is_empty());
    }

    #[test]
    fn test_degree_with_intermediates() {
        let column = AlgebraicExpression::<i32>::Reference(AlgebraicReference {
            name: "column".to_string(),
            poly_id: PolyID {
                id: 0,
                ptype: PolynomialType::Committed,
            },
            next: false,
        });
        let one = AlgebraicExpression::Number(1);

        let column_squared = column.clone() * column.clone();
        let column_squared_ref = AlgebraicReference {
            name: "column_squared".to_string(),
            poly_id: PolyID {
                id: 1,
                ptype: PolynomialType::Intermediate,
            },
            next: false,
        };
        let column_squared_intermediate =
            AlgebraicExpression::<i32>::Reference(column_squared_ref.clone());

        let intermediate_definitions = [(column_squared_ref.to_thin(), column_squared.clone())]
            .into_iter()
            .collect();
        let mut cache = Default::default();

        let expr = column_squared_intermediate.clone() + one.clone();
        let degree = expr.degree_with_cache(&intermediate_definitions, &mut cache);
        assert_eq!(degree, 2);

        let expr = column_squared_intermediate.clone() + column.clone();
        let degree = expr.degree_with_cache(&intermediate_definitions, &mut cache);
        assert_eq!(degree, 2);

        let expr = column_squared_intermediate.clone() * column_squared_intermediate.clone();
        let degree = expr.degree_with_cache(&intermediate_definitions, &mut cache);
        assert_eq!(degree, 4);

        let expr = column_squared_intermediate.clone()
            * (column_squared_intermediate.clone() + one.clone());
        let degree = expr.degree_with_cache(&intermediate_definitions, &mut cache);
        assert_eq!(degree, 4);

        let expr = column_squared_intermediate.clone() * column.clone();
        let degree = expr.degree_with_cache(&intermediate_definitions, &mut cache);
        assert_eq!(degree, 3);
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

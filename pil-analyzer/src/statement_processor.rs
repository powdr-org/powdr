use std::collections::{BTreeMap, HashSet};
use std::iter;
use std::sync::Arc;

use itertools::Itertools;

use powdr_ast::analyzed::{DegreeRange, TypedExpression};
use powdr_ast::parsed::asm::SymbolPath;
use powdr_ast::parsed::types::TupleType;
use powdr_ast::parsed::{
    self,
    types::{ArrayType, Type, TypeScheme},
    EnumDeclaration, EnumVariant, FunctionDefinition, FunctionKind, LambdaExpression, NamedType,
    PilStatement, PolynomialName, TraitDeclaration,
};
use powdr_ast::parsed::{
    ArrayExpression, NamedExpression, StructDeclaration, SymbolCategory, TraitImplementation,
    TypeDeclaration,
};
use powdr_parser_util::{Error, SourceRef};
use std::str::FromStr;

use powdr_ast::analyzed::{
    Expression, FunctionValueDefinition, PolynomialType, PublicDeclaration, Symbol, SymbolKind,
};

use crate::type_processor::TypeProcessor;
use crate::{untyped_evaluator, AnalysisDriver};

use crate::expression_processor::ExpressionProcessor;

pub enum PILItem {
    Definition(Symbol, Option<FunctionValueDefinition>),
    PublicDeclaration(PublicDeclaration),
    ProofItem(Expression),
    TraitImplementation(TraitImplementation<Expression>),
}

pub struct Counters {
    symbol_counters: BTreeMap<SymbolKind, u64>,
    identity_counter: u64,
    public_counter: u64,
}

impl Default for Counters {
    fn default() -> Self {
        Self {
            symbol_counters: [
                SymbolKind::Poly(PolynomialType::Committed),
                SymbolKind::Poly(PolynomialType::Constant),
                SymbolKind::Poly(PolynomialType::Intermediate),
                SymbolKind::Other(),
            ]
            .into_iter()
            .map(|k| (k, 0))
            .collect(),
            identity_counter: 0,
            public_counter: 0,
        }
    }
}

impl Counters {
    /// Creates a new counter struct that can dispense IDs that do not conflict with the
    /// provided existing IDs.
    pub fn with_existing<'a>(
        symbols: impl IntoIterator<Item = &'a Symbol>,
        identity: Option<u64>,
        public: Option<u64>,
    ) -> Self {
        let mut counters = Self::default();
        if let Some(id) = identity {
            counters.identity_counter = id + 1;
        }
        if let Some(id) = public {
            counters.public_counter = id + 1;
        }
        for symbol in symbols {
            let counter = counters.symbol_counters.get_mut(&symbol.kind).unwrap();
            let next = symbol.id + symbol.length.unwrap_or(1);
            *counter = std::cmp::max(*counter, next);
        }
        counters
    }

    pub fn dispense_identity_id(&mut self) -> u64 {
        let id = self.identity_counter;
        self.identity_counter += 1;
        id
    }

    pub fn dispense_symbol_id(&mut self, kind: SymbolKind, length: Option<u64>) -> u64 {
        let counter = self.symbol_counters.get_mut(&kind).unwrap();
        let id = *counter;
        *counter += length.unwrap_or(1);
        id
    }

    pub fn dispense_public_id(&mut self) -> u64 {
        let id = self.public_counter;
        self.public_counter += 1;
        id
    }
}

pub struct StatementProcessor<'a, D> {
    driver: D,
    counters: &'a mut Counters,
    degree: Option<DegreeRange>,
}

impl<'a, D> StatementProcessor<'a, D>
where
    D: AnalysisDriver,
{
    pub fn new(driver: D, counters: &'a mut Counters, degree: Option<DegreeRange>) -> Self {
        StatementProcessor {
            driver,
            counters,
            degree,
        }
    }

    pub fn handle_statement(&mut self, statement: PilStatement) -> Result<Vec<PILItem>, Error> {
        match statement {
            PilStatement::Include(_, _) => {
                panic!("Includes must be handled outside the statement processor.")
            }
            PilStatement::Namespace(_, _, _) => {
                panic!("Namespaces must be handled outside the statement processor.")
            }
            PilStatement::PolynomialDefinition(source, name, value) => {
                let (name, ty) = self.name_and_type_from_polynomial_name(name, Type::Inter)?;
                self.handle_symbol_definition(
                    source,
                    name,
                    SymbolKind::Poly(PolynomialType::Intermediate),
                    None,
                    ty,
                    Some(FunctionDefinition::Expression(value)),
                )
            }
            PilStatement::PublicDeclaration(source, name, polynomial, array_index, index) => {
                self.handle_public_declaration(source, name, polynomial, array_index, index)
            }
            PilStatement::PolynomialConstantDefinition(source, name, definition) => self
                .handle_symbol_definition(
                    source,
                    name,
                    SymbolKind::Poly(PolynomialType::Constant),
                    None,
                    Some(Type::Col.into()),
                    Some(definition),
                ),
            PilStatement::PolynomialCommitDeclaration(source, stage, polynomials, None) => {
                self.handle_witness_polynomial_declarations(source, stage, polynomials)
            }
            PilStatement::PolynomialCommitDeclaration(
                source,
                stage,
                mut polynomials,
                Some(definition),
            ) => {
                assert!(polynomials.len() == 1);
                let (name, ty) =
                    self.name_and_type_from_polynomial_name(polynomials.pop().unwrap(), Type::Col)?;

                self.handle_symbol_definition(
                    source,
                    name,
                    SymbolKind::Poly(PolynomialType::Committed),
                    stage,
                    ty,
                    Some(definition),
                )
            }
            PilStatement::LetStatement(source, name, type_scheme, value) => {
                self.handle_generic_definition(source, name, type_scheme, value)
            }
            PilStatement::EnumDeclaration(source, enum_declaration) => self
                .handle_symbol_definition(
                    source,
                    enum_declaration.name.clone(),
                    SymbolKind::Other(),
                    None,
                    None,
                    Some(FunctionDefinition::TypeDeclaration(TypeDeclaration::Enum(
                        enum_declaration.clone(),
                    ))),
                ),
            PilStatement::TraitDeclaration(source, trait_decl) => self.handle_symbol_definition(
                source,
                trait_decl.name.clone(),
                SymbolKind::Other(),
                None,
                None,
                Some(FunctionDefinition::TraitDeclaration(trait_decl.clone())),
            ),
            PilStatement::TraitImplementation(_, trait_impl) => {
                let trait_impl = self.process_trait_implementation(trait_impl)?;
                Ok(vec![PILItem::TraitImplementation(trait_impl)])
            }
            PilStatement::Expression(_, expr) => {
                let new_expr = self
                    .expression_processor(&Default::default())
                    .process_expression(expr)?;

                Ok(vec![PILItem::ProofItem(new_expr)])
            }
            PilStatement::StructDeclaration(source, struct_declaration) => self
                .handle_symbol_definition(
                    source,
                    struct_declaration.name.clone(),
                    SymbolKind::Other(),
                    None,
                    None,
                    Some(FunctionDefinition::TypeDeclaration(
                        TypeDeclaration::Struct(struct_declaration.clone()),
                    )),
                ),
        }
    }

    fn name_and_type_from_polynomial_name(
        &mut self,
        PolynomialName { name, array_size }: PolynomialName,
        base_type: Type,
    ) -> Result<(String, Option<TypeScheme>), Error> {
        let ty = Some(match array_size {
            None => base_type.into(),
            Some(len) => {
                let len = self
                    .expression_processor(&Default::default())
                    .process_expression(len)
                    .map_err(|err| {
                        err.extend_message(|m| format!("Failed to process length expression: {m}"))
                    })?;
                let length = untyped_evaluator::evaluate_expression_to_int(self.driver, len)
                    .map(|length| {
                        length
                            .try_into()
                            .unwrap_or_else(|_| panic!("Array length too large."))
                    })
                    .map_err(|e| {
                        panic!("Error evaluating length of array of witness columns {name}:\n{e}")
                    })
                    .ok();
                Type::Array(ArrayType {
                    base: Box::new(base_type),
                    length,
                })
                .into()
            }
        });
        Ok((name, ty))
    }

    fn handle_generic_definition(
        &mut self,
        source: SourceRef,
        name: String,
        type_scheme: Option<TypeScheme<parsed::Expression>>,
        value: Option<parsed::Expression>,
    ) -> Result<Vec<PILItem>, Error> {
        let type_scheme = type_scheme.map(|ts| {
            let vars = ts.vars;
            let duplicates = vars.vars().duplicates().collect::<Vec<_>>();
            if !duplicates.is_empty() {
                panic!(
                    "Duplicate type variables in declaration of \"{name}\":\n{}",
                    duplicates.iter().format(", ")
                );
            }
            let declared_type_vars = vars.vars().collect::<HashSet<_>>();
            let ty = self.type_processor(&declared_type_vars).process_type(ts.ty);
            let contained_type_vars = ty.contained_type_vars().collect::<HashSet<_>>();
            if contained_type_vars != declared_type_vars {
                assert!(contained_type_vars.is_subset(&declared_type_vars));
                panic!(
                    "Unused type variable(s) in declaration: {}\nlet<{vars}> {name}: {ty}",
                    declared_type_vars
                        .difference(&contained_type_vars)
                        .format(", ")
                );
            };
            TypeScheme { vars, ty }
        });

        match value {
            None => {
                // No value provided => treat it as a witness column.
                let ty = type_scheme
                    .map(|ts| {
                        assert!(ts.vars.is_empty());
                        let ty = ts.ty;
                        if let Type::Array(ArrayType { base, length }) = &ty {
                            if base.as_ref() != &Type::Col {
                                panic!("Symbol {name} is declared without value and thus must be a witness column array, but its type is {ty} instead of col[].");
                            }
                            if length.is_none() {
                                panic!("Explicit array length required for column {name}: {ty}");
                            }
                        } else if ty != Type::Col {
                            panic!("Symbol {name} is declared without value and thus must be a witness column, but its type is {ty} instead of col.");
                        }
                        ty
                    })
                    .unwrap_or(Type::Col);
                self.handle_symbol_definition(
                    source,
                    name,
                    SymbolKind::Poly(PolynomialType::Committed),
                    None,
                    Some(ty.into()),
                    None,
                )
            }
            Some(value) => {
                let symbol_kind = type_scheme
                    .as_ref()
                    .map(Self::symbol_kind_from_type)
                    .unwrap_or(SymbolKind::Other());

                self.handle_symbol_definition(
                    source,
                    name,
                    symbol_kind,
                    None,
                    type_scheme,
                    Some(FunctionDefinition::Expression(value)),
                )
            }
        }
    }

    fn symbol_kind_from_type(ts: &TypeScheme) -> SymbolKind {
        if !ts.vars.is_empty() {
            return SymbolKind::Other();
        }
        match &ts.ty {
            Type::Inter => SymbolKind::Poly(PolynomialType::Intermediate),
            Type::Col => SymbolKind::Poly(PolynomialType::Constant),
            Type::Array(ArrayType { base, length: _ }) if base.as_ref() == &Type::Col => {
                // Array of fixed columns
                SymbolKind::Poly(PolynomialType::Constant)
            }
            Type::Array(ArrayType { base, length: _ }) if base.as_ref() == &Type::Inter => {
                SymbolKind::Poly(PolynomialType::Intermediate)
            }
            // Otherwise, treat it as "generic definition"
            _ => SymbolKind::Other(),
        }
    }

    fn handle_witness_polynomial_declarations(
        &mut self,
        source: SourceRef,
        stage: Option<u32>,
        polynomials: Vec<PolynomialName>,
    ) -> Result<Vec<PILItem>, Error> {
        let result = polynomials
            .into_iter()
            .map(|poly_name| {
                let (name, ty) = self.name_and_type_from_polynomial_name(poly_name, Type::Col)?;
                self.handle_symbol_definition(
                    source.clone(),
                    name,
                    SymbolKind::Poly(PolynomialType::Committed),
                    stage,
                    ty,
                    None,
                )
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect();

        Ok(result)
    }

    fn handle_symbol_definition(
        &mut self,
        source: SourceRef,
        name: String,
        symbol_kind: SymbolKind,
        stage: Option<u32>,
        type_scheme: Option<TypeScheme>,
        value: Option<FunctionDefinition>,
    ) -> Result<Vec<PILItem>, Error> {
        let length = type_scheme.as_ref().and_then(|t| {
            if symbol_kind == SymbolKind::Other() {
                None
            } else if let Type::Array(ArrayType { length, base: _ }) = t.ty {
                if length.is_none() && symbol_kind != SymbolKind::Other() {
                    panic!("Explicit array length required for column {name}.");
                }
                length
            } else {
                None
            }
        });
        assert!(stage.is_none() || symbol_kind == SymbolKind::Poly(PolynomialType::Committed));

        let id = self.counters.dispense_symbol_id(symbol_kind, length);
        let symbol = Symbol {
            id,
            source: source.clone(),
            stage,
            absolute_name: self.driver.resolve_decl(&name),
            kind: symbol_kind,
            length,
            degree: self.degree,
        };

        match value {
            Some(FunctionDefinition::TypeDeclaration(TypeDeclaration::Enum(enum_decl))) => {
                assert_eq!(symbol_kind, SymbolKind::Other());
                self.process_enum_declaration(source, name, symbol, enum_decl)
            }
            Some(FunctionDefinition::TypeDeclaration(TypeDeclaration::Struct(struct_decl))) => {
                assert_eq!(symbol_kind, SymbolKind::Other());
                self.process_struct_declaration(symbol, struct_decl)
            }
            Some(FunctionDefinition::TraitDeclaration(trait_decl)) => {
                self.process_trait_declaration(source, name, symbol, trait_decl)
            }
            Some(FunctionDefinition::Expression(expr)) => {
                self.process_expression_symbol(symbol_kind, symbol, type_scheme, expr)
            }
            Some(FunctionDefinition::Array(value)) => {
                self.process_array_symbol(symbol, type_scheme, value)
            }
            None => Ok(vec![PILItem::Definition(symbol, None)]),
        }
    }

    fn process_expression_symbol(
        &mut self,
        symbol_kind: SymbolKind,
        symbol: Symbol,
        type_scheme: Option<TypeScheme>,
        expr: parsed::Expression,
    ) -> Result<Vec<PILItem>, Error> {
        if symbol_kind == SymbolKind::Poly(PolynomialType::Committed) {
            // The only allowed value for a witness column is a query function.
            assert!(matches!(
                expr,
                parsed::Expression::LambdaExpression(
                    _,
                    LambdaExpression {
                        kind: FunctionKind::Query,
                        ..
                    }
                )
            ));
            assert!(type_scheme.is_none() || type_scheme == Some(Type::Col.into()));
        }
        let type_vars = type_scheme
            .as_ref()
            .map(|ts| ts.vars.vars().collect())
            .unwrap_or_default();
        let value = FunctionValueDefinition::Expression(TypedExpression {
            e: self
                .expression_processor(&type_vars)
                .process_expression(expr)?,
            type_scheme,
        });

        Ok(vec![PILItem::Definition(symbol, Some(value))])
    }

    fn process_array_symbol(
        &mut self,
        symbol: Symbol,
        type_scheme: Option<TypeScheme>,
        value: ArrayExpression,
    ) -> Result<Vec<PILItem>, Error> {
        let expression = self
            .expression_processor(&Default::default())
            .process_array_expression(value)?;
        assert!(type_scheme.is_none() || type_scheme == Some(Type::Col.into()));
        let value = FunctionValueDefinition::Array(expression);

        Ok(vec![PILItem::Definition(symbol, Some(value))])
    }

    /// Given a list of (absolute_name, value) pairs, create PIL items for each of them.
    fn process_inner_definitions(
        &mut self,
        source: SourceRef,
        inner_items: Vec<(String, FunctionValueDefinition)>,
    ) -> Vec<PILItem> {
        inner_items
            .into_iter()
            .map(|(absolute_name, value)| {
                let symbol = Symbol {
                    id: self.counters.dispense_symbol_id(SymbolKind::Other(), None),
                    source: source.clone(),
                    absolute_name,
                    stage: None,
                    kind: SymbolKind::Other(),
                    length: None,
                    degree: None,
                };
                PILItem::Definition(symbol, Some(value))
            })
            .collect()
    }

    fn handle_public_declaration(
        &mut self,
        source: SourceRef,
        name: String,
        poly: parsed::NamespacedPolynomialReference,
        array_index: Option<parsed::Expression>,
        index: parsed::Expression,
    ) -> Result<Vec<PILItem>, Error> {
        let id = self.counters.dispense_public_id();
        let name = self.driver.resolve_decl(&name);
        let polynomial = self
            .expression_processor(&Default::default())
            .process_namespaced_polynomial_reference(poly)
            .map_err(|err| source.with_error(err))?;
        let type_vars = Default::default();
        let mut expression_processor = self.expression_processor(&type_vars);
        let array_index = array_index
            .map(|i| {
                let i = expression_processor.process_expression(i).map_err(|err| {
                    err.extend_message(|m| format!("Failed to process array index: {m}"))
                })?;
                let index: u64 = untyped_evaluator::evaluate_expression_to_int(self.driver, i)
                    .unwrap()
                    .try_into()
                    .unwrap();
                assert!(index <= usize::MAX as u64);
                Ok(index as usize)
            })
            .transpose()?;
        let index = expression_processor.process_expression(index)?;
        Ok(vec![PILItem::PublicDeclaration(PublicDeclaration {
            id,
            source,
            name: name.to_string(),
            polynomial,
            array_index,
            index: untyped_evaluator::evaluate_expression_to_int(self.driver, index)
                .unwrap()
                .try_into()
                .unwrap(),
        })])
    }

    fn expression_processor<'b>(
        &'b self,
        type_vars: &'b HashSet<&'b String>,
    ) -> ExpressionProcessor<'b, D> {
        ExpressionProcessor::new(self.driver, type_vars)
    }

    fn type_processor<'b>(&'b self, type_vars: &'b HashSet<&'b String>) -> TypeProcessor<'b, D> {
        TypeProcessor::new(self.driver, type_vars)
    }

    fn process_enum_declaration(
        &mut self,
        source: SourceRef,
        name: String,
        symbol: Symbol,
        enum_decl: EnumDeclaration<parsed::Expression>,
    ) -> Result<Vec<PILItem>, Error> {
        let type_vars = enum_decl.type_vars.vars().collect();
        let variants = enum_decl
            .variants
            .into_iter()
            .map(|v| self.process_enum_variant(v, &type_vars))
            .collect();
        let enum_decl = EnumDeclaration {
            name: self.driver.resolve_decl(&enum_decl.name),
            type_vars: enum_decl.type_vars,
            variants,
        };

        let inner_items: Vec<_> = enum_decl
            .variants
            .iter()
            .map(|variant| {
                (
                    self.driver
                        .resolve_namespaced_decl(&[&name, &variant.name])
                        .relative_to(&Default::default())
                        .to_string(),
                    FunctionValueDefinition::TypeConstructor(
                        Arc::new(enum_decl.clone()),
                        variant.clone(),
                    ),
                )
            })
            .collect();
        let var_items = self.process_inner_definitions(source, inner_items);

        Ok(iter::once(PILItem::Definition(
            symbol,
            Some(FunctionValueDefinition::TypeDeclaration(
                TypeDeclaration::Enum(enum_decl.clone()),
            )),
        ))
        .chain(var_items)
        .collect())
    }

    fn process_enum_variant(
        &self,
        enum_variant: EnumVariant<parsed::Expression>,
        type_vars: &HashSet<&String>,
    ) -> EnumVariant {
        EnumVariant {
            name: enum_variant.name,
            fields: enum_variant.fields.map(|f| {
                f.into_iter()
                    .map(|ty| self.type_processor(type_vars).process_type(ty))
                    .collect()
            }),
        }
    }

    fn process_struct_declaration(
        &mut self,
        symbol: Symbol,
        struct_decl: StructDeclaration<parsed::Expression>,
    ) -> Result<Vec<PILItem>, Error> {
        let StructDeclaration {
            name,
            type_vars,
            fields,
        } = struct_decl;
        let type_vars_set = type_vars.vars().collect();

        let fields = fields
            .into_iter()
            .map(|v| NamedType {
                name: v.name,
                ty: self.type_processor(&type_vars_set).process_type(v.ty),
            })
            .collect();

        let struct_decl = StructDeclaration {
            name: self.driver.resolve_decl(&name),
            type_vars,
            fields,
        };

        Ok(iter::once(PILItem::Definition(
            symbol,
            Some(FunctionValueDefinition::TypeDeclaration(
                TypeDeclaration::Struct(struct_decl),
            )),
        ))
        .collect())
    }

    fn process_trait_declaration(
        &mut self,
        source: SourceRef,
        name: String,
        symbol: Symbol,
        trait_decl: TraitDeclaration<parsed::Expression>,
    ) -> Result<Vec<PILItem>, Error> {
        let type_vars = trait_decl.type_vars.iter().collect();
        let functions = trait_decl
            .functions
            .into_iter()
            .map(|f| NamedType {
                name: f.name,
                ty: self.type_processor(&type_vars).process_type(f.ty),
            })
            .collect();
        let trait_decl = TraitDeclaration {
            name: self.driver.resolve_decl(&trait_decl.name),
            type_vars: trait_decl.type_vars,
            functions,
        };

        let inner_items = trait_decl
            .functions
            .iter()
            .map(|function| {
                (
                    self.driver
                        .resolve_namespaced_decl(&[&name, &function.name])
                        .relative_to(&Default::default())
                        .to_string(),
                    FunctionValueDefinition::TraitFunction(
                        Arc::new(trait_decl.clone()),
                        function.clone(),
                    ),
                )
            })
            .collect();
        let trait_functions = self.process_inner_definitions(source, inner_items);

        Ok(iter::once(PILItem::Definition(
            symbol,
            Some(FunctionValueDefinition::TraitDeclaration(
                trait_decl.clone(),
            )),
        ))
        .chain(trait_functions)
        .collect())
    }

    fn process_trait_implementation(
        &self,
        trait_impl: parsed::TraitImplementation<parsed::Expression>,
    ) -> Result<TraitImplementation<Expression>, Error> {
        let type_vars: HashSet<_> = trait_impl.type_scheme.vars.vars().collect();
        if !type_vars.is_empty() {
            unimplemented!("Generic impls are not supported yet.");
        }
        let functions = trait_impl
            .functions
            .into_iter()
            .map(|named| {
                let processed_expr = self
                    .expression_processor(&type_vars)
                    .process_expression(Arc::try_unwrap(named.body).unwrap())?;

                Ok(NamedExpression {
                    name: named.name,
                    body: Arc::new(processed_expr),
                })
            })
            .collect::<Result<Vec<NamedExpression<Arc<Expression>>>, Error>>()?;

        let Type::Tuple(TupleType { items }) = trait_impl.type_scheme.ty.clone() else {
            panic!("Type from trait scheme is not a tuple.")
        };

        let mapped_types: Vec<_> = items
            .into_iter()
            .map(|mut ty| {
                ty.map_to_type_vars(&type_vars);
                ty
            })
            .collect();

        let name = SymbolPath::from_str(
            &self
                .driver
                .resolve_ref(&trait_impl.name, SymbolCategory::TraitDeclaration)
                .map_err(|err| {
                    trait_impl
                        .source_ref
                        .with_error(format!("Cannot find trait {}: {}", trait_impl.name, err))
                })?,
        )
        .unwrap();

        Ok(TraitImplementation {
            name,
            source_ref: trait_impl.source_ref,
            type_scheme: TypeScheme {
                vars: trait_impl.type_scheme.vars,
                ty: Type::Tuple(TupleType {
                    items: mapped_types,
                }),
            },
            functions,
        })
    }
}

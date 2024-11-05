//! Component that turns data from the PILAnalyzer into Analyzed,
//! i.e. it turns more complex expressions in identities to simpler expressions.

use core::fmt::Debug;
use std::{
    collections::{hash_map::Entry, BTreeMap, HashMap, HashSet},
    iter::once,
    str::FromStr,
    sync::Arc,
};

use num_traits::sign::Signed;

use powdr_ast::{
    analyzed::{
        self, AlgebraicBinaryOperation, AlgebraicExpression, AlgebraicReference,
        AlgebraicUnaryOperation, Analyzed, Challenge, ConnectIdentity, DegreeRange, Expression,
        FunctionValueDefinition, Identity, LookupIdentity, PermutationIdentity,
        PhantomLookupIdentity, PhantomPermutationIdentity, PolyID, PolynomialIdentity,
        PolynomialReference, PolynomialType, PublicDeclaration, Reference, SelectedExpressions,
        SolvedTraitImpls, StatementIdentifier, Symbol, SymbolKind,
    },
    parsed::{
        self,
        asm::{AbsoluteSymbolPath, SymbolPath},
        display::format_type_scheme_around_name,
        types::{ArrayType, Type},
        visitor::{AllChildren, ExpressionVisitable},
        ArrayLiteral, BinaryOperation, BlockExpression, FunctionCall, FunctionKind,
        LambdaExpression, LetStatementInsideBlock, NamedExpression, Number, Pattern,
        SourceReference, StructExpression, TraitImplementation, TypedExpression, UnaryOperation,
    },
};
use powdr_number::{BigUint, FieldElement};
use powdr_parser_util::SourceRef;

use crate::{
    evaluator::{
        self, evaluate_function_call, Closure, Definitions, EnumValue, EvalError, StructValue,
        SymbolLookup, Value,
    },
    statement_processor::Counters,
};

pub fn condense<T: FieldElement>(
    mut definitions: HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
    solved_impls: SolvedTraitImpls,
    public_declarations: HashMap<String, PublicDeclaration>,
    proof_items: &[Expression],
    trait_impls: Vec<TraitImplementation<Expression>>,
    source_order: Vec<StatementIdentifier>,
    auto_added_symbols: HashSet<String>,
) -> Analyzed<T> {
    let mut condenser = Condenser::new(&definitions, &solved_impls);

    let mut condensed_identities = vec![];
    let mut prover_functions = vec![];
    let mut intermediate_columns = HashMap::new();
    let mut new_columns = vec![];
    let mut new_values = HashMap::new();
    // Condense identities and intermediate columns and update the source order.
    let source_order = source_order
        .into_iter()
        .flat_map(|s| {
            // Potentially modify the current namespace.
            if let StatementIdentifier::Definition(name) = &s {
                let mut namespace =
                    AbsoluteSymbolPath::default().join(SymbolPath::from_str(name).unwrap());
                namespace.pop();
                condenser.set_namespace_and_degree(namespace, definitions[name].0.degree);
            }

            // Condense identities and definitions.
            let statement = match s {
                StatementIdentifier::ProofItem(index) => {
                    condenser.condense_proof_item(&proof_items[index]);
                    None
                }
                StatementIdentifier::Definition(name)
                    if matches!(
                        definitions[&name].0.kind,
                        SymbolKind::Poly(PolynomialType::Intermediate)
                    ) =>
                {
                    let (symbol, definition) = &definitions[&name];
                    let Some(FunctionValueDefinition::Expression(e)) = definition else {
                        panic!("Expected expression")
                    };
                    let value = if let Some(length) = symbol.length {
                        let scheme = e.type_scheme.as_ref();
                        assert!(
                            scheme.unwrap().vars.is_empty()
                                && matches!(
                                &scheme.unwrap().ty,
                                Type::Array(ArrayType { base, length: _ })
                                if base.as_ref() == &Type::Inter),
                            "Intermediate column type has to be inter[], but got: {}",
                            format_type_scheme_around_name(&name, &e.type_scheme)
                        );
                        let result = condenser.condense_to_array_of_algebraic_expressions(&e.e);
                        assert_eq!(result.len() as u64, length);
                        result
                    } else {
                        assert_eq!(
                            e.type_scheme,
                            Some(Type::Inter.into()),
                            "Intermediate column type has to be inter, but got: {}",
                            format_type_scheme_around_name(&name, &e.type_scheme)
                        );
                        vec![condenser.condense_to_algebraic_expression(&e.e)]
                    };
                    intermediate_columns.insert(name.clone(), (symbol.clone(), value));
                    Some(StatementIdentifier::Definition(name))
                }
                s => Some(s),
            };

            let mut intermediate_values = condenser.extract_new_intermediate_column_values();

            // Extract and prepend the new columns, then identities, prover functions
            // and finally the original statement (if it exists).
            let new_cols = condenser
                .extract_new_columns()
                .into_iter()
                .map(|new_col| {
                    if new_col.kind == SymbolKind::Poly(PolynomialType::Intermediate) {
                        let name = new_col.absolute_name.clone();
                        let values = intermediate_values.remove(&name).unwrap();
                        intermediate_columns.insert(name, (new_col.clone(), values));
                    } else {
                        new_columns.push(new_col.clone());
                    }
                    StatementIdentifier::Definition(new_col.absolute_name)
                })
                .collect::<Vec<_>>();

            assert!(intermediate_values.is_empty(), "");

            let identity_statements = condenser
                .extract_new_constraints()
                .into_iter()
                .map(|identity| {
                    let index = condensed_identities.len();
                    condensed_identities.push(identity);
                    StatementIdentifier::ProofItem(index)
                })
                .collect::<Vec<_>>();

            let new_prover_functions = condenser
                .extract_new_prover_functions()
                .into_iter()
                .map(|f| {
                    let index = prover_functions.len();
                    prover_functions.push(f);
                    StatementIdentifier::ProverFunction(index)
                })
                .collect::<Vec<_>>();

            for (name, value) in condenser.extract_new_column_values() {
                if new_values.insert(name.clone(), value).is_some() {
                    panic!("Column {name} already has a hint set, but tried to add another one.",)
                }
            }

            new_cols
                .into_iter()
                .chain(identity_statements)
                .chain(new_prover_functions)
                .chain(statement)
        })
        .collect();

    definitions.retain(|name, _| !intermediate_columns.contains_key(name));
    for symbol in new_columns {
        definitions.insert(symbol.absolute_name.clone(), (symbol, None));
    }
    for (name, new_value) in new_values {
        if let Some((_, value)) = definitions.get_mut(&name) {
            if !value.is_none() {
                panic!(
                    "Column {name} already has a value / hint set, but tried to add another one."
                )
            }
            *value = Some(new_value);
        } else {
            panic!("Column {name} not found.");
        }
    }

    Analyzed {
        definitions,
        solved_impls,
        public_declarations,
        intermediate_columns,
        identities: condensed_identities,
        prover_functions,
        trait_impls,
        source_order,
        auto_added_symbols,
    }
}

type SymbolCache<'a, T> = HashMap<String, BTreeMap<Option<Vec<Type>>, Arc<Value<'a, T>>>>;

pub struct Condenser<'a, T> {
    degree: Option<DegreeRange>,
    /// All the definitions from the PIL file.
    symbols: &'a HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
    /// Pointers to expressions for all referenced trait implementations and the concrete types.
    solved_impls: &'a SolvedTraitImpls,
    /// Evaluation cache.
    symbol_values: SymbolCache<'a, T>,
    /// Current namespace (for names of generated columns).
    namespace: AbsoluteSymbolPath,
    /// ID dispensers.
    counters: Counters,
    /// The generated columns since the last extraction in creation order.
    new_columns: Vec<Symbol>,
    /// The hints and fixed column definitions added since the last extraction.
    new_column_values: HashMap<String, FunctionValueDefinition>,
    /// The values of intermediate columns generated since the last extraction.
    new_intermediate_column_values: HashMap<String, Vec<AlgebraicExpression<T>>>,
    /// The names of all new columns ever generated, to avoid duplicates.
    new_symbols: HashSet<String>,
    /// Constraints added since the last extraction. The values should be enums of type `std::prelude::Constr`.
    new_constraints: Vec<(Arc<Value<'a, T>>, SourceRef)>,
    /// Prover functions added since the last extraction.
    new_prover_functions: Vec<Expression>,
    /// The current stage. New columns are created at that stage.
    stage: u32,
}

impl<'a, T: FieldElement> Condenser<'a, T> {
    pub fn new(
        symbols: &'a HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
        solved_impls: &'a SolvedTraitImpls,
    ) -> Self {
        let counters = Counters::with_existing(symbols.values().map(|(sym, _)| sym), None, None);
        Self {
            degree: None,
            symbols,
            solved_impls,
            symbol_values: Default::default(),
            namespace: Default::default(),
            counters,
            new_columns: vec![],
            new_column_values: Default::default(),
            new_intermediate_column_values: Default::default(),
            new_symbols: HashSet::new(),
            new_constraints: vec![],
            new_prover_functions: vec![],
            stage: 0,
        }
    }

    pub fn condense_proof_item(&mut self, item: &'a Expression) {
        evaluator::evaluate(item, self)
            .and_then(|expr| {
                if let Value::Tuple(items) = expr.as_ref() {
                    assert!(items.is_empty());
                    Ok(())
                } else {
                    self.add_proof_items(expr, item.source_reference().clone())
                }
            })
            .unwrap_or_else(|err| {
                panic!(
                    "Error reducing expression to constraint:\nExpression: {item}\nError: {err:?}"
                )
            });
    }

    /// Sets the current namespace which will be used for newly generated witness columns.
    pub fn set_namespace_and_degree(
        &mut self,
        namespace: AbsoluteSymbolPath,
        degree: Option<DegreeRange>,
    ) {
        self.namespace = namespace;
        self.degree = degree;
    }

    /// Returns columns generated since the last call to this function.
    pub fn extract_new_columns(&mut self) -> Vec<Symbol> {
        std::mem::take(&mut self.new_columns)
    }

    /// Return the new column values (fixed column definitions or witness column hints)
    /// added since the last call to this function.
    pub fn extract_new_column_values(&mut self) -> HashMap<String, FunctionValueDefinition> {
        std::mem::take(&mut self.new_column_values)
    }

    /// Return the values of intermediate columns generated since the last call to this function.
    pub fn extract_new_intermediate_column_values(
        &mut self,
    ) -> HashMap<String, Vec<AlgebraicExpression<T>>> {
        std::mem::take(&mut self.new_intermediate_column_values)
    }

    /// Returns the new constraints generated since the last call to this function.
    pub fn extract_new_constraints(&mut self) -> Vec<Identity<T>> {
        self.new_constraints
            .drain(..)
            .map(|(item, source)| to_constraint(item.as_ref(), source, &mut self.counters))
            .collect()
    }

    /// Returns the new prover functions generated since the last call to this function.
    pub fn extract_new_prover_functions(&mut self) -> Vec<Expression> {
        std::mem::take(&mut self.new_prover_functions)
    }

    /// Evaluates the expression and expects it to result in an algebraic expression.
    fn condense_to_algebraic_expression(&mut self, e: &'a Expression) -> AlgebraicExpression<T> {
        let result = evaluator::evaluate(e, self).unwrap_or_else(|err| {
            panic!("Error reducing expression to constraint:\nExpression: {e}\nError: {err:?}")
        });
        match result.as_ref() {
            Value::Expression(expr) => expr.clone(),
            _ => panic!("Expected expression but got {result}"),
        }
    }

    /// Evaluates the expression and expects it to result in an array of algebraic expressions.
    fn condense_to_array_of_algebraic_expressions(
        &mut self,
        e: &'a Expression,
    ) -> Vec<AlgebraicExpression<T>> {
        let result = evaluator::evaluate(e, self).unwrap_or_else(|err| {
            panic!("Error reducing expression to constraint:\nExpression: {e}\nError: {err:?}")
        });
        match result.as_ref() {
            Value::Array(items) => items
                .iter()
                .map(|item| match item.as_ref() {
                    Value::Expression(expr) => expr.clone(),
                    _ => panic!("Expected expression but got {item}"),
                })
                .collect(),
            _ => panic!("Expected array of algebraic expressions but got {result}"),
        }
    }
}

impl<'a, T: FieldElement> SymbolLookup<'a, T> for Condenser<'a, T> {
    fn lookup(
        &mut self,
        name: &'a str,
        type_args: &Option<Vec<Type>>,
    ) -> Result<Arc<Value<'a, T>>, EvalError> {
        // Cache already computed values.
        // Note that the cache is essential because otherwise
        // we re-evaluate simple values, which users would not expect.
        if let Some(v) = self
            .symbol_values
            .get(name)
            .and_then(|map| map.get(type_args))
        {
            return Ok(v.clone());
        }
        let value = Definitions::lookup_with_symbols(
            self.symbols,
            self.solved_impls,
            name,
            type_args,
            self,
        )?;
        self.symbol_values
            .entry(name.to_string())
            .or_default()
            .entry(type_args.clone())
            .or_insert_with(|| value.clone());
        Ok(value)
    }

    fn lookup_public_reference(&self, name: &str) -> Result<Arc<Value<'a, T>>, EvalError> {
        Definitions {
            definitions: self.symbols,
            solved_impls: self.solved_impls,
        }
        .lookup_public_reference(name)
    }

    fn min_degree(&self) -> Result<Arc<Value<'a, T>>, EvalError> {
        let degree = self.degree.ok_or(EvalError::DataNotAvailable)?;
        Ok(Value::Integer(degree.min.into()).into())
    }

    fn max_degree(&self) -> Result<Arc<Value<'a, T>>, EvalError> {
        let degree = self.degree.ok_or(EvalError::DataNotAvailable)?;
        Ok(Value::Integer(degree.max.into()).into())
    }

    fn degree(&self) -> Result<Arc<Value<'a, T>>, EvalError> {
        let degree = self.degree.ok_or(EvalError::DataNotAvailable)?;
        if degree.min == degree.max {
            Ok(Value::Integer(degree.min.into()).into())
        } else {
            Err(EvalError::DataNotAvailable)
        }
    }

    fn new_column(
        &mut self,
        name: &str,
        ty: Option<&Type>,
        stage: Option<u32>,
        value: Option<Arc<Value<'a, T>>>,
        source: SourceRef,
    ) -> Result<Arc<Value<'a, T>>, EvalError> {
        let name = self.find_unused_name(name);
        let mut length = None;
        let mut is_array = false;
        let kind = match (ty, &value) {
            (Some(Type::Inter), Some(_)) => SymbolKind::Poly(PolynomialType::Intermediate),
            (Some(Type::Array(ArrayType { base, length: len })), Some(_))
                if base.as_ref() == &Type::Inter =>
            {
                is_array = true;
                length = *len;
                SymbolKind::Poly(PolynomialType::Intermediate)
            }
            (Some(Type::Col) | None, Some(_)) => SymbolKind::Poly(PolynomialType::Constant),
            (Some(Type::Col) | None, None) => SymbolKind::Poly(PolynomialType::Committed),
            _ => {
                return Err(EvalError::TypeError(format!(
                    "Invalid type for new column {name}: {}.",
                    ty.map(|ty| ty.to_string()).unwrap_or_default(),
                )))
            }
        };

        if kind == SymbolKind::Poly(PolynomialType::Intermediate) {
            let expr = if is_array {
                let Value::Array(exprs) = value.unwrap().as_ref().clone() else {
                    panic!("Expected array");
                };
                if let Some(length) = length {
                    if exprs.len() as u64 != length {
                        return Err(EvalError::TypeError(format!(
                            "Error creating intermediate column array {name}: Expected array of length {length} as value but it has {} elements." ,
                            exprs.len(),
                        )));
                    }
                } else {
                    length = Some(exprs.len() as u64);
                }
                exprs
                    .into_iter()
                    .map(|expr| {
                        let Value::Expression(expr) = expr.as_ref() else {
                            panic!("Expected algebraic expression");
                        };
                        expr.clone()
                    })
                    .collect()
            } else {
                let Value::Expression(expr) = value.unwrap().as_ref().clone() else {
                    panic!("Expected algebraic expression");
                };
                vec![expr]
            };
            self.new_intermediate_column_values
                .insert(name.clone(), expr);
        } else if let Some(value) = value {
            let value = try_to_function_value_definition(value.as_ref(), FunctionKind::Pure)
                .map_err(|e| match e {
                    EvalError::TypeError(e) => {
                        EvalError::TypeError(format!("Error creating fixed column {name}:\n{e}"))
                    }
                    _ => e,
                })?;

            self.new_column_values.insert(name.clone(), value);
        }

        if self.stage != 0 && stage.is_some() {
            return Err(EvalError::TypeError(format!(
                "Tried to create a column with an explicit stage ({}) while the current stage was not zero, but {}.",
                stage.unwrap(), self.stage
            )));
        }

        let stage = if matches!(
            kind,
            SymbolKind::Poly(PolynomialType::Constant | PolynomialType::Intermediate)
        ) {
            // Fixed columns are pre-stage 0 and the stage of an intermediate column
            // is the max of the stages in the value, so we omit it in both cases.
            assert!(stage.is_none());
            None
        } else {
            Some(stage.unwrap_or(self.stage))
        };

        let symbol = Symbol {
            id: self.counters.dispense_symbol_id(kind, length),
            source,
            absolute_name: name.clone(),
            stage,
            kind,
            length,
            degree: self.degree,
        };

        self.new_symbols.insert(name.clone());
        self.new_columns.push(symbol.clone());

        Ok((if is_array {
            Value::Array(
                symbol
                    .array_elements()
                    .map(|(name, poly_id)| {
                        Value::Expression(AlgebraicExpression::Reference(AlgebraicReference {
                            name,
                            poly_id,
                            next: false,
                        }))
                        .into()
                    })
                    .collect(),
            )
        } else {
            Value::Expression(AlgebraicExpression::Reference(AlgebraicReference {
                name,
                poly_id: PolyID::from(&symbol),
                next: false,
            }))
        })
        .into())
    }

    fn set_hint(
        &mut self,
        col: Arc<Value<'a, T>>,
        expr: Arc<Value<'a, T>>,
    ) -> Result<(), EvalError> {
        let name = match col.as_ref() {
            Value::Expression(AlgebraicExpression::Reference(AlgebraicReference {
                name,
                poly_id,
                next: false,
            })) => {
                if poly_id.ptype != PolynomialType::Committed {
                    return Err(EvalError::TypeError(format!(
                        "Expected reference to witness column as first argument for std::prelude::set_hint, but got {} column {name}.",
                        poly_id.ptype
                    )));
                }
                if name.contains('[') {
                    return Err(EvalError::TypeError(format!(
                        "Array elements are not supported for std::prelude::set_hint (called on {name})."
                    )));
                }
                name.clone()
            }
            col => {
                return Err(EvalError::TypeError(format!(
                    "Expected reference to witness column as first argument for std::prelude::set_hint, but got {col}: {}",
                    col.type_formatted()
                )));
            }
        };

        let value =
            try_to_function_value_definition(expr.as_ref(), FunctionKind::Query).map_err(|e| {
                match e {
                    EvalError::TypeError(e) => {
                        EvalError::TypeError(format!("Error setting hint for column {col}:\n{e}"))
                    }
                    _ => e,
                }
            })?;
        match self.new_column_values.entry(name) {
            Entry::Vacant(entry) => entry.insert(value),
            Entry::Occupied(_) => {
                return Err(EvalError::TypeError(format!(
                    "Column {col} already has a hint set, but tried to add another one."
                )));
            }
        };
        Ok(())
    }

    fn add_proof_items(
        &mut self,
        items: Arc<Value<'a, T>>,
        source: SourceRef,
    ) -> Result<(), EvalError> {
        match items.as_ref() {
            Value::Array(items) => {
                for item in items {
                    self.new_constraints.push((item.clone(), source.clone()));
                }
            }
            Value::Closure(..) => {
                let e = try_value_to_expression(&items).map_err(|e| {
                    EvalError::TypeError(format!("Error adding prover function:\n{e}"))
                })?;

                self.new_prover_functions.push(e);
            }
            _ => self.new_constraints.push((items, source)),
        }
        Ok(())
    }

    fn capture_constraints(
        &mut self,
        fun: Arc<Value<'a, T>>,
    ) -> Result<Arc<Value<'a, T>>, EvalError> {
        let existing_constraints = self.new_constraints.len();
        let result = evaluate_function_call(fun, vec![], self);
        let constrs = self
            .new_constraints
            .drain(existing_constraints..)
            .map(|(c, _)| c)
            .collect();
        let result = result?;
        assert!(
            matches!(result.as_ref(), Value::Tuple(items) if items.is_empty()),
            "Function should return ()"
        );

        Ok(Arc::new(Value::Array(constrs)))
    }

    fn at_next_stage(&mut self, fun: Arc<Value<'a, T>>) -> Result<(), EvalError> {
        self.stage += 1;
        let result = evaluate_function_call(fun, vec![], self);
        self.stage -= 1;
        let result = result?;
        if !matches!(result.as_ref(), Value::Tuple(items) if items.is_empty()) {
            panic!();
        }
        Ok(())
    }
}

impl<'a, T: FieldElement> Condenser<'a, T> {
    fn find_unused_name(&self, name: &str) -> String {
        once(None)
            .chain((1..).map(Some))
            .map(|cnt| format!("{name}{}", cnt.map(|c| format!("_{c}")).unwrap_or_default()))
            .map(|name| {
                self.namespace
                    .with_part(&name)
                    .relative_to(&Default::default())
                    .to_string()
            })
            .find(|name| !self.symbols.contains_key(name) && !self.new_symbols.contains(name))
            .unwrap()
    }
}

fn to_constraint<T: FieldElement>(
    constraint: &Value<'_, T>,
    source: SourceRef,
    counters: &mut Counters,
) -> Identity<T> {
    let Value::Enum(EnumValue {
        enum_decl,
        variant,
        data,
    }) = constraint
    else {
        panic!("Expected constraint but got {constraint}")
    };
    assert_eq!(enum_decl.name, "std::prelude::Constr");
    let fields = data.as_ref().unwrap();
    match &**variant {
        "Identity" => {
            assert_eq!(fields.len(), 2);
            PolynomialIdentity {
                id: counters.dispense_identity_id(),
                source,
                expression: to_expr(&fields[0]) - to_expr(&fields[1]),
            }
            .into()
        }
        "Lookup" | "Permutation" | "PhantomLookup" | "PhantomPermutation" => {
            if variant == &"PhantomLookup" {
                assert_eq!(fields.len(), 3);
            } else {
                assert_eq!(fields.len(), 2);
            }

            let (sel_from, sel_to) = if let Value::Tuple(t) = fields[0].as_ref() {
                assert_eq!(t.len(), 2);
                (&t[0], &t[1])
            } else {
                unreachable!()
            };

            let (from, to): (Vec<_>, Vec<_>) = if let Value::Array(a) = fields[1].as_ref() {
                a.iter()
                    .map(|pair| {
                        if let Value::Tuple(pair) = pair.as_ref() {
                            assert_eq!(pair.len(), 2);
                            (pair[0].as_ref(), pair[1].as_ref())
                        } else {
                            unreachable!()
                        }
                    })
                    .unzip()
            } else {
                unreachable!()
            };

            let id = counters.dispense_identity_id();
            let left = to_selected_exprs(sel_from, from);
            let right = to_selected_exprs(sel_to, to);

            match *variant {
                "Lookup" => LookupIdentity {
                    id,
                    source,
                    left,
                    right,
                }
                .into(),
                "Permutation" => PermutationIdentity {
                    id,
                    source,
                    left,
                    right,
                }
                .into(),
                "PhantomPermutation" => PhantomPermutationIdentity {
                    id,
                    source,
                    left,
                    right,
                }
                .into(),
                "PhantomLookup" => {
                    let multiplicity = to_expr(&fields[2]);
                    PhantomLookupIdentity {
                        id,
                        source,
                        left,
                        right,
                        multiplicity,
                    }
                    .into()
                }
                _ => unreachable!(),
            }
        }
        "Connection" => {
            assert_eq!(fields.len(), 1);

            let (from, to): (Vec<_>, Vec<_>) = if let Value::Array(a) = fields[0].as_ref() {
                a.iter()
                    .map(|pair| {
                        if let Value::Tuple(pair) = pair.as_ref() {
                            assert_eq!(pair.len(), 2);
                            (pair[0].as_ref(), pair[1].as_ref())
                        } else {
                            unreachable!()
                        }
                    })
                    .unzip()
            } else {
                unreachable!()
            };

            ConnectIdentity {
                id: counters.dispense_identity_id(),
                source,
                left: from.into_iter().map(to_expr).collect(),
                right: to.into_iter().map(to_expr).collect(),
            }
            .into()
        }
        _ => panic!("Expected constraint but got {constraint}"),
    }
}

fn to_selected_exprs<'a, T: FieldElement>(
    selector: &Value<'a, T>,
    exprs: Vec<&Value<'a, T>>,
) -> SelectedExpressions<T> {
    SelectedExpressions {
        selector: to_selector_expr(selector),
        expressions: exprs.into_iter().map(to_expr).collect(),
    }
}

/// Turns an optional selector expression into an algebraic expression. `None` gets turned into 1.
fn to_selector_expr<T: FieldElement>(value: &Value<'_, T>) -> AlgebraicExpression<T> {
    let Value::Enum(enum_value) = value else {
        panic!("Expected option but got {value:?}")
    };
    assert_eq!(enum_value.enum_decl.name, "std::prelude::Option");
    match enum_value.variant {
        "None" => T::one().into(),
        "Some" => {
            let fields = enum_value.data.as_ref().unwrap();
            assert_eq!(fields.len(), 1);
            to_expr(&fields[0])
        }
        _ => panic!(),
    }
}

fn to_expr<T: Clone + Debug>(value: &Value<'_, T>) -> AlgebraicExpression<T> {
    if let Value::Expression(expr) = value {
        (*expr).clone()
    } else {
        panic!()
    }
}

/// Turns a runtime value (usually a closure) into a FunctionValueDefinition
/// (i.e. an expression) and sets the expected function kind.
/// Does allow some forms of captured variables by prefixing them
/// via let statements.
fn try_to_function_value_definition<T: FieldElement>(
    value: &Value<'_, T>,
    expected_kind: FunctionKind,
) -> Result<FunctionValueDefinition, EvalError> {
    let mut e = try_value_to_expression(value)?;

    // Set the lambda kind since this is used to detect hints in some cases.
    // Can probably be removed once we have prover functions.
    if let Expression::LambdaExpression(_, LambdaExpression { kind, .. }) = &mut e {
        if *kind != FunctionKind::Pure && *kind != expected_kind {
            return Err(EvalError::TypeError(format!(
                "Expected {expected_kind} lambda expression but got {kind}.",
            )));
        }
        *kind = expected_kind;
    }

    Ok(FunctionValueDefinition::Expression(TypedExpression {
        e,
        type_scheme: None,
    }))
}

/// Turns a closure back into a (source) expression by prefixing
/// potentially captured variables as let statements.
fn try_closure_to_expression<T: FieldElement>(
    closure: &evaluator::Closure<'_, T>,
) -> Result<Expression, EvalError> {
    if !closure.type_args.is_empty() {
        return Err(EvalError::TypeError(
            "Lambda expression must not have type arguments.".to_string(),
        ));
    }

    // A closure essentially consists of a lambda expression (i.e. source code)
    // and an environment, which is a stack of runtime values. Some of these
    // values are captured, but not all of them.
    // If no values are captured, we can just return the lambda expression.
    // Otherwise, we will convert the captured values to expressions (using
    // try_value_to_expression) and introduce them as variables using let statements.

    // Create a map from old id to (new id, name, value) for all captured variables.
    let captured_var_refs = captured_var_refs(closure).collect::<BTreeMap<_, _>>();
    let env_map: BTreeMap<_, _> = closure
        .environment
        .iter()
        .enumerate()
        .filter_map(|(old_id, value)| {
            captured_var_refs
                .get(&(old_id as u64))
                .map(|name| (old_id as u64, (name, value)))
        })
        .enumerate()
        // Since we return a new expression we essentially start with an empty environment,
        // and thus the new IDs of the captured variables start with 0.
        // If we add more let statements further up in the call chain, they might be modified again.
        .map(|(new_id, (old_id, (&name, value)))| (old_id, (new_id as u64, name, value)))
        .collect();

    // Create the let statements for the captured variables.
    let statements = env_map
        .values()
        .map(|(new_id, name, value)| {
            let mut expr = try_value_to_expression(value.as_ref()).map_err(|e| {
                EvalError::TypeError(format!(
                    "Error converting captured variable {name} to expression:\n{e}",
                ))
            })?;
            // The call to try_value_to_expression assumed a fresh environment,
            // but we already have `new_id` let statements at this point,
            // so we adjust the local variable references inside `expr` accordingly.
            shift_local_var_refs(&mut expr, *new_id);

            Ok(LetStatementInsideBlock {
                pattern: Pattern::Variable(SourceRef::unknown(), (*name).clone()),
                // We do not know the type.
                ty: None,
                value: Some(expr),
            }
            .into())
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Adjust the variable references inside the lambda expression
    // to the new environment.
    let e = convert_closure_body(closure, env_map).into();

    Ok(if statements.is_empty() {
        e
    } else {
        BlockExpression {
            statements,
            expr: Some(Box::new(e)),
        }
        .into()
    })
}

/// Returns an iterator over all references to variables declared outside the closure,
/// i.e. the captured variables.
/// This does not include references to module-level variables.
fn captured_var_refs<'a, T>(
    closure: &'a Closure<'_, T>,
) -> impl Iterator<Item = (u64, &'a String)> {
    let environment_size = closure.environment.len() as u64;
    closure.lambda.all_children().filter_map(move |e| {
        if let Expression::Reference(_, Reference::LocalVar(id, name)) = e {
            (*id < environment_size).then_some((*id, name))
        } else {
            None
        }
    })
}

/// Convert the IDs of local variable references in the body of the closure to match the new environment
/// and return the new LambdaExpression.
fn convert_closure_body<T: FieldElement, V>(
    closure: &Closure<'_, T>,
    env_map: BTreeMap<u64, (u64, &String, V)>,
) -> LambdaExpression<analyzed::Expression> {
    let mut lambda = closure.lambda.clone();

    let old_environment_size = closure.environment.len() as u64;
    let new_environment_size = env_map.len() as u64;
    lambda.pre_visit_expressions_mut(&mut |e| {
        if let Expression::Reference(_, Reference::LocalVar(id, _)) = e {
            if *id >= old_environment_size {
                // This is a parameter of the function or a local variable
                // defined inside the function, i.e. not a variable referencing
                // a captured value.
                // We keep the ID but shift it to match the new environment size.
                *id = *id - old_environment_size + new_environment_size;
            } else {
                // Assign the new ID from the environment map.
                *id = env_map[id].0;
            }
        }
    });
    lambda
}

/// Increments all local variable reference IDs in `e` by `shift`,
/// to counter the effect of adding new variable declarations.
fn shift_local_var_refs(e: &mut Expression, shift: u64) {
    if let Expression::Reference(_, Reference::LocalVar(id, _)) = e {
        *id += shift;
    }

    e.children_mut()
        .for_each(|e| shift_local_var_refs(e, shift));
}

fn try_algebraic_expression_to_expression<T: FieldElement>(
    e: &AlgebraicExpression<T>,
) -> Result<Expression, EvalError> {
    Ok(match e {
        AlgebraicExpression::Reference(AlgebraicReference {
            name,
            poly_id: _,
            next,
        }) => {
            let e = Expression::Reference(
                SourceRef::unknown(),
                Reference::Poly(PolynomialReference {
                    name: name.clone(),
                    type_args: None,
                }),
            );
            if *next {
                UnaryOperation {
                    op: parsed::UnaryOperator::Next,
                    expr: Box::new(e),
                }
                .into()
            } else {
                e
            }
        }

        AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation { left, op, right }) => {
            BinaryOperation {
                left: Box::new(try_algebraic_expression_to_expression(left)?),
                op: (*op).into(),
                right: Box::new(try_algebraic_expression_to_expression(right)?),
            }
            .into()
        }

        AlgebraicExpression::UnaryOperation(AlgebraicUnaryOperation { op, expr }) => {
            UnaryOperation {
                op: (*op).into(),
                expr: Box::new(try_algebraic_expression_to_expression(expr)?),
            }
            .into()
        }

        AlgebraicExpression::Challenge(Challenge { id, stage }) => {
            let function = Expression::Reference(
                SourceRef::unknown(),
                Reference::Poly(PolynomialReference {
                    name: "std::prelude::challenge".to_string(),
                    type_args: None,
                }),
            )
            .into();
            let arguments = [*stage as u64, *id]
                .into_iter()
                .map(|x| BigUint::from(x).into())
                .collect();
            Expression::FunctionCall(
                SourceRef::unknown(),
                FunctionCall {
                    function,
                    arguments,
                },
            )
        }

        AlgebraicExpression::Number(n) => Number {
            value: n.to_arbitrary_integer(),
            type_: Some(Type::Expr),
        }
        .into(),

        AlgebraicExpression::PublicReference(s) => {
            Expression::PublicReference(SourceRef::unknown(), s.clone())
        }
    })
}

/// Tries to convert an evaluator value to an expression with the same value.
fn try_value_to_expression<T: FieldElement>(value: &Value<'_, T>) -> Result<Expression, EvalError> {
    Ok(match value {
        Value::Integer(v) => {
            if v.is_negative() {
                UnaryOperation {
                    op: parsed::UnaryOperator::Minus,
                    expr: Box::new(try_value_to_expression(&Value::<T>::Integer(-v))?),
                }
                .into()
            } else {
                Number {
                    value: BigUint::try_from(v).unwrap(),
                    type_: Some(Type::Int),
                }
                .into()
            }
        }
        Value::FieldElement(v) => Number {
            value: v.to_arbitrary_integer(),
            type_: Some(Type::Fe),
        }
        .into(),
        Value::String(s) => Expression::String(SourceRef::unknown(), s.clone()),
        Value::Bool(b) => Expression::Reference(
            SourceRef::unknown(),
            Reference::Poly(PolynomialReference {
                name: if *b {
                    "std::prelude::true"
                } else {
                    "std::prelude::false"
                }
                .to_string(),
                type_args: None,
            }),
        ),
        Value::Tuple(items) => Expression::Tuple(
            SourceRef::unknown(),
            items
                .iter()
                .map(|i| try_value_to_expression(i))
                .collect::<Result<_, _>>()?,
        ),
        Value::Array(items) => ArrayLiteral {
            items: items
                .iter()
                .map(|i| try_value_to_expression(i))
                .collect::<Result<_, _>>()?,
        }
        .into(),
        Value::Closure(c) => try_closure_to_expression(c)?,
        Value::TypeConstructor(type_constructor) => {
            return Err(EvalError::TypeError(format!(
                "Converting type constructor to expression not supported: {type_constructor}.",
            )))
        }
        Value::Enum(enum_value) => {
            let variant_ref = Expression::Reference(
                SourceRef::unknown(),
                Reference::Poly(PolynomialReference {
                    name: format!("{}::{}", enum_value.enum_decl.name, enum_value.variant),
                    // We do not know the type args here.
                    type_args: None,
                }),
            );
            match &enum_value.data {
                None => variant_ref,
                Some(items) => FunctionCall {
                    function: Box::new(variant_ref),
                    arguments: items
                        .iter()
                        .map(|i| try_value_to_expression(i))
                        .collect::<Result<_, _>>()?,
                }
                .into(),
            }
        }
        Value::BuiltinFunction(_) => {
            return Err(EvalError::TypeError(
                "Converting builtin functions to expressions not supported.".to_string(),
            ))
        }
        Value::Struct(StructValue { name, fields }) => {
            let name = Reference::Poly(PolynomialReference {
                name: name.to_string(),
                // We do not know the type args here.
                type_args: None,
            });
            let fields = fields
                .iter()
                .map(|(name, value)| {
                    Ok(NamedExpression {
                        name: name.to_string(),
                        body: Box::new(try_value_to_expression(value)?),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;

            StructExpression { name, fields }.into()
        }
        Value::Expression(e) => try_algebraic_expression_to_expression(e)?,
    })
}

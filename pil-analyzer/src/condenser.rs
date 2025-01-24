//! Component that turns data from the PILAnalyzer into Analyzed,
//! i.e. it turns more complex expressions in identities to simpler expressions.

use core::fmt::Debug;
use std::{
    collections::{hash_map::Entry, BTreeMap, HashMap, HashSet},
    iter::once,
    str::FromStr,
    sync::Arc,
};

use powdr_ast::analyzed::{
    AlgebraicExpression, AlgebraicReference, Analyzed, ConnectIdentity, DegreeRange, Expression,
    ExpressionList, FunctionValueDefinition, Identity, LookupIdentity, PermutationIdentity,
    PhantomBusInteractionIdentity, PhantomLookupIdentity, PhantomPermutationIdentity, PolyID,
    PolynomialIdentity, PolynomialType, PublicDeclaration, SelectedExpressions, SolvedTraitImpls,
    StatementIdentifier, Symbol, SymbolKind,
};
use powdr_ast::parsed::{
    asm::{AbsoluteSymbolPath, SymbolPath},
    display::format_type_scheme_around_name,
    types::{ArrayType, Type},
    FunctionKind, SourceReference, TraitImplementation,
};
use powdr_number::FieldElement;
use powdr_parser_util::SourceRef;

use crate::{
    evaluator::{
        self, evaluate_function_call, Definitions, EnumValue, EvalError, SymbolLookup, Value,
    },
    expressionizer::{try_to_function_value_definition, try_value_to_expression},
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

            #[allow(clippy::iter_over_hash_type)]
            // TODO: is this deterministic?
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
    #[allow(clippy::iter_over_hash_type)]
    // This is deterministic because insertion order does not matter.
    for symbol in new_columns {
        definitions.insert(symbol.absolute_name.clone(), (symbol, None));
    }
    #[allow(clippy::iter_over_hash_type)]
    // This is deterministic because definitions can be updated in any order.
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
    /// Mapping from polynomial ID to name (does not contain array elements),
    /// updated with new columns.
    poly_id_to_name: BTreeMap<(PolynomialType, u64), String>,
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
        let poly_id_to_name = symbols
            .iter()
            .filter_map(|(name, (symbol, _))| match &symbol.kind {
                SymbolKind::Poly(poly_type) => Some(((*poly_type, symbol.id), name.clone())),
                _ => None,
            })
            .collect();

        Self {
            degree: None,
            symbols,
            solved_impls,
            symbol_values: Default::default(),
            poly_id_to_name,
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
        let poly_type = match (ty, &value) {
            (Some(Type::Inter), Some(_)) => PolynomialType::Intermediate,
            (Some(Type::Array(ArrayType { base, length: len })), Some(_))
                if base.as_ref() == &Type::Inter =>
            {
                is_array = true;
                length = *len;
                PolynomialType::Intermediate
            }
            (Some(Type::Col) | None, Some(_)) => PolynomialType::Constant,
            (Some(Type::Col) | None, None) => PolynomialType::Committed,
            _ => {
                return Err(EvalError::TypeError(format!(
                    "Invalid type for new column {name}: {}.",
                    ty.map(|ty| ty.to_string()).unwrap_or_default(),
                )))
            }
        };

        if poly_type == PolynomialType::Intermediate {
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
            let value = try_to_function_value_definition(
                &self.poly_id_to_name,
                value.as_ref(),
                FunctionKind::Pure,
            )
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
            poly_type,
            PolynomialType::Constant | PolynomialType::Intermediate
        ) {
            // Fixed columns are pre-stage 0 and the stage of an intermediate column
            // is the max of the stages in the value, so we omit it in both cases.
            assert!(stage.is_none());
            None
        } else {
            Some(stage.unwrap_or(self.stage))
        };

        let kind = SymbolKind::Poly(poly_type);
        let id = self.counters.dispense_symbol_id(kind, length);
        let symbol = Symbol {
            id,
            source,
            absolute_name: name.clone(),
            stage,
            kind,
            length,
            degree: self.degree,
        };

        self.new_symbols.insert(name.clone());
        self.new_columns.push(symbol.clone());
        self.poly_id_to_name.insert((poly_type, id), name.clone());

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

        let value = try_to_function_value_definition(
            &self.poly_id_to_name,
            expr.as_ref(),
            FunctionKind::Query,
        )
        .map_err(|e| match e {
            EvalError::TypeError(e) => {
                EvalError::TypeError(format!("Error setting hint for column {col}:\n{e}"))
            }
            _ => e,
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
                let e = try_value_to_expression(&self.poly_id_to_name, &items).map_err(|e| {
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

impl<T: FieldElement> Condenser<'_, T> {
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
        "PhantomBusInteraction" => PhantomBusInteractionIdentity {
            id: counters.dispense_identity_id(),
            source,
            multiplicity: to_expr(&fields[0]),
            payload: ExpressionList(match fields[1].as_ref() {
                Value::Array(fields) => fields.iter().map(|f| to_expr(f)).collect(),
                _ => panic!("Expected array, got {:?}", fields[1]),
            }),
            latch: to_expr(&fields[2]),
        }
        .into(),
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

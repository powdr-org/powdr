use std::{collections::HashMap, sync::OnceLock};

use itertools::Itertools;
use powdr_ast::{
    analyzed::{Analyzed, Expression, FunctionValueDefinition, PolynomialReference, Reference},
    parsed::{
        asm::{Part, SymbolPath},
        display::quote,
        types::{ArrayType, FunctionType, TupleType, Type, TypeScheme},
        visitor::AllChildren,
        ArrayLiteral, BinaryOperation, BinaryOperator, BlockExpression, EnumDeclaration,
        FunctionCall, IfExpression, IndexAccess, LambdaExpression, LetStatementInsideBlock,
        MatchArm, MatchExpression, Number, Pattern, StatementInsideBlock, TypeDeclaration,
        UnaryOperation,
    },
};
use powdr_number::{BigInt, BigUint, FieldElement, LargeInt};

pub trait DefinitionFetcher {
    fn get_definition(&self, symbol: &str) -> Option<&FunctionValueDefinition>;
}

impl<T> DefinitionFetcher for Analyzed<T> {
    fn get_definition(&self, symbol: &str) -> Option<&FunctionValueDefinition> {
        self.definitions
            .get(symbol)
            .and_then(|(_, def)| def.as_ref())
    }
}

pub struct CodeGenerator<'a, T, Def: DefinitionFetcher> {
    definitions: &'a Def,
    /// Symbols mapping to either their code or an error message explaining
    /// why they could not be compiled.
    /// While the code is still being generated, this contains `None`.
    symbols: HashMap<String, Result<Option<String>, String>>,
    phantom: std::marker::PhantomData<T>,
}

pub fn escape_symbol(s: &str) -> String {
    // TODO better escaping
    s.replace('.', "_").replace("::", "_")
}

impl<'a, T: FieldElement, Def: DefinitionFetcher> CodeGenerator<'a, T, Def> {
    pub fn new(definitions: &'a Def) -> Self {
        Self {
            definitions,
            symbols: Default::default(),
            phantom: Default::default(),
        }
    }

    /// Tries to generate code for the symbol and all its dependencies.
    /// On success, returns an expression string for referencing the symbol,
    /// i.e. it evaluates to the value of the symbol.
    /// On failure, returns an error string.
    /// After a failure, `self` can still be used to request other symbols.
    /// The code can later be retrieved via `generated_code`.
    pub fn request_symbol(&mut self, name: &str, type_args: &[Type]) -> Result<String, String> {
        // For now, code generation is generic, only the reference uses the type args.
        // If that changes at some point, we need to store the type args in the symbol map as well.
        match self.symbols.get(name) {
            Some(Err(e)) => return Err(e.clone()),
            Some(_) => {}
            None => {
                let name = name.to_string();
                self.symbols.insert(name.clone(), Ok(None));
                match self.generate_code(&name) {
                    Ok(code) => {
                        self.symbols.insert(name.clone(), Ok(Some(code)));
                    }
                    Err(err) => {
                        self.symbols.insert(name.clone(), Err(err.clone()));
                        return Err(err);
                    }
                }
            }
        }
        Ok(self.symbol_reference(name, type_args))
    }

    /// Returns the concatenation of all successfully compiled symbols.
    pub fn generated_code(self) -> String {
        self.symbols
            .into_iter()
            .filter_map(|(s, r)| match r {
                Ok(Some(code)) => Some((s, code)),
                _ => None,
            })
            .sorted()
            .map(|(_, code)| code)
            .format("\n")
            .to_string()
    }

    fn generate_code(&mut self, symbol: &str) -> Result<String, String> {
        if let Some(code) = try_generate_builtin::<T>(symbol) {
            return Ok(code.clone());
        }

        let definition = self
            .definitions
            .get_definition(symbol)
            .ok_or_else(|| format!("No definition for {symbol}."))?;

        match definition {
            FunctionValueDefinition::TypeDeclaration(TypeDeclaration::Enum(EnumDeclaration {
                type_vars,
                variants,
                ..
            })) => Ok(format!(
                "#[derive(Clone)]\nenum {}<{type_vars}> {{\n{}\n}}\n",
                escape_symbol(symbol),
                variants
                    .iter()
                    .map(|v| {
                        let fields = v
                            .fields
                            .as_ref()
                            .map(|fields| format!("({})", fields.iter().map(map_type).join(", ")))
                            .unwrap_or_default();
                        format!("    {}{fields}", v.name)
                    })
                    .join(",\n")
            )),
            FunctionValueDefinition::TypeConstructor(decl, _) => {
                self.request_symbol(&decl.name, &[])?;
                Ok(String::new())
            }
            FunctionValueDefinition::Expression(value) => {
                let type_scheme = value
                    .type_scheme
                    .as_ref()
                    .ok_or_else(|| format!("Symbol does not have a type: {symbol}"))?;

                Ok(match (&value.e, type_scheme) {
                    (Expression::LambdaExpression(_, expr), type_scheme) => {
                        self.try_format_function(symbol, expr, type_scheme)?
                    }
                    _ => {
                        let type_scheme = value.type_scheme.as_ref().unwrap();
                        assert!(type_scheme.vars.is_empty());
                        let ty = if type_scheme.ty == Type::Col {
                            Type::Function(FunctionType {
                                params: vec![Type::Int],
                                value: Box::new(Type::Fe),
                            })
                        } else {
                            type_scheme.ty.clone()
                        };
                        // We need a lazy static here because we want symbols to only be
                        // evaluated once and the code is not `const` in the general case.
                        format!(
                            "lazy_static::lazy_static! {{\n\
                            static ref {}: {} = {};\n\
                            }}\n",
                            escape_symbol(symbol),
                            map_type(&ty),
                            self.format_expr(&value.e, 0)?
                        )
                    }
                })
            }
            _ => Err(format!("Definition of this kind not supported: {symbol}")),
        }
    }

    fn try_format_function(
        &mut self,
        name: &str,
        LambdaExpression { params, body, .. }: &LambdaExpression<Expression>,
        TypeScheme { vars, ty }: &TypeScheme,
    ) -> Result<String, String> {
        let (param_types, return_type) = &match ty {
            Type::Function(FunctionType { params, value }) => (params.clone(), (**value).clone()),
            Type::Col => {
                assert!(vars.is_empty());
                // TODO we assume it is an int -> fe function, even though other
                // types are possible.
                // At some point, the type inference algorithm should store the derived type.
                // Alternatively, we could insert a trait conversion function and store the type
                // in the trait vars.
                (vec![Type::Int], Type::Fe)
            }
            _ => return Err(format!("Expected function type, got {ty}")),
        };

        let var_height = params.iter().map(|p| p.variables().count()).sum::<usize>();

        let generics = if vars.is_empty() {
            String::new()
        } else {
            // TODO The bounds here will probably not compile because
            // some of the built-in ones do not exist as rust traits.
            // Also traits are not yet implemented in this compiler.
            format!(
                "<{}>",
                vars.bounds()
                    .map(|(var, bounds)| {
                        format!(
                            "{var}: Clone + Send + Sync{} + 'static",
                            bounds.iter().map(|b| format!(" + {b}")).format("")
                        )
                    })
                    .format(", ")
            )
        };
        Ok(format!(
            "fn {}{generics}(({}): ({})) -> {} {{ {} }}\n",
            escape_symbol(name),
            params.iter().format(", "),
            param_types.iter().map(map_type).format(", "),
            map_type(return_type),
            self.format_expr(body, var_height)?
        ))
    }

    fn format_expr(&mut self, e: &Expression, var_height: usize) -> Result<String, String> {
        Ok(match e {
            Expression::Reference(_, Reference::LocalVar(_id, name)) => name.clone(),
            Expression::Reference(_, Reference::Poly(PolynomialReference { name, type_args })) => {
                self.request_symbol(name, type_args.as_ref().unwrap())?
            }
            Expression::Number(
                _,
                Number {
                    value,
                    type_: Some(type_),
                },
            ) => match type_ {
                Type::Int => format_unsigned_integer(value),
                Type::Fe => {
                    let val = u64::try_from(value)
                        .map_err(|_| "Large numbers for fe not yet implemented.".to_string())?;
                    format!("FieldElement::from({val}_u64)",)
                }
                Type::Expr => {
                    let val = u64::try_from(value)
                        .map_err(|_| "Large numbers for expr not yet implemented.".to_string())?;
                    format!("Expr::from({val}_u64)")
                }
                Type::TypeVar(tv) => {
                    if let Ok(v) = u64::try_from(value) {
                        format!("{tv}::from_u64({v}_u64)")
                    } else {
                        let v_bytes = value.to_le_bytes();
                        let v = v_bytes.iter().map(|b| format!("{b}_u8")).format(", ");
                        format!("{tv}::from_le_bytes([{v}])")
                    }
                }
                _ => unreachable!(),
            },
            Expression::FunctionCall(
                _,
                FunctionCall {
                    function,
                    arguments,
                },
            ) => {
                format!(
                    "({}).call(({}))",
                    self.format_expr(function, var_height)?,
                    arguments
                        .iter()
                        .map(|a| self.format_expr(a, var_height))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        // TODO these should all be refs -> turn all types to arc
                        .map(|x| format!("{x}.clone()"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Expression::BinaryOperation(_, BinaryOperation { left, op, right }) => {
                let left = self.format_expr(left, var_height)?;
                let right = self.format_expr(right, var_height)?;
                match op {
                    BinaryOperator::ShiftLeft => {
                        format!("(({left}).clone() << usize::try_from(({right}).clone()).unwrap())")
                    }
                    BinaryOperator::ShiftRight => {
                        format!("(({left}).clone() >> usize::try_from(({right}).clone()).unwrap())")
                    }
                    BinaryOperator::Add => {
                        format!("Add::add(({left}).clone(), ({right}).clone())")
                    }
                    _ => format!("(({left}).clone() {op} ({right}).clone())"),
                }
            }
            Expression::UnaryOperation(_, UnaryOperation { op, expr }) => {
                format!("({op} ({}).clone())", self.format_expr(expr, var_height)?)
            }
            Expression::IndexAccess(_, IndexAccess { array, index }) => {
                format!(
                    "{}[usize::try_from({}).unwrap()].clone()",
                    self.format_expr(array, var_height)?,
                    self.format_expr(index, var_height)?
                )
            }
            Expression::LambdaExpression(
                _,
                LambdaExpression {
                    params,
                    body,
                    param_types,
                    ..
                },
            ) => {
                // Number of new variables introduced in the parameters.
                let new_vars = params.iter().map(|p| p.variables().count()).sum::<usize>();
                // We create clones of the captured variables so that we can move them into the closure.
                let captured_vars = body
                    .all_children()
                    .filter_map(|e| {
                        if let Expression::Reference(_, Reference::LocalVar(id, name)) = e {
                            (*id < var_height as u64).then_some(name)
                        } else {
                            None
                        }
                    })
                    .unique()
                    .map(|v| format!("let {v} = {v}.clone();"))
                    .format("\n");
                format!(
                    "Callable::Closure(std::sync::Arc::new({{\n{captured_vars}\nmove |({}): ({})| {{ ({}).clone() }}\n}}))",
                    params.iter().format(", "),
                    param_types.iter().map(map_type).format(", "),
                    self.format_expr(body, var_height + new_vars)?
                )
            }
            Expression::IfExpression(
                _,
                IfExpression {
                    condition,
                    body,
                    else_body,
                },
            ) => {
                format!(
                    "if {} {{ {} }} else {{ {} }}",
                    self.format_expr(condition, var_height)?,
                    self.format_expr(body, var_height)?,
                    self.format_expr(else_body, var_height)?
                )
            }
            Expression::ArrayLiteral(_, ArrayLiteral { items }) => {
                format!(
                    "PilVec::from(vec![{}])",
                    items
                        .iter()
                        .map(|i| self.format_expr(i, var_height))
                        .collect::<Result<Vec<_>, _>>()?
                        .join(", ")
                )
            }
            Expression::String(_, s) => format!("{}.to_string()", quote(s)),
            Expression::Tuple(_, items) => format!(
                "({})",
                items
                    .iter()
                    .map(|i| Ok(format!("({}.clone())", self.format_expr(i, var_height)?)))
                    .collect::<Result<Vec<_>, String>>()?
                    .join(", ")
            ),
            Expression::BlockExpression(_, BlockExpression { statements, expr }) => {
                let (formatted_statements, var_height) = statements.iter().try_fold(
                    (vec![], var_height),
                    |(mut formatted, var_height), s| {
                        let (formatted_statement, var_height) =
                            self.format_statement(s, var_height)?;
                        formatted.push(formatted_statement);
                        Ok::<_, String>((formatted, var_height))
                    },
                )?;
                format!(
                    "{{\n{}\n{}\n}}",
                    formatted_statements.join("\n"),
                    expr.as_ref()
                        .map(|e| self.format_expr(e.as_ref(), var_height))
                        .transpose()?
                        .unwrap_or_default()
                )
            }
            Expression::MatchExpression(_, MatchExpression { scrutinee, arms }) => {
                // We cannot use rust match expressions directly.
                // Instead, we compile to a sequence of `if let Some(...)` statements.

                // TODO try to find a solution where we do not introduce a variable
                // or at least make it unique.
                let var_name = "scrutinee__";
                format!(
                    "{{\nlet {var_name} = ({}).clone();\n{}\n}}\n",
                    self.format_expr(scrutinee, var_height)?,
                    arms.iter()
                        .map(|MatchArm { pattern, value }| {
                            let new_vars = pattern.variables().count();
                            let (bound_vars, arm_test) = check_pattern(var_name, pattern)?;
                            Ok(format!(
                                "if let Some({bound_vars}) = ({arm_test}) {{\n{}\n}}",
                                self.format_expr(value, var_height + new_vars)?,
                            ))
                        })
                        .chain(std::iter::once(Ok("{ panic!(\"No match\"); }".to_string())))
                        .collect::<Result<Vec<_>, String>>()?
                        .join(" else ")
                )
            }
            _ => return Err(format!("Implement {e}")),
        })
    }

    /// Formats a statement given a current variable height.
    /// Returns the formatted statement and the new variable height.
    fn format_statement(
        &mut self,
        s: &StatementInsideBlock<Expression>,
        var_height: usize,
    ) -> Result<(String, usize), String> {
        Ok(match s {
            StatementInsideBlock::LetStatement(LetStatementInsideBlock { pattern, ty, value }) => {
                let Some(value) = value else {
                    return Err(format!(
                        "Column creating 'let'-statements not yet supported: {s}"
                    ));
                };
                let value = self.format_expr(value, var_height)?;
                let var_name = "scrutinee__";
                let ty = ty
                    .as_ref()
                    .map(|ty| format!(": {}", map_type(ty)))
                    .unwrap_or_default();

                let (vars, code) = check_pattern(var_name, pattern)?;
                // TODO At some point, Rustc could complain that it needs an explicit type
                // for `{vars}`. We cannot use `ty` for that because the pattern translation
                // results in `()` for parts that do not have any captured variables.
                // The best way is probably to modify `check_pattern` to return the types
                (
                    format!("let {vars} = (|{var_name}{ty}| {code})({value}).unwrap();"),
                    var_height + pattern.variables().count(),
                )
            }
            StatementInsideBlock::Expression(e) => {
                (format!("{};", self.format_expr(e, var_height)?), var_height)
            }
        })
    }

    /// Returns a string expression evaluating to the value of the symbol.
    /// This is either the escaped name of the symbol or a deref operator
    /// applied to it.
    fn symbol_reference(&self, symbol: &str, type_args: &[Type]) -> String {
        let type_args = if type_args.is_empty() {
            "".to_string()
        } else {
            format!("::<{}>", type_args.iter().map(map_type).join(", "))
        };
        if is_builtin::<T>(symbol) {
            return format!("Callable::Fn({}{type_args})", escape_symbol(symbol));
        }
        match self.definitions.get_definition(symbol).unwrap() {
            FunctionValueDefinition::Expression(typed_expr) => {
                if matches!(typed_expr.e, Expression::LambdaExpression(..)) {
                    format!("Callable::Fn({}{type_args})", escape_symbol(symbol))
                } else {
                    format!("(*{}{type_args})", escape_symbol(symbol))
                }
            }
            FunctionValueDefinition::TypeConstructor(decl, variant) => {
                let formatted_variant = format!(
                    "{}::{}{type_args}",
                    escape_symbol(&decl.name),
                    escape_symbol(&variant.name)
                );
                if let Some(fields) = &variant.fields {
                    // Callable::Fn takes only a single argument, so we pack the fields into a tuple.
                    let field_vars = (0..fields.len()).map(|i| format!("v_{i}")).join(", ");
                    format!("Callable::Fn(|({field_vars})| {formatted_variant}({field_vars}))")
                } else {
                    formatted_variant
                }
            }
            _ => format!("(*{}{type_args})", escape_symbol(symbol)),
        }
    }
}

/// Used for patterns in match and let statements:
/// `value_name` is an expression string that is to be matched against `pattern`.
/// Returns a rust pattern string (tuple of bound variables, might be nested) and a code string
/// that, when executed, returns an Option with the values for the bound variables if the pattern
/// matched `value_name` and `None` otherwise.
///
/// So if `let (vars, code) = check_pattern("x", pattern)?;`, then the return value
/// can be used like this: `if let Some({vars}) = ({code}) {{ .. }}`
fn check_pattern(value_name: &str, pattern: &Pattern) -> Result<(String, String), String> {
    Ok(match pattern {
        Pattern::CatchAll(_) => ("()".to_string(), "Some(())".to_string()),
        Pattern::Number(_, n) => (
            "_".to_string(),
            format!(
                "({value_name}.clone() == {}).then_some(())",
                format_signed_integer(n)
            ),
        ),
        Pattern::String(_, s) => (
            "_".to_string(),
            format!("({value_name}.clone() == {}).then_some(())", quote(s)),
        ),
        Pattern::Tuple(_, items) => {
            let mut vars = vec![];
            let inner_code = items
                .iter()
                .enumerate()
                .map(|(i, item)| {
                    let (v, code) = check_pattern(&format!("{value_name}.{i}"), item)?;
                    vars.push(v);
                    Ok(format!("({code})?"))
                })
                .collect::<Result<Vec<_>, String>>()?
                .join(", ");
            (
                format!("({})", vars.join(", ")),
                format!("(|| Some(({inner_code})))()"),
            )
        }
        Pattern::Array(_, items) => {
            let mut vars = vec![];
            let mut ellipsis_seen = false;
            // This will be code to check the individual items in the array pattern.
            let inner_code = items
                .iter()
                .enumerate()
                .filter_map(|(i, item)| {
                    if matches!(item, Pattern::Ellipsis(_)) {
                        ellipsis_seen = true;
                        return None;
                    }
                    // Compute an expression to access the item.
                    Some(if ellipsis_seen {
                        let i_rev = items.len() - i;
                        (format!("{value_name}[{value_name}.len() - {i_rev}]"), item)
                    } else {
                        (format!("{value_name}[{i}]"), item)
                    })
                })
                .map(|(access_name, item)| {
                    let (v, code) = check_pattern(&access_name, item)?;
                    vars.push(v);
                    Ok(format!("({code})?"))
                })
                .collect::<Result<Vec<_>, String>>()?
                .join(", ");
            let length_check = if ellipsis_seen {
                format!("{value_name}.len() >= {}", items.len() - 1)
            } else {
                format!("{value_name}.len() == {}", items.len())
            };
            (
                format!("({})", vars.join(", ")),
                format!("if {length_check} {{ (|| Some(({inner_code})))() }} else {{ None }}"),
            )
        }
        Pattern::Variable(_, var) => (var.to_string(), format!("Some({value_name}.clone())")),
        Pattern::Enum(_, symbol, None) => (
            "()".to_string(),
            format!(
                "(matches!({value_name}, {}).then_some(()))",
                escape_enum_variant(symbol.clone())
            ),
        ),
        Pattern::Enum(_, symbol, Some(items)) => {
            // We first match the enum variant and bind all items to variables and
            // the recursively match the items, even if they are catch-all.
            // TODO check if we need `item__{i}` to be unique, i.e. if there could be clashes
            // with already existing variables or other patterns.
            let mut vars = vec![];
            let item_name = |i| format!("item__{i}");
            let inner_code = items
                .iter()
                .enumerate()
                .map(|(i, item)| {
                    let (v, code) = check_pattern(&item_name(i), item)?;
                    vars.push(v);
                    Ok(format!("({code})?"))
                })
                .collect::<Result<Vec<_>, String>>()?
                .join(", ");

            (
                format!("({})", vars.into_iter().format(", ")),
                format!(
                    "(|| if let {}({}) = ({value_name}).clone() {{ Some(({inner_code})) }} else {{ None }})()",
                    escape_enum_variant(symbol.clone()),
                    (0..items.len()).map(item_name).join(", "),
                ),
            )
        }
        Pattern::Ellipsis(_) => unreachable!(),
    })
}

fn format_unsigned_integer(n: &BigUint) -> String {
    if let Ok(n) = u64::try_from(n) {
        format!("ibig::IBig::from({n}_u64)")
    } else {
        format!(
            "ibig::IBig::from(ibig::UBig::from_le_bytes(&[{}]))",
            n.to_le_bytes()
                .iter()
                .map(|b| format!("{b}_u8"))
                .format(", ")
        )
    }
}

fn format_signed_integer(n: &BigInt) -> String {
    if let Ok(n) = BigUint::try_from(n) {
        format_unsigned_integer(&n)
    } else {
        format!(
            "-{}",
            format_unsigned_integer(&BigUint::try_from(-n).unwrap())
        )
    }
}

fn escape_enum_variant(mut s: SymbolPath) -> String {
    if let Some(Part::Named(variant)) = s.pop() {
        format!("{}::{variant}", escape_symbol(&s.to_string()))
    } else {
        panic!("Expected enum variant name.");
    }
}

fn map_type(ty: &Type) -> String {
    match ty {
        Type::Bottom | Type::Bool => format!("{ty}"),
        Type::Int => "ibig::IBig".to_string(),
        Type::Fe => "FieldElement".to_string(),
        Type::String => "String".to_string(),
        Type::Expr => "Expr".to_string(),
        Type::Array(ArrayType { base, length: _ }) => format!("PilVec<{}>", map_type(base)),
        Type::Tuple(TupleType { items }) => format!("({})", items.iter().map(map_type).join(", ")),
        Type::Function(ft) => format!(
            "Callable<({}), {}>",
            ft.params.iter().map(map_type).join(", "),
            map_type(&ft.value)
        ),
        Type::TypeVar(tv) => tv.to_string(),
        Type::NamedType(path, None) => escape_symbol(&path.to_string()),
        Type::NamedType(path, Some(type_args)) => {
            format!(
                "{}::<{}>",
                escape_symbol(&path.to_string()),
                type_args.iter().map(map_type).join(", ")
            )
        }
        Type::Col | Type::Inter => unreachable!(),
    }
}

fn get_builtins<T: FieldElement>() -> &'static HashMap<String, String> {
    static BUILTINS: OnceLock<HashMap<String, String>> = OnceLock::new();
    BUILTINS.get_or_init(|| {
        [
            (
                "std::array::len",
                "<T>(a: PilVec<T>) -> ibig::IBig { ibig::IBig::from(a.len()) }".to_string(),
            ),
            (
                "std::check::panic",
                "(s: String) -> ! { panic!(\"{s}\"); }".to_string(),
            ),
            (
                "std::convert::fe",
                "<T: Into<FieldElement>>(n: T) -> FieldElement { n.into() }".to_string(),
            ),
            (
                "std::convert::int",
                "<T: Into<ibig::IBig>>(n: T) -> ibig::IBig { n.into() }".to_string(),
            ),
            (
                "std::field::modulus",
                format!(
                    "() -> ibig::IBig {{ {} }}",
                    format_unsigned_integer(&T::modulus().to_arbitrary_integer())
                ),
            ),
            (
                "std::prover::degree",
                "(_: ()) -> ibig::IBig { DEGREE.read().unwrap().as_ref().unwrap().clone() }"
                    .to_string(),
            ),
        ]
        .into_iter()
        .map(|(name, code)| {
            (
                name.to_string(),
                format!("fn {}{code}", escape_symbol(name)),
            )
        })
        .collect()
    })
}

fn is_builtin<T: FieldElement>(symbol: &str) -> bool {
    get_builtins::<T>().contains_key(symbol)
}

fn try_generate_builtin<T: FieldElement>(symbol: &str) -> Option<&String> {
    get_builtins::<T>().get(symbol)
}

#[cfg(test)]
mod test {
    use powdr_number::GoldilocksField;
    use powdr_pil_analyzer::analyze_string;

    use pretty_assertions::assert_eq;

    use super::CodeGenerator;

    fn compile(input: &str, syms: &[&str]) -> String {
        let analyzed = analyze_string::<GoldilocksField>(input).unwrap();
        let mut compiler = CodeGenerator::<GoldilocksField, _>::new(&analyzed);
        for s in syms {
            compiler.request_symbol(s, &[]).unwrap();
        }
        compiler.generated_code()
    }

    #[test]
    fn empty_code() {
        let result = compile("", &[]);
        assert_eq!(result, "");
    }

    #[test]
    fn simple_fun() {
        let result = compile("let c: int -> int = |i| i;", &["c"]);
        assert_eq!(result, "fn c((i): (ibig::IBig)) -> ibig::IBig { i }\n");
    }

    #[test]
    fn fun_calls() {
        let result = compile(
            "let c: int -> int = |i| i + 20; let d = |k| c(k * 20);",
            &["c", "d"],
        );
        assert_eq!(
            result,
            "fn c((i): (ibig::IBig)) -> ibig::IBig { Add::add((i).clone(), (ibig::IBig::from(20_u64)).clone()) }\n\
            \n\
            fn d((k): (ibig::IBig)) -> ibig::IBig { (Callable::Fn(c)).call((((k).clone() * (ibig::IBig::from(20_u64)).clone()).clone())) }\n\
            "
        );
    }
}

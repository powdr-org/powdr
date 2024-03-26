use std::fmt::{Display, Formatter, Result};

use itertools::Itertools;

use crate::{
    parsed::{BinaryOperator, UnaryOperator},
    write_indented_by, write_items, write_items_indented,
};

use self::types::{ArrayType, FunctionType, TupleType, TypeBounds};

use super::{asm::*, *};

impl Display for PILFile {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write_items(f, &self.0)
    }
}

impl Display for ASMProgram {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.main)
    }
}

impl Display for ASMModule {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write_items(f, &self.statements)
    }
}

impl Display for ModuleStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            ModuleStatement::SymbolDefinition(SymbolDefinition { name, value }) => match value {
                SymbolValue::Machine(
                    m @ Machine {
                        arguments:
                            MachineArguments {
                                latch,
                                operation_id,
                            },
                        ..
                    },
                ) => {
                    if let (None, None) = (latch, operation_id) {
                        write!(f, "machine {name} {m}")
                    } else {
                        write!(
                            f,
                            "machine {name}({}, {}) {m}",
                            latch.as_deref().unwrap_or("_"),
                            operation_id.as_deref().unwrap_or("_"),
                        )
                    }
                }
                SymbolValue::Import(i) => {
                    write!(f, "{i} as {name};")
                }
                SymbolValue::Module(m @ Module::External(_)) => {
                    write!(f, "mod {m}")
                }
                SymbolValue::Module(m @ Module::Local(_)) => {
                    write!(f, "mod {name} {m}")
                }
                SymbolValue::Expression(TypedExpression { e, type_scheme }) => {
                    write!(
                        f,
                        "let{} = {e};",
                        format_type_scheme_around_name(name, type_scheme)
                    )
                }
                SymbolValue::TypeDeclaration(ty) => write!(f, "{ty}"),
            },
        }
    }
}

impl Display for Module {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Module::External(name) => write!(f, "{name};"),
            Module::Local(module) => {
                writeln!(f, "{{")?;
                write_items_indented(f, &module.statements)?;
                write!(f, "}}")
            }
        }
    }
}

impl Display for Import {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "use {}", self.path)
    }
}

impl Display for Machine {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        writeln!(f, "{{")?;
        write_items_indented(f, &self.statements)?;
        write!(f, "}}")
    }
}

impl Display for InstructionBody {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            InstructionBody::Local(elements) => write!(
                f,
                "{{ {} }}",
                elements
                    .iter()
                    .map(format_instruction_statement)
                    .format(", ")
            ),
            InstructionBody::CallablePlookup(r) => write!(f, " = {r};"),
            InstructionBody::CallablePermutation(r) => write!(f, " ~ {r};"),
        }
    }
}

fn format_instruction_statement(stmt: &PilStatement) -> String {
    match stmt {
        PilStatement::Expression(_, _)
        | PilStatement::PlookupIdentity(_, _, _)
        | PilStatement::PermutationIdentity(_, _, _)
        | PilStatement::ConnectIdentity(_, _, _) => {
            // statements inside instruction definition don't end in semicolon
            let mut s = format!("{stmt}");
            assert_eq!(s.pop(), Some(';'));
            s
        }
        _ => panic!("invalid statement inside instruction body: {}", stmt),
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}{}",
            self.params.prepend_space_if_non_empty(),
            self.body
        )
    }
}

impl Display for LinkDeclaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "link {} {} {};",
            self.flag,
            if self.is_permutation { "~>" } else { "=>" },
            self.to,
        )
    }
}

impl Display for CallableRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}.{} {}", self.instance, self.callable, self.params)
    }
}

impl Display for MachineStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            MachineStatement::Degree(_, degree) => write!(f, "degree {};", degree),
            MachineStatement::CallSelectors(_, sel) => write!(f, "call_selectors {};", sel),
            MachineStatement::Pil(_, statement) => write!(f, "{statement}"),
            MachineStatement::Submachine(_, ty, name) => write!(f, "{ty} {name};"),
            MachineStatement::RegisterDeclaration(_, name, flag) => write!(
                f,
                "reg {}{};",
                name,
                flag.as_ref()
                    .map(|flag| format!("[{flag}]"))
                    .unwrap_or_default()
            ),
            MachineStatement::InstructionDeclaration(_, name, instruction) => {
                write!(f, "instr {}{}", name, instruction)
            }
            MachineStatement::LinkDeclaration(_, link) => {
                write!(f, "{link}")
            }
            MachineStatement::FunctionDeclaration(_, name, params, statements) => {
                write!(
                    f,
                    "function {name}{} {{\n{}\n}}",
                    params.prepend_space_if_non_empty(),
                    statements.iter().format("\n")
                )
            }
            MachineStatement::OperationDeclaration(_, name, operation_id, params) => {
                let params_str = params.prepend_space_if_non_empty();
                write!(f, "operation {name}{operation_id}{params_str};")
            }
        }
    }
}

impl Display for OperationId {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match &self.id {
            Some(id) => write!(f, "<{id}>"),
            None => write!(f, ""),
        }
    }
}

impl Display for AssignmentRegister {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}",
            match self {
                Self::Register(r) => r.to_string(),
                Self::Wildcard => "_".to_string(),
            }
        )
    }
}

impl Display for FunctionStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            FunctionStatement::Assignment(_, write_regs, assignment_reg, expression) => write!(
                f,
                "{} <={}= {};",
                write_regs.join(", "),
                assignment_reg
                    .as_ref()
                    .map(|s| s.iter().format(", ").to_string())
                    .unwrap_or_default(),
                expression
            ),
            FunctionStatement::Instruction(_, name, inputs) => write!(
                f,
                "{}{};",
                name,
                if inputs.is_empty() {
                    "".to_string()
                } else {
                    format!(" {}", inputs.iter().format(", "))
                }
            ),
            FunctionStatement::Label(_, name) => write!(f, "{name}:"),
            FunctionStatement::DebugDirective(_, dir) => write!(f, "{dir}"),
            FunctionStatement::Return(_, values) => write!(
                f,
                "return{};",
                if values.is_empty() {
                    "".to_string()
                } else {
                    format!(" {}", values.iter().format(", "))
                }
            ),
        }
    }
}

impl Display for DebugDirective {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            DebugDirective::File(nr, path, file) => {
                write!(f, ".debug file {nr} {} {};", quote(path), quote(file))
            }
            DebugDirective::Loc(file, line, col) => {
                write!(f, ".debug loc {file} {line} {col};")
            }
            DebugDirective::OriginalInstruction(insn) => {
                write!(f, ".debug insn \"{insn}\";")
            }
        }
    }
}

impl Display for RegisterFlag {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            RegisterFlag::IsPC => write!(f, "@pc"),
            RegisterFlag::IsAssignment => write!(f, "<="),
            RegisterFlag::IsReadOnly => write!(f, "@r"),
        }
    }
}

impl<T: Display> Display for Params<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}{}{}",
            self.inputs.iter().format(", "),
            if self.outputs.is_empty() {
                ""
            } else if self.inputs.is_empty() {
                "-> "
            } else {
                " -> "
            },
            self.outputs.iter().format(", ")
        )
    }
}

impl<Ref: Display> Display for IndexAccess<Ref> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}[{}]", self.array, self.index)
    }
}

impl<Ref: Display> Display for FunctionCall<Ref> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}({})",
            self.function,
            format_expressions(&self.arguments)
        )
    }
}

impl<Ref: Display> Display for MatchArm<Ref> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{} => {},", self.pattern, self.value,)
    }
}

impl<Ref: Display> Display for MatchPattern<Ref> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            MatchPattern::CatchAll => write!(f, "_"),
            MatchPattern::Pattern(p) => write!(f, "{p}"),
        }
    }
}

impl<Ref: Display> Display for IfExpression<Ref> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "if {} {} else {}",
            self.condition, self.body, self.else_body
        )
    }
}

impl<Ref: Display> Display for LetStatementInsideBlock<Ref> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "let {}", self.name)?;
        if let Some(v) = &self.value {
            write!(f, " = {v};")
        } else {
            write!(f, ";")
        }
    }
}

impl Display for Param {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}{}{}",
            self.name,
            self.index
                .as_ref()
                .map(|i| format!("[{i}]"))
                .unwrap_or_default(),
            self.ty
                .as_ref()
                .map(|ty| format!(": {}", ty))
                .unwrap_or_default()
        )
    }
}

pub fn quote(input: &str) -> String {
    format!("\"{}\"", input.escape_default())
}

impl Display for PilStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            PilStatement::Include(_, path) => write!(f, "include {};", quote(path)),
            PilStatement::Namespace(_, name, poly_length) => {
                write!(f, "namespace {name}({poly_length});")
            }
            PilStatement::LetStatement(_, name, type_scheme, value) => write_indented_by(
                f,
                format!(
                    "let{}{};",
                    format_type_scheme_around_name(name, type_scheme),
                    value
                        .as_ref()
                        .map(|value| format!(" = {value}"))
                        .unwrap_or_default()
                ),
                1,
            ),
            PilStatement::PolynomialDefinition(_, name, value) => {
                write_indented_by(f, format!("pol {name} = {value};"), 1)
            }
            PilStatement::PublicDeclaration(_, name, poly, array_index, index) => {
                write_indented_by(
                    f,
                    format!(
                        "public {name} = {poly}{}({index});",
                        array_index
                            .as_ref()
                            .map(|i| format!("[{i}]"))
                            .unwrap_or_default()
                    ),
                    1,
                )
            }
            PilStatement::PolynomialConstantDeclaration(_, names) => {
                write_indented_by(f, format!("pol constant {};", names.iter().format(", ")), 1)
            }
            PilStatement::PolynomialConstantDefinition(_, name, definition) => {
                write_indented_by(f, format!("pol constant {name}{definition};"), 1)
            }
            PilStatement::PolynomialCommitDeclaration(_, stage, names, value) => write_indented_by(
                f,
                format!(
                    "pol commit {}{}{};",
                    stage.map(|s| format!("stage({s}) ")).unwrap_or_default(),
                    names.iter().format(", "),
                    value.as_ref().map(|v| format!("{v}")).unwrap_or_default()
                ),
                1,
            ),
            PilStatement::PlookupIdentity(_, left, right) => {
                write_indented_by(f, format!("{left} in {right};"), 1)
            }
            PilStatement::PermutationIdentity(_, left, right) => {
                write_indented_by(f, format!("{left} is {right};"), 1)
            }
            PilStatement::ConnectIdentity(_, left, right) => write_indented_by(
                f,
                format!(
                    "{{ {} }} connect {{ {} }};",
                    format_expressions(left),
                    format_expressions(right)
                ),
                1,
            ),
            PilStatement::ConstantDefinition(_, name, value) => {
                write_indented_by(f, format!("constant {name} = {value};"), 1)
            }
            PilStatement::Expression(_, e) => write_indented_by(f, format!("{e};"), 1),
            PilStatement::EnumDeclaration(_, enum_decl) => write_indented_by(f, enum_decl, 1),
        }
    }
}

impl Display for ArrayExpression {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            ArrayExpression::Value(expressions) => {
                write!(f, "[{}]", format_expressions(expressions))
            }
            ArrayExpression::RepeatedValue(expressions) => {
                write!(f, "[{}]*", format_expressions(expressions))
            }
            ArrayExpression::Concat(left, right) => write!(f, "{left} + {right}"),
        }
    }
}

impl Display for FunctionDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            FunctionDefinition::Array(array_expression) => {
                write!(f, " = {array_expression}")
            }
            FunctionDefinition::Query(Expression::LambdaExpression(lambda)) => write!(
                f,
                "({}) query {}",
                lambda.params.iter().format(", "),
                lambda.body,
            ),
            FunctionDefinition::Query(e) => {
                write!(f, " query = {e}")
            }
            FunctionDefinition::Expression(Expression::LambdaExpression(lambda))
                if lambda.params.len() == 1 =>
            {
                let body = if matches!(lambda.body.as_ref(), Expression::BlockExpression(_, _)) {
                    format!("{}", lambda.body)
                } else {
                    format!("{{ {} }}", lambda.body)
                };
                write!(f, "({}) {body}", lambda.params.iter().format(", "),)
            }
            FunctionDefinition::Expression(e) => write!(f, " = {e}"),
            FunctionDefinition::TypeDeclaration(_) => {
                panic!("Should not use this formatting function.")
            }
        }
    }
}

impl<E: Display> Display for EnumDeclaration<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        writeln!(f, "enum {} {{", self.name)?;
        write_items_indented(f, self.variants.iter())?;
        write!(f, "}}")
    }
}

impl<E: Display> Display for EnumVariant<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.name)?;
        if let Some(fields) = &self.fields {
            write!(
                f,
                "({})",
                fields.iter().map(format_type_with_parentheses).format(", ")
            )?;
        }
        write!(f, ",")
    }
}

pub fn format_expressions<Ref: Display>(expressions: &[Expression<Ref>]) -> String {
    format!("{}", expressions.iter().format(", "))
}

impl<Ref: Display> Display for Expression<Ref> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Expression::Reference(reference) => write!(f, "{reference}"),
            Expression::PublicReference(name) => write!(f, ":{name}"),
            Expression::Number(value, _) => write!(f, "{value}"),
            Expression::String(value) => write!(f, "{}", quote(value)),
            Expression::Tuple(items) => write!(f, "({})", format_expressions(items)),
            Expression::LambdaExpression(lambda) => write!(f, "{}", lambda),
            Expression::ArrayLiteral(array) => write!(f, "{array}"),
            Expression::BinaryOperation(left, op, right) => write!(f, "({left} {op} {right})"),
            Expression::UnaryOperation(op, exp) => {
                if op.is_prefix() {
                    write!(f, "{op}{exp}")
                } else {
                    write!(f, "{exp}{op}")
                }
            }
            Expression::IndexAccess(index_access) => write!(f, "{index_access}"),
            Expression::FunctionCall(fun_call) => write!(f, "{fun_call}"),
            Expression::FreeInput(input) => write!(f, "${{ {input} }}"),
            Expression::MatchExpression(scrutinee, arms) => {
                writeln!(f, "match {scrutinee} {{")?;
                write_items_indented(f, arms)?;
                write!(f, "}}")
            }
            Expression::IfExpression(e) => write!(f, "{e}"),
            Expression::BlockExpression(statements, expr) => {
                if statements.is_empty() {
                    write!(f, "{{ {expr} }}")
                } else {
                    writeln!(f, "{{")?;
                    write_items_indented(f, statements)?;
                    write_indented_by(f, expr, 1)?;
                    write!(f, "\n}}")
                }
            }
        }
    }
}

impl Display for PolynomialName {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}{}",
            self.name,
            self.array_size
                .as_ref()
                .map(|s| format!("[{s}]"))
                .unwrap_or_default()
        )
    }
}

impl Display for NamespacedPolynomialReference {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.path.to_dotted_string())
    }
}

impl<Ref: Display> Display for LambdaExpression<Ref> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "(|{}| {})", self.params.iter().format(", "), self.body)
    }
}

impl<Ref: Display> Display for ArrayLiteral<Ref> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "[{}]", self.items.iter().format(", "))
    }
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}",
            match self {
                BinaryOperator::Add => "+",
                BinaryOperator::Sub => "-",
                BinaryOperator::Mul => "*",
                BinaryOperator::Div => "/",
                BinaryOperator::Mod => "%",
                BinaryOperator::Pow => "**",
                BinaryOperator::BinaryAnd => "&",
                BinaryOperator::BinaryXor => "^",
                BinaryOperator::BinaryOr => "|",
                BinaryOperator::ShiftLeft => "<<",
                BinaryOperator::ShiftRight => ">>",
                BinaryOperator::LogicalOr => "||",
                BinaryOperator::LogicalAnd => "&&",
                BinaryOperator::Less => "<",
                BinaryOperator::LessEqual => "<=",
                BinaryOperator::Equal => "==",
                BinaryOperator::Identity => "=",
                BinaryOperator::NotEqual => "!=",
                BinaryOperator::GreaterEqual => ">=",
                BinaryOperator::Greater => ">",
            }
        )
    }
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}",
            match self {
                UnaryOperator::Minus => "-",
                UnaryOperator::LogicalNot => "!",
                UnaryOperator::Next => "'",
            }
        )
    }
}

impl<E: Display> Display for Type<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Type::Bottom => write!(f, "!"),
            Type::Bool => write!(f, "bool"),
            Type::Int => write!(f, "int"),
            Type::Fe => write!(f, "fe"),
            Type::String => write!(f, "string"),
            Type::Col => write!(f, "col"),
            Type::Expr => write!(f, "expr"),
            Type::Constr => write!(f, "constr"),
            Type::Array(array) => write!(f, "{array}"),
            Type::Tuple(tuple) => write!(f, "{tuple}"),
            Type::Function(fun) => write!(f, "{fun}"),
            Type::TypeVar(name) => write!(f, "{name}"),
            Type::NamedType(name) => write!(f, "{name}"),
        }
    }
}

impl<E: Display> Display for ArrayType<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}[{}]",
            format_type_with_parentheses(&self.base),
            self.length.iter().format("")
        )
    }
}

impl<E: Display> Display for TupleType<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "({})", format_list_of_types(&self.items))
    }
}

impl<E: Display> Display for FunctionType<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}{}-> {}",
            format_list_of_types(&self.params),
            if self.params.is_empty() { "" } else { " " },
            format_type_with_parentheses(&self.value)
        )
    }
}

fn format_type_with_parentheses<E: Display>(name: &Type<E>) -> String {
    if name.needs_parentheses() {
        format!("({name})")
    } else {
        name.to_string()
    }
}

fn format_list_of_types<E: Display>(types: &[Type<E>]) -> String {
    types
        .iter()
        .map(format_type_with_parentheses)
        .format(", ")
        .to_string()
}

pub fn format_type_scheme_around_name<E: Display>(
    name: &str,
    type_scheme: &Option<TypeScheme<E>>,
) -> String {
    if let Some(type_scheme) = type_scheme {
        format!(
            "{} {name}: {}",
            type_scheme.type_vars_to_string(),
            type_scheme.ty
        )
    } else {
        format!(" {name}")
    }
}

impl Display for TypeBounds {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        fn format_var((var, bounds): (&String, &BTreeSet<String>)) -> String {
            format!(
                "{var}{}",
                if bounds.is_empty() {
                    String::new()
                } else {
                    format!(": {}", bounds.iter().join(" + "))
                }
            )
        }
        write!(f, "{}", self.bounds().map(format_var).format(", "))
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn params() {
        let p = Param {
            name: "abc".into(),
            index: None,
            ty: Some("ty".into()),
        };
        assert_eq!(p.to_string(), "abc: ty");
        let empty = Params::<Param>::default();
        assert_eq!(empty.to_string(), "");
        assert_eq!(empty.prepend_space_if_non_empty(), "");
        let in_out = Params {
            inputs: vec![
                Param {
                    name: "abc".into(),
                    index: Some(7u32.into()),
                    ty: Some("ty0".into()),
                },
                Param {
                    name: "def".into(),
                    index: None,
                    ty: Some("ty1".into()),
                },
            ],
            outputs: vec![
                Param {
                    name: "abc".into(),
                    index: None,
                    ty: Some("ty0".into()),
                },
                Param {
                    name: "def".into(),
                    index: Some(2u32.into()),
                    ty: Some("ty1".into()),
                },
            ],
        };
        assert_eq!(
            in_out.to_string(),
            "abc[7]: ty0, def: ty1 -> abc: ty0, def[2]: ty1"
        );
        assert_eq!(
            in_out.prepend_space_if_non_empty(),
            " abc[7]: ty0, def: ty1 -> abc: ty0, def[2]: ty1"
        );
        let out = Params {
            inputs: vec![],
            outputs: vec![Param {
                name: "abc".into(),
                index: None,
                ty: Some("ty".into()),
            }],
        };
        assert_eq!(out.to_string(), "-> abc: ty");
        assert_eq!(out.prepend_space_if_non_empty(), " -> abc: ty");
        let _in = Params {
            inputs: vec![Param {
                name: "abc".into(),
                index: None,
                ty: Some("ty".into()),
            }],
            outputs: vec![],
        };
        assert_eq!(_in.to_string(), "abc: ty");
        assert_eq!(_in.prepend_space_if_non_empty(), " abc: ty");
    }

    #[test]
    fn symbol_paths() {
        let s = SymbolPath::from_parts(vec![
            Part::Named("x".to_string()),
            Part::Super,
            Part::Named("y".to_string()),
        ]);
        assert_eq!(s.to_string(), "x::super::y");
        let p = parse_absolute_path("::abc");
        assert_eq!(p.to_string(), "::abc");

        assert_eq!(p.with_part("t").to_string(), "::abc::t");

        assert_eq!(p.clone().join(s.clone()).to_string(), "::abc::y");
        assert_eq!(SymbolPath::from(p.join(s)).to_string(), "::abc::y");
    }
}

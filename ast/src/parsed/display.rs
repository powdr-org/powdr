use std::fmt::{Display, Formatter, Result};

use itertools::Itertools;

use crate::{
    indent,
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
            ModuleStatement::SymbolDefinition(symbol_def) => write!(f, "{symbol_def}"),
            ModuleStatement::TraitImplementation(trait_impl) => write!(f, "{trait_impl}"),
        }
    }
}

impl Display for SymbolDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let SymbolDefinition { name, value } = self;
        match value {
            SymbolValue::Machine(m) => {
                write!(f, "machine {name}{m}")
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
            SymbolValue::TraitDeclaration(trait_decl) => write!(f, "{trait_decl}"),
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
        writeln!(f, "{}{} {{", &self.params, &self.properties)?;
        write_items_indented(f, &self.statements)?;
        write!(f, "}}")
    }
}

impl Display for MachineParams {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let args = self.0.iter().join(", ");
        if !args.is_empty() {
            write!(f, "({args})")?;
        }
        Ok(())
    }
}

impl Display for MachineProperties {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let props = self
            .degree
            .as_ref()
            .map(|s| format!("degree: {s}"))
            .into_iter()
            .chain(self.latch.as_ref().map(|s| format!("latch: {s}")))
            .chain(
                self.operation_id
                    .as_ref()
                    .map(|s| format!("operation_id: {s}")),
            )
            .chain(
                self.call_selectors
                    .as_ref()
                    .map(|s| format!("call_selectors: {s}")),
            )
            .join(", ");
        if !props.is_empty() {
            write!(f, " with {props}")?;
        }
        Ok(())
    }
}

impl Display for InstructionBody {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{{ {} }}",
            self.0.iter().map(format_instruction_statement).format(", ")
        )
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
        _ => panic!("invalid statement inside instruction body: {stmt}"),
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}{}{}",
            self.params.prepend_space_if_non_empty(),
            if self.links.is_empty() {
                "".to_string()
            } else {
                " ".to_string() + &self.links.iter().join(" ")
            },
            self.body
        )
    }
}

impl Display for LinkDeclaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "link {}{} {}",
            if self.flag == 1.into() {
                "".to_string()
            } else {
                format!("if {} ", self.flag)
            },
            if self.is_permutation { "~>" } else { "=>" },
            self.link,
        )
    }
}

impl Display for CallableRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}{}.{}({})",
            match &self.params.outputs[..] {
                [] => "".to_string(),
                [output] => format!("{output} = "),
                outputs => format!("({}) = ", outputs.iter().join(", ")),
            },
            self.instance,
            self.callable,
            self.params.inputs.iter().join(", ")
        )
    }
}

impl Display for MachineStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            MachineStatement::Pil(_, statement) => write!(f, "{statement}"),
            MachineStatement::Submachine(_, ty, name, args) => {
                let mut args = args.iter().join(", ");
                if !args.is_empty() {
                    args = format!("({args})");
                }
                write!(f, "{ty} {name}{args};")
            }
            MachineStatement::RegisterDeclaration(_, name, flag) => write!(
                f,
                "reg {}{};",
                name,
                flag.as_ref()
                    .map(|flag| format!("[{flag}]"))
                    .unwrap_or_default()
            ),
            MachineStatement::InstructionDeclaration(_, name, instruction) => {
                write!(f, "instr {name}{instruction}")
            }
            MachineStatement::LinkDeclaration(_, link) => {
                write!(f, "{link};")
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

impl<E: Display> Display for IndexAccess<Expression<E>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        if self.array.precedence().is_none() {
            write!(f, "{}[{}]", self.array, self.index)
        } else {
            write!(f, "({})[{}]", self.array, self.index)
        }
    }
}

impl<E: Display> Display for FunctionCall<Expression<E>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        if self.function.precedence().is_none() {
            write!(f, "{}({})", self.function, format_list(&self.arguments))
        } else {
            write!(f, "({})({})", self.function, format_list(&self.arguments))
        }
    }
}

impl<E: Display> Display for MatchArm<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{} => {},", self.pattern, self.value,)
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Pattern::CatchAll(_) => write!(f, "_"),
            Pattern::Ellipsis(_) => write!(f, ".."),
            Pattern::Number(_, n) => write!(f, "{n}"),
            Pattern::String(_, s) => write!(f, "{}", quote(s)),
            Pattern::Tuple(_, t) => write!(f, "({})", t.iter().format(", ")),
            Pattern::Array(_, a) => write!(f, "[{}]", a.iter().format(", ")),
            Pattern::Variable(_, v) => write!(f, "{v}"),
            Pattern::Enum(_, name, fields) => write!(
                f,
                "{name}{}",
                fields
                    .as_ref()
                    .map(|fields| format!("({})", fields.iter().format(", ")))
                    .unwrap_or_default()
            ),
        }
    }
}

impl<E: Display> Display for IfExpression<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "if {} {} else {}",
            self.condition, self.body, self.else_body
        )
    }
}

impl<E: Display> Display for StatementInsideBlock<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            StatementInsideBlock::LetStatement(s) => write!(f, "{s}"),
            StatementInsideBlock::Expression(e) => write!(f, "{e};"),
        }
    }
}

impl<E: Display> Display for LetStatementInsideBlock<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "let {}", self.pattern)?;
        if let Some(ty) = &self.ty {
            write!(f, ": {ty}")?;
        }
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
                .map(|ty| format!(": {ty}"))
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
                write!(f, "namespace")?;
                let name = name.to_string();
                match poly_length {
                    None if name.is_empty() => {
                        write!(f, ";")
                    }
                    None => {
                        write!(f, " {name};")
                    }
                    Some(poly_length) => {
                        write!(f, " {name}({poly_length});")
                    }
                }
            }
            PilStatement::LetStatement(_, pattern, type_scheme, value) => write_indented_by(
                f,
                format!(
                    "let{}{};",
                    format_type_scheme_around_name(pattern, type_scheme),
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
                    "[ {} ] connect [ {} ];",
                    format_list(left),
                    format_list(right)
                ),
                1,
            ),
            PilStatement::Expression(_, e) => write_indented_by(f, format!("{e};"), 1),
            PilStatement::EnumDeclaration(_, enum_decl) => write_indented_by(f, enum_decl, 1),
            PilStatement::TraitImplementation(_, trait_impl) => write_indented_by(f, trait_impl, 1),
            PilStatement::TraitDeclaration(_, trait_decl) => write_indented_by(f, trait_decl, 1),
        }
    }
}

impl Display for FunctionDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            FunctionDefinition::Expression(Expression::LambdaExpression(_, lambda))
                if lambda.params.len() == 1 =>
            {
                write!(
                    f,
                    "({}) {}{}",
                    format_list(&lambda.params),
                    match lambda.kind {
                        FunctionKind::Pure => "".into(),
                        _ => format!("{} ", &lambda.kind),
                    },
                    lambda.body
                )
            }
            FunctionDefinition::Expression(e) => write!(f, " = {e}"),
            FunctionDefinition::TypeDeclaration(_) | FunctionDefinition::TraitDeclaration(_) => {
                panic!("Should not use this formatting function.")
            }
        }
    }
}

impl<E: Display> Display for TraitDeclaration<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "trait {name}<{type_vars}> {{\n{functions}}}",
            name = self.name,
            type_vars = self.type_vars.iter().format(", "),
            functions = indent(
                self.functions.iter().map(|m| format!("{m},\n")).format(""),
                1
            )
        )
    }
}

impl<E: Display> Display for TraitFunction<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}: {}", self.name, self.ty)
    }
}

impl<E: Display> Display for EnumDeclaration<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.to_string_with_name(&self.name))
    }
}

impl<E: Display> EnumDeclaration<E> {
    /// Formats the enum declaration, exchanging its name by the provided one.
    pub fn to_string_with_name(&self, name: &str) -> String {
        let type_vars = if self.type_vars.is_empty() {
            Default::default()
        } else {
            format!("<{}>", self.type_vars)
        };
        format!(
            "enum {name}{type_vars} {{\n{}}}",
            indent(
                self.variants.iter().map(|v| format!("{v},\n")).format(""),
                1
            )
        )
    }
}

impl<E: Display> Display for TraitImplementation<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let type_vars = if self.type_scheme.vars.is_empty() {
            Default::default()
        } else {
            format!("<{}>", self.type_scheme.vars)
        };

        let Type::Tuple(TupleType { items }) = &self.type_scheme.ty else {
            panic!("Type from trait scheme is not a tuple.")
        };

        let trait_vars = if items.is_empty() {
            Default::default()
        } else {
            format!("<{}>", items.iter().format(", "))
        };

        write!(
            f,
            "impl{type_vars} {trait_name}{trait_vars} {{\n{methods}}}",
            trait_name = self.name,
            methods = indent(
                self.functions.iter().map(|m| format!("{m},\n")).format(""),
                1
            )
        )
    }
}

impl<Expr: Display> Display for SelectedExpressions<Expr> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}{}",
            self.selector
                .as_ref()
                .map(|s| format!("{s} $ "))
                .unwrap_or_default(),
            self.expressions
        )
    }
}

impl<E: Display> Display for NamedExpression<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}: {}", self.name, self.body)
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
        Ok(())
    }
}

fn format_list<L: IntoIterator<Item = I>, I: Display>(list: L) -> String {
    format!("{}", list.into_iter().format(", "))
}

impl<Ref: Display> Display for Expression<Ref> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Expression::Reference(_, reference) => write!(f, "{reference}"),
            Expression::PublicReference(_, name) => write!(f, ":{name}"),
            Expression::Number(_, Number { value, .. }) => write!(f, "{value}"),
            Expression::String(_, value) => write!(f, "{}", quote(value)),
            Expression::Tuple(_, items) => write!(f, "({})", format_list(items)),
            Expression::LambdaExpression(_, lambda) => write!(f, "{lambda}"),
            Expression::ArrayLiteral(_, array) => write!(f, "{array}"),
            Expression::BinaryOperation(_, binaryop) => {
                write!(f, "{binaryop}")
            }
            Expression::UnaryOperation(_, unaryop) => {
                write!(f, "{unaryop}")
            }
            Expression::IndexAccess(_, index_access) => write!(f, "{index_access}"),
            Expression::FunctionCall(_, fun_call) => write!(f, "{fun_call}"),
            Expression::FreeInput(_, input) => write!(f, "${{ {input} }}"),
            Expression::MatchExpression(_, match_expr) => {
                write!(f, "{match_expr}")
            }
            Expression::IfExpression(_, e) => write!(f, "{e}"),
            Expression::BlockExpression(_, block_expr) => {
                write!(f, "{block_expr}")
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
        if let Some(type_args) = &self.type_args {
            write!(f, "{}::{}", self.path, format_type_args(type_args))
        } else {
            write!(f, "{}", self.path.to_dotted_string())
        }
    }
}

impl<E: Display> Display for LambdaExpression<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "({}|{}| {})",
            match self.kind {
                FunctionKind::Pure => "".into(),
                _ => format!("{} ", &self.kind),
            },
            format_list(&self.params),
            self.body
        )
    }
}

impl<E: Display> Display for MatchExpression<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        writeln!(f, "match {} {{", self.scrutinee)?;
        write_items_indented(f, &self.arms)?;
        write!(f, "}}")
    }
}

impl Display for FunctionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FunctionKind::Pure => write!(f, "pure"),
            FunctionKind::Constr => write!(f, "constr"),
            FunctionKind::Query => write!(f, "query"),
        }
    }
}

impl<E: Display> Display for ArrayLiteral<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "[{}]", format_list(&self.items))
    }
}

impl<E> Display for BinaryOperation<E>
where
    E: Display + Precedence,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let force_parentheses = matches!(self.op, BinaryOperator::Pow);

        let op_precedence = self.op.precedence().unwrap();
        let use_left_parentheses = match self.left.precedence() {
            Some(left_precedence) => {
                force_parentheses
                    || left_precedence > op_precedence
                    || (left_precedence == op_precedence
                        && self.op.associativity() != BinaryOperatorAssociativity::Left)
            }
            None => false,
        };

        let use_right_parentheses = match self.right.precedence() {
            Some(right_precedence) => {
                force_parentheses
                    || right_precedence > op_precedence
                    || (right_precedence == op_precedence
                        && self.op.associativity() != BinaryOperatorAssociativity::Right)
            }
            None => false,
        };

        let left_string = if use_left_parentheses {
            format!("({})", self.left)
        } else {
            format!("{}", self.left)
        };
        let right_string = if use_right_parentheses {
            format!("({})", self.right)
        } else {
            format!("{}", self.right)
        };

        write!(f, "{left_string} {} {right_string}", self.op)
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

impl<E> Display for UnaryOperation<E>
where
    E: Display + Precedence,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let exp_string = match (self.op.precedence(), self.expr.precedence()) {
            (Some(precedence), Some(inner_precedence)) if precedence < inner_precedence => {
                format!("({})", self.expr)
            }
            _ => {
                format!("{}", self.expr)
            }
        };

        if self.op.is_prefix() {
            write!(f, "{}{exp_string}", self.op)
        } else {
            write!(f, "{exp_string}{}", self.op)
        }
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

impl<E: Display> Display for BlockExpression<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        if self.statements.is_empty() {
            if let Some(expr) = &self.expr {
                write!(f, "{{ {expr} }}")
            } else {
                write!(f, "{{ }}")
            }
        } else {
            writeln!(f, "{{")?;
            write_items_indented(f, &self.statements)?;
            if let Some(expr) = &self.expr {
                write_indented_by(f, expr, 1)?;
            }
            write!(f, "\n}}")
        }
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
            Type::Array(array) => write!(f, "{array}"),
            Type::Tuple(tuple) => write!(f, "{tuple}"),
            Type::Function(fun) => write!(f, "{fun}"),
            Type::TypeVar(name) => write!(f, "{name}"),
            Type::NamedType(name, Some(args)) => {
                write!(f, "{name}{}", format_type_args(args))
            }
            Type::NamedType(name, None) => write!(f, "{name}"),
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

/// Formats a list of types to be used as values for type arguments
/// and puts them in angle brackets.
/// Puts the last item in parentheses if it ends in `>` to avoid parser problems.
pub fn format_type_args<E: Display>(args: &[Type<E>]) -> String {
    format!(
        "<{}>",
        args.iter()
            .map(|arg| arg.to_string())
            .map(|s| {
                if s.contains('>') {
                    format!("({s})")
                } else {
                    s
                }
            })
            .join(", ")
    )
}

pub fn format_type_scheme_around_name<E: Display, N: Display>(
    name: &N,
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
        write!(
            f,
            "{}",
            self.bounds()
                .map(|(var, bounds)| TypeBounds::format_var_bound(var, bounds))
                .format(", ")
        )
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
            ty: "ty".parse().ok(),
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
                    ty: "ty0".parse().ok(),
                },
                Param {
                    name: "def".into(),
                    index: None,
                    ty: "ty1".parse().ok(),
                },
            ],
            outputs: vec![
                Param {
                    name: "abc".into(),
                    index: None,
                    ty: "ty0".parse().ok(),
                },
                Param {
                    name: "def".into(),
                    index: Some(2u32.into()),
                    ty: "ty1".parse().ok(),
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
                ty: "ty".parse().ok(),
            }],
        };
        assert_eq!(out.to_string(), "-> abc: ty");
        assert_eq!(out.prepend_space_if_non_empty(), " -> abc: ty");
        let _in = Params {
            inputs: vec![Param {
                name: "abc".into(),
                index: None,
                ty: "ty".parse().ok(),
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

    #[cfg(test)]
    mod parentheses {
        use powdr_parser::parse;
        use powdr_parser::test_utils::ClearSourceRefs;
        use powdr_parser_util::UnwrapErrToStderr;
        use pretty_assertions::assert_eq;
        use test_log::test;

        type TestCase = (&'static str, &'static str);

        fn test_paren(test_case: &TestCase) {
            let (input, expected) = test_case;
            let mut parsed = parse(None, input).unwrap_err_to_stderr();
            let printed = parsed.to_string();
            assert_eq!(expected.trim(), printed.trim());
            let mut re_parsed = parse(None, printed.as_str()).unwrap_err_to_stderr();

            parsed.clear_source_refs();
            re_parsed.clear_source_refs();
            assert_eq!(parsed, re_parsed);
        }

        #[test]
        fn binary_op() {
            let test_cases: Vec<TestCase> = vec![
                // Complete line
                ("let t = ((x + y) * z);", "let t = (x + y) * z;"),
                // Don't add extra
                ("-x + y * !z;", "-x + y * !z;"),
                ("x = (y <= z);", "x = (y <= z);"),
                ("(x = y) <= z;", "(x = y) <= z;"),
                ("x + y + z;", "x + y + z;"),
                ("x * y * z;", "x * y * z;"),
                ("x / y / z;", "x / y / z;"),
                // Remove unneeded
                ("(-x) + y * (!z);", "-x + y * !z;"),
                ("(x * y) * z;", "x * y * z;"),
                ("(x / y) / z;", "x / y / z;"),
                ("(x ** (y ** z));", "x ** (y ** z);"),
                ("(x - (y + z));", "x - (y + z);"),
                // Observe associativity
                ("x * (y * z);", "x * (y * z);"),
                ("x / (y / z);", "x / (y / z);"),
                ("x ** (y ** z);", "x ** (y ** z);"),
                ("(x ** y) ** z;", "(x ** y) ** z;"),
                // Don't remove needed
                ("(x + y) * z;", "(x + y) * z;"),
                ("((x + y) * z);", "(x + y) * z;"),
                ("-(x + y);", "-(x + y);"),
                // function call
                ("(a + b)(2);", "(a + b)(2);"),
                // Index access
                ("(a + b)[2];", "(a + b)[2];"),
                ("(i < 7) && (6 >= -i);", "i < 7 && 6 >= -i;"),
                // Power test
                ("(-x) ** (-y);", "(-x) ** (-y);"),
                ("2 ** x';", "2 ** (x');"),
                ("(2 ** x)';", "(2 ** x)';"),
            ];

            for test_case in test_cases {
                test_paren(&test_case);
            }
        }

        #[test]
        fn lambda_ex() {
            let test_cases: Vec<TestCase> = vec![
                ("let x = 1 + (|i| i + 2);", "let x = 1 + (|i| i + 2);"),
                ("let x = 1 + (|i| i) + 2;", "let x = 1 + (|i| i) + 2;"),
                ("let x = 1 + (|i| (i + 2));", "let x = 1 + (|i| i + 2);"),
                ("let x = (1 + (|i| i)) + 2;", "let x = 1 + (|i| i) + 2;"),
                ("let x = (1 + (|i| (i + 2)));", "let x = 1 + (|i| i + 2);"),
                ("let x = (1 + (|i| i + 2));", "let x = 1 + (|i| i + 2);"),
                // Index access
                ("(|i| i)[j];", "(|i| i)[j];"),
            ];

            for test_case in test_cases {
                test_paren(&test_case);
            }
        }

        #[test]
        fn complex() {
            let test_cases: Vec<TestCase> = vec![
            // Don't change concise expression
            (
                "a | b * (c << d + e) & (f ^ g) = h * (i + g);",
                "a | b * (c << d + e) & (f ^ g) = h * (i + g);",
            ),
            // Remove extra parentheses
            (
                "(a | ((b * (c << (d + e))) & (f ^ g))) = (h * ((i + g)));",
                "a | b * (c << d + e) & (f ^ g) = h * (i + g);",
            ),
            (
                "instr_or $ [0, X, Y, Z] is (main_bin.latch * main_bin.sel[0]) $ [main_bin.operation_id, main_bin.A, main_bin.B, main_bin.C];",
                "instr_or $ [0, X, Y, Z] is main_bin.latch * main_bin.sel[0] $ [main_bin.operation_id, main_bin.A, main_bin.B, main_bin.C];",
            ),
            (
                "instr_or $ [0, X, Y, Z] is main_bin.latch * main_bin.sel[0] $ [main_bin.operation_id, main_bin.A, main_bin.B, main_bin.C];",
                "instr_or $ [0, X, Y, Z] is main_bin.latch * main_bin.sel[0] $ [main_bin.operation_id, main_bin.A, main_bin.B, main_bin.C];",
            ),
            (
                "pc' = (1 - first_step') * ((((instr__jump_to_operation * _operation_id) + (instr__loop * pc)) + (instr_return * 0)) + ((1 - ((instr__jump_to_operation + instr__loop) + instr_return)) * (pc + 1)));",
                "pc' = (1 - first_step') * (instr__jump_to_operation * _operation_id + instr__loop * pc + instr_return * 0 + (1 - (instr__jump_to_operation + instr__loop + instr_return)) * (pc + 1));",
            ),
            (
                "let root_of_unity_for_log_degree: int -> fe = |n| root_of_unity ** (2**(32 - n));",
                "let root_of_unity_for_log_degree: int -> fe = (|n| root_of_unity ** (2 ** (32 - n)));",
            ),
        ];

            for test_case in test_cases {
                test_paren(&test_case);
            }
        }

        #[test]
        fn index_access_parentheses() {
            let test_cases: Vec<TestCase> = vec![
                ("(x')(2);", "(x')(2);"),
                ("x[2](2);", "x[2](2);"),
                ("(x')[2];", "(x')[2];"),
                ("-x[2];", "-x[2];"),
                ("(-x)[2];", "(-x)[2];"),
                ("-(x[2]);", "-x[2];"),
                ("1 + x[2];", "1 + x[2];"),
                ("1 + x(2);", "1 + x(2);"),
            ];

            for test_case in test_cases {
                test_paren(&test_case);
            }
        }
    }
}

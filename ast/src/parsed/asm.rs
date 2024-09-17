use std::{
    fmt::{Display, Formatter},
    iter::{empty, once, repeat},
    str::FromStr,
};

use itertools::Itertools;
use powdr_number::BigUint;

use derive_more::From;
use powdr_parser_util::{Error, SourceRef};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::parsed::{BinaryOperation, BinaryOperator};

use super::{
    visitor::Children, EnumDeclaration, EnumVariant, Expression, PilStatement, SourceReference,
    StructDeclaration, TraitDeclaration, TraitImplementation, TypedExpression,
};

#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct ASMProgram {
    pub main: ASMModule,
}

#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct ASMModule {
    pub statements: Vec<ModuleStatement>,
}

impl ASMModule {
    pub fn symbol_definitions(&self) -> impl Iterator<Item = &SymbolDefinition> {
        self.statements.iter().filter_map(|s| match s {
            ModuleStatement::SymbolDefinition(d) => Some(d),
            ModuleStatement::TraitImplementation(_) => None,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, From)]
pub enum ModuleStatement {
    SymbolDefinition(SymbolDefinition),
    TraitImplementation(TraitImplementation<Expression>),
}

impl ModuleStatement {
    pub fn defined_names(&self) -> Option<&String> {
        match self {
            ModuleStatement::SymbolDefinition(d) => Some(&d.name),
            ModuleStatement::TraitImplementation(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolDefinition {
    pub name: String,
    pub value: SymbolValue,
}

#[derive(Debug, Clone, PartialEq, Eq, From)]
pub enum SymbolValue {
    /// A machine definition
    Machine(Machine),
    /// An import of a symbol from another module
    Import(Import),
    /// A module definition
    Module(Module),
    /// A generic symbol / function.
    Expression(TypedExpression),
    /// A type declaration (currently only enums or structs)
    TypeDeclaration(TypeDeclaration),
    /// A trait declaration
    TraitDeclaration(TraitDeclaration<Expression>),
}

impl SymbolValue {
    pub fn as_ref(&self) -> SymbolValueRef {
        match self {
            SymbolValue::Machine(machine) => SymbolValueRef::Machine(machine),
            SymbolValue::Import(i) => SymbolValueRef::Import(i),
            SymbolValue::Module(m) => SymbolValueRef::Module(m.as_ref()),
            SymbolValue::Expression(e) => SymbolValueRef::Expression(e),
            SymbolValue::TypeDeclaration(t) => SymbolValueRef::TypeDeclaration(t),
            SymbolValue::TraitDeclaration(t) => SymbolValueRef::TraitDeclaration(t),
        }
    }
}

#[derive(Debug, PartialEq, Eq, From)]
pub enum SymbolValueRef<'a> {
    /// A machine definition
    Machine(&'a Machine),
    /// An import of a symbol from another module
    Import(&'a Import),
    /// A module definition
    Module(ModuleRef<'a>),
    /// A generic symbol / function.
    Expression(&'a TypedExpression),
    /// A type declaration (currently only enums or structs)
    TypeDeclaration(&'a TypeDeclaration),
    /// A type constructor of an enum.
    TypeConstructor(&'a EnumVariant<Expression>),
    /// A trait declaration
    TraitDeclaration(&'a TraitDeclaration<Expression>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDeclaration {
    Enum(EnumDeclaration<Expression>),
    Struct(StructDeclaration<Expression>),
}

impl From<EnumDeclaration<Expression>> for SymbolValue {
    fn from(value: EnumDeclaration<Expression>) -> Self {
        SymbolValue::TypeDeclaration(TypeDeclaration::Enum(value))
    }
}

impl From<StructDeclaration<Expression>> for SymbolValue {
    fn from(value: StructDeclaration<Expression>) -> Self {
        SymbolValue::TypeDeclaration(TypeDeclaration::Struct(value))
    }
}

impl Children<Expression> for TypeDeclaration {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        match self {
            TypeDeclaration::Enum(e) => Box::new(e.variants.iter().flat_map(|v| v.children())),
            TypeDeclaration::Struct(s) => {
                Box::new(s.fields.iter().flat_map(|(_f, ty)| ty.children()))
            }
        }
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        match self {
            TypeDeclaration::Enum(e) => {
                Box::new(e.variants.iter_mut().flat_map(|v| v.children_mut()))
            }
            TypeDeclaration::Struct(s) => {
                Box::new(s.fields.iter_mut().flat_map(|(_f, ty)| ty.children_mut()))
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, From)]
pub enum Module {
    External(String),
    Local(ASMModule),
}

impl Module {
    fn as_ref(&self) -> ModuleRef {
        match self {
            Module::External(n) => ModuleRef::External(n),
            Module::Local(m) => ModuleRef::Local(m),
        }
    }
}

#[derive(Debug, PartialEq, Eq, From)]
pub enum ModuleRef<'a> {
    External(&'a str),
    Local(&'a ASMModule),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Import {
    /// the path imported in the source
    pub path: SymbolPath,
}

/// A symbol path is a sequence of strings separated by ``::`.
/// It can contain the special word `super`, which goes up a level.
/// If it does not start with `::`, it is relative.
#[derive(
    Default, Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash, Serialize, Deserialize, JsonSchema,
)]
pub struct SymbolPath {
    /// The parts between each `::`.
    parts: Vec<Part>,
}

impl SymbolPath {
    pub fn from_identifier(name: String) -> Self {
        Self {
            parts: vec![Part::Named(name)],
        }
    }

    pub fn from_parts<P: IntoIterator<Item = Part>>(parts: P) -> Self {
        Self {
            parts: parts.into_iter().collect(),
        }
    }

    pub fn join<P: Into<Self>>(mut self, other: P) -> Self {
        self.parts.extend(other.into().parts);
        self
    }

    pub fn try_to_identifier(&self) -> Option<&String> {
        match &self.parts[..] {
            [Part::Named(name)] => Some(name),
            _ => None,
        }
    }

    pub fn try_last_part_mut(&mut self) -> Option<&mut String> {
        self.parts.last_mut().and_then(|p| match p {
            Part::Super => None,
            Part::Named(n) => Some(n),
        })
    }

    pub fn try_last_part(&self) -> Option<&String> {
        self.parts.last().and_then(|p| match p {
            Part::Super => None,
            Part::Named(n) => Some(n),
        })
    }

    /// Returns the last part of the path. Panics if it is "super" or if the path is empty.
    pub fn name(&self) -> &String {
        self.try_last_part().unwrap()
    }

    pub fn parts(&self) -> impl DoubleEndedIterator + ExactSizeIterator<Item = &Part> {
        self.parts.iter()
    }

    pub fn into_parts(self) -> impl DoubleEndedIterator + ExactSizeIterator<Item = Part> {
        self.parts.into_iter()
    }
}

impl FromStr for SymbolPath {
    type Err = String;

    /// Parses a symbol path using the "::" notation.
    fn from_str(s: &str) -> Result<Self, String> {
        let parts = s
            .split("::")
            .map(|s| {
                if s == "super" {
                    Part::Super
                } else {
                    Part::Named(s.to_string())
                }
            })
            .collect();
        Ok(Self { parts })
    }
}

impl From<AbsoluteSymbolPath> for SymbolPath {
    fn from(value: AbsoluteSymbolPath) -> Self {
        Self {
            parts: once(String::new())
                .chain(value.parts)
                .map(Part::Named)
                .collect(),
        }
    }
}

impl Display for SymbolPath {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.parts.iter().format("::"))
    }
}

/// An absolute symbol path is a resolved SymbolPath,
/// which means it has to start with `::` and it cannot contain
/// the word `super`.
#[derive(Default, Debug, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub struct AbsoluteSymbolPath {
    /// Contains the parts after the initial `::`.
    parts: Vec<String>,
}

/// Parses a path like `::path::to::symbol`.
/// Panics if the path does not start with '::'.
pub fn parse_absolute_path(s: &str) -> AbsoluteSymbolPath {
    match s.strip_prefix("::") {
        Some("") => AbsoluteSymbolPath::default(),
        Some(s) => s
            .split("::")
            .fold(AbsoluteSymbolPath::default(), |path, part| {
                path.with_part(part)
            }),
        None => panic!("Absolute symbol path does not start with '::': {s}"),
    }
}

impl AbsoluteSymbolPath {
    /// Removes and returns the last path component (unless empty).
    pub fn pop(&mut self) -> Option<String> {
        self.parts.pop()
    }

    /// Returns the path one level higher.
    pub fn parent(mut self) -> AbsoluteSymbolPath {
        self.pop().unwrap();
        self
    }

    pub fn len(&self) -> usize {
        self.parts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn parts(&self) -> impl DoubleEndedIterator + ExactSizeIterator<Item = &str> {
        self.parts.iter().map(|p| p.as_str())
    }

    /// Returns an iterator over all paths (not parts!) from self to the root.
    pub fn iter_to_root(&self) -> impl Iterator<Item = AbsoluteSymbolPath> + '_ {
        (0..=self.parts.len()).rev().map(|i| AbsoluteSymbolPath {
            parts: self.parts[..i].to_vec(),
        })
    }

    /// Appends a part to the end of the path.
    pub fn push(&mut self, part: String) {
        self.parts.push(part);
    }

    /// Returns the relative path from base to self.
    /// In other words, base.join(self.relative_to(base)) == self.
    pub fn relative_to(&self, base: &AbsoluteSymbolPath) -> SymbolPath {
        let common_prefix_len = self.common_prefix(base).parts.len();
        // Start with max(0, base.parts.len() - common_root.parts.len())
        // repetitions of "super".
        let parts = repeat(Part::Super)
            .take(base.parts.len().saturating_sub(common_prefix_len))
            // append the parts of self after the common root.
            .chain(
                self.parts
                    .iter()
                    .skip(common_prefix_len)
                    .cloned()
                    .map(Part::Named),
            )
            .collect();
        SymbolPath { parts }
    }

    /// Returns the common prefix of two paths.
    pub fn common_prefix(&self, other: &AbsoluteSymbolPath) -> AbsoluteSymbolPath {
        let parts = self
            .parts
            .iter()
            .zip(other.parts.iter())
            .map_while(|(a, b)| if a == b { Some(a.clone()) } else { None })
            .collect();

        AbsoluteSymbolPath { parts }
    }

    /// Resolves a relative path in the context of this absolute path.
    pub fn join<P: Into<SymbolPath>>(mut self, other: P) -> Self {
        for part in other.into().parts {
            match part {
                Part::Super => {
                    self.pop().unwrap();
                }
                Part::Named(name) => {
                    if name.is_empty() {
                        self.parts.clear();
                    } else {
                        self.parts.push(name);
                    }
                }
            }
        }
        self
    }

    /// Appends a part to the end of the path and returns a new copy.
    pub fn with_part(&self, part: &str) -> Self {
        assert!(!part.is_empty());
        let mut parts = self.parts.clone();
        parts.push(part.to_string());
        Self { parts }
    }
}

impl Display for AbsoluteSymbolPath {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "::{}", self.parts.iter().format("::"))
    }
}

#[derive(
    Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash, Serialize, Deserialize, JsonSchema,
)]
pub enum Part {
    Super,
    Named(String),
}

impl TryInto<String> for Part {
    type Error = ();

    fn try_into(self) -> Result<String, Self::Error> {
        if let Part::Named(name) = self {
            Ok(name)
        } else {
            Err(())
        }
    }
}

impl Display for Part {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Part::Super => write!(f, "super"),
            Part::Named(name) => write!(f, "{name}"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Machine {
    pub params: MachineParams,
    pub properties: MachineProperties,
    pub statements: Vec<MachineStatement>,
}

impl Machine {
    /// Returns a vector of all local variables / names defined in the machine.
    pub fn local_names(&self) -> Box<dyn Iterator<Item = &String> + '_> {
        Box::new(
            self.statements
                .iter()
                .flat_map(|s| -> Box<dyn Iterator<Item = &String> + '_> {
                    match s {
                        MachineStatement::Submachine(_, _, name, _)
                        | MachineStatement::RegisterDeclaration(_, name, _) => Box::new(once(name)),
                        MachineStatement::Pil(_, statement) => {
                            Box::new(statement.symbol_definition_names().map(|(s, _)| s))
                        }
                        MachineStatement::InstructionDeclaration(_, _, _)
                        | MachineStatement::LinkDeclaration(_, _)
                        | MachineStatement::FunctionDeclaration(_, _, _, _)
                        | MachineStatement::OperationDeclaration(_, _, _, _) => Box::new(empty()),
                    }
                })
                .chain(self.params.defined_names())
                .chain(self.properties.defined_names()),
        )
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Default, Clone)]
pub struct MachineParams(pub Vec<Param>);

impl MachineParams {
    pub fn defined_names(&self) -> impl Iterator<Item = &String> {
        self.0.iter().map(|p| &p.name)
    }

    pub fn try_from_params(source_ref: SourceRef, params: Vec<Param>) -> Result<Self, Error> {
        for p in &params {
            if p.index.is_some() || p.ty.is_none() || p.name.is_empty() {
                return Err(source_ref.with_error(format!("invalid machine argument: `{p}`")));
            }
        }
        Ok(MachineParams(params))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Default, Clone)]
pub struct MachineProperties {
    pub degree: Option<Expression>,
    pub min_degree: Option<Expression>,
    pub max_degree: Option<Expression>,
    pub latch: Option<String>,
    pub operation_id: Option<String>,
    pub call_selectors: Option<String>,
}

impl MachineProperties {
    pub fn defined_names(&self) -> impl Iterator<Item = &String> {
        self.call_selectors.iter()
    }

    pub fn try_from_prop_list(
        source_ref: SourceRef,
        prop_list: Vec<(String, Expression)>,
    ) -> Result<Self, Error> {
        let mut props: Self = Default::default();
        for (name, value) in prop_list {
            let mut already_defined = false;
            match name.as_str() {
                "degree" => {
                    if props.degree.replace(value).is_some() {
                        already_defined = true;
                    }
                }
                "min_degree" => {
                    if props.min_degree.replace(value).is_some() {
                        already_defined = true;
                    }
                }
                "max_degree" => {
                    if props.max_degree.replace(value).is_some() {
                        already_defined = true;
                    }
                }
                "latch" => {
                    let id = value.try_to_identifier().ok_or_else(|| {
                        source_ref.with_error(format!(
                            "`{name}` machine property expects a local column name"
                        ))
                    })?;
                    if props.latch.replace(id.clone()).is_some() {
                        already_defined = true;
                    }
                }
                "operation_id" => {
                    let id = value.try_to_identifier().ok_or_else(|| {
                        source_ref.with_error(format!(
                            "`{name}` machine property expects a local column name"
                        ))
                    })?;
                    if props.operation_id.replace(id.clone()).is_some() {
                        already_defined = true;
                    }
                }
                "call_selectors" => {
                    let id = value.try_to_identifier().ok_or_else(|| {
                        source_ref.with_error(format!(
                            "`{name}` machine property expects a new column name"
                        ))
                    })?;
                    if props.call_selectors.replace(id.clone()).is_some() {
                        already_defined = true;
                    }
                }
                _ => {
                    return Err(source_ref.with_error(format!("unknown machine property `{name}`")));
                }
            }
            if already_defined {
                return Err(source_ref.with_error(format!("`{name}` already defined")));
            }
        }
        Ok(props)
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Default)]
pub struct Params<T> {
    pub inputs: Vec<T>,
    pub outputs: Vec<T>,
}

pub type CallableParams = Params<Expression>;
// TODO: should we have separate Param types here?
// - Function: doesn't use `index` or `type`
// - Instruction: doesn't use `index`
// - Operation: doesn't use `type`
pub type FunctionParams = Params<Param>;
pub type InstructionParams = Params<Param>;
pub type OperationParams = Params<Param>;

impl<T> Params<T> {
    pub fn new(inputs: Vec<T>, outputs: Vec<T>) -> Self {
        Self { inputs, outputs }
    }

    pub fn is_empty(&self) -> bool {
        self.inputs.is_empty() && self.outputs.is_empty()
    }

    pub fn inputs_and_outputs(&self) -> impl Iterator<Item = &T> {
        self.inputs.iter().chain(self.outputs.iter())
    }

    pub fn inputs_and_outputs_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.inputs.iter_mut().chain(self.outputs.iter_mut())
    }
}

impl<T: Display> Params<T> {
    pub fn prepend_space_if_non_empty(&self) -> String {
        let mut params_str = self.to_string();
        if !self.is_empty() {
            params_str = format!(" {params_str}");
        }
        params_str
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
/// the operation id necessary to call this function from the outside
pub struct OperationId {
    pub id: Option<BigUint>,
}

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub struct Instruction {
    pub params: InstructionParams,
    pub links: Vec<LinkDeclaration>,
    pub body: InstructionBody,
}

impl Children<Expression> for Instruction {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        Box::new(
            self.body
                .0
                .iter()
                .flat_map(|s| s.children())
                .chain(self.links.iter().flat_map(|d| d.children())),
        )
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        Box::new(
            self.body
                .0
                .iter_mut()
                .flat_map(|s| s.children_mut())
                .chain(self.links.iter_mut().flat_map(|d| d.children_mut())),
        )
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum MachineStatement {
    Pil(SourceRef, PilStatement),
    Submachine(SourceRef, SymbolPath, String, Vec<Expression>),
    RegisterDeclaration(SourceRef, String, Option<RegisterFlag>),
    InstructionDeclaration(SourceRef, String, Instruction),
    LinkDeclaration(SourceRef, LinkDeclaration),
    FunctionDeclaration(SourceRef, String, FunctionParams, Vec<FunctionStatement>),
    OperationDeclaration(SourceRef, String, OperationId, OperationParams),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct LinkDeclaration {
    pub flag: Expression,
    pub link: CallableRef,
    pub is_permutation: bool,
}

impl Children<Expression> for LinkDeclaration {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        Box::new(once(&self.flag).chain(self.link.params.inputs_and_outputs()))
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        Box::new(once(&mut self.flag).chain(self.link.params.inputs_and_outputs_mut()))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct CallableRef {
    pub instance: String,
    pub callable: String,
    pub params: CallableParams,
}

/// RHS of instruction link definitions are parsed as `Expression`s which should conform to:
/// `OUT = submachine.operation(IN1, IN2, ..., INn)`
/// or
/// `(OUT1, OUT2, ..., OUTn) = submachine.operation(IN1, IN2, ..., INn)`
impl TryFrom<Expression> for CallableRef {
    type Error = Error;

    fn try_from(value: Expression) -> Result<Self, Self::Error> {
        let mut outputs = vec![];
        let rhs = match value {
            Expression::BinaryOperation(
                _,
                BinaryOperation {
                    left,
                    op: BinaryOperator::Identity,
                    right,
                },
            ) => {
                outputs = if let Expression::Tuple(_, elements) = *left {
                    elements
                } else {
                    vec![*left]
                };
                *right
            }
            expr => expr,
        };

        let source_ref = match rhs {
            Expression::FunctionCall(_, call) => {
                let inputs = call.arguments;
                match *call.function {
                    Expression::Reference(source_ref, reference)
                        if reference.path.parts().len() == 2 =>
                    {
                        if reference.type_args.is_some() {
                            return Err(source_ref
                                .with_error("types not expected in link definition".to_string()));
                        }
                        let (l, r) = reference.path.into_parts().next_tuple().unwrap();
                        let instance = l.try_into().unwrap();
                        let callable = r.try_into().unwrap();
                        return Ok(CallableRef {
                            instance,
                            callable,
                            params: CallableParams { inputs, outputs },
                        });
                    }
                    expr => expr.source_reference().clone(),
                }
            }
            expr => expr.source_reference().clone(),
        };
        Err(source_ref
            .with_error("link definition RHS must be a call to `submachine.operation`".to_string()))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct InstructionBody(pub Vec<PilStatement>);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AssignmentRegister {
    Register(String),
    Wildcard,
}

impl AssignmentRegister {
    pub fn unwrap(self) -> String {
        match self {
            AssignmentRegister::Register(r) => r,
            AssignmentRegister::Wildcard => panic!("cannot unwrap wildcard"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum FunctionStatement {
    Assignment(
        SourceRef,
        Vec<String>,
        Option<Vec<AssignmentRegister>>,
        Box<Expression>,
    ),
    Instruction(SourceRef, String, Vec<Expression>),
    Label(SourceRef, String),
    DebugDirective(SourceRef, DebugDirective),
    Return(SourceRef, Vec<Expression>),
}

impl Children<Expression> for FunctionStatement {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        match self {
            FunctionStatement::Assignment(_, _, _, e) => Box::new(once(e.as_ref())),
            FunctionStatement::Instruction(_, _, expressions)
            | FunctionStatement::Return(_, expressions) => Box::new(expressions.iter()),
            FunctionStatement::Label(_, _) | FunctionStatement::DebugDirective(_, _) => {
                Box::new(empty())
            }
        }
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        match self {
            FunctionStatement::Assignment(_, _, _, e) => Box::new(once(e.as_mut())),
            FunctionStatement::Instruction(_, _, expressions)
            | FunctionStatement::Return(_, expressions) => Box::new(expressions.iter_mut()),
            FunctionStatement::Label(_, _) | FunctionStatement::DebugDirective(_, _) => {
                Box::new(empty())
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum DebugDirective {
    File(usize, String, String),
    Loc(usize, usize, usize),
    OriginalInstruction(String),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum RegisterFlag {
    IsPC,
    IsAssignment,
    IsReadOnly,
}

#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Param {
    pub name: String,
    pub index: Option<BigUint>,
    pub ty: Option<SymbolPath>,
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn common_prefix() {
        assert_eq!(
            parse_absolute_path("::a::b").common_prefix(&parse_absolute_path("::a::c")),
            parse_absolute_path("::a")
        );
        assert_eq!(
            parse_absolute_path("::a::b").common_prefix(&parse_absolute_path("::a")),
            parse_absolute_path("::a")
        );
        assert_eq!(
            parse_absolute_path("::a").common_prefix(&parse_absolute_path("::a::c")),
            parse_absolute_path("::a")
        );
        assert_eq!(
            parse_absolute_path("::x").common_prefix(&parse_absolute_path("::y::t")),
            parse_absolute_path("::")
        );
        assert_eq!(
            parse_absolute_path("::x::r::v").common_prefix(&parse_absolute_path("::x::r::t")),
            parse_absolute_path("::x::r")
        );
    }

    #[test]
    fn relative_to() {
        assert_eq!(
            parse_absolute_path("::a::b")
                .relative_to(&parse_absolute_path("::a::c"))
                .to_string(),
            "super::b".to_string()
        );
        assert_eq!(
            parse_absolute_path("::a::b")
                .relative_to(&parse_absolute_path("::a"))
                .to_string(),
            "b".to_string()
        );
        assert_eq!(
            parse_absolute_path("::x")
                .relative_to(&parse_absolute_path("::y::t"))
                .to_string(),
            "super::super::x".to_string()
        );
        assert_eq!(
            parse_absolute_path("::x::r::v")
                .relative_to(&parse_absolute_path("::x::r"))
                .to_string(),
            "v".to_string()
        );
        assert_eq!(
            parse_absolute_path("::x")
                .relative_to(&parse_absolute_path("::x::t::k"))
                .to_string(),
            "super::super".to_string()
        );
        assert_eq!(
            parse_absolute_path("::x")
                .relative_to(&parse_absolute_path("::x"))
                .to_string(),
            "".to_string()
        );
    }

    #[test]
    fn relative_to_join() {
        let v = parse_absolute_path("::x::r::v");
        let base = parse_absolute_path("::x::t");
        let rel = v.relative_to(&base);
        assert_eq!(base.join(rel), v);
    }
}

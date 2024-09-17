use std::collections::BTreeMap;

use powdr_number::BigUint;

use crate::{
    asm_analysis::MachineDegree,
    parsed::{
        asm::{AbsoluteSymbolPath, CallableParams, OperationParams},
        EnumDeclaration, Expression, PilStatement, StructDeclaration, TypedExpression,
    },
};

mod display;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Location {
    limbs: Vec<String>,
}

impl Location {
    pub fn main() -> Self {
        Self {
            limbs: vec!["main".into()],
        }
    }

    pub fn parent(&self) -> Option<Self> {
        if self.limbs.is_empty() {
            return None;
        }
        let mut parent = self.clone();
        parent.limbs.pop();
        Some(parent)
    }

    pub fn join<S: Into<String>>(mut self, limb: S) -> Self {
        self.limbs.push(limb.into());
        self
    }
}

#[derive(Clone)]
pub struct PILGraph {
    pub main: Machine,
    pub entry_points: Vec<Operation>,
    pub objects: BTreeMap<Location, Object>,
    pub definitions: BTreeMap<AbsoluteSymbolPath, TypeOrExpression>,
}

#[derive(Clone)]
pub enum TypeOrExpression {
    Type(Type),
    Expression(TypedExpression),
}

#[derive(Clone)]
pub enum Type {
    Enum(EnumDeclaration<Expression>),
    Struct(StructDeclaration<Expression>),
}

impl From<EnumDeclaration<Expression>> for Type {
    fn from(decl: EnumDeclaration<Expression>) -> Self {
        Self::Enum(decl)
    }
}

impl From<StructDeclaration<Expression>> for Type {
    fn from(decl: StructDeclaration<Expression>) -> Self {
        Self::Struct(decl)
    }
}

#[derive(Default, Clone)]
pub struct Object {
    pub degree: MachineDegree,
    /// the pil identities for this machine
    pub pil: Vec<PilStatement>,
    /// the links from this machine to its children
    pub links: Vec<Link>,
    /// name of the latch column
    pub latch: Option<String>,
    /// call selector array
    pub call_selectors: Option<String>,
    /// true if this machine has a PC
    pub has_pc: bool,
}

#[derive(Clone, Debug)]
/// A link between two machines
pub struct Link {
    /// the link source, i.e. a flag and some arguments
    pub from: LinkFrom,
    /// the link target, i.e. a callable in some machine
    pub to: LinkTo,
    /// true if this is a permutation link
    pub is_permutation: bool,
}

#[derive(Clone, Debug)]
pub struct LinkFrom {
    /// the instruction flag, if this is an instruction link
    pub instr_flag: Option<Expression>,
    /// the link flag
    pub link_flag: Expression,
    /// lhs arguments of the link
    pub params: CallableParams,
}

#[derive(Clone, Debug, PartialOrd, Ord, Eq, PartialEq)]
pub struct LinkTo {
    /// the machine we link to
    pub machine: Machine,
    /// the operation we link to
    pub operation: Operation,
    /// index into the permutation selector (None if lookup)
    pub selector_idx: Option<u64>,
}

#[derive(Clone, Debug, PartialOrd, Ord, Eq, PartialEq)]
pub struct Machine {
    /// the location of this instance
    pub location: Location,
    /// its latch
    pub latch: Option<String>,
    /// call selector array
    pub call_selectors: Option<String>,
    /// its operation id
    pub operation_id: Option<String>,
}

#[derive(Clone, Debug, PartialOrd, Ord, Eq, PartialEq)]
pub struct Operation {
    /// the name of the operation
    pub name: String,
    /// the value of the operation id of this machine which activates this operation
    pub id: Option<BigUint>,
    /// the parameters
    pub params: OperationParams,
}

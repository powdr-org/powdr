use std::collections::BTreeMap;

use powdr_number::BigUint;

use crate::{
    asm_analysis::MachineDegree,
    parsed::{
        asm::{AbsoluteSymbolPath, CallableParams, OperationParams},
        Expression, PilStatement,
    },
};

mod display;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
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
pub struct MachineInstanceGraph {
    pub main: Location,
    pub objects: BTreeMap<Location, Object>,
    /// List of module-level PIL statements (utility functions,
    /// data structures, etc) by module path
    pub statements: BTreeMap<AbsoluteSymbolPath, Vec<PilStatement>>,
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
    /// the operation id for this machine
    /// TODO: This could be made non optional for simplicity: in the case where we have a single operation, it could be optimized away
    pub operation_id: Option<String>,
    /// the operations for this machine
    pub operations: BTreeMap<String, Operation>,
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

#[derive(Clone, Debug, PartialOrd, Ord, Eq, PartialEq, Hash)]
pub struct LinkTo {
    /// the machine we link to
    pub machine: Location,
    /// the operation we link to
    pub operation: String,
}

#[derive(Clone, Debug, PartialOrd, Ord, Eq, PartialEq)]
pub struct Operation {
    /// the value of the operation id of this machine which activates this operation
    pub id: Option<BigUint>,
    /// the parameters
    pub params: OperationParams,
}

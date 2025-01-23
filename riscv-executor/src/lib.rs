//! A specialized executor for our RISC-V assembly that can speedup witgen and
//! help with making partition decisions.
//!
//! WARNING: the general witness generation/execution code over the polynomial
//! constraints try to ensure the determinism of the instructions. If we bypass
//! much of witness generation using the present module, we lose the
//! non-determinism verification.
//!
//! TODO: perform determinism verification for each instruction independently
//! from execution.

use std::{
    collections::{BTreeMap, HashMap},
    fmt::{self, Display, Formatter},
    path::Path,
    sync::Arc,
    time::Instant,
};

use num_derive::{FromPrimitive, ToPrimitive};

use builder::TraceBuilder;

use itertools::Itertools;
use powdr_ast::{
    analyzed::{AlgebraicExpression, Analyzed, Identity, LookupIdentity},
    asm_analysis::{AnalysisASMFile, CallableSymbol, FunctionStatement, LabelStatement, Machine},
    parsed::{
        asm::{parse_absolute_path, AssignmentRegister, DebugDirective},
        BinaryOperation, Expression, FunctionCall, Number, UnaryOperation,
    },
};
use tiny_keccak::keccakf;

use powdr_executor::constant_evaluator::VariablySizedColumn;
use powdr_number::{write_polys_csv_file, FieldElement, LargeInt};
pub use profiler::ProfilerOptions;

pub mod arith;
mod poseidon2_gl;
pub mod poseidon_gl;
mod profiler;
mod submachines;
use submachines::*;
mod memory;
use memory::*;
mod pil;

use crate::profiler::Profiler;

#[derive(Debug)]
struct SubmachineOp<F: FieldElement> {
    // pil identity id of the link
    identity_id: u64,
    // these are the RHS values of the lookup (i.e., inside brackets in the PIL lookup).
    // This is a fixed size to avoid allocations in the common case.
    lookup_args: [F; 4],
    // TODO: this is just for the hand-written poseidon_gl submachine,
    // we give it the input values because it doesn't have access to memory
    extra: Vec<F>,
}

/// Enum with asm machine RISCV instruction. Helps avoid using raw strings in the code.
macro_rules! instructions {
    ($($name:ident),*) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[allow(non_camel_case_types)]
        enum Instruction {
            $($name,)*
            Count
        }

        impl Instruction {
            fn count() -> usize {
                Self::Count as usize
            }

            fn from_name(s: &str) -> Option<Self> {
                match s {
                    $(stringify!($name) => Some(Self::$name),)*
                    _ => None
                }
            }

            fn flag(&self) -> &'static str {
                match *self {
                    $(Self::$name => concat!("main::instr_", stringify!($name)),)*
                    Self::Count => panic!(),
                }
            }
        }
    };
}

instructions! {
    set_reg,
    get_reg,
    affine,
    mstore,
    mstore_bootloader,
    mload,
    load_bootloader_input,
    assert_bootloader_input,
    load_label,
    jump,
    jump_dyn,
    jump_to_bootloader_input,
    branch_if_diff_nonzero,
    branch_if_diff_equal,
    skip_if_equal,
    branch_if_diff_greater_than,
    is_diff_greater_than,
    is_equal_zero,
    is_not_equal,
    add_wrap,
    wrap16,
    sub_wrap_with_offset,
    sign_extend_byte,
    sign_extend_16_bits,
    to_signed,
    divremu,
    mul,
    and,
    or,
    xor,
    shl,
    shr,
    invert_gl,
    split_gl,
    poseidon_gl,
    poseidon2_gl,
    affine_256,
    mod_256,
    ec_add,
    ec_double,
    commit_public,
    fail,
    keccakf
}

/// Enum with columns directly accessed by the executor (as to avoid matching on strings)
macro_rules! known_witness_col {
    ($($name:ident),*) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, ToPrimitive, FromPrimitive)]
        #[allow(non_camel_case_types)]
        #[repr(usize)]
        enum KnownWitnessCol {
            $($name,)*
            Count // this is a sentinel so we know how many variants we have
        }

        impl KnownWitnessCol {
            fn count() -> usize {
                Self::Count as usize
            }

            fn all() -> Vec<Self> {
                vec![
                    $(Self::$name,)*
                ]
            }

            fn name(&self) -> &'static str {
                match *self {
                    $(Self::$name => concat!("main::", stringify!($name)),)*
                    Self::Count => panic!(),
                }
            }
        }
    };
}

known_witness_col! {
    _operation_id,
    pc_update,
    X,
    Y,
    Z,
    W,
    Y_free_value,
    X_free_value,
    tmp1_col,
    tmp2_col,
    tmp3_col,
    tmp4_col,
    X_b1,
    X_b2,
    X_b3,
    X_b4,
    XX,
    XXIsZero,
    XX_inv,
    Y_b5,
    Y_b6,
    Y_b7,
    Y_b8,
    Y_7bit,
    Y_15bit,
    REM_b1,
    REM_b2,
    REM_b3,
    REM_b4,
    wrap_bit,
    instr_load_label_param_l,
    instr_jump_param_l,
    instr_branch_if_diff_nonzero_param_l,
    instr_branch_if_diff_equal_param_l,
    instr_branch_if_diff_greater_than_param_l,
    jump_to_shutdown_routine,
    // instructions
    instr_set_reg,
    instr_get_reg,
    instr_affine,
    instr_mstore,
    instr_mstore_bootloader,
    instr_mload,
    instr_load_bootloader_input,
    instr_assert_bootloader_input,
    instr_load_label,
    instr_jump,
    instr_jump_dyn,
    instr_jump_to_bootloader_input,
    instr_branch_if_diff_nonzero,
    instr_branch_if_diff_equal,
    instr_skip_if_equal,
    instr_branch_if_diff_greater_than,
    instr_is_diff_greater_than,
    instr_is_equal_zero,
    instr_is_not_equal,
    instr_add_wrap,
    instr_wrap16,
    instr_sub_wrap_with_offset,
    instr_sign_extend_byte,
    instr_sign_extend_16_bits,
    instr_to_signed,
    instr_divremu,
    instr_mul,
    instr_and,
    instr_or,
    instr_xor,
    instr_shl,
    instr_shr,
    instr_invert_gl,
    instr_split_gl,
    instr_poseidon_gl,
    instr_poseidon2_gl,
    instr_affine_256,
    instr_mod_256,
    instr_ec_add,
    instr_ec_double,
    instr_commit_public,
    instr_fail
}

/// Enum with submachines known to the RISCV executor
macro_rules! machine_instances {
    ($($name:ident),*) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, ToPrimitive, FromPrimitive)]
        #[allow(non_camel_case_types)]
        #[repr(usize)]
        enum MachineInstance {
            $($name,)*
            Count
        }

        #[allow(unused)]
        impl MachineInstance {
            fn count() -> usize {
                Self::Count as usize
            }

            fn all() -> Vec<Self> {
                vec![
                    $(Self::$name,)*
                ]
            }

            fn name(&self) -> &'static str {
                match *self {
                    $(Self::$name => stringify!($name),)*
                    Self::Count => panic!(),
                }
            }

            fn namespace(&self) -> &'static str {
                match *self {
                    $(Self::$name => concat!("main_", stringify!($name)),)*
                    Self::Count => panic!(),
                }
            }
        }
    };
}

machine_instances! {
    memory,
    regs,
    publics,
    binary,
    shift,
    split_gl,
    poseidon_gl
    // TODO: these are not implemented yet
    // poseidon2_gl,
    // keccakf
    // arith,
}

macro_rules! known_fixed_col {
    ($($name:ident),*) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, ToPrimitive, FromPrimitive)]
        #[allow(non_camel_case_types)]
        #[repr(usize)]
        enum KnownFixedCol {
            $($name,)*
        }

        impl KnownFixedCol {
            fn all() -> Vec<Self> {
                vec![
                    $(Self::$name,)*
                ]
            }

            fn name(&self) -> &'static str {
                match *self {
                    $(Self::$name => concat!("main__rom::p_", stringify!($name)),)*
                }
            }
        }
    };
}

known_fixed_col! {
    X_const,
    Y_const,
    Z_const,
    W_const,
    Y_read_free,
    X_read_free
}

/// Initial value of the PC.
///
/// To match the ZK proof witness, the PC must start after some offset used for
/// proof initialization.
///
/// TODO: get this value from some authoritative place
const PC_INITIAL_VAL: usize = 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Elem<F: FieldElement> {
    /// Only the ranges of i32 and u32 are actually valid for a Binary value.
    /// I.e., [-2**31, 2**32).
    Binary(i64),
    Field(F),
}

impl<F: FieldElement> Elem<F> {
    /// Try to interpret the value of a field as a binary, if it can be represented either as a
    /// u32 or a i32.
    pub fn try_from_fe_as_bin(value: &F) -> Option<Self> {
        let integer = value.to_signed_integer();

        u32::try_from(&integer)
            .map(From::from)
            .or_else(|_| i32::try_from(integer).map(From::from))
            .map(Self::Binary)
            .ok()
    }

    pub fn from_u32_as_fe(value: u32) -> Self {
        Self::Field(F::from(value))
    }

    pub fn from_i32_as_fe(value: i32) -> Self {
        Self::Field(F::from(value))
    }

    pub fn from_bool_as_fe(value: bool) -> Self {
        if value {
            Self::Field(F::one())
        } else {
            Self::Field(F::zero())
        }
    }

    /// Interprets the value of self as a field element.
    pub fn into_fe(self) -> F {
        match self {
            Self::Field(f) => f,
            Self::Binary(b) => b.into(),
        }
    }

    /// Interprets the value of self as an i64, ignoring higher bytes if a field element
    pub fn as_i64_from_lower_bytes(&self) -> i64 {
        match self {
            Self::Binary(b) => *b,
            Self::Field(f) => {
                let mut bytes = f.to_bytes_le();
                bytes.truncate(8);
                i64::from_le_bytes(bytes.try_into().unwrap())
            }
        }
    }

    pub fn bin(&self) -> i64 {
        match self {
            Self::Binary(b) => *b,
            Self::Field(_) => panic!(),
        }
    }

    fn u(&self) -> u32 {
        self.bin().try_into().unwrap()
    }

    fn s(&self) -> i32 {
        self.bin().try_into().unwrap()
    }

    fn is_zero(&self) -> bool {
        match self {
            Self::Binary(b) => *b == 0,
            Self::Field(f) => f.is_zero(),
        }
    }

    fn add(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Binary(a), Self::Binary(b)) => Self::Binary(a.checked_add(*b).unwrap()),
            (Self::Field(a), Self::Field(b)) => Self::Field(*a + *b),
            (Self::Binary(a), Self::Field(b)) => Self::Field(F::from(*a) + *b),
            (Self::Field(a), Self::Binary(b)) => Self::Field(*a + F::from(*b)),
        }
    }

    fn sub(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Binary(a), Self::Binary(b)) => Self::Binary(a.checked_sub(*b).unwrap()),
            (Self::Field(a), Self::Field(b)) => Self::Field(*a - *b),
            (Self::Binary(a), Self::Field(b)) => Self::Field(F::from(*a) - *b),
            (Self::Field(a), Self::Binary(b)) => Self::Field(*a - F::from(*b)),
        }
    }

    fn mul(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Binary(a), Self::Binary(b)) => match a.checked_mul(*b) {
                Some(v) => Self::Binary(v),
                None => {
                    let a = F::from(*a);
                    let b = F::from(*b);
                    Self::Field(a * b)
                }
            },
            (Self::Field(a), Self::Field(b)) => Self::Field(*a * *b),
            (Self::Binary(a), Self::Field(b)) => Self::Field(F::from(*a) * *b),
            (Self::Field(a), Self::Binary(b)) => Self::Field(*a * F::from(*b)),
        }
    }

    fn div(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Binary(a), Self::Binary(b)) => Self::Binary(a / b),
            (Self::Field(a), Self::Field(b)) => Self::Field(*a / *b),
            (Self::Binary(a), Self::Field(b)) => Self::Field(F::from(*a) / *b),
            (Self::Field(a), Self::Binary(b)) => Self::Field(*a / F::from(*b)),
        }
    }
}

fn decompose_lower32(x: i64) -> (u8, u8, u8, u8, u8) {
    let b1 = (x & 0xff) as u8;
    let b2 = ((x >> 8) & 0xff) as u8;
    let b3 = ((x >> 16) & 0xff) as u8;
    let b4 = ((x >> 24) & 0xff) as u8;
    let sign = ((x >> 31) & 1) as u8;
    (b1, b2, b3, b4, sign)
}

impl<F: FieldElement> From<i64> for Elem<F> {
    fn from(value: i64) -> Self {
        Self::Binary(value)
    }
}

impl<F: FieldElement> From<u32> for Elem<F> {
    fn from(value: u32) -> Self {
        Self::Binary(value as i64)
    }
}

impl<F: FieldElement> From<i32> for Elem<F> {
    fn from(value: i32) -> Self {
        Self::Binary(value as i64)
    }
}

impl<F: FieldElement> From<usize> for Elem<F> {
    fn from(value: usize) -> Self {
        Self::Binary(value as i64)
    }
}

impl<F: FieldElement> Display for Elem<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Binary(b) => write!(f, "{b}"),
            Self::Field(fe) => write!(f, "{fe}"),
        }
    }
}

pub type MemoryState = HashMap<u32, u32>;
pub type RegisterMemoryState<F> = HashMap<u32, F>;

#[derive(Debug)]
pub enum MemOperationKind {
    Read,
    Write,
}

#[derive(Debug)]
pub struct MemOperation {
    /// The row of the execution trace the memory operation happened.
    pub row: usize,
    pub kind: MemOperationKind,
    pub address: u32,
}

pub struct ExecutionTrace<F: FieldElement> {
    reg_map: HashMap<String, u16>,

    /// Writes and reads to memory.
    mem_ops: Vec<MemOperation>,

    /// The length of the trace, after applying the reg_writes.
    len: usize,

    /// the pc value at each row
    pc_trace: Vec<u32>,
    /// values of non-pc asm registers at each row
    reg_trace: Vec<Vec<F>>,
    /// reg writes to be set on the trace on the next row
    reg_writes: Vec<Option<F>>,

    /// Calls into submachines
    submachine_ops: Vec<Vec<SubmachineOp<F>>>,

    /// Columns directly accessed by the executor, indexed by the enum value for
    /// fast access. Some columns may be optimized away, so we rely on the PIL
    /// columns to know what should be present in the end.
    /// We keep a row based flat vec for memory locality.
    known_cols: Vec<F>,

    /// all witness columns obtained from the optimized pil.
    all_cols: Vec<String>,
}

impl<F: FieldElement> ExecutionTrace<F> {
    pub fn new(witness_cols: Vec<String>, reg_map: HashMap<String, u16>) -> Self {
        ExecutionTrace {
            reg_trace: reg_map.keys().map(|_| Vec::new()).collect(),
            reg_writes: vec![None; reg_map.len()],
            reg_map,
            mem_ops: Vec::new(),
            len: PC_INITIAL_VAL + 1,
            pc_trace: Vec::new(),
            submachine_ops: MachineInstance::all().iter().map(|_| Vec::new()).collect(),
            known_cols: vec![],
            all_cols: witness_cols,
        }
    }

    /// transpose the register write operations into value columns
    fn generate_registers_trace(&mut self) -> Vec<(String, Vec<F>)> {
        let mut reg_values: Vec<Vec<F>> =
            vec![Vec::with_capacity(self.pc_trace.len().next_power_of_two()); self.reg_map.len()];

        // reverse lookup
        let idx_reg: HashMap<u16, &str> =
            self.reg_map.iter().map(|(k, &v)| (v, k.as_str())).collect();

        for i in 0..self.reg_map.len() {
            let reg = idx_reg[&(i as u16)];
            if reg == "pc" {
                reg_values[i].extend(self.pc_trace.iter().map(|&v| F::from(v)));
            } else {
                reg_values[i] = std::mem::take(&mut self.reg_trace[i]);
            }
        }

        reg_values
            .into_iter()
            .enumerate()
            .map(|(i, values)| (format!("main::{}", idx_reg[&(i as u16)]), values))
            .collect()
    }
}

#[derive(Default)]
pub struct RegisterMemory<F: FieldElement> {
    last: HashMap<u32, Elem<F>>,
    second_last: HashMap<u32, Elem<F>>,
}

impl<F: FieldElement> RegisterMemory<F> {
    pub fn for_bootloader(&self) -> HashMap<u32, F> {
        self.second_last
            .iter()
            .map(|(k, v)| (*k, v.into_fe()))
            .collect()
    }
}

mod builder {
    use std::{cell::RefCell, cmp, collections::HashMap, time::Instant};

    use powdr_ast::{
        analyzed::{Analyzed, DegreeRange},
        asm_analysis::{Machine, RegisterTy},
    };
    use powdr_number::FieldElement;
    use rayon::iter::{IntoParallelIterator, ParallelBridge, ParallelExtend, ParallelIterator};

    use crate::{
        pil, BinaryMachine, Elem, ExecMode, Execution, ExecutionTrace, KnownWitnessCol,
        MachineInstance, MemOperation, MemOperationKind, MemoryMachine, MemoryState,
        PoseidonGlMachine, PublicsMachine, RegisterMemory, ShiftMachine, SplitGlMachine,
        Submachine, SubmachineBoxed, SubmachineOp, PC_INITIAL_VAL,
    };

    fn namespace_degree_range<F: FieldElement>(
        opt_pil: &Analyzed<F>,
        namespace: &str,
    ) -> DegreeRange {
        opt_pil
            .committed_polys_in_source_order()
            .find(|(s, _)| s.absolute_name.contains(&format!("{namespace}::")))
            .and_then(|(s, _)| s.degree)
            // all machines/columns should have a degree range defined
            .unwrap()
    }

    fn register_names(main: &Machine) -> Vec<&str> {
        main.registers
            .iter()
            .filter_map(|statement| {
                if statement.ty != RegisterTy::Assignment {
                    Some(&statement.name[..])
                } else {
                    None
                }
            })
            .collect()
    }

    pub struct TraceBuilder<'b, F: FieldElement> {
        trace: ExecutionTrace<F>,

        submachines: HashMap<MachineInstance, RefCell<Box<dyn Submachine<F>>>>,

        /// Maximum rows we can run before we stop the execution.
        max_rows: usize,

        // index of special case registers to look after:
        pc_idx: u16,

        /// The value of PC at the start of the execution of the current row.
        curr_pc: Elem<F>,

        /// The PC in the register bank refers to the batches, we have to track our
        /// actual program counter independently.
        next_statement_line: u32,

        /// When PC is written, we need to know what line to actually execute next
        /// from this map of batch to statement line.
        batch_to_line_map: &'b [u32],

        /// Current register bank
        regs: Vec<Elem<F>>,

        /// Current memory.
        mem: HashMap<u32, u32>,

        /// Separate register memory, last and second last.
        reg_mem: RegisterMemory<F>,

        /// The execution mode we running.
        /// Fast: do not save the register's trace and memory accesses.
        /// Trace: save everything - needed for continuations.
        mode: ExecMode,
    }

    impl<'a, 'b: 'a, F: FieldElement> TraceBuilder<'b, F> {
        /// Creates a new builder.
        ///
        /// May fail if max_rows_len is too small or if the main machine is
        /// empty. In this case, the final (empty) execution trace is returned
        /// in Err.
        pub fn new(
            main: &'a Machine,
            opt_pil: Option<&Analyzed<F>>,
            witness_cols: Vec<String>,
            mem: MemoryState,
            batch_to_line_map: &'b [u32],
            max_rows_len: usize,
            mode: ExecMode,
        ) -> Result<Self, Box<Execution<F>>> {
            let reg_map = register_names(main)
                .into_iter()
                .enumerate()
                .map(|(i, name)| (name.to_string(), i as u16))
                .collect::<HashMap<String, u16>>();

            let reg_len = reg_map.len();

            // To save cache/memory bandwidth, I set the register index to be
            // u16, so panic if it doesn't fit (it obviously will fit for RISC-V).
            <usize as TryInto<u16>>::try_into(reg_len).unwrap();

            let pc_idx = reg_map["pc"];
            let mut regs = vec![0.into(); reg_len];
            regs[pc_idx as usize] = PC_INITIAL_VAL.into();

            let submachines: HashMap<_, RefCell<Box<dyn Submachine<F>>>> =
                if let ExecMode::Witness = mode {
                    [
                        (
                            MachineInstance::memory,
                            RefCell::new(Box::new(MemoryMachine::new("main_memory", &witness_cols)))
                                as RefCell<Box<dyn Submachine<F>>>, // this first `as` is needed to coerce the type of the array
                        ),
                        (
                            MachineInstance::regs,
                            RefCell::new(Box::new(MemoryMachine::new("main_regs", &witness_cols))),
                        ),
                        (
                            MachineInstance::binary,
                            RefCell::new(BinaryMachine::new_boxed("main_binary", &witness_cols)),
                        ),
                        (
                            MachineInstance::shift,
                            RefCell::new(ShiftMachine::new_boxed("main_shift", &witness_cols)),
                        ),
                        (
                            MachineInstance::split_gl,
                            RefCell::new(SplitGlMachine::new_boxed("main_split_gl", &witness_cols)),
                        ),
                        (
                            MachineInstance::publics,
                            RefCell::new(PublicsMachine::new_boxed("main_publics", &witness_cols)),
                        ),
                        (
                            MachineInstance::poseidon_gl,
                            RefCell::new(PoseidonGlMachine::new_boxed(
                                "main_poseidon_gl",
                                &witness_cols,
                            )),
                        ),
                    ]
                    .into_iter()
                    .collect()
                } else {
                    Default::default()
                };

            let mut ret = Self {
                pc_idx,
                curr_pc: PC_INITIAL_VAL.into(),
                trace: ExecutionTrace::new(witness_cols, reg_map),
                submachines,
                next_statement_line: 1,
                batch_to_line_map,
                max_rows: max_rows_len,
                regs,
                mem,
                reg_mem: Default::default(),
                mode,
            };

            if ret.has_enough_rows() || ret.set_next_pc().is_none() {
                Err(Box::new(ret.finish(opt_pil, vec![])))
            } else {
                Ok(ret)
            }
        }

        pub(crate) fn pc_trace(&self) -> &[u32] {
            &self.trace.pc_trace
        }

        pub(crate) fn submachine_op(
            &mut self,
            m: MachineInstance,
            identity_id: u64,
            lookup_args: &[F],
            extra: &[F],
        ) {
            if let ExecMode::Witness = self.mode {
                self.trace
                    .submachine_ops
                    .get_mut(m as usize)
                    .unwrap()
                    .push(SubmachineOp {
                        identity_id,
                        lookup_args: lookup_args.try_into().unwrap(),
                        extra: extra.to_vec(),
                    });
            }
        }

        pub(crate) fn main_columns_len(&self) -> usize {
            let cols_len = self.trace.known_cols.len() / KnownWitnessCol::count();

            // sanity check
            if let ExecMode::Witness = self.mode {
                assert!(self.trace.len <= cols_len);
            }

            cols_len
        }

        // convert the flat array of rows into a hashmap of columns.
        pub(crate) fn generate_main_columns(&mut self) -> HashMap<String, Vec<F>> {
            let main_columns_len = self.main_columns_len();
            let cols: HashMap<String, Vec<F>> = KnownWitnessCol::all()
                .into_par_iter()
                .map(|col| {
                    let mut values = Vec::with_capacity(main_columns_len.next_power_of_two());
                    for i in 0..main_columns_len {
                        values.push(
                            self.trace.known_cols[i * KnownWitnessCol::count() + col as usize],
                        );
                    }
                    (col.name().to_string(), values)
                })
                .collect();
            cols
        }

        /// get the value of PC as of the start of the execution of the current row.
        pub(crate) fn get_pc(&self) -> Elem<F> {
            self.curr_pc
        }

        /// get the value of PC as updated by the last executed instruction.
        /// The actual PC is only updated when moving to a new row.
        pub(crate) fn get_next_pc(&self) -> Elem<F> {
            self.regs[self.pc_idx as usize]
        }

        /// get current value of register
        pub(crate) fn get_reg(&self, idx: &str) -> Elem<F> {
            self.get_reg_idx(self.trace.reg_map[idx])
        }

        /// get current value of register by register index instead of name
        fn get_reg_idx(&self, idx: u16) -> Elem<F> {
            if idx == self.pc_idx {
                return self.get_pc();
            }
            self.regs[idx as usize]
        }

        /// sets the PC
        pub(crate) fn set_pc(&mut self, value: Elem<F>) {
            // updates the internal statement-based program counter accordingly:
            self.next_statement_line = self.batch_to_line_map[value.u() as usize];
            self.set_reg_idx(self.pc_idx, value);
        }

        /// set next value of register, accounting to x0 writes
        ///
        /// to set the PC, use set_pc() instead of this
        pub(crate) fn set_reg(&mut self, idx: &str, value: impl Into<Elem<F>>) {
            self.set_reg_impl(idx, value.into())
        }

        fn set_reg_impl(&mut self, idx: &str, value: Elem<F>) {
            let idx = self.trace.reg_map[idx];
            assert!(idx != self.pc_idx);
            self.set_reg_idx(idx, value);
        }

        /// raw set next value of register by register index instead of name
        fn set_reg_idx(&mut self, idx: u16, value: Elem<F>) {
            // Record register write in trace. Only for non-pc, non-assignment registers.
            if let ExecMode::Trace | ExecMode::Witness = self.mode {
                if idx != self.pc_idx {
                    self.trace.reg_writes[idx as usize] = Some(value.into_fe());
                }
            }
            self.regs[idx as usize] = value;
        }

        pub fn set_col_idx(&mut self, col: KnownWitnessCol, idx: usize, value: Elem<F>) {
            if let ExecMode::Witness = self.mode {
                let idx = (KnownWitnessCol::count() * idx) + col as usize;
                *self.trace.known_cols.get_mut(idx).unwrap() = value.into_fe();
            }
        }

        pub fn set_col(&mut self, col: KnownWitnessCol, value: Elem<F>) {
            if let ExecMode::Witness = self.mode {
                let idx = (self.trace.known_cols.len() - KnownWitnessCol::count()) + col as usize;
                *self.trace.known_cols.get_mut(idx).unwrap() = value.into_fe();
            }
        }

        pub fn col_is_defined(&self, name: &str) -> bool {
            if let ExecMode::Trace | ExecMode::Witness = self.mode {
                self.trace.all_cols.contains(&name.to_string())
            } else {
                false
            }
        }

        pub fn push_row(&mut self, pc: u32) {
            if let ExecMode::Trace | ExecMode::Witness = self.mode {
                self.trace.pc_trace.push(pc);
                self.trace
                    .reg_trace
                    .iter_mut()
                    .enumerate()
                    .for_each(|(idx, v)| {
                        // set the value from the write or copy the previous value
                        if let Some(w) = self.trace.reg_writes[idx].take() {
                            v.push(w);
                        } else {
                            v.push(v.last().cloned().unwrap_or(F::zero()));
                        }
                    });
            }
            if let ExecMode::Witness = self.mode {
                let new_len = self.trace.known_cols.len() + KnownWitnessCol::count();
                self.trace.known_cols.resize(new_len, F::zero());
            }
        }

        /// advance to next row, returns the index to the statement that must be
        /// executed now, or None if the execution is finished
        pub fn advance(&mut self) -> Option<u32> {
            let next_pc = self.regs[self.pc_idx as usize];
            if self.curr_pc != next_pc {
                // If we are at the limit of rows, stop the execution
                if self.has_enough_rows() {
                    return None;
                }

                self.trace.len += 1;
                self.set_col(KnownWitnessCol::pc_update, next_pc);
                self.push_row(next_pc.u());

                self.curr_pc = next_pc;
            }

            // advance to the next statement
            let st_line = self.next_statement_line;

            // optimistically advance the internal and register PCs
            self.next_statement_line += 1;
            self.set_next_pc().and(Some(st_line))
        }

        pub(crate) fn set_mem(&mut self, addr: u32, val: u32, step: u32, identity_id: u64) {
            if let ExecMode::Witness = self.mode {
                self.submachine_op(
                    MachineInstance::memory,
                    identity_id,
                    &[1.into(), addr.into(), step.into(), val.into()],
                    &[],
                );
            }
            if let ExecMode::Trace | ExecMode::Witness = self.mode {
                self.trace.mem_ops.push(MemOperation {
                    row: self.trace.len,
                    kind: MemOperationKind::Write,
                    address: addr,
                });
            }

            self.mem.insert(addr, val);
        }

        pub(crate) fn get_mem(&mut self, addr: u32, step: u32, identity_id: u64) -> u32 {
            let val = *self.mem.get(&addr).unwrap_or(&0);
            if let ExecMode::Witness = self.mode {
                self.submachine_op(
                    MachineInstance::memory,
                    identity_id,
                    &[0.into(), addr.into(), step.into(), val.into()],
                    &[],
                );
            }
            if let ExecMode::Trace | ExecMode::Witness = self.mode {
                self.trace.mem_ops.push(MemOperation {
                    row: self.trace.len,
                    kind: MemOperationKind::Read,
                    address: addr,
                });
            }
            val
        }

        pub(crate) fn set_reg_mem(&mut self, addr: u32, val: Elem<F>) {
            if addr != 0 {
                self.reg_mem.last.insert(addr, val);
            }
        }

        pub(crate) fn get_reg_mem(&mut self, addr: u32) -> Elem<F> {
            let zero: Elem<F> = 0u32.into();
            if addr == 0 {
                zero
            } else {
                *self.reg_mem.last.get(&addr).unwrap_or(&zero)
            }
        }

        pub(crate) fn backup_reg_mem(&mut self) {
            self.reg_mem.second_last = self.reg_mem.last.clone();
        }

        pub fn finish(
            mut self,
            opt_pil: Option<&Analyzed<F>>,
            program_columns: Vec<(String, Vec<F>)>,
        ) -> Execution<F> {
            if let ExecMode::Fast = self.mode {
                return Execution {
                    trace_len: self.trace.len,
                    memory: self.mem,
                    memory_accesses: Vec::new(),
                    trace: HashMap::new(),
                    register_memory: HashMap::new(),
                };
            }

            let pil = opt_pil.unwrap();

            let start = Instant::now();

            // turn register write operations into witness columns
            let mut cols = self
                .trace
                .generate_registers_trace()
                .into_iter()
                .collect::<HashMap<_, _>>();
            log::debug!(
                "Generating register traces took {}s",
                start.elapsed().as_secs_f64(),
            );

            let main_degree = {
                let range = namespace_degree_range(pil, "main");
                std::cmp::max(self.trace.len.next_power_of_two() as u32, range.min as u32)
            };

            // fill up reg trace to degree
            cols.values_mut().for_each(|v| {
                let last = *v.last().unwrap();
                v.resize(main_degree as usize, last);
            });

            // trace mode doesn't generate a full witness
            if let ExecMode::Trace = self.mode {
                return Execution {
                    trace_len: self.trace.len,
                    memory: self.mem,
                    memory_accesses: std::mem::take(&mut self.trace.mem_ops),
                    trace: cols,
                    register_memory: self.reg_mem.for_bootloader(),
                };
            }

            // add reg columns to trace
            cols.extend(self.generate_main_columns());

            // add program columns to main trace
            cols.extend(program_columns);

            // fill up main trace to degree
            cols.values_mut().for_each(|v| {
                let last = *v.last().unwrap();
                v.resize(main_degree as usize, last);
            });

            log::debug!(
                "Finalizing main machine trace took {}s",
                start.elapsed().as_secs_f64(),
            );

            // generate witness for submachines
            // ----------------------------
            let links = pil::links_from_pil(pil);

            // cache for identity_id->selector
            let mut id_sel = Vec::new(); // TODO: assumes identity_ids are small enough!
            for l in links.iter() {
                if id_sel.len() <= l.id() as usize {
                    id_sel.resize(l.id() as usize + 1, None);
                }
                id_sel[l.id() as usize] = pil::extract_selector(l);
            }

            let start = Instant::now();
            let subm_cols = self
                .submachines
                .into_iter()
                // take each submachine and get its operations
                .map(|(m, machine)| {
                    let ops =
                        std::mem::take(self.trace.submachine_ops.get_mut(m as usize).unwrap());
                    (m, machine.into_inner(), ops)
                })
                // handle submachines in parallel
                .par_bridge()
                .flat_map(|(m, mut machine, ops)| {
                    // apply the operations to the submachine
                    ops.into_iter().for_each(|op| {
                        let selector = &id_sel[op.identity_id as usize];
                        machine.add_operation(selector.as_deref(), &op.lookup_args, &op.extra);
                    });

                    // finalize and extend the submachine traces and add to full trace
                    if machine.len() > 0 {
                        let range = namespace_degree_range(pil, machine.namespace());
                        // extend with dummy blocks up to the required machine degree
                        let machine_degree =
                            std::cmp::max(machine.len().next_power_of_two(), range.min as u32);
                        machine.finish(machine_degree)
                    } else if m == MachineInstance::publics {
                        // for the publics machine, even with no operations being
                        // issued, the declared "publics" force the cells to be
                        // filled. We add operations here to emulate that.
                        for i in 0..8 {
                            machine.add_operation(
                                None,
                                &[i.into(), 0.into(), 0.into(), 0.into()],
                                &[],
                            );
                        }
                        machine.finish(8)
                    } else {
                        // keep machine columns empty
                        machine.finish(0)
                    }
                });
            cols.par_extend(subm_cols);

            log::debug!(
                "Generating submachine traces took {}s",
                start.elapsed().as_secs_f64(),
            );

            // filter columns present in the witness. Some columns may be optimized away.
            let cols: HashMap<String, Vec<F>> = cols
                .into_iter()
                .filter(|(col, _)| self.trace.all_cols.contains(col))
                .collect();

            let missing_cols = self
                .trace
                .all_cols
                .iter()
                .filter(|col| !cols.contains_key(*col));

            log::debug!("RISCV executor missing columns: {:?}", missing_cols);

            Execution {
                trace_len: self.trace.len,
                memory: self.mem,
                memory_accesses: std::mem::take(&mut self.trace.mem_ops),
                trace: cols,
                register_memory: self.reg_mem.for_bootloader(),
            }
        }

        /// Should we stop the execution because the maximum number of rows has
        /// been reached?
        fn has_enough_rows(&self) -> bool {
            self.trace.len >= self.max_rows
        }

        /// Optimistically increment PC, but the execution might rewrite it.
        ///
        /// Only do it when running the last statement of a batch.
        fn set_next_pc(&mut self) -> Option<()> {
            let pc = self.curr_pc.u();
            let line_of_next_batch = *self.batch_to_line_map.get(pc as usize + 1)?;

            match self.next_statement_line.cmp(&line_of_next_batch) {
                cmp::Ordering::Less => (),
                cmp::Ordering::Equal => {
                    // Write it directly. We don't want to call set_reg_idx and
                    // trace the natural increment of the PC.
                    self.regs[self.pc_idx as usize] = (pc + 1).into();
                }
                cmp::Ordering::Greater => {
                    if pc < 2 {
                        // end of program, no real batch to execute
                        return None;
                    }
                    panic!(
                        "next_statement_line: {} > line_of_next_batch: {}",
                        self.next_statement_line, line_of_next_batch
                    );
                }
            };

            Some(())
        }
    }
}

pub fn get_main_machine(program: &AnalysisASMFile) -> &Machine {
    program.get_machine(&parse_absolute_path("::Main")).unwrap()
}

struct PreprocessedMain<'a, F: FieldElement> {
    /// list of all statements (batches expanded)
    statements: Vec<&'a FunctionStatement>,
    /// label to batch number
    label_map: HashMap<&'a str, Elem<F>>,
    /// batch number to its first statement idx
    batch_to_line_map: Vec<u32>,
    /// file number to (dir,name)
    debug_files: Vec<(&'a str, &'a str)>,
    /// function label to batch number
    function_starts: BTreeMap<usize, &'a str>,
    /// .debug loc to batch number
    location_starts: BTreeMap<usize, (usize, usize)>,
}

/// Returns the list of instructions, directly indexable by PC, the map from
/// labels to indices into that list, and the list with the start of each batch.
fn preprocess_main_function<F: FieldElement>(machine: &Machine) -> PreprocessedMain<F> {
    let CallableSymbol::Function(main_function) = &machine.callable.0["main"] else {
        panic!("main function missing")
    };

    let orig_statements = &main_function.body.statements;

    let mut statements = Vec::new();
    let mut label_map = HashMap::new();
    let mut batch_to_line_map = vec![0; PC_INITIAL_VAL];
    let mut debug_files = Vec::new();
    let mut function_starts = BTreeMap::new();
    let mut location_starts = BTreeMap::new();

    for (batch_idx, batch) in orig_statements.iter_batches().enumerate() {
        batch_to_line_map.push(statements.len() as u32);
        let mut statement_seen = false;
        for s in batch.statements {
            match s {
                FunctionStatement::Assignment(_)
                | FunctionStatement::Instruction(_)
                | FunctionStatement::Return(_) => {
                    statement_seen = true;
                    statements.push(s)
                }
                FunctionStatement::DebugDirective(d) => {
                    match &d.directive {
                        DebugDirective::File(idx, dir, file) => {
                            // debug files should be densely packed starting
                            // from 1, so the idx should match vec size + 1:
                            assert_eq!(*idx, debug_files.len() + 1);
                            debug_files.push((dir.as_str(), file.as_str()));
                        }
                        DebugDirective::Loc(file, line, _) => {
                            location_starts.insert(batch_idx + PC_INITIAL_VAL, (*file, *line));
                            statements.push(s);
                        }
                        DebugDirective::OriginalInstruction(_) => {
                            // keep debug locs for debugging purposes
                            statements.push(s);
                        }
                    }
                }
                FunctionStatement::Label(LabelStatement { source: _, name }) => {
                    // assert there are no statements in the middle of a block
                    assert!(!statement_seen);
                    label_map.insert(name.as_str(), (batch_idx + PC_INITIAL_VAL).into());
                    // TODO: would looking for "___dot_Lfunc_begin" be less hacky? would require more work to handle ecalls though...
                    if !name.contains("___dot_L") {
                        function_starts.insert(batch_idx + PC_INITIAL_VAL, name.as_str());
                    }
                    statements.push(s);
                }
            }
        }
    }
    assert!(statements.len() <= u32::MAX as usize);

    // add a final element to the map so the queries don't overflow:
    batch_to_line_map.push(statements.len() as u32);

    PreprocessedMain {
        statements,
        label_map,
        batch_to_line_map,
        debug_files,
        function_starts,
        location_starts,
    }
}

type Callback<'a, F> = dyn powdr_executor::witgen::QueryCallback<F> + 'a;

struct Executor<'a, 'b, F: FieldElement> {
    proc: TraceBuilder<'b, F>,
    label_map: HashMap<&'a str, Elem<F>>,
    inputs: &'b Callback<'b, F>,
    bootloader_inputs: Vec<Elem<F>>,
    fixed: Arc<Vec<(String, VariablySizedColumn<F>)>>,
    // program columns: maps "ROM" fixed cols to respective witness cols
    program_cols: HashMap<String, String>,
    step: u32,
    mode: ExecMode,

    pil_links: Vec<Identity<F>>,
    // instead of a hash map (instruction,target), we keep a flat vec, and index
    // using the instruction (rows) and target machine (columns).
    pil_instruction_links: Vec<Option<Vec<Identity<F>>>>,
    pil_other_links: HashMap<(&'static str, &'static str), Vec<Identity<F>>>,
    // these are "hot" fixed columns that are accessed directly by the executor
    cached_fixed_cols: Vec<Vec<F>>,
}

impl<F: FieldElement> Executor<'_, '_, F> {
    fn init(&mut self) {
        self.step = 4;

        if let ExecMode::Witness = self.mode {
            for c in KnownFixedCol::all() {
                self.cached_fixed_cols
                    .push(self.get_fixed(c.name()).unwrap().clone());
            }
        }

        for i in 0..2 {
            self.proc.push_row(i);
            self.proc
                .set_col_idx(KnownWitnessCol::_operation_id, i as usize, 2.into());
            self.proc
                .set_col_idx(KnownWitnessCol::pc_update, i as usize, (i + 1).into());
        }
    }

    fn get_fixed(&self, name: &str) -> Option<&Vec<F>> {
        self.fixed
            .iter()
            .find(|(n, _)| n == name)
            // ROM is uniquely sized, which for now is all we looking at
            .map(|(_, v)| v.get_uniquely_sized().expect("not uniquely sized!"))
    }

    fn get_known_fixed(&self, col: KnownFixedCol, row: usize) -> F {
        self.cached_fixed_cols
            .get(col as usize)
            .map(|v| v[row])
            .unwrap_or_default()
    }

    fn sink_id(&self) -> u32 {
        // sink_id is the length of the ROM. we find it by looking at the line instr__loop activates
        self.get_fixed("main__rom::p_instr__loop")
            .unwrap()
            .iter()
            .position(|val| val.is_one())
            .map(|pos| pos as u32)
            .expect("could not find sink_id by looking at the p_instr__loop column")
    }

    /// read register value, updating the register memory machine
    fn reg_read(&mut self, step_offset: u32, reg: u32, identity_id: u64) -> Elem<F> {
        let val = self.proc.get_reg_mem(reg);
        self.proc.submachine_op(
            MachineInstance::regs,
            identity_id,
            &[
                0.into(),
                reg.into(),
                (self.step + step_offset).into(),
                val.into_fe(),
            ],
            &[],
        );
        val
    }

    /// write value to register, updating the register memory machine
    fn reg_write(&mut self, step_offset: u32, reg: u32, val: Elem<F>, identity_id: u64) {
        self.proc.submachine_op(
            MachineInstance::regs,
            identity_id,
            &[
                1.into(),
                reg.into(),
                (self.step + step_offset).into(),
                val.into_fe(),
            ],
            &[],
        );
        self.proc.set_reg_mem(reg, val);
    }

    /// Gets the identity id for a link associated with a given instruction.
    /// idx is based on the order link appear in the assembly (assumed to be the same in the optimized pil).
    fn instr_link_id(&mut self, instr: Instruction, target: MachineInstance, idx: usize) -> u64 {
        if let ExecMode::Witness = self.mode {
            let entries = self
                .pil_instruction_links
                .get_mut(instr as usize * MachineInstance::count() + target as usize)
                .unwrap()
                .get_or_insert_with(|| {
                    pil::find_instruction_links(&self.pil_links, instr.flag(), target.namespace())
                });
            entries.get(idx).unwrap().id()
        } else {
            // we don't care about identity ids in non witness mode
            0
        }
    }

    /// Find the identity id of a link.
    fn link_id(&mut self, from: &'static str, target: &'static str, idx: usize) -> u64 {
        if let ExecMode::Witness = self.mode {
            let entries = self
                .pil_other_links
                .entry((from, target))
                .or_insert_with(|| pil::find_links(&self.pil_links, from, target));
            entries.get(idx).unwrap().id()
        } else {
            // we don't care about identity ids in fast mode
            0
        }
    }

    fn exec_instruction(&mut self, name: &str, args: &[Expression]) -> Option<Elem<F>> {
        // shorthand macros for setting/getting main machine witness values in the current row
        macro_rules! set_col {
            ($name:ident, $val:expr) => {
                self.proc.set_col(KnownWitnessCol::$name, $val);
            };
        }

        macro_rules! get_fixed {
            ($name:ident) => {
                if let ExecMode::Witness = self.mode {
                    Elem::Field(
                        self.get_known_fixed(KnownFixedCol::$name, self.proc.get_pc().u() as usize),
                    )
                } else {
                    Elem::Field(F::zero())
                }
            };
        }

        macro_rules! submachine_op {
            ($machine:ident, $selector:expr, $args:expr, $($extra:expr),*) => {
                self.proc.submachine_op(MachineInstance::$machine, $selector, $args, &[$($extra, )*])
            };
        }

        let args = args
            .iter()
            .map(|expr| self.eval_expression(expr).unwrap())
            .collect::<Vec<_>>();

        self.proc.backup_reg_mem();

        if self.proc.col_is_defined("main::X_const") {
            set_col!(X, get_fixed!(X_const));
        }

        if self.proc.col_is_defined("main::Y_const") {
            set_col!(Y, get_fixed!(Y_const));
        }

        if self.proc.col_is_defined("main::Z_const") {
            set_col!(Z, get_fixed!(Z_const));
        }

        if self.proc.col_is_defined("main::W_const") {
            set_col!(W, get_fixed!(W_const));
        }

        let instr = Instruction::from_name(name).expect("unknown instruction");

        let r = match instr {
            Instruction::set_reg => {
                let addr = args[0].u();
                let val = args[1];

                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                self.reg_write(0, addr, val, lid);

                set_col!(Y, val);

                if !get_fixed!(Y_read_free).is_zero() {
                    set_col!(Y_free_value, val);
                }

                None
            }
            Instruction::get_reg => {
                // setting the flag because the rom fixed column for the `get_reg` flag gets optimized away...
                set_col!(instr_get_reg, 1.into());
                let addr = args[0].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val = self.reg_read(0, addr, lid);

                Some(val)
            }
            Instruction::affine => {
                let read_reg = args[0].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg, lid);
                let write_reg = args[1].u();
                let factor = args[2];
                let offset = args[3];

                let res = val1.mul(&factor).add(&offset);

                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                self.reg_write(1, write_reg, res, lid);
                set_col!(tmp1_col, val1);

                None
            }

            Instruction::mstore | Instruction::mstore_bootloader => {
                let read_reg1 = args[0].u();
                let read_reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let addr1 = self.reg_read(0, read_reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let addr2 = self.reg_read(1, read_reg2, lid);
                let offset = args[2].bin();
                let read_reg3 = args[3].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 2);
                let value = self.reg_read(2, read_reg3, lid);

                let addr = addr1.bin() - addr2.bin() + offset;
                // assumptions from the asm machine
                assert!(addr >= 0);
                assert_eq!(addr % 4, 0);

                set_col!(
                    wrap_bit,
                    if addr > u32::MAX as i64 {
                        Elem::Field(F::one())
                    } else {
                        Elem::Field(F::zero())
                    }
                );

                let addr = addr as u32;
                let lid = self.instr_link_id(instr, MachineInstance::memory, 0);
                self.proc.set_mem(addr, value.u(), self.step + 3, lid);

                set_col!(tmp1_col, addr1);
                set_col!(tmp2_col, addr2);
                set_col!(tmp3_col, value);

                let (b1, b2, b3, b4, _sign) = decompose_lower32(addr.into());
                set_col!(X_b1, Elem::from_u32_as_fe(b1.into()));
                set_col!(X_b2, Elem::from_u32_as_fe(b2.into()));
                set_col!(X_b3, Elem::from_u32_as_fe(b3.into()));
                set_col!(X_b4, Elem::from_u32_as_fe(b4.into()));

                None
            }
            Instruction::mload => {
                let read_reg = args[0].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let addr1 = self.reg_read(0, read_reg, lid);
                let offset = args[1].bin();
                let write_addr1 = args[2].u();
                let write_addr2 = args[3].u();

                let addr = addr1.bin() + offset;

                let lid = self.instr_link_id(instr, MachineInstance::memory, 0);
                let val = self
                    .proc
                    .get_mem(addr as u32 & 0xfffffffc, self.step + 1, lid);
                let rem = addr % 4;

                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                self.reg_write(2, write_addr1, val.into(), lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 2);
                self.reg_write(3, write_addr2, rem.into(), lid);

                set_col!(tmp1_col, addr1);
                set_col!(tmp3_col, Elem::from_u32_as_fe(val));
                set_col!(tmp4_col, Elem::from_u32_as_fe(rem as u32));

                let v = addr1.add(&args[1]).as_i64_from_lower_bytes();
                let (b1, b2, b3, b4, _sign) = decompose_lower32(v);
                set_col!(X_b1, Elem::from_u32_as_fe((b1 / 4).into()));
                set_col!(X_b2, Elem::from_u32_as_fe(b2.into()));
                set_col!(X_b3, Elem::from_u32_as_fe(b3.into()));
                set_col!(X_b4, Elem::from_u32_as_fe(b4.into()));
                set_col!(
                    wrap_bit,
                    Elem::from_u32_as_fe(((v as u64 >> 32) & 1) as u32)
                );

                None
            }
            // TODO: update to witness generation for continuations
            Instruction::load_bootloader_input => {
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let addr = self.reg_read(0, args[0].u(), lid);
                let write_addr = args[1].u();
                let factor = args[2].bin();
                let offset = args[3].bin();

                let addr = addr.bin() * factor + offset;
                let val = self.bootloader_inputs[addr as usize];

                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                self.reg_write(2, write_addr, val, lid);

                None
            }
            // TODO: update to witness generation for continuations
            Instruction::assert_bootloader_input => {
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let addr = self.reg_read(0, args[0].u(), lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let val = self.reg_read(1, args[1].u(), lid);
                let factor = args[2].bin();
                let offset = args[3].bin();

                let addr = (addr.bin() * factor + offset) as usize;
                let actual_val = self.bootloader_inputs[addr];

                assert_eq!(val, actual_val);

                None
            }
            Instruction::load_label => {
                let write_reg = args[0].u();
                let label = args[1];
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                self.reg_write(0, write_reg, label, lid);

                set_col!(tmp1_col, label);

                set_col!(instr_load_label_param_l, label);

                None
            }
            Instruction::jump => {
                let label = args[0];
                let next_pc = self.proc.get_pc().u() + 1;
                let write_reg = args[1].u();

                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                self.reg_write(0, write_reg, next_pc.into(), lid);

                self.proc.set_pc(label);

                set_col!(instr_jump_param_l, label);

                None
            }
            Instruction::jump_dyn => {
                let read_reg = args[0].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let addr = self.reg_read(0, read_reg, lid);
                let next_pc = self.proc.get_pc().u() + 1;
                let write_reg = args[1].u();

                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                self.reg_write(0, write_reg, next_pc.into(), lid);

                self.proc.set_pc(addr);

                set_col!(tmp1_col, addr);

                None
            }
            // TODO: update to witness generation for continuations
            Instruction::jump_to_bootloader_input => {
                let bootloader_input_idx = args[0].bin() as usize;
                let addr = self.bootloader_inputs[bootloader_input_idx];
                self.proc.set_pc(addr);

                None
            }
            Instruction::branch_if_diff_nonzero => {
                let read_reg1 = args[0].u();
                let read_reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let val2 = self.reg_read(1, read_reg2, lid);

                let val: Elem<F> = val1.sub(&val2);
                let label = args[2];
                if !val.is_zero() {
                    self.proc.set_pc(label);
                }

                set_col!(tmp1_col, val1);
                set_col!(tmp2_col, val2);
                set_col!(XX, val);
                set_col!(XXIsZero, Elem::from_bool_as_fe(val.is_zero()));
                if !val.is_zero() {
                    set_col!(XX_inv, Elem::Field(F::one() / val.into_fe()));
                }

                set_col!(instr_branch_if_diff_nonzero_param_l, label);

                None
            }
            Instruction::branch_if_diff_equal => {
                let read_reg1 = args[0].u();
                let read_reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let val2 = self.reg_read(1, read_reg2, lid);
                let offset = args[2];
                let val: Elem<F> = val1.sub(&val2).sub(&offset);
                let label = args[3];

                if val.is_zero() {
                    self.proc.set_pc(label);
                }

                set_col!(tmp1_col, val1);
                set_col!(tmp2_col, val2);
                set_col!(XX, val);
                set_col!(XXIsZero, Elem::from_bool_as_fe(val.is_zero()));
                if !val.is_zero() {
                    set_col!(XX_inv, Elem::Field(F::one() / val.into_fe()));
                }

                set_col!(instr_branch_if_diff_equal_param_l, label);

                None
            }
            Instruction::skip_if_equal => {
                let read_reg1 = args[0].u();
                let read_reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let val2 = self.reg_read(1, read_reg2, lid);
                let offset = args[2];
                let cond = args[3];
                let val: Elem<F> = val1.sub(&val2).add(&offset);

                if val.is_zero() {
                    let pc = self.proc.get_pc().s();
                    self.proc.set_pc((pc + cond.s() + 1).into());
                }

                set_col!(tmp1_col, val1);
                set_col!(tmp2_col, val2);
                set_col!(XX, val);
                set_col!(XXIsZero, Elem::from_bool_as_fe(val.is_zero()));
                if !val.is_zero() {
                    set_col!(XX_inv, Elem::Field(F::one() / val.into_fe()));
                }

                None
            }
            Instruction::branch_if_diff_greater_than => {
                let read_reg1 = args[0].u();
                let read_reg2 = args[1].u();
                // We can't call u() because input registers may have come from
                // a call to `to_signed`, which stores a signed integer.
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let val2 = self.reg_read(1, read_reg2, lid);
                let offset = args[2];
                let val: Elem<F> = val1.sub(&val2).sub(&offset);
                let label = args[3];

                if val.bin() > 0 {
                    self.proc.set_pc(label);
                }

                set_col!(tmp1_col, val1);
                set_col!(tmp2_col, val2);

                set_col!(instr_branch_if_diff_greater_than_param_l, label);

                let p = Elem::from_u32_as_fe(u32::MAX);
                let val_p = val.add(&p);

                let v = val_p.as_i64_from_lower_bytes();
                let (b1, b2, b3, b4, _sign) = decompose_lower32(v);
                set_col!(X_b1, Elem::from_u32_as_fe(b1.into()));
                set_col!(X_b2, Elem::from_u32_as_fe(b2.into()));
                set_col!(X_b3, Elem::from_u32_as_fe(b3.into()));
                set_col!(X_b4, Elem::from_u32_as_fe(b4.into()));
                set_col!(
                    wrap_bit,
                    if val.bin() > 0 {
                        Elem::Field(F::one())
                    } else {
                        Elem::Field(F::zero())
                    }
                );

                None
            }
            Instruction::is_diff_greater_than => {
                let read_reg1 = args[0].u();
                let read_reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let val2 = self.reg_read(1, read_reg2, lid);

                let offset = args[2];
                let write_reg = args[3].u();
                let val = val1.sub(&val2).sub(&offset);

                let r = if val.bin() > 0 { 1 } else { 0 };
                let lid = self.instr_link_id(instr, MachineInstance::regs, 2);
                self.reg_write(2, write_reg, r.into(), lid);

                set_col!(tmp1_col, val1);
                set_col!(tmp2_col, val2);

                let p = Elem::from_u32_as_fe(u32::MAX);
                let val = val.add(&p);
                let v = val.as_i64_from_lower_bytes();
                let (b1, b2, b3, b4, _sign) = decompose_lower32(v);
                set_col!(X_b1, Elem::from_u32_as_fe(b1.into()));
                set_col!(X_b2, Elem::from_u32_as_fe(b2.into()));
                set_col!(X_b3, Elem::from_u32_as_fe(b3.into()));
                set_col!(X_b4, Elem::from_u32_as_fe(b4.into()));
                set_col!(wrap_bit, Elem::from_u32_as_fe(r));

                None
            }
            Instruction::is_equal_zero => {
                let read_reg = args[0].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val = self.reg_read(0, read_reg, lid);
                let write_reg = args[1].u();

                let r = if val.is_zero() { 1 } else { 0 };
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                self.reg_write(2, write_reg, r.into(), lid);

                set_col!(tmp1_col, val);
                set_col!(XX, val);
                set_col!(XXIsZero, Elem::from_bool_as_fe(val.is_zero()));
                if !val.is_zero() {
                    set_col!(XX_inv, Elem::Field(F::one() / val.into_fe()));
                }

                None
            }
            Instruction::is_not_equal => {
                let read_reg1 = args[0].u();
                let read_reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let val2 = self.reg_read(1, read_reg2, lid);
                let write_reg = args[2].u();
                let val: Elem<F> = (val1.bin() - val2.bin()).into();

                let r = if !val.is_zero() { 1 } else { 0 };
                let lid = self.instr_link_id(instr, MachineInstance::regs, 2);
                self.reg_write(2, write_reg, r.into(), lid);

                set_col!(tmp1_col, val1);
                set_col!(tmp2_col, val2);
                set_col!(tmp3_col, Elem::from_u32_as_fe(r));
                set_col!(XX, val);
                set_col!(XXIsZero, Elem::from_bool_as_fe(val.is_zero()));
                if !val.is_zero() {
                    set_col!(XX_inv, Elem::Field(F::one() / val.into_fe()));
                }

                None
            }
            Instruction::add_wrap => {
                let read_reg1 = args[0].u();
                let read_reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let val2 = self.reg_read(1, read_reg2, lid);
                set_col!(tmp1_col, val1);
                set_col!(tmp2_col, val2);
                let offset = args[2];
                let write_reg = args[3].u();

                let val = val1.add(&val2).add(&offset);
                // assumptions from the asm machine
                assert!(val.bin() < (2 << 33));
                assert!(val.bin() >= 0);
                // don't use .u() here: we are deliberately discarding the
                // higher bits
                let r = val.bin() as u32;
                let lid = self.instr_link_id(instr, MachineInstance::regs, 2);
                self.reg_write(2, write_reg, r.into(), lid);
                set_col!(tmp3_col, Elem::from_u32_as_fe(r));

                let v = val.as_i64_from_lower_bytes();
                let (b1, b2, b3, b4, _sign) = decompose_lower32(v);
                set_col!(X_b1, Elem::from_u32_as_fe(b1.into()));
                set_col!(X_b2, Elem::from_u32_as_fe(b2.into()));
                set_col!(X_b3, Elem::from_u32_as_fe(b3.into()));
                set_col!(X_b4, Elem::from_u32_as_fe(b4.into()));
                set_col!(
                    wrap_bit,
                    if v > 0xffffffff {
                        Elem::Field(F::one())
                    } else {
                        Elem::Field(F::zero())
                    }
                );

                None
            }
            Instruction::wrap16 => {
                let read_reg = args[0].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val = self.reg_read(0, read_reg, lid);
                let factor = args[1].bin();
                let write_reg = args[2].u();
                let val_offset: Elem<F> = (val.bin() * factor).into();

                // don't use .u() here: we are deliberately discarding the
                // higher bits
                let r = val_offset.bin() as u32;
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                self.reg_write(3, write_reg, r.into(), lid);

                set_col!(tmp1_col, val);
                let tmp3_val = Elem::from_u32_as_fe(r);
                set_col!(tmp3_col, tmp3_val);

                let v = tmp3_val.as_i64_from_lower_bytes();
                let (b1, b2, b3, b4, _sign) = decompose_lower32(v);
                set_col!(X_b1, Elem::from_u32_as_fe(b1.into()));
                set_col!(X_b2, Elem::from_u32_as_fe(b2.into()));
                set_col!(X_b3, Elem::from_u32_as_fe(b3.into()));
                set_col!(X_b4, Elem::from_u32_as_fe(b4.into()));

                let (b5, b6, _b7, _b8, _sign) = decompose_lower32(val_offset.bin() >> 32);
                set_col!(Y_b5, Elem::from_u32_as_fe(b5.into()));
                set_col!(Y_b6, Elem::from_u32_as_fe(b6.into()));

                None
            }
            Instruction::sub_wrap_with_offset => {
                let read_reg1 = args[0].u();
                let read_reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let val2 = self.reg_read(1, read_reg2, lid);
                let offset = args[2];
                let write_reg = args[3].u();
                let val = val1.sub(&val2).add(&offset);

                let r_i64: i64 = val.bin() + 0x100000000;
                let r = r_i64 as u32;
                let lid = self.instr_link_id(instr, MachineInstance::regs, 2);
                self.reg_write(2, write_reg, r.into(), lid);

                set_col!(tmp1_col, val1);
                set_col!(tmp2_col, val2);
                set_col!(tmp3_col, Elem::from_u32_as_fe(r));

                let (b1, b2, b3, b4, _sign) = decompose_lower32(r_i64);
                set_col!(X_b1, Elem::from_u32_as_fe(b1.into()));
                set_col!(X_b2, Elem::from_u32_as_fe(b2.into()));
                set_col!(X_b3, Elem::from_u32_as_fe(b3.into()));
                set_col!(X_b4, Elem::from_u32_as_fe(b4.into()));
                set_col!(
                    wrap_bit,
                    if r_i64 > 0xffffffff {
                        Elem::Field(F::one())
                    } else {
                        Elem::Field(F::zero())
                    }
                );

                None
            }
            Instruction::sign_extend_byte => {
                let read_reg = args[0].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val = self.reg_read(0, read_reg, lid);
                let write_reg = args[1].u();

                // Sign extend the byte
                let byte_val = (val.u() as u8) as i8;
                let extended_val = byte_val as i32 as u32;
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                self.reg_write(3, write_reg, extended_val.into(), lid);

                set_col!(tmp1_col, val);
                set_col!(tmp3_col, Elem::from_u32_as_fe(extended_val));

                let v = val.as_i64_from_lower_bytes();
                let (b1, b2, b3, b4, _sign) = decompose_lower32(v);
                // first 7bits
                set_col!(Y_7bit, Elem::from_u32_as_fe((b1 & 0x7f).into()));
                // no X_b1 needed here
                set_col!(X_b2, Elem::from_u32_as_fe(b2.into()));
                set_col!(X_b3, Elem::from_u32_as_fe(b3.into()));
                set_col!(X_b4, Elem::from_u32_as_fe(b4.into()));
                set_col!(
                    wrap_bit,
                    if byte_val < 0 {
                        Elem::Field(F::one())
                    } else {
                        Elem::Field(F::zero())
                    }
                );

                None
            }
            Instruction::sign_extend_16_bits => {
                let read_reg = args[0].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val = self.reg_read(0, read_reg, lid);
                let write_reg = args[1].u();

                // Perform sign extension on the 16-bit value
                let sign_bit = (val.u() & 0x8000) != 0;
                let extended_val = if sign_bit {
                    val.u() | 0xFFFF0000
                } else {
                    val.u() & 0x0000FFFF
                };
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                self.reg_write(3, write_reg, extended_val.into(), lid);

                set_col!(tmp1_col, val);
                set_col!(tmp3_col, Elem::from_u32_as_fe(extended_val));

                let v = val.as_i64_from_lower_bytes();
                let (b1, b2, b3, b4, _) = decompose_lower32(v);

                set_col!(X_b1, Elem::from_u32_as_fe(b1.into()));
                set_col!(X_b3, Elem::from_u32_as_fe(b3.into()));
                set_col!(X_b4, Elem::from_u32_as_fe(b4.into()));
                set_col!(Y_7bit, Elem::from_u32_as_fe((b2 & 0x7f).into()));
                set_col!(Y_15bit, Elem::from_u32_as_fe(val.u() & 0x7fff));
                set_col!(
                    wrap_bit,
                    if sign_bit {
                        Elem::Field(F::one())
                    } else {
                        Elem::Field(F::zero())
                    }
                );

                None
            }
            Instruction::to_signed => {
                let read_reg = args[0].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val = self.reg_read(0, read_reg, lid);
                let write_reg = args[1].u();
                let r = val.u() as i32;

                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                self.reg_write(1, write_reg, r.into(), lid);

                set_col!(tmp1_col, val);
                set_col!(tmp3_col, Elem::from_i32_as_fe(r));

                let (b1, b2, b3, b4, _sign) = decompose_lower32(val.u().into());
                set_col!(X_b1, Elem::from_u32_as_fe(b1.into()));
                set_col!(X_b2, Elem::from_u32_as_fe(b2.into()));
                set_col!(X_b3, Elem::from_u32_as_fe(b3.into()));
                set_col!(
                    wrap_bit,
                    if b4 & 0x80 != 0 {
                        Elem::Field(F::one())
                    } else {
                        Elem::Field(F::zero())
                    }
                );

                set_col!(Y_7bit, Elem::from_u32_as_fe(b4 as u32 & 0x7f));

                None
            }
            Instruction::fail => {
                // TODO: handle it better
                panic!("reached a fail instruction")
            }
            Instruction::divremu => {
                let read_reg1 = args[0].u();
                let read_reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let val2 = self.reg_read(1, read_reg2, lid);
                let write_reg1 = args[2].u();
                let write_reg2 = args[3].u();

                let y = val1.u();
                let x = val2.u();
                let div;
                let rem;
                if x != 0 {
                    div = y / x;
                    rem = y % x;
                } else {
                    div = 0xffffffff;
                    rem = y;
                }

                let lid = self.instr_link_id(instr, MachineInstance::regs, 2);
                self.reg_write(2, write_reg1, div.into(), lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 3);
                self.reg_write(3, write_reg2, rem.into(), lid);

                let tmp3_val = Elem::from_u32_as_fe(div);
                set_col!(tmp1_col, val1);
                set_col!(tmp2_col, val2);
                set_col!(tmp3_col, tmp3_val);
                set_col!(tmp4_col, Elem::from_u32_as_fe(rem));
                set_col!(XX, val2);
                set_col!(XXIsZero, Elem::from_bool_as_fe(val2.is_zero()));
                if !val2.is_zero() {
                    set_col!(XX_inv, Elem::Field(F::one() / val2.into_fe()));
                }

                let v = tmp3_val.as_i64_from_lower_bytes();
                let (b1, b2, b3, b4, _sign) = decompose_lower32(v);
                set_col!(X_b1, Elem::from_u32_as_fe(b1.into()));
                set_col!(X_b2, Elem::from_u32_as_fe(b2.into()));
                set_col!(X_b3, Elem::from_u32_as_fe(b3.into()));
                set_col!(X_b4, Elem::from_u32_as_fe(b4.into()));

                let (rem_b1, rem_b2, rem_b3, rem_b4, _sign) = decompose_lower32(rem.into());
                set_col!(REM_b1, Elem::from_u32_as_fe(rem_b1.into()));
                set_col!(REM_b2, Elem::from_u32_as_fe(rem_b2.into()));
                set_col!(REM_b3, Elem::from_u32_as_fe(rem_b3.into()));
                set_col!(REM_b4, Elem::from_u32_as_fe(rem_b4.into()));

                if x > 0 {
                    let diff = x - rem - 1;
                    let (b5, b6, b7, b8, _sign) = decompose_lower32(diff.into());
                    set_col!(Y_b5, Elem::from_u32_as_fe(b5.into()));
                    set_col!(Y_b6, Elem::from_u32_as_fe(b6.into()));
                    set_col!(Y_b7, Elem::from_u32_as_fe(b7.into()));
                    set_col!(Y_b8, Elem::from_u32_as_fe(b8.into()));
                }

                None
            }
            Instruction::mul => {
                let read_reg1 = args[0].u();
                let read_reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let val2 = self.reg_read(1, read_reg2, lid);
                let write_reg1 = args[2].u();
                let write_reg2 = args[3].u();

                let r = val1.u() as u64 * val2.u() as u64;
                let lo = r as u32;
                let hi = (r >> 32) as u32;

                let lid = self.instr_link_id(instr, MachineInstance::regs, 2);
                self.reg_write(2, write_reg1, lo.into(), lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 3);
                self.reg_write(3, write_reg2, hi.into(), lid);

                set_col!(tmp1_col, val1);
                set_col!(tmp2_col, val2);
                set_col!(tmp3_col, Elem::from_u32_as_fe(lo));
                set_col!(tmp4_col, Elem::from_u32_as_fe(hi));

                let lid = self.instr_link_id(instr, MachineInstance::split_gl, 0);
                submachine_op!(split_gl, lid, &[r.into(), lo.into(), hi.into(), 0.into()],);
                None
            }
            Instruction::and | Instruction::or | Instruction::xor => {
                let read_reg1 = args[0].u();
                let read_reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let val2 = self.reg_read(1, read_reg2, lid);
                let offset = args[2].bin();
                let write_reg = args[3].u();
                let val2_offset: Elem<F> = (val2.bin() + offset).into();

                set_col!(tmp1_col, val1);
                set_col!(tmp2_col, val2);

                let (r, op_id) = match instr {
                    Instruction::and => (val1.u() & val2_offset.u(), 0),
                    Instruction::or => (val1.u() | val2_offset.u(), 1),
                    Instruction::xor => (val1.u() ^ val2_offset.u(), 2),
                    _ => unreachable!(),
                };

                let lid = self.instr_link_id(instr, MachineInstance::binary, 0);
                submachine_op!(
                    binary,
                    lid,
                    &[
                        op_id.into(),
                        val1.into_fe(),
                        val2_offset.into_fe(),
                        r.into()
                    ],
                );

                let lid = self.instr_link_id(instr, MachineInstance::regs, 2);
                self.reg_write(3, write_reg, r.into(), lid);

                set_col!(tmp3_col, Elem::from_u32_as_fe(r));

                None
            }
            Instruction::shl | Instruction::shr => {
                let read_reg1 = args[0].u();
                let read_reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let val2 = self.reg_read(1, read_reg2, lid);
                let offset = args[2].bin();
                let write_reg = args[3].u();
                let val2_offset: Elem<F> = (val2.bin() + offset).into();

                let (r, op_id) = match instr {
                    Instruction::shl => (val1.u() << val2_offset.u(), 0),
                    Instruction::shr => (val1.u() >> val2_offset.u(), 1),
                    _ => unreachable!(),
                };

                let lid = self.instr_link_id(instr, MachineInstance::shift, 0);
                submachine_op!(
                    shift,
                    lid,
                    &[
                        op_id.into(),
                        val1.into_fe(),
                        val2_offset.into_fe(),
                        r.into()
                    ],
                );

                let lid = self.instr_link_id(instr, MachineInstance::regs, 2);
                self.reg_write(3, write_reg, r.into(), lid);

                set_col!(tmp1_col, val1);
                set_col!(tmp2_col, val2);
                set_col!(tmp3_col, Elem::from_u32_as_fe(r));

                None
            }
            Instruction::invert_gl => {
                let low_addr = args[0].u();
                let high_addr = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let low = self.reg_read(0, low_addr, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let high = self.reg_read(1, high_addr, lid);
                let inv = F::one() / F::from((high.u() as u64) << 32 | low.u() as u64);
                let inv_u64 = inv.to_integer().try_into_u64().unwrap();
                let (low_inv, high_inv) = (inv_u64 as u32, (inv_u64 >> 32) as u32);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 2);
                self.reg_write(2, low_addr, low_inv.into(), lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 3);
                self.reg_write(3, high_addr, high_inv.into(), lid);

                set_col!(tmp1_col, low);
                set_col!(tmp2_col, high);
                set_col!(tmp3_col, Elem::from_u32_as_fe(low_inv));
                set_col!(tmp4_col, Elem::from_u32_as_fe(high_inv));
                set_col!(XX_inv, Elem::Field(inv));

                let lid = self.instr_link_id(instr, MachineInstance::split_gl, 0);
                submachine_op!(
                    split_gl,
                    lid,
                    &[inv, low_inv.into(), high_inv.into(), 0.into()],
                );
                None
            }
            Instruction::split_gl => {
                let read_reg = args[0].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let val1 = self.reg_read(0, read_reg, lid);
                let write_reg1 = args[1].u();
                let write_reg2 = args[2].u();

                let value_fe = val1.into_fe();
                // This instruction is only for Goldilocks, so the value must
                // fit into a u64.
                let value = value_fe.to_integer().try_into_u64().unwrap();
                let lo = (value & 0xffffffff) as u32;
                let hi = (value >> 32) as u32;

                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                self.reg_write(2, write_reg1, lo.into(), lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 2);
                self.reg_write(3, write_reg2, hi.into(), lid);

                set_col!(tmp1_col, val1);
                set_col!(tmp3_col, Elem::from_u32_as_fe(lo));
                set_col!(tmp4_col, Elem::from_u32_as_fe(hi));

                let lid = self.instr_link_id(instr, MachineInstance::split_gl, 0);
                submachine_op!(
                    split_gl,
                    lid,
                    &[value.into(), lo.into(), hi.into(), 0.into()],
                );
                None
            }
            Instruction::poseidon_gl => {
                let reg1 = args[0].u();
                let reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let input_ptr = self.reg_read(0, reg1, lid);
                assert!(is_multiple_of_4(input_ptr.u()));
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let output_ptr = self.reg_read(1, reg2, lid);
                assert!(is_multiple_of_4(output_ptr.u()));

                set_col!(tmp1_col, input_ptr);
                set_col!(tmp2_col, output_ptr);
                set_col!(tmp3_col, (input_ptr.u() >> 2).into());
                set_col!(tmp4_col, (output_ptr.u() >> 2).into());

                let (b1, b2, b3, b4, _sign) = decompose_lower32(input_ptr.u() as i64 >> 2);
                set_col!(X_b1, Elem::from_u32_as_fe(b1.into()));
                set_col!(X_b2, Elem::from_u32_as_fe(b2.into()));
                set_col!(X_b3, Elem::from_u32_as_fe(b3.into()));
                set_col!(X_b4, Elem::from_u32_as_fe(b4.into()));

                let (b5, b6, b7, b8, _sign) = decompose_lower32(output_ptr.u() as i64 >> 2);
                set_col!(Y_b5, Elem::from_u32_as_fe(b5.into()));
                set_col!(Y_b6, Elem::from_u32_as_fe(b6.into()));
                set_col!(Y_b7, Elem::from_u32_as_fe(b7.into()));
                set_col!(Y_b8, Elem::from_u32_as_fe(b8.into()));

                let inputs = (0..12)
                    .map(|i| {
                        // memory reads from the poseidon machine
                        let lid = self.link_id("main_poseidon_gl", "main_memory", 0);
                        let lo = self.proc.get_mem(input_ptr.u() + 8 * i, self.step, lid);
                        let lid = self.link_id("main_poseidon_gl", "main_memory", 1);
                        let hi = self.proc.get_mem(input_ptr.u() + 8 * i + 4, self.step, lid);
                        F::from(((hi as u64) << 32) | lo as u64)
                    })
                    .collect::<Vec<_>>();

                let outputs = poseidon_gl::poseidon_gl(&inputs);
                outputs.iter().enumerate().rev().for_each(|(i, v)| {
                    // the .rev() is not necessary, but makes the split_gl
                    // operations in the same "order" as automatic witgen
                    let val = v.to_integer().try_into_u64().unwrap();
                    let hi = (val >> 32) as u32;
                    let lo = (val & 0xffffffff) as u32;
                    // memory writes from the poseidon machine
                    let lid = self.link_id("main_poseidon_gl", "main_memory", 2);
                    self.proc
                        .set_mem(output_ptr.u() + 8 * i as u32, lo, self.step + 1, lid);
                    let lid = self.link_id("main_poseidon_gl", "main_memory", 3);
                    self.proc
                        .set_mem(output_ptr.u() + 8 * i as u32 + 4, hi, self.step + 1, lid);
                    let lid = self.link_id("main_poseidon_gl", "main_split_gl", 0);
                    submachine_op!(split_gl, lid, &[*v, lo.into(), hi.into(), 0.into()],);
                });

                let lid = self.instr_link_id(instr, MachineInstance::poseidon_gl, 0);
                submachine_op!(
                    poseidon_gl,
                    lid,
                    &[
                        input_ptr.into_fe(),
                        output_ptr.into_fe(),
                        self.step.into(),
                        0.into()
                    ],
                    inputs[0],
                    inputs[1],
                    inputs[2],
                    inputs[3],
                    inputs[4],
                    inputs[5],
                    inputs[6],
                    inputs[7],
                    inputs[8],
                    inputs[9],
                    inputs[10],
                    inputs[11],
                    outputs[0],
                    outputs[1],
                    outputs[2],
                    outputs[3]
                );
                None
            }
            Instruction::poseidon2_gl => {
                let input_ptr = self.proc.get_reg_mem(args[0].u()).u();
                assert!(is_multiple_of_4(input_ptr));

                let inputs: [u64; 8] = (0..16)
                    .map(|i| self.proc.get_mem(input_ptr + i * 4, 0, 0))
                    .chunks(2)
                    .into_iter()
                    .map(|mut chunk| {
                        let low = chunk.next().unwrap() as u64;
                        let high = chunk.next().unwrap() as u64;
                        (high << 32) | low
                    })
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                let result = poseidon2_gl::poseidon2_gl(&inputs)
                    .into_iter()
                    .flat_map(|v| vec![(v & 0xffffffff) as u32, (v >> 32) as u32]);

                let output_ptr = self.proc.get_reg_mem(args[1].u()).u();
                assert!(is_multiple_of_4(output_ptr));
                result.enumerate().for_each(|(i, v)| {
                    self.proc.set_mem(output_ptr + i as u32 * 4, v, 0, 0);
                });

                None
            }
            Instruction::affine_256 => {
                // a * b + c = d
                let input_ptr_a = self.proc.get_reg_mem(args[0].u()).u();
                assert!(is_multiple_of_4(input_ptr_a));
                let input_ptr_b = self.proc.get_reg_mem(args[1].u()).u();
                assert!(is_multiple_of_4(input_ptr_b));
                let input_ptr_c = self.proc.get_reg_mem(args[2].u()).u();
                assert!(is_multiple_of_4(input_ptr_c));
                let output_ptr_d = self.proc.get_reg_mem(args[3].u()).u();
                assert!(is_multiple_of_4(output_ptr_d));

                let a = (0..8)
                    .map(|i| F::from(self.proc.get_mem(input_ptr_a + i * 4, 0, 0)))
                    .collect::<Vec<_>>();
                let b = (0..8)
                    .map(|i| F::from(self.proc.get_mem(input_ptr_b + i * 4, 0, 0)))
                    .collect::<Vec<_>>();
                let c = (0..8)
                    .map(|i| F::from(self.proc.get_mem(input_ptr_c + i * 4, 0, 0)))
                    .collect::<Vec<_>>();
                let result = arith::affine_256(&a, &b, &c);

                result.0.iter().enumerate().for_each(|(i, &v)| {
                    self.proc.set_mem(
                        output_ptr_d + i as u32 * 4,
                        v.to_integer().try_into_u32().unwrap(),
                        1,
                        1,
                    );
                });
                result.1.iter().enumerate().for_each(|(i, &v)| {
                    self.proc.set_mem(
                        output_ptr_d + (result.0.len() as u32 * 4) + (i as u32 * 4),
                        v.to_integer().try_into_u32().unwrap(),
                        1,
                        1,
                    );
                });

                // TODO: main_arith event
                None
            }
            Instruction::mod_256 => {
                // a mod b = c
                let input_ptr_a = self.proc.get_reg_mem(args[0].u()).u();
                assert!(is_multiple_of_4(input_ptr_a));
                let input_ptr_b = self.proc.get_reg_mem(args[1].u()).u();
                assert!(is_multiple_of_4(input_ptr_b));
                let output_ptr_c = self.proc.get_reg_mem(args[2].u()).u();
                assert!(is_multiple_of_4(output_ptr_c));

                let ah = (0..8)
                    .map(|i| F::from(self.proc.get_mem(input_ptr_a + i * 4, 0, 0)))
                    .collect::<Vec<_>>();
                let al = (8..16)
                    .map(|i| F::from(self.proc.get_mem(input_ptr_a + i * 4, 0, 0)))
                    .collect::<Vec<_>>();
                let b = (0..8)
                    .map(|i| F::from(self.proc.get_mem(input_ptr_b + i * 4, 0, 0)))
                    .collect::<Vec<_>>();
                let result = arith::mod_256(&ah, &al, &b);

                result.iter().enumerate().for_each(|(i, &v)| {
                    self.proc.set_mem(
                        output_ptr_c + i as u32 * 4,
                        v.to_integer().try_into_u32().unwrap(),
                        1,
                        1,
                    );
                });

                // TODO: main_arith event
                None
            }
            Instruction::ec_add => {
                // a + b = c
                let input_ptr_a = self.proc.get_reg_mem(args[0].u()).u();
                assert!(is_multiple_of_4(input_ptr_a));
                let input_ptr_b = self.proc.get_reg_mem(args[1].u()).u();
                assert!(is_multiple_of_4(input_ptr_b));
                let output_ptr_c = self.proc.get_reg_mem(args[2].u()).u();
                assert!(is_multiple_of_4(output_ptr_c));

                let ax = (0..8)
                    .map(|i| F::from(self.proc.get_mem(input_ptr_a + i * 4, 0, 0)))
                    .collect::<Vec<_>>();
                let ay = (8..16)
                    .map(|i| F::from(self.proc.get_mem(input_ptr_a + i * 4, 0, 0)))
                    .collect::<Vec<_>>();
                let bx = (0..8)
                    .map(|i| F::from(self.proc.get_mem(input_ptr_b + i * 4, 0, 0)))
                    .collect::<Vec<_>>();
                let by = (8..16)
                    .map(|i| F::from(self.proc.get_mem(input_ptr_b + i * 4, 0, 0)))
                    .collect::<Vec<_>>();

                let result = arith::ec_add(&ax, &ay, &bx, &by);
                result.0.iter().enumerate().for_each(|(i, &v)| {
                    self.proc.set_mem(
                        output_ptr_c + i as u32 * 4,
                        v.to_integer().try_into_u32().unwrap(),
                        1,
                        1,
                    );
                });
                result.1.iter().enumerate().for_each(|(i, &v)| {
                    self.proc.set_mem(
                        output_ptr_c + (result.0.len() as u32 * 4) + (i as u32 * 4),
                        v.to_integer().try_into_u32().unwrap(),
                        1,
                        1,
                    );
                });

                // TODO: main_arith event
                None
            }
            Instruction::ec_double => {
                // a * 2 = b
                let input_ptr_a = self.proc.get_reg_mem(args[0].u()).u();
                assert!(is_multiple_of_4(input_ptr_a));
                let output_ptr_b = self.proc.get_reg_mem(args[1].u()).u();
                assert!(is_multiple_of_4(output_ptr_b));

                let ax = (0..8)
                    .map(|i| F::from(self.proc.get_mem(input_ptr_a + i * 4, 0, 0)))
                    .collect::<Vec<_>>();
                let ay = (8..16)
                    .map(|i| F::from(self.proc.get_mem(input_ptr_a + i * 4, 0, 0)))
                    .collect::<Vec<_>>();

                let result = arith::ec_double(&ax, &ay);
                result.0.iter().enumerate().for_each(|(i, &v)| {
                    self.proc.set_mem(
                        output_ptr_b + i as u32 * 4,
                        v.to_integer().try_into_u32().unwrap(),
                        1,
                        1,
                    );
                });
                result.1.iter().enumerate().for_each(|(i, &v)| {
                    self.proc.set_mem(
                        output_ptr_b + (result.0.len() as u32 * 4) + (i as u32 * 4),
                        v.to_integer().try_into_u32().unwrap(),
                        1,
                        1,
                    );
                });

                // TODO: main_arith event
                None
            }
            Instruction::commit_public => {
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let idx = self.reg_read(0, args[0].u(), lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let limb = self.reg_read(0, args[1].u(), lid);
                set_col!(tmp1_col, idx);
                set_col!(tmp2_col, limb);
                log::debug!("Committing public: idx={idx}, limb={limb}");
                let lid = self.instr_link_id(instr, MachineInstance::publics, 0);
                submachine_op!(
                    publics,
                    lid,
                    &[idx.into_fe(), limb.into_fe(), 0.into(), 0.into()],
                );
                None
            }
            Instruction::keccakf => {
                let reg1 = args[0].u();
                let reg2 = args[1].u();
                let lid = self.instr_link_id(instr, MachineInstance::regs, 0);
                let input_ptr = self.reg_read(0, reg1, lid);
                let lid = self.instr_link_id(instr, MachineInstance::regs, 1);
                let output_ptr = self.reg_read(1, reg2, lid);

                set_col!(tmp1_col, input_ptr);
                set_col!(tmp2_col, output_ptr);

                let mut state = [0u64; 25];

                for (i, state_i) in state.iter_mut().enumerate() {
                    let hi = self
                        .proc
                        .get_mem(input_ptr.u() + 8 * i as u32 + 4, self.step, lid);
                    let lo = self
                        .proc
                        .get_mem(input_ptr.u() + 8 * i as u32, self.step, lid);
                    *state_i = ((hi as u64) << 32) | lo as u64;
                }

                keccakf(&mut state);

                for (i, val) in state.iter().enumerate() {
                    let lo = *val as u32;
                    let hi = (val >> 32) as u32;

                    self.proc
                        .set_mem(output_ptr.u() + i as u32 * 8, lo, self.step + 1, lid);
                    self.proc
                        .set_mem(output_ptr.u() + i as u32 * 8 + 4, hi, self.step + 1, lid);
                }

                //let lid = self.instr_link_id(instr, "main_keccakf", 0);
                //submachine_op!(keccakf, lid, &[input_ptr.into_fe(), output_ptr.into_fe()],);
                //main_op!(keccakf32_memory);
                None
            }
            Instruction::Count => unreachable!(),
        };

        r
    }

    fn eval_expression(&mut self, expression: &Expression) -> Option<Elem<F>> {
        match expression {
            Expression::Reference(_, r) => {
                // an identifier looks like this:
                let name = r.try_to_identifier().unwrap();

                // labels share the identifier space with registers:
                // try one, then the other
                let val = self
                    .label_map
                    .get(name.as_str())
                    .cloned()
                    .unwrap_or_else(|| self.proc.get_reg(name.as_str()));
                Some(val)
            }
            Expression::PublicReference(_, _) => todo!(),
            Expression::Number(_, Number { value: n, .. }) => {
                let unsigned: u32 = n
                    .try_into()
                    .unwrap_or_else(|_| panic!("Value does not fit in 32 bits."));

                Some(unsigned.into())
            }
            Expression::String(_, _) => todo!(),
            Expression::Tuple(_, _) => todo!(),
            Expression::LambdaExpression(_, _) => todo!(),
            Expression::ArrayLiteral(_, _) => todo!(),
            Expression::BinaryOperation(
                _,
                BinaryOperation {
                    left: l,
                    op,
                    right: r,
                },
            ) => {
                let l = &self.eval_expression(l).unwrap();
                let r = &self.eval_expression(r).unwrap();

                let result = match (l, r) {
                    (Elem::Binary(l), Elem::Binary(r)) => match op {
                        powdr_ast::parsed::BinaryOperator::Add => Elem::Binary(l + r),
                        powdr_ast::parsed::BinaryOperator::Sub => Elem::Binary(l - r),
                        powdr_ast::parsed::BinaryOperator::Mul => match l.checked_mul(*r) {
                            // Multiplication is a special case as the input for
                            // poseidon_gl requires field multiplication. So,
                            // if native multiplication overflows, we use field
                            // multiplication.
                            //
                            // TODO: support types in the zkVM specification, so
                            // that we don't have to guess which kind of
                            // arithmetic we have to use.
                            Some(v) => Elem::Binary(v),
                            None => {
                                let l = F::from(*l);
                                let r = F::from(*r);
                                Elem::Field(l * r)
                            }
                        },
                        powdr_ast::parsed::BinaryOperator::Div => Elem::Binary(l / r),
                        powdr_ast::parsed::BinaryOperator::Mod => Elem::Binary(l % r),
                        powdr_ast::parsed::BinaryOperator::Pow => {
                            Elem::Binary(l.pow(u32::try_from(*r).unwrap()))
                        }
                        _ => todo!(),
                    },
                    (Elem::Field(l), Elem::Field(r)) => {
                        let result = match op {
                            // We need to subtract field elements in the bootloader:
                            powdr_ast::parsed::BinaryOperator::Sub => *l - *r,
                            _ => todo!(),
                        };
                        Elem::Field(result)
                    }
                    (Elem::Binary(l), Elem::Field(r)) => {
                        // We need to add a field element to a binary when calling poseidon_gl:
                        let result = match op {
                            powdr_ast::parsed::BinaryOperator::Add => F::from(*l) + *r,
                            _ => todo!(),
                        };
                        Elem::Field(result)
                    }
                    _ => panic!("tried to operate a binary value with a field value"),
                };

                Some(result)
            }
            Expression::UnaryOperation(_, UnaryOperation { op, expr: arg }) => {
                let arg = self.eval_expression(arg).unwrap().bin();
                let result = match op {
                    powdr_ast::parsed::UnaryOperator::Minus => -arg,
                    powdr_ast::parsed::UnaryOperator::LogicalNot => todo!(),
                    powdr_ast::parsed::UnaryOperator::Next => unreachable!(),
                };

                Some(Elem::Binary(result))
            }
            Expression::FunctionCall(
                _,
                FunctionCall {
                    function,
                    arguments,
                },
            ) => match function.as_ref() {
                Expression::Reference(_, f) if f.to_string() == "std::prover::eval" => {
                    self.eval_expression(&arguments[0])
                }
                Expression::Reference(_, f) if f.to_string() == "std::convert::int" => {
                    // whatever. we don't need to convert anything
                    self.eval_expression(&arguments[0])
                }
                Expression::Reference(_, f) => {
                    self.exec_instruction(f.try_to_identifier().unwrap(), arguments)
                }
                _ => {
                    unimplemented!(
                        "Function call not implemented: {function}{}",
                        arguments.iter().format(", ")
                    )
                }
            },
            Expression::FreeInput(_, expr) => {
                let Expression::FunctionCall(
                    _,
                    FunctionCall {
                        function,
                        arguments,
                    },
                ) = expr.as_ref()
                else {
                    panic!("Free input does not match pattern: {expr}");
                };
                let Expression::Reference(_, f) = function.as_ref() else {
                    panic!("Free input does not match pattern: {expr}");
                };
                let variant = f
                    .to_string()
                    .strip_prefix("std::prelude::Query::")
                    .unwrap_or_else(|| panic!("Free input does not match pattern: {expr}"))
                    .to_string();
                let values = arguments
                    .iter()
                    .map(|arg| self.eval_expression(arg).unwrap().to_string())
                    .collect::<Vec<_>>();
                let query = format!("{variant}({})", values.join(","));
                match (self.inputs)(&query).unwrap() {
                    Some(val) => {
                        let e = Elem::try_from_fe_as_bin(&val)
                            .expect("field value does not fit into u32 or i32");
                        Some(e)
                    }
                    None => {
                        panic!("unknown query command: {query}");
                    }
                }
            }
            Expression::MatchExpression(_, _) => todo!(),
            Expression::IfExpression(_, _) => panic!(),
            Expression::BlockExpression(_, _) => panic!(),
            Expression::IndexAccess(_, _) => todo!(),
            Expression::StructExpression(_, _) => todo!(),
        }
    }

    /// generate witness program columns from the pc values of the execution
    fn generate_program_columns(&mut self) -> Vec<(String, Vec<F>)> {
        let mut cols = vec![];
        for (fcol, pcol) in &self.program_cols {
            let mut values: Vec<F> = Vec::with_capacity(self.proc.pc_trace().len());
            let fixed_values = self.get_fixed(fcol).unwrap();
            for pc in self.proc.pc_trace() {
                values.push(fixed_values[*pc as usize])
            }
            cols.push((pcol.to_string(), values))
        }
        cols
    }
}

pub type FixedColumns<F> = Arc<Vec<(String, VariablySizedColumn<F>)>>;

/// Result of the execution.
/// If executing in ExecMode::Fast, trace and memory fields will be empty.
pub struct Execution<F: FieldElement> {
    /// number of rows used by the execution (not of the full main columns, which are extended to a power-of-two)
    pub trace_len: usize,
    /// witness columns
    pub trace: HashMap<String, Vec<F>>,
    /// final memory state
    pub memory: MemoryState,
    /// sequence of memory accesses
    pub memory_accesses: Vec<MemOperation>,
    /// final register memory state
    pub register_memory: RegisterMemoryState<F>,
}

#[derive(Clone, Copy)]
enum ExecMode {
    /// Doesn't generate any execution information besides the length of the trace
    Fast,
    /// Generate traces for memory and powdr asm registers
    Trace,
    /// Generate the full witness
    Witness,
}

/// Execute a Powdr/RISCV assembly program, without generating a witness.
/// Returns the execution trace length.
pub fn execute<F: FieldElement>(
    asm: &AnalysisASMFile,
    initial_memory: MemoryState,
    prover_ctx: &Callback<F>,
    bootloader_inputs: &[F],
    profiling: Option<ProfilerOptions>,
    precompile_blocks: HashMap<String, Vec<FunctionStatement>>,
) -> (usize, HashMap<String, u64>) {
    log::info!("Executing...");
    let res = execute_inner(
        asm,
        None,
        None,
        initial_memory,
        prover_ctx,
        bootloader_inputs,
        usize::MAX,
        ExecMode::Fast,
        profiling,
        precompile_blocks,
    );
    (res.0.trace_len, res.1)
}

/// Execute generating a witness for the PC and powdr asm registers.
#[allow(clippy::too_many_arguments)]
pub fn execute_with_trace<F: FieldElement>(
    asm: &AnalysisASMFile,
    opt_pil: &Analyzed<F>,
    fixed: FixedColumns<F>,
    initial_memory: MemoryState,
    prover_ctx: &Callback<F>,
    bootloader_inputs: &[F],
    max_steps_to_execute: Option<usize>,
    profiling: Option<ProfilerOptions>,
) -> (Execution<F>, HashMap<String, u64>) {
    log::info!("Executing (trace generation)...");

    execute_inner(
        asm,
        Some(opt_pil),
        Some(fixed),
        initial_memory,
        prover_ctx,
        bootloader_inputs,
        max_steps_to_execute.unwrap_or(usize::MAX),
        ExecMode::Trace,
        profiling,
        Default::default(),
    )
}

/// Execute generating a full witness for the program
#[allow(clippy::too_many_arguments)]
pub fn execute_with_witness<F: FieldElement>(
    asm: &AnalysisASMFile,
    opt_pil: &Analyzed<F>,
    fixed: FixedColumns<F>,
    initial_memory: MemoryState,
    prover_ctx: &Callback<F>,
    bootloader_inputs: &[F],
    max_steps_to_execute: Option<usize>,
    profiling: Option<ProfilerOptions>,
) -> (Execution<F>, HashMap<String, u64>) {
    log::info!("Executing (trace generation)...");

    execute_inner(
        asm,
        Some(opt_pil),
        Some(fixed),
        initial_memory,
        prover_ctx,
        bootloader_inputs,
        max_steps_to_execute.unwrap_or(usize::MAX),
        ExecMode::Witness,
        profiling,
        Default::default(),
    )
}

#[allow(clippy::too_many_arguments)]
fn execute_inner<F: FieldElement>(
    asm: &AnalysisASMFile,
    opt_pil: Option<&Analyzed<F>>,
    fixed: Option<FixedColumns<F>>,
    initial_memory: MemoryState,
    prover_ctx: &Callback<F>,
    bootloader_inputs: &[F],
    max_steps_to_execute: usize,
    mode: ExecMode,
    profiling: Option<ProfilerOptions>,
    precompile_blocks: HashMap<String, Vec<FunctionStatement>>,
) -> (Execution<F>, HashMap<String, u64>) {
    let start = Instant::now();
    let main_machine = get_main_machine(asm);

    let mut label_freq: HashMap<String, u64> = Default::default();

    let PreprocessedMain {
        statements,
        label_map,
        batch_to_line_map,
        debug_files,
        function_starts,
        location_starts,
    } = preprocess_main_function(main_machine);

    let witness_cols: Vec<String> = opt_pil
        .map(|pil| {
            pil.committed_polys_in_source_order()
                .flat_map(|(s, _)| s.array_elements().map(|(name, _)| name))
                .collect()
        })
        .unwrap_or_default();

    // program columns to witness columns
    let program_cols: HashMap<_, _> = opt_pil
        .map(|pil| {
            pil.identities
                .iter()
                .flat_map(|id| match id {
                    Identity::Lookup(LookupIdentity { left, right, .. }) => left
                        .expressions
                        .iter()
                        .zip(right.expressions.iter())
                        .filter_map(|(l, r)| match (l, r) {
                            (
                                AlgebraicExpression::Reference(l),
                                AlgebraicExpression::Reference(r),
                            ) => {
                                if r.name.starts_with("main__rom::p_")
                                    && witness_cols.contains(&l.name)
                                {
                                    Some((r.name.clone(), l.name.clone()))
                                } else {
                                    None
                                }
                            }
                            _ => None,
                        })
                        .collect::<Vec<_>>(),
                    _ => vec![],
                })
                .collect()
        })
        .unwrap_or_default();

    let proc = match TraceBuilder::<'_, F>::new(
        main_machine,
        opt_pil,
        witness_cols,
        initial_memory,
        &batch_to_line_map,
        max_steps_to_execute,
        mode,
    ) {
        Ok(proc) => proc,
        Err(ret) => return (*ret, Default::default()),
    };

    let bootloader_inputs = bootloader_inputs
        .iter()
        .map(|v| Elem::try_from_fe_as_bin(v).unwrap_or(Elem::Field(*v)))
        .collect();

    let pil_links = opt_pil.map(pil::links_from_pil).unwrap_or_default();

    // We clear the QueryCallback's virtual FS before the execution.
    (prover_ctx)("Clear").unwrap();
    let mut e = Executor {
        proc,
        label_map,
        inputs: prover_ctx,
        bootloader_inputs,
        fixed: fixed.unwrap_or_default(),
        program_cols,
        step: 0,
        mode,
        pil_links,
        pil_instruction_links: vec![None; Instruction::count() * MachineInstance::count()],
        pil_other_links: Default::default(),
        cached_fixed_cols: Default::default(),
    };

    e.init();

    let mut profiler =
        profiling.map(|opt| Profiler::new(opt, &debug_files[..], function_starts, location_starts));

    let mut curr_pc = 0u32;
    e.proc.push_row(PC_INITIAL_VAL as u32);
    let mut last = Instant::now();
    let mut count = 0;
    loop {
        let stm = statements[curr_pc as usize];

        log::trace!("l {curr_pc}: {stm}",);

        e.step += 4;

        count += 1;
        if count % 10000 == 0 {
            let now = Instant::now();
            let elapsed = now - last;
            if elapsed.as_secs_f64() > 1.0 {
                last = now;
                log::debug!("instructions/s: {}", count as f64 / elapsed.as_secs_f64(),);
                count = 0;
            }
        }

        match stm {
            FunctionStatement::Assignment(a) => {
                let pc = e.proc.get_pc().u();
                e.proc.set_col(KnownWitnessCol::_operation_id, 2.into());
                if let Some(p) = &mut profiler {
                    p.add_instruction_cost(pc as usize);
                }

                let results = e.eval_expression(a.rhs.as_ref());
                assert_eq!(a.lhs_with_reg.len(), 1);

                let asgn_reg = a.lhs_with_reg[0].1.clone();
                if let AssignmentRegister::Register(x) = asgn_reg {
                    assert_eq!(x, "X"); // we currently only assign through X
                    let x_const =
                        Elem::Field(e.get_known_fixed(KnownFixedCol::X_const, pc as usize));

                    match a.rhs.as_ref() {
                        Expression::FreeInput(_, _expr) => {
                            // we currently only use X for free inputs
                            assert!(x_const.is_zero());
                            e.proc.set_col(KnownWitnessCol::X, results.unwrap());
                            e.proc
                                .set_col(KnownWitnessCol::X_free_value, results.unwrap());
                        }
                        _ => {
                            // We're assinging a value or the result of an instruction.
                            // Currently, only X used as the assignment register in this case.
                            let x = results.unwrap();
                            e.proc.set_col(KnownWitnessCol::X, x);

                            let x_read_free = Elem::Field(
                                e.get_known_fixed(KnownFixedCol::X_read_free, pc as usize),
                            );

                            // We need to solve for X_free_value:
                            // X = X_const + X_read_free * X_free_value
                            // X - X_const = X_read_free * X_free_value
                            // X_free_value = (X - X_const) / X_read_free
                            let x_free_value = if x_read_free.is_zero() {
                                Elem::Field(F::zero())
                            } else {
                                x.sub(&x_const).div(&x_read_free)
                            };
                            e.proc.set_col(KnownWitnessCol::X_free_value, x_free_value);
                        }
                    }
                } else {
                    panic!("should be an assignment register");
                }

                for ((dest, _), val) in a.lhs_with_reg.iter().zip(results) {
                    e.proc.set_reg(dest, val);
                }
            }
            FunctionStatement::Instruction(i)
                if precompile_blocks.contains_key(&i.instruction.to_string()) =>
            {
                let name = i.instruction.to_string();
                let pc = e.proc.get_pc();

                for stmt in precompile_blocks.get(&name).unwrap() {
                    match stmt {
                        FunctionStatement::Instruction(i) => {
                            e.exec_instruction(&i.instruction, &i.inputs);
                        }
                        _ => unreachable!(),
                    }
                }

                e.proc.set_pc((pc.u() + 1).into());
            }
            FunctionStatement::Instruction(i) => {
                e.proc.set_col(KnownWitnessCol::_operation_id, 2.into());

                if let Some(p) = &mut profiler {
                    p.add_instruction_cost(e.proc.get_pc().u() as usize);
                }

                if ["jump", "jump_dyn"].contains(&i.instruction.as_str()) {
                    let pc_before = e.proc.get_pc().u();

                    e.exec_instruction(&i.instruction, &i.inputs);

                    // we can't use `get_pc/get_reg`, as its value is only updated when moving to the next row
                    let pc_after = e.proc.get_next_pc().u();

                    let target_reg = e.eval_expression(&i.inputs[1]).unwrap().u();

                    if let Some(p) = &mut profiler {
                        let pc_return = e.proc.get_reg_mem(target_reg).u();
                        // in the generated powdr asm, not writing to `x1` means the returning pc is ignored
                        if target_reg != 1 {
                            p.jump(pc_after as usize);
                        } else {
                            p.jump_and_link(
                                pc_before as usize,
                                pc_after as usize,
                                pc_return as usize,
                            );
                        }
                    }
                } else {
                    e.exec_instruction(&i.instruction, &i.inputs);
                }
            }
            FunctionStatement::Return(_) => {
                e.proc.set_col(KnownWitnessCol::_operation_id, 2.into());
                break;
            }
            FunctionStatement::DebugDirective(dd) => {
                e.step -= 4;
                match &dd.directive {
                    DebugDirective::Loc(file, line, column) => {
                        let (dir, file) = debug_files[file - 1];
                        log::trace!("Executed {dir}/{file}:{line}:{column}");
                    }
                    DebugDirective::OriginalInstruction(insn) => {
                        log::trace!("  {insn}");
                    }
                    DebugDirective::File(_, _, _) => unreachable!(),
                };
            }
            FunctionStatement::Label(LabelStatement { source: _, name }) => {
                label_freq
                    .entry(name.clone())
                    .and_modify(|e| *e += 1)
                    .or_insert(1);
                //unreachable!()
            }
        };

        curr_pc = match e.proc.advance() {
            Some(pc) => pc,
            None => break,
        };
    }

    if let Some(mut p) = profiler {
        p.finish();
    }

    let mut program_columns = vec![];

    log::debug!("Program execution took {}s", start.elapsed().as_secs_f64());

    if let ExecMode::Trace | ExecMode::Witness = mode {
        let sink_id = e.sink_id();

        // reset
        e.proc.set_col(KnownWitnessCol::pc_update, 0.into());
        e.proc.set_pc(0.into());
        assert!(e.proc.advance().is_none());
        e.proc
            .set_col(KnownWitnessCol::_operation_id, sink_id.into());

        // jump_to_operation
        e.proc.set_col(KnownWitnessCol::pc_update, 1.into());
        e.proc.set_pc(1.into());
        e.proc.set_reg("query_arg_1", 0);
        e.proc.set_reg("query_arg_2", 0);
        assert!(e.proc.advance().is_none());
        e.proc
            .set_col(KnownWitnessCol::_operation_id, sink_id.into());

        // loop
        e.proc.set_col(KnownWitnessCol::pc_update, sink_id.into());
        e.proc.set_pc(sink_id.into());
        assert!(e.proc.advance().is_none());
        e.proc.set_col(KnownWitnessCol::pc_update, sink_id.into());
        e.proc
            .set_col(KnownWitnessCol::_operation_id, sink_id.into());

        if let ExecMode::Witness = mode {
            let start = Instant::now();
            program_columns = e.generate_program_columns();
            log::debug!(
                "Generating program columns took {}s",
                start.elapsed().as_secs_f64()
            );
        }
    }

    /*
        let blocks = powdr_analysis::collect_basic_blocks(&asm);
        let blocks = blocks
            .into_iter()
            .map(|(name, b)| {
                let freq = label_freq.get(&name).unwrap_or(&0);
                let l = b.len() as u64;
                (name, b, freq, freq * l)
            })
            .sorted_by_key(|(_, _, _, cost)| std::cmp::Reverse(*cost))
            .collect::<Vec<_>>();
        for (name, block, freq, cost) in &blocks {
            println!(
                "{name}: size = {}, freq = {freq}, cost = {cost}",
                block.len()
            );
        }
    */

    (e.proc.finish(opt_pil, program_columns), label_freq)
}

/// Utility function for writing the executor witness CSV file.
///
/// If `all_witness_cols` is given, all columns there will also be output, but have empty values when not present in the executor witness
/// (this is useful for debugging, for easy comparison with auto witgen export CSV file).
pub fn write_executor_csv<F: FieldElement, P: AsRef<Path>>(
    file_path: P,
    executor_witness: &[(String, Vec<F>)],
    all_witness_cols: Option<&[String]>,
) {
    let columns: Vec<_> = if let Some(witness_cols) = all_witness_cols {
        witness_cols
            .iter()
            .map(|name| {
                if let Some((_, values)) = executor_witness.iter().find(|(n, _)| n == name) {
                    (name, values.as_ref())
                } else {
                    (name, [].as_ref())
                }
            })
            .collect()
    } else {
        executor_witness
            .iter()
            .map(|(name, values)| (name, values.as_ref()))
            .collect()
    };

    write_polys_csv_file(
        std::fs::File::create(file_path.as_ref()).unwrap(),
        powdr_number::CsvRenderMode::Hex,
        &columns[..],
    );
}

fn is_multiple_of_4(n: u32) -> bool {
    n % 4 == 0
}

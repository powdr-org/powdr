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
    io,
};

use builder::TraceBuilder;

use itertools::Itertools;
use powdr_ast::{
    asm_analysis::{AnalysisASMFile, CallableSymbol, FunctionStatement, LabelStatement, Machine},
    parsed::{
        asm::DebugDirective, BinaryOperation, Expression, FunctionCall, Number, UnaryOperation,
    },
};
use powdr_number::{FieldElement, LargeInt};

pub mod arith;
pub mod poseidon_gl;

use crate::{
    get_main_machine,
    profiler::{Profiler, ProfilerOptions},
};
use crate::{
    register_by_idx, Callback, ExecMode, ExecutionTrace, MemoryState, RegisterMemoryState,
    PC_INITIAL_VAL,
};

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
        if let Some(v) = value.to_integer().try_into_u32() {
            Some(Self::Binary(v as i64))
        } else {
            value.try_into_i32().map(|v| Self::Binary(v as i64))
        }
    }

    /// Interprets the value of self as a field element.
    pub fn into_fe(self) -> F {
        match self {
            Self::Field(f) => f,
            Self::Binary(b) => b.into(),
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

#[derive(Default)]
pub struct RegisterMemory<F: FieldElement> {
    last: HashMap<u32, Elem<F>>,
    second_last: HashMap<u32, Elem<F>>,
}

impl<F: FieldElement> RegisterMemory<F> {
    pub fn for_bootloader(&self) -> HashMap<u32, Vec<F>> {
        self.second_last
            .iter()
            .map(|(k, v)| (*k, vec![v.into_fe()]))
            .collect()
    }
}

mod builder {
    use std::{cmp, collections::HashMap};

    use powdr_ast::asm_analysis::{Machine, RegisterTy};
    use powdr_number::FieldElement;

    use super::{Elem, RegisterMemory};

    use crate::{
        ExecMode, ExecutionTrace, MemOperation, MemOperationKind, MemoryState, RegWrite,
        RegisterMemoryState, PC_INITIAL_VAL,
    };

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

    impl<'a, 'b, F: FieldElement> TraceBuilder<'b, F> {
        /// Creates a new builder.
        ///
        /// May fail if max_rows_len is too small or if the main machine is
        /// empty. In this case, the final (empty) execution trace is returned
        /// in Err.
        #[allow(clippy::type_complexity)]
        pub fn new(
            main: &'a Machine,
            mem: MemoryState,
            batch_to_line_map: &'b [u32],
            max_rows_len: usize,
            mode: ExecMode,
        ) -> Result<Self, Box<(ExecutionTrace<F>, MemoryState, RegisterMemoryState<F>)>> {
            let reg_map = register_names(main)
                .into_iter()
                .enumerate()
                .map(|(i, name)| (name.to_string(), i as u16))
                .collect::<HashMap<String, u16>>();

            let reg_len = reg_map.len();

            // To save cache/memory bandwidth, I set the register index to be
            // u16, so panic if it doesn't fit (it obviously will fit for RISC-V).
            <usize as TryInto<u16>>::try_into(reg_len).unwrap();

            // To avoid a special case when replaying the trace, we create a
            // special write operation that sets the PC with 0 in the first row.
            let pc_idx = reg_map["pc"];
            let reg_writes = vec![RegWrite {
                row: 0,
                reg_idx: pc_idx,
                val: 0.into(),
            }];

            let mut regs = vec![0.into(); reg_len];
            regs[pc_idx as usize] = PC_INITIAL_VAL.into();

            let mut ret = Self {
                pc_idx,
                curr_pc: PC_INITIAL_VAL.into(),
                trace: ExecutionTrace {
                    reg_map,
                    reg_writes,
                    mem_ops: Vec::new(),
                    len: PC_INITIAL_VAL + 1,
                },
                next_statement_line: 1,
                batch_to_line_map,
                max_rows: max_rows_len,
                regs,
                mem,
                reg_mem: Default::default(),
                mode,
            };

            if ret.has_enough_rows() || ret.set_next_pc().is_none() {
                Err(Box::new(ret.finish()))
            } else {
                Ok(ret)
            }
        }

        /// get current value of PC
        pub(crate) fn get_pc(&self) -> Elem<F> {
            self.curr_pc
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
            // Record register write in trace.
            if let ExecMode::Trace = self.mode {
                self.trace.reg_writes.push(RegWrite {
                    row: self.trace.len,
                    reg_idx: idx,
                    val: value.into_fe(),
                });
            }

            self.regs[idx as usize] = value;
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
                self.curr_pc = next_pc;
            }

            // advance to the next statement
            let st_line = self.next_statement_line;

            // optimistically advance the internal and register PCs
            self.next_statement_line += 1;
            self.set_next_pc().and(Some(st_line))
        }

        pub(crate) fn set_mem(&mut self, addr: u32, val: u32) {
            if let ExecMode::Trace = self.mode {
                self.trace.mem_ops.push(MemOperation {
                    row: self.trace.len,
                    kind: MemOperationKind::Write,
                    address: addr,
                });
            }

            self.mem.insert(addr, val);
        }

        pub(crate) fn get_mem(&mut self, addr: u32) -> u32 {
            if let ExecMode::Trace = self.mode {
                self.trace.mem_ops.push(MemOperation {
                    row: self.trace.len,
                    kind: MemOperationKind::Read,
                    address: addr,
                });
            }

            *self.mem.get(&addr).unwrap_or(&0)
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

        pub fn finish(self) -> (ExecutionTrace<F>, MemoryState, RegisterMemoryState<F>) {
            (self.trace, self.mem, self.reg_mem.for_bootloader())
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

struct Executor<'a, 'b, F: FieldElement> {
    proc: TraceBuilder<'b, F>,
    label_map: HashMap<&'a str, Elem<F>>,
    inputs: &'b Callback<'b, F>,
    bootloader_inputs: Vec<Elem<F>>,
    _stdout: io::Stdout,
}

impl<'a, 'b, F: FieldElement> Executor<'a, 'b, F> {
    fn exec_instruction(&mut self, name: &str, args: &[Expression]) -> Vec<Elem<F>> {
        let args = args
            .iter()
            .map(|expr| self.eval_expression(expr)[0])
            .collect::<Vec<_>>();

        self.proc.backup_reg_mem();

        match name {
            "set_reg" => {
                let addr = args[0].u();
                self.proc.set_reg_mem(addr, args[1]);

                Vec::new()
            }
            "get_reg" => {
                let addr = args[0].u();
                let val = self.proc.get_reg_mem(addr);

                vec![val]
            }
            "affine" => {
                let val = self.proc.get_reg_mem(args[0].u());
                let write_reg = args[1].u();
                let factor = args[2];
                let offset = args[3];

                let val = val.mul(&factor).add(&offset);

                self.proc.set_reg_mem(write_reg, val);

                Vec::new()
            }

            "mstore" | "mstore_bootloader" => {
                let addr1 = self.proc.get_reg_mem(args[0].u());
                let addr2 = self.proc.get_reg_mem(args[1].u());
                let offset = args[2].bin();
                let value = self.proc.get_reg_mem(args[3].u());

                let addr = addr1.bin() - addr2.bin() + offset;
                let addr = addr as u32;
                assert_eq!(addr % 4, 0);
                self.proc.set_mem(addr, value.u());

                Vec::new()
            }
            "mload" => {
                let addr1 = self.proc.get_reg_mem(args[0].u());
                let offset = args[1].bin();
                let write_addr1 = args[2].u();
                let write_addr2 = args[3].u();

                let addr = addr1.bin() + offset;

                let val = self.proc.get_mem(addr as u32 & 0xfffffffc);
                let rem = addr % 4;

                self.proc.set_reg_mem(write_addr1, val.into());
                self.proc.set_reg_mem(write_addr2, rem.into());

                Vec::new()
            }
            "load_bootloader_input" => {
                let addr = self.proc.get_reg_mem(args[0].u());
                let write_addr = args[1].u();
                let factor = args[2].bin();
                let offset = args[3].bin();

                let addr = addr.bin() * factor + offset;
                let val = self.bootloader_inputs[addr as usize];

                self.proc.set_reg_mem(write_addr, val);

                Vec::new()
            }
            "assert_bootloader_input" => {
                let addr = self.proc.get_reg_mem(args[0].u());
                let val = self.proc.get_reg_mem(args[1].u());
                let factor = args[2].bin();
                let offset = args[3].bin();

                let addr = (addr.bin() * factor + offset) as usize;
                let actual_val = self.bootloader_inputs[addr];

                assert_eq!(val, actual_val);

                Vec::new()
            }
            "load_label" => {
                let write_reg = args[0].u();
                self.proc.set_reg_mem(write_reg, args[1]);

                Vec::new()
            }
            "jump" => {
                let next_pc = self.proc.get_pc().u() + 1;
                let write_reg = args[1].u();

                self.proc.set_reg_mem(write_reg, next_pc.into());

                self.proc.set_pc(args[0]);

                Vec::new()
            }
            "jump_dyn" => {
                let addr = self.proc.get_reg_mem(args[0].u());
                let next_pc = self.proc.get_pc().u() + 1;
                let write_reg = args[1].u();

                self.proc.set_reg_mem(write_reg, next_pc.into());

                self.proc.set_pc(addr);

                Vec::new()
            }
            "jump_to_bootloader_input" => {
                let bootloader_input_idx = args[0].bin() as usize;
                let addr = self.bootloader_inputs[bootloader_input_idx];
                self.proc.set_pc(addr);

                Vec::new()
            }
            "branch_if_diff_nonzero" => {
                let val1 = self.proc.get_reg_mem(args[0].u());
                let val2 = self.proc.get_reg_mem(args[1].u());

                let val: Elem<F> = val1.sub(&val2);
                if !val.is_zero() {
                    self.proc.set_pc(args[2]);
                }

                Vec::new()
            }
            "branch_if_diff_equal" => {
                let val1 = self.proc.get_reg_mem(args[0].u());
                let val2 = self.proc.get_reg_mem(args[1].u());
                let offset = args[2];
                let val: Elem<F> = val1.sub(&val2).sub(&offset);
                if val.is_zero() {
                    self.proc.set_pc(args[3]);
                }

                Vec::new()
            }
            "skip_if_equal" => {
                let val1 = self.proc.get_reg_mem(args[0].u());
                let val2 = self.proc.get_reg_mem(args[1].u());
                let offset = args[2];
                let val: Elem<F> = val1.sub(&val2).add(&offset);

                if val.is_zero() {
                    let pc = self.proc.get_pc().s();
                    self.proc.set_pc((pc + args[3].s() + 1).into());
                }

                Vec::new()
            }
            "branch_if_diff_greater_than" => {
                let val1 = self.proc.get_reg_mem(args[0].u());
                let val2 = self.proc.get_reg_mem(args[1].u());
                let offset = args[2];
                let val: Elem<F> = val1.sub(&val2).sub(&offset);
                if val.bin() > 0 {
                    self.proc.set_pc(args[3]);
                }

                Vec::new()
            }
            "is_diff_greater_than" => {
                let val1 = self.proc.get_reg_mem(args[0].u());
                let val2 = self.proc.get_reg_mem(args[1].u());

                let offset = args[2];
                let write_reg = args[3].u();
                let val = val1.sub(&val2).sub(&offset);

                let r = if val.bin() > 0 { 1 } else { 0 };
                self.proc.set_reg_mem(write_reg, r.into());

                Vec::new()
            }
            "is_equal_zero" => {
                let val = self.proc.get_reg_mem(args[0].u());
                let write_reg = args[1].u();

                let r = if val.is_zero() { 1 } else { 0 };
                self.proc.set_reg_mem(write_reg, r.into());

                Vec::new()
            }
            "is_not_equal" => {
                let val1 = self.proc.get_reg_mem(args[0].u());
                let val2 = self.proc.get_reg_mem(args[1].u());
                let write_reg = args[2].u();
                let val: Elem<F> = (val1.bin() - val2.bin()).into();

                let r = if !val.is_zero() { 1 } else { 0 };
                self.proc.set_reg_mem(write_reg, r.into());

                Vec::new()
            }
            "add_wrap" => {
                let val1 = self.proc.get_reg_mem(args[0].u());
                let val2 = self.proc.get_reg_mem(args[1].u());
                let offset = args[2];
                let write_reg = args[3].u();

                let val = val1.add(&val2).add(&offset);
                // don't use .u() here: we are deliberately discarding the
                // higher bits
                let r = val.bin() as u32;
                self.proc.set_reg_mem(write_reg, r.into());

                Vec::new()
            }
            "wrap16" => {
                let val = self.proc.get_reg_mem(args[0].u());
                let factor = args[1].bin();
                let write_reg = args[2].u();
                let val: Elem<F> = (val.bin() * factor).into();

                // don't use .u() here: we are deliberately discarding the
                // higher bits
                let r = val.bin() as u32;
                self.proc.set_reg_mem(write_reg, r.into());

                Vec::new()
            }
            "sub_wrap_with_offset" => {
                let val1 = self.proc.get_reg_mem(args[0].u());
                let val2 = self.proc.get_reg_mem(args[1].u());
                let offset = args[2];
                let write_reg = args[3].u();
                let val = val1.sub(&val2).add(&offset);

                let r = (val.bin() + 0x100000000) as u32;
                self.proc.set_reg_mem(write_reg, r.into());

                Vec::new()
            }
            "sign_extend_byte" => {
                let val = self.proc.get_reg_mem(args[0].u());
                let write_reg = args[1].u();

                let r = val.u() as i8 as u32;
                self.proc.set_reg_mem(write_reg, r.into());

                Vec::new()
            }
            "sign_extend_16_bits" => {
                let val = self.proc.get_reg_mem(args[0].u());
                let write_reg = args[1].u();

                let r = val.u() as i16 as u32;

                self.proc.set_reg_mem(write_reg, r.into());

                Vec::new()
            }
            "to_signed" => {
                let val = self.proc.get_reg_mem(args[0].u());
                let write_reg = args[1].u();
                let r = val.u() as i32;

                self.proc.set_reg_mem(write_reg, r.into());

                Vec::new()
            }
            "fail" => {
                // TODO: handle it better
                panic!("reached a fail instruction")
            }
            "divremu" => {
                let val1 = self.proc.get_reg_mem(args[0].u());
                let val2 = self.proc.get_reg_mem(args[1].u());
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

                self.proc.set_reg_mem(write_reg1, div.into());
                self.proc.set_reg_mem(write_reg2, rem.into());

                Vec::new()
            }
            "mul" => {
                let val1 = self.proc.get_reg_mem(args[0].u());
                let val2 = self.proc.get_reg_mem(args[1].u());
                let write_reg1 = args[2].u();
                let write_reg2 = args[3].u();

                let r = val1.u() as u64 * val2.u() as u64;
                let lo = r as u32;
                let hi = (r >> 32) as u32;

                self.proc.set_reg_mem(write_reg1, lo.into());
                self.proc.set_reg_mem(write_reg2, hi.into());

                Vec::new()
            }
            "and" | "or" | "xor" => {
                let val1 = self.proc.get_reg_mem(args[0].u());
                let val2 = self.proc.get_reg_mem(args[1].u());
                let offset = args[2].bin();
                let write_reg = args[3].u();
                let val2: Elem<F> = (val2.bin() + offset).into();

                let r = match name {
                    "and" => val1.u() & val2.u(),
                    "or" => val1.u() | val2.u(),
                    "xor" => val1.u() ^ val2.u(),
                    _ => unreachable!(),
                };

                self.proc.set_reg_mem(write_reg, r.into());

                Vec::new()
            }
            "shl" | "shr" => {
                let val1 = self.proc.get_reg_mem(args[0].u());
                let val2 = self.proc.get_reg_mem(args[1].u());
                let offset = args[2].bin();
                let write_reg = args[3].u();
                let val2: Elem<F> = (val2.bin() + offset).into();

                let r = match name {
                    "shl" => val1.u() << val2.u(),
                    "shr" => val1.u() >> val2.u(),
                    _ => unreachable!(),
                };

                self.proc.set_reg_mem(write_reg, r.into());

                Vec::new()
            }
            "split_gl" => {
                let val1 = self.proc.get_reg_mem(args[0].u());
                let write_reg1 = args[1].u();
                let write_reg2 = args[2].u();

                let value = val1.into_fe().to_integer();
                // This instruction is only for Goldilocks, so the value must
                // fit into a u64.
                let value = value.try_into_u64().unwrap();
                let lo = (value & 0xffffffff) as u32;
                let hi = (value >> 32) as u32;

                self.proc.set_reg_mem(write_reg1, lo.into());
                self.proc.set_reg_mem(write_reg2, hi.into());

                Vec::new()
            }
            "poseidon_gl" => {
                let input_ptr = self.proc.get_reg_mem(args[0].u()).u();
                assert_eq!(input_ptr % 4, 0);

                let inputs = (0..24)
                    .map(|i| self.proc.get_mem(input_ptr + i * 4))
                    .chunks(2)
                    .into_iter()
                    .map(|mut chunk| {
                        let low = chunk.next().unwrap() as u64;
                        let high = chunk.next().unwrap() as u64;
                        F::from((high << 32) | low)
                    })
                    .collect::<Vec<_>>();

                let result = poseidon_gl::poseidon_gl(&inputs)
                    .into_iter()
                    .flat_map(|v| {
                        let v = v.to_integer().try_into_u64().unwrap();
                        vec![(v & 0xffffffff) as u32, (v >> 32) as u32]
                    })
                    .collect::<Vec<_>>();

                let output_ptr = self.proc.get_reg_mem(args[1].u()).u();
                assert_eq!(output_ptr % 4, 0);
                result.iter().enumerate().for_each(|(i, &v)| {
                    self.proc.set_mem(output_ptr + i as u32 * 4, v);
                });

                vec![]
            }
            "affine_256" => {
                assert!(args.is_empty());
                // take input from registers
                let x1 = (0..8)
                    .map(|i| self.proc.get_reg(&register_by_idx(i)).into_fe())
                    .collect::<Vec<_>>();
                let y1 = (0..8)
                    .map(|i| self.proc.get_reg(&register_by_idx(i + 8)).into_fe())
                    .collect::<Vec<_>>();
                let x2 = (0..8)
                    .map(|i| self.proc.get_reg(&register_by_idx(i + 16)).into_fe())
                    .collect::<Vec<_>>();
                let result = arith::affine_256(&x1, &y1, &x2);
                // store result in registers
                (0..8).for_each(|i| {
                    self.proc
                        .set_reg(&register_by_idx(i), Elem::Field(result.0[i]))
                });
                (0..8).for_each(|i| {
                    self.proc
                        .set_reg(&register_by_idx(i + 8), Elem::Field(result.1[i]))
                });

                vec![]
            }
            "mod_256" => {
                assert!(args.is_empty());
                // take input from registers
                let y2 = (0..8)
                    .map(|i| self.proc.get_reg(&register_by_idx(i)).into_fe())
                    .collect::<Vec<_>>();
                let y3 = (0..8)
                    .map(|i| self.proc.get_reg(&register_by_idx(i + 8)).into_fe())
                    .collect::<Vec<_>>();
                let x1 = (0..8)
                    .map(|i| self.proc.get_reg(&register_by_idx(i + 16)).into_fe())
                    .collect::<Vec<_>>();
                let result = arith::mod_256(&y2, &y3, &x1);
                // store result in registers
                (0..8).for_each(|i| {
                    self.proc
                        .set_reg(&register_by_idx(i), Elem::Field(result[i]))
                });
                vec![]
            }
            "ec_add" => {
                assert!(args.is_empty());
                // take input from registers
                let x1 = (0..8)
                    .map(|i| self.proc.get_reg(&register_by_idx(i)).into_fe())
                    .collect::<Vec<_>>();
                let y1 = (0..8)
                    .map(|i| self.proc.get_reg(&register_by_idx(i + 8)).into_fe())
                    .collect::<Vec<_>>();
                let x2 = (0..8)
                    .map(|i| self.proc.get_reg(&register_by_idx(i + 16)).into_fe())
                    .collect::<Vec<_>>();
                let y2 = (0..8)
                    .map(|i| self.proc.get_reg(&register_by_idx(i + 24)).into_fe())
                    .collect::<Vec<_>>();
                let result = arith::ec_add(&x1, &y1, &x2, &y2);
                // store result in registers
                (0..8).for_each(|i| {
                    self.proc
                        .set_reg(&register_by_idx(i), Elem::Field(result.0[i]))
                });
                (0..8).for_each(|i| {
                    self.proc
                        .set_reg(&register_by_idx(i + 8), Elem::Field(result.1[i]))
                });

                vec![]
            }
            "ec_double" => {
                assert!(args.is_empty());
                // take input from registers
                let x = (0..8)
                    .map(|i| self.proc.get_reg(&register_by_idx(i)).into_fe())
                    .collect::<Vec<_>>();
                let y = (0..8)
                    .map(|i| self.proc.get_reg(&register_by_idx(i + 8)).into_fe())
                    .collect::<Vec<_>>();
                let result = arith::ec_double(&x, &y);
                // store result in registers
                (0..8).for_each(|i| {
                    self.proc
                        .set_reg(&register_by_idx(i), Elem::Field(result.0[i]))
                });
                (0..8).for_each(|i| {
                    self.proc
                        .set_reg(&register_by_idx(i + 8), Elem::Field(result.1[i]))
                });

                vec![]
            }
            instr => {
                panic!("unknown instruction: {instr}. Make sure the program was also compiled for the {:?} field", F::known_field().unwrap());
            }
        }
    }

    fn eval_expression(&mut self, expression: &Expression) -> Vec<Elem<F>> {
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
                vec![val]
            }
            Expression::PublicReference(_, _) => todo!(),
            Expression::Number(_, Number { value: n, .. }) => {
                let unsigned: u32 = n
                    .try_into()
                    .unwrap_or_else(|_| panic!("Value does not fit in 32 bits."));

                vec![unsigned.into()]
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
                let l = &self.eval_expression(l)[0];
                let r = &self.eval_expression(r)[0];

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

                vec![result]
            }
            Expression::UnaryOperation(_, UnaryOperation { op, expr: arg }) => {
                let arg = self.eval_expression(arg)[0].bin();
                let result = match op {
                    powdr_ast::parsed::UnaryOperator::Minus => -arg,
                    powdr_ast::parsed::UnaryOperator::LogicalNot => todo!(),
                    powdr_ast::parsed::UnaryOperator::Next => unreachable!(),
                };

                vec![Elem::Binary(result)]
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
                    .map(|arg| self.eval_expression(arg)[0].to_string())
                    .collect::<Vec<_>>();
                let query = format!("{variant}({})", values.join(","));
                match (self.inputs)(&query).unwrap() {
                    Some(val) => {
                        let e = Elem::try_from_fe_as_bin(&val)
                            .expect("field value does not fit into u32 or i32");
                        vec![e]
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
            Expression::StructExpression(_, _) => panic!(),
        }
    }
}

/// return true if the expression is a jump instruction
fn is_jump(e: &Expression) -> bool {
    if let Expression::FunctionCall(_, FunctionCall { function, .. }) = e {
        if let Expression::Reference(_, f) = function.as_ref() {
            return ["jump", "jump_dyn"].contains(&f.try_to_identifier().unwrap().as_str());
        }
    }
    false
}

pub fn execute_ast<F: FieldElement>(
    program: &AnalysisASMFile,
    initial_memory: MemoryState,
    inputs: &Callback<F>,
    bootloader_inputs: &[F],
    max_steps_to_execute: usize,
    mode: ExecMode,
    profiling: Option<ProfilerOptions>,
) -> (ExecutionTrace<F>, MemoryState, RegisterMemoryState<F>) {
    let main_machine = get_main_machine(program);
    let PreprocessedMain {
        statements,
        label_map,
        batch_to_line_map,
        debug_files,
        function_starts,
        location_starts,
    } = preprocess_main_function(main_machine);

    let proc = match TraceBuilder::<'_, F>::new(
        main_machine,
        initial_memory,
        &batch_to_line_map,
        max_steps_to_execute,
        mode,
    ) {
        Ok(proc) => proc,
        Err(ret) => return *ret,
    };

    let bootloader_inputs = bootloader_inputs
        .iter()
        .map(|v| Elem::try_from_fe_as_bin(v).unwrap_or(Elem::Field(*v)))
        .collect();

    let mut e = Executor {
        proc,
        label_map,
        inputs,
        bootloader_inputs,
        _stdout: io::stdout(),
    };

    let mut profiler =
        profiling.map(|opt| Profiler::new(opt, &debug_files[..], function_starts, location_starts));

    let mut curr_pc = 0u32;
    loop {
        let stm = statements[curr_pc as usize];

        log::trace!("l {curr_pc}: {stm}",);

        match stm {
            FunctionStatement::Assignment(a) => {
                if let Some(p) = &mut profiler {
                    p.add_instruction_cost(e.proc.get_pc().u() as usize);
                }

                let pc_before = e.proc.get_reg("pc").u() as usize;

                let results = e.eval_expression(a.rhs.as_ref());
                assert_eq!(a.lhs_with_reg.len(), results.len());

                let pc_after = e.proc.get_reg("pc").u() as usize;

                if is_jump(a.rhs.as_ref()) {
                    let pc_return = results[0].u() as usize;
                    assert_eq!(a.lhs_with_reg.len(), 1);
                    if let Some(p) = &mut profiler {
                        // in the generated powdr asm, writing to `tmp1` means the returning pc is ignored
                        if a.lhs_with_reg[0].0 == "tmp1" {
                            p.jump(pc_after);
                        } else {
                            p.jump_and_link(
                                pc_before as usize,
                                pc_after as usize,
                                pc_return as usize,
                            );
                        }
                    }
                }

                for ((dest, _), val) in a.lhs_with_reg.iter().zip(results) {
                    e.proc.set_reg(dest, val);
                }
            }
            FunctionStatement::Instruction(i) => {
                if let Some(p) = &mut profiler {
                    p.add_instruction_cost(e.proc.get_pc().u() as usize);
                }

                if ["jump", "jump_dyn"].contains(&i.instruction.as_str()) {
                    let pc_return = e.proc.get_pc().u() + 1;
                    let pc_before = e.proc.get_reg("pc").u();

                    e.exec_instruction(&i.instruction, &i.inputs);

                    let pc_after = e.proc.get_reg("pc").u();

                    let target_reg = e.eval_expression(&i.inputs[1]);
                    assert_eq!(target_reg.len(), 1);
                    let target_reg = target_reg[0].u();

                    if let Some(p) = &mut profiler {
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
            FunctionStatement::Return(_) => break,
            FunctionStatement::DebugDirective(dd) => {
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
            FunctionStatement::Label(_) => {
                unreachable!()
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
    e.proc.finish()
}

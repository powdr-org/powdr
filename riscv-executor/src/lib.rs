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

use std::collections::HashMap;

use powdr_ast::{
    asm_analysis::{AnalysisASMFile, Machine},
    parsed::asm::parse_absolute_path,
};
use powdr_number::{FieldElement, KnownField};

pub mod large_field;
mod profiler;
pub mod small_field;
pub use profiler::ProfilerOptions;

/// Initial value of the PC.
///
/// To match the ZK proof witness, the PC must start after some offset used for
/// proof initialization.
///
/// TODO: get this value from some authoritative place
const PC_INITIAL_VAL: usize = 2;

pub enum ExecMode {
    Fast,
    Trace,
}

pub type MemoryState = HashMap<u32, u32>;
/// Value of registers is Vec<F> to unify the output for different field sizes
pub type RegisterMemoryState<F> = HashMap<u32, Vec<F>>;

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

pub struct RegWrite<F: FieldElement> {
    /// The row of the execution trace this write will result into. Multiple
    /// writes at the same row are valid: the last write to a given reg_idx will
    /// define the final value of the register in that row.
    row: usize,
    /// Index of the register in the register bank.
    reg_idx: u16,
    val: F,
}

pub struct ExecutionTrace<F: FieldElement> {
    pub reg_map: HashMap<String, u16>,

    /// Values of the registers in the execution trace.
    ///
    /// Each N elements is a row with all registers, where N is the number of
    /// registers.
    pub reg_writes: Vec<RegWrite<F>>,

    /// Writes and reads to memory.
    pub mem_ops: Vec<MemOperation>,

    /// The length of the trace, after applying the reg_writes.
    pub len: usize,
}

impl<F: FieldElement> ExecutionTrace<F> {
    /// Replay the execution and get the register values per trace row.
    pub fn replay(&self) -> TraceReplay<F> {
        TraceReplay {
            trace: self,
            regs: vec![0.into(); self.reg_map.len()],
            pc_idx: self.reg_map["pc"] as usize,
            next_write: 0,
            next_r: 0,
        }
    }
}

pub struct TraceReplay<'a, F: FieldElement> {
    trace: &'a ExecutionTrace<F>,
    regs: Vec<F>,
    pc_idx: usize,
    next_write: usize,
    next_r: usize,
}

impl<'a, F: FieldElement> TraceReplay<'a, F> {
    /// Returns the next row's registers value.
    ///
    /// Just like an iterator's next(), but returns the value borrowed from self.
    pub fn next_row(&mut self) -> Option<&[F]> {
        if self.next_r == self.trace.len {
            return None;
        }

        // we optimistically increment the PC, if it is a jump or special case,
        // one of the writes will overwrite it
        self.regs[self.pc_idx] += 1.into();

        while let Some(next_write) = self.trace.reg_writes.get(self.next_write) {
            if next_write.row > self.next_r {
                break;
            }
            self.next_write += 1;

            self.regs[next_write.reg_idx as usize] = next_write.val;
        }

        self.next_r += 1;
        Some(&self.regs[..])
    }
}

pub fn get_main_machine(program: &AnalysisASMFile) -> &Machine {
    program.get_machine(&parse_absolute_path("::Main")).unwrap()
}

type Callback<'a, F> = dyn powdr_executor::witgen::QueryCallback<F> + 'a;

/// Execute a Powdr/RISCV assembly source.
///
/// Generic argument F is just used by the powdr_parser, before everything is
/// converted to i64, so it is important to the execution itself.
pub fn execute<F: FieldElement>(
    asm_source: &str,
    initial_memory: MemoryState,
    inputs: &Callback<F>,
    bootloader_inputs: &[F],
    mode: ExecMode,
    profiling: Option<ProfilerOptions>,
) -> (ExecutionTrace<F>, MemoryState, RegisterMemoryState<F>) {
    log::info!("Parsing...");
    let parsed = powdr_parser::parse_asm(None, asm_source).unwrap();
    log::info!("Resolving imports...");
    let resolved = powdr_importer::load_dependencies_and_resolve(None, parsed).unwrap();
    log::info!("Analyzing...");
    let analyzed = powdr_analysis::analyze(resolved).unwrap();

    log::info!("Executing...");
    execute_ast(
        &analyzed,
        initial_memory,
        inputs,
        bootloader_inputs,
        usize::MAX,
        mode,
        profiling,
    )
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
    match F::known_field() {
        Some(KnownField::BabyBearField | KnownField::Mersenne31Field) => small_field::execute_ast(
            program,
            initial_memory,
            inputs,
            bootloader_inputs,
            max_steps_to_execute,
            mode,
            profiling,
        ),
        Some(KnownField::GoldilocksField | KnownField::Bn254Field) => large_field::execute_ast(
            program,
            initial_memory,
            inputs,
            bootloader_inputs,
            max_steps_to_execute,
            mode,
            profiling,
        ),
        _ => panic!("Unsupported field size"),
    }
}

/// FIXME: copied from `riscv/runtime.rs` instead of adding dependency.
/// Helper function for register names used in submachine instruction params.
pub(crate) fn register_by_idx(idx: usize) -> String {
    format!("xtra{idx}")
}

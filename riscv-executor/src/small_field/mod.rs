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

use powdr_ast::asm_analysis::AnalysisASMFile;
use powdr_number::FieldElement;

use crate::{
    Callback, ExecMode, ExecutionTrace, MemoryState, ProfilerOptions, RegisterMemoryState,
};

pub fn execute_ast<F: FieldElement>(
    _program: &AnalysisASMFile,
    _initial_memory: MemoryState,
    _inputs: &Callback<F>,
    _bootloader_inputs: &[F],
    _max_steps_to_execute: usize,
    _mode: ExecMode,
    _profiling: Option<ProfilerOptions>,
) -> (ExecutionTrace<F>, MemoryState, RegisterMemoryState<F>) {
    todo!()
}

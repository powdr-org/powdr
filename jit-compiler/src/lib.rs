mod codegen;
mod compiler;

use std::{collections::HashMap, fs};

use codegen::CodeGenerator;
use compiler::{call_cargo, generate_glue_code, load_library};
use powdr_ast::analyzed::Analyzed;
use powdr_number::FieldElement;

pub type SymbolMap = HashMap<String, fn(u64) -> u64>;

/// Compiles the given symbols (and their dependencies) and returns them as a map
/// from symbol name to function pointer.
/// Only functions of type (int -> int) are supported for now.
pub fn compile<T: FieldElement>(
    analyzed: &Analyzed<T>,
    requested_symbols: &[&str],
) -> Result<SymbolMap, String> {
    log::info!("JIT-compiling {} symbols...", requested_symbols.len());

    let mut codegen = CodeGenerator::new(analyzed);
    let successful_symbols = requested_symbols
        .iter()
        .filter_map(|&sym| {
            if let Err(e) = codegen.request_symbol(sym) {
                log::warn!("Unable to generate code for symbol {sym}: {e}");
                None
            } else {
                Some(sym)
            }
        })
        .collect::<Vec<_>>();

    if successful_symbols.is_empty() {
        return Ok(Default::default());
    };

    let glue_code = generate_glue_code(&successful_symbols, analyzed)?;

    let (dir, lib_path) = call_cargo(&format!("{glue_code}\n{}\n", codegen.compiled_symbols()))?;
    let metadata = fs::metadata(&lib_path).unwrap();

    log::info!(
        "Loading library of size {} MB...",
        metadata.len() as f64 / 1000000.0
    );

    let result = load_library(&lib_path, &successful_symbols);
    log::info!("Done.");

    drop(dir);
    result
}
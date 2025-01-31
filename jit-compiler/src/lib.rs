mod codegen;
mod compiler;

use std::{
    collections::{HashMap, HashSet},
    fs,
    sync::Arc,
};

use codegen::CodeGenerator;
use compiler::{generate_glue_code, load_library};

use itertools::Itertools;
use powdr_ast::analyzed::Analyzed;
use powdr_number::FieldElement;

pub use compiler::call_cargo;

pub struct CompiledPIL {
    #[allow(dead_code)]
    library: Arc<libloading::Library>,
    set_degree_fun: extern "C" fn(u64),
    fixed_columns: HashMap<String, FixedColFunction>,
}

impl CompiledPIL {
    /// Sets the degree returned by `std::prover::degree` in the loaded library.
    pub fn set_degree(&self, degree: u64) {
        (self.set_degree_fun)(degree)
    }
    pub fn get_fixed_column(&self, name: &str) -> Option<&FixedColFunction> {
        self.fixed_columns.get(name)
    }
}

/// Wrapper around a dynamically loaded function.
/// Prevents the dynamically loaded library to be unloaded while the function is still in use.
#[derive(Clone)]
pub struct FixedColFunction {
    #[allow(dead_code)]
    library: Arc<libloading::Library>,
    function: extern "C" fn(u64) -> u64,
}

impl FixedColFunction {
    pub fn call(&self, arg: u64) -> u64 {
        (self.function)(arg)
    }
}

/// JIT-compiles the given symbols (and their dependencies) and loads the binary
/// as a shared library.
/// Only functions of type (int -> int) are supported for now.
pub fn compile<T: FieldElement>(
    analyzed: &Analyzed<T>,
    requested_symbols: &[&str],
) -> Result<CompiledPIL, String> {
    // TODO this should be changed back to Info after the introduction of the ToCol trait.
    log::debug!("JIT-compiling {} symbols...", requested_symbols.len());

    let mut codegen = CodeGenerator::<T, _>::new(analyzed);
    let successful_symbols = requested_symbols
        .iter()
        .filter_map(|&sym| match codegen.request_symbol(sym, &[]) {
            Err(e) => {
                log::debug!("Unable to generate code for symbol {sym}: {e}");
                None
            }
            Ok(access) => Some((sym, access)),
        })
        .collect::<Vec<_>>();
    let successful_symbol_names: Vec<_> = successful_symbols.iter().map(|(s, _)| *s).collect();

    if successful_symbols.len() < requested_symbols.len() {
        let successful_hash = successful_symbol_names.iter().collect::<HashSet<_>>();
        // TODO this should be changed back to Info after the introduction of the ToCol trait.
        log::debug!(
            "Unable to generate code during JIT-compilation for the following symbols. Will use interpreter instead.\n{}",
            requested_symbols
                .iter()
                .filter(|&sym| !successful_hash.contains(sym))
                .format(", ")
        );
    }

    let glue_code = generate_glue_code(&successful_symbols, analyzed)?;

    let opt_level = None;
    let lib_file = call_cargo(
        &format!("{glue_code}\n{}\n", codegen.generated_code()),
        opt_level,
    )?;
    let metadata = fs::metadata(&lib_file.path).unwrap();

    log::info!(
        "Loading library of size {} MB...",
        metadata.len() as f64 / (1024.0 * 1024.0)
    );

    let result = load_library(&lib_file.path, &successful_symbol_names)?;
    log::info!("Done.");
    Ok(result)
}

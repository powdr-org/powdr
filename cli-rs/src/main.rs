//! The powdr-rs CLI tool

mod util;

use clap::{CommandFactory, Parser, Subcommand};
use env_logger::fmt::Color;
use env_logger::{Builder, Target};
use log::LevelFilter;

use powdr::number::{
    BabyBearField, BigUint, Bn254Field, FieldElement, GoldilocksField, KnownField, KoalaBearField,
};
use powdr::riscv::{CompilerOptions, RuntimeLibs};
use powdr::riscv_executor::{write_executor_csv, ProfilerOptions};
use powdr::Pipeline;

use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::ffi::OsStr;
use std::time::Instant;
use std::{
    io::{self, Write},
    path::Path,
};

use strum::{Display, EnumString, EnumVariantNames};

#[derive(Clone, EnumString, EnumVariantNames, Display)]
pub enum FieldArgument {
    #[strum(serialize = "bb")]
    Bb,
    #[strum(serialize = "kb")]
    Kb,
    #[strum(serialize = "gl")]
    Gl,
    #[strum(serialize = "bn254")]
    Bn254,
}

impl FieldArgument {
    pub fn as_known_field(&self) -> KnownField {
        match self {
            FieldArgument::Bb => KnownField::BabyBearField,
            FieldArgument::Kb => KnownField::KoalaBearField,
            FieldArgument::Gl => KnownField::GoldilocksField,
            FieldArgument::Bn254 => KnownField::Bn254Field,
        }
    }
}

#[derive(Parser)]
#[command(name = "powdr-rs", author, version, about, long_about = None)]
struct Cli {
    #[arg(long, hide = true)]
    markdown_help: bool,

    /// Set log filter value [ off, error, warn, info, debug, trace ]
    #[arg(long)]
    #[arg(default_value_t = LevelFilter::Info)]
    log_level: LevelFilter,

    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    /// Compile rust code to Powdr assembly.
    /// Needs `rustup component add rust-src --toolchain nightly-2024-08-01`.
    Compile {
        /// input rust code, points to a crate dir or its Cargo.toml file
        file: String,

        /// The field to use
        #[arg(long)]
        #[arg(default_value_t = FieldArgument::Gl)]
        #[arg(value_parser = clap_enum_variants!(FieldArgument))]
        field: FieldArgument,

        /// Directory for output files.
        #[arg(short, long)]
        #[arg(default_value_t = String::from("."))]
        output_directory: String,

        /// Comma-separated list of coprocessors.
        #[arg(long)]
        coprocessors: Option<String>,

        /// Run a long execution in chunks (Experimental and not sound!)
        #[arg(short, long)]
        #[arg(default_value_t = false)]
        continuations: bool,

        /// Maximum trace length for powdr machines (2 ^ max_degree_log).
        #[arg(long)]
        max_degree_log: Option<u8>,
    },
    /// Translate a RISC-V statically linked executable to powdr assembly.
    RiscvElf {
        /// Input file
        #[arg(required = true)]
        file: String,

        /// The field to use
        #[arg(long)]
        #[arg(default_value_t = FieldArgument::Gl)]
        #[arg(value_parser = clap_enum_variants!(FieldArgument))]
        field: FieldArgument,

        /// Directory for output files.
        #[arg(short, long)]
        #[arg(default_value_t = String::from("."))]
        output_directory: String,

        /// Comma-separated list of coprocessors.
        #[arg(long)]
        coprocessors: Option<String>,

        /// Run a long execution in chunks (Experimental and not sound!)
        #[arg(short, long)]
        #[arg(default_value_t = false)]
        continuations: bool,
    },
    /// Execute a RISCV powdr-asm file with given inputs.
    /// Does not generate a witness.
    Execute {
        /// input powdr-asm code compiled from Rust/RISCV
        file: String,

        /// The field to use
        #[arg(long)]
        #[arg(default_value_t = FieldArgument::Gl)]
        #[arg(value_parser = clap_enum_variants!(FieldArgument))]
        field: FieldArgument,

        /// Comma-separated list of free inputs (numbers).
        #[arg(short, long)]
        #[arg(default_value_t = String::new())]
        inputs: String,

        /// Directory for output files.
        #[arg(short, long)]
        #[arg(default_value_t = String::from("."))]
        output_directory: String,

        /// Generate a flamegraph plot of the execution ("[file].svg")
        #[arg(long)]
        #[arg(default_value_t = false)]
        generate_flamegraph: bool,

        /// Generate callgrind file of the execution ("[file].callgrind")
        #[arg(long)]
        #[arg(default_value_t = false)]
        generate_callgrind: bool,

        #[arg(long)]
        #[arg(default_value_t = false)]
        auto_precompiles: bool,
    },
    /// Execute and generate a valid witness for a RISCV powdr-asm file with the given inputs.
    Witgen {
        /// input powdr-asm code compiled from Rust/RISCV
        file: String,

        /// The field to use
        #[arg(long)]
        #[arg(default_value_t = FieldArgument::Gl)]
        #[arg(value_parser = clap_enum_variants!(FieldArgument))]
        field: FieldArgument,

        /// Comma-separated list of free inputs (numbers).
        #[arg(short, long)]
        #[arg(default_value_t = String::new())]
        inputs: String,

        /// Directory for output files.
        #[arg(short, long)]
        #[arg(default_value_t = String::from("."))]
        output_directory: String,

        /// Run a long execution in chunks (Experimental and not sound!)
        #[arg(short, long)]
        #[arg(default_value_t = false)]
        continuations: bool,

        /// Export the executor generated witness columns as a CSV file. Useful for debugging executor issues.
        #[arg(long)]
        #[arg(default_value_t = false)]
        executor_csv: bool,

        /// Generate a flamegraph plot of the execution ("[file].svg")
        #[arg(long)]
        #[arg(default_value_t = false)]
        generate_flamegraph: bool,

        /// Generate callgrind file of the execution ("[file].callgrind")
        #[arg(long)]
        #[arg(default_value_t = false)]
        generate_callgrind: bool,
    },
}

fn main() -> Result<(), io::Error> {
    let args = Cli::parse();

    let mut builder = Builder::new();
    builder
        .filter_level(args.log_level)
        .parse_default_env()
        .target(Target::Stdout)
        .format(|buf, record| {
            let mut style = buf.style();

            // we allocate as there is no way to look into the message otherwise
            let msg = record.args().to_string();

            // add colors for the diffs
            match &msg {
                s if s.starts_with('+') => {
                    style.set_color(Color::Green);
                }
                s if s.starts_with('-') => {
                    style.set_color(Color::Red);
                }
                _ => {}
            }

            writeln!(buf, "{}", style.value(msg))
        })
        .init();

    if args.markdown_help {
        clap_markdown::print_help_markdown::<Cli>();
        Ok(())
    } else if let Some(command) = args.command {
        run_command(command);
        Ok(())
    } else {
        Cli::command().print_help()
    }
}

fn split_inputs<T: FieldElement>(inputs: &str) -> Vec<T> {
    inputs
        .split(',')
        .map(|x| x.trim())
        .filter(|x| !x.is_empty())
        .map(|x| x.parse::<BigUint>().unwrap().into())
        .collect()
}

#[allow(clippy::print_stderr)]
fn run_command(command: Commands) {
    let result = match command {
        Commands::Compile {
            file,
            field,
            output_directory,
            coprocessors,
            continuations,
            max_degree_log,
        } => compile_rust(
            &file,
            field.as_known_field(),
            Path::new(&output_directory),
            coprocessors,
            continuations,
            max_degree_log,
        ),
        Commands::RiscvElf {
            file,
            field,
            output_directory,
            coprocessors,
            continuations,
        } => compile_riscv_elf(
            &file,
            field.as_known_field(),
            Path::new(&output_directory),
            coprocessors,
            continuations,
        ),
        Commands::Execute {
            file,
            field,
            inputs,
            output_directory,
            generate_flamegraph,
            generate_callgrind,
            auto_precompiles,
        } => {
            let profiling = if generate_callgrind || generate_flamegraph {
                Some(ProfilerOptions {
                    file_stem: Path::new(&file)
                        .file_stem()
                        .and_then(OsStr::to_str)
                        .map(String::from),
                    output_directory: output_directory.clone(),
                    flamegraph: generate_flamegraph,
                    callgrind: generate_callgrind,
                })
            } else {
                None
            };
            if !auto_precompiles {
                call_with_field!(execute_fast::<field>(
                    Path::new(&file),
                    split_inputs(&inputs),
                    Path::new(&output_directory),
                    profiling
                ))
            } else {
                call_with_field!(autoprecompiles::<field>(
                    Path::new(&file),
                    split_inputs(&inputs),
                    Path::new(&output_directory)
                ))
            }
        }
        Commands::Witgen {
            file,
            field,
            inputs,
            output_directory,
            continuations,
            executor_csv,
            generate_flamegraph,
            generate_callgrind,
        } => {
            let profiling = if generate_callgrind || generate_flamegraph {
                Some(ProfilerOptions {
                    file_stem: Path::new(&file)
                        .file_stem()
                        .and_then(OsStr::to_str)
                        .map(String::from),
                    output_directory: output_directory.clone(),
                    flamegraph: generate_flamegraph,
                    callgrind: generate_callgrind,
                })
            } else {
                None
            };
            call_with_field!(execute::<field>(
                Path::new(&file),
                split_inputs(&inputs),
                Path::new(&output_directory),
                continuations,
                executor_csv,
                profiling
            ))
        }
    };
    if let Err(errors) = result {
        for error in errors {
            eprintln!("{}", error);
        }
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_arguments)]
fn compile_rust(
    file_name: &str,
    field: KnownField,
    output_dir: &Path,
    coprocessors: Option<String>,
    continuations: bool,
    max_degree_log: Option<u8>,
) -> Result<(), Vec<String>> {
    let libs = coprocessors_to_options(coprocessors)?;
    let mut options = CompilerOptions::new(field, libs, continuations);
    if let Some(max_degree_log) = max_degree_log {
        options = options.with_max_degree_log(max_degree_log);
    }
    powdr::riscv::compile_rust(file_name, options, output_dir, true, None)
        .ok_or_else(|| vec!["could not compile rust".to_string()])?;

    Ok(())
}

fn compile_riscv_elf(
    input_file: &str,
    field: KnownField,
    output_dir: &Path,
    coprocessors: Option<String>,
    continuations: bool,
) -> Result<(), Vec<String>> {
    let libs = coprocessors_to_options(coprocessors)?;
    let options = CompilerOptions::new(field, libs, continuations);
    powdr::riscv::compile_riscv_elf(input_file, Path::new(input_file), options, output_dir, true)
        .ok_or_else(|| vec!["could not translate RISC-V executable".to_string()])?;

    Ok(())
}

fn execute_fast<F: FieldElement>(
    file_name: &Path,
    inputs: Vec<F>,
    output_dir: &Path,
    profiling: Option<ProfilerOptions>,
) -> Result<(), Vec<String>> {
    let mut pipeline = Pipeline::<F>::default()
        .from_asm_file(file_name.to_path_buf())
        .with_prover_inputs(inputs)
        .with_output(output_dir.into(), true);

    let asm = pipeline.compute_analyzed_asm().unwrap().clone();

    let start = Instant::now();

    let (trace_len, _) = powdr::riscv_executor::execute::<F>(
        &asm,
        powdr::riscv_executor::MemoryState::new(),
        pipeline.data_callback().unwrap(),
        &[],
        profiling,
        Default::default(),
    );

    let duration = start.elapsed();
    log::info!("Executor done in: {:?}", duration);
    log::info!("Execution trace length: {}", trace_len);
    Ok(())
}

fn autoprecompiles<F: FieldElement>(
    file_name: &Path,
    inputs: Vec<F>,
    output_dir: &Path,
) -> Result<(), Vec<String>> {
    let mut pipeline = Pipeline::<F>::default()
        .from_asm_file(file_name.to_path_buf())
        .with_prover_inputs(inputs)
        .with_backend(powdr::backend::BackendType::Plonky3Composite, None)
        .with_output(output_dir.into(), true);

    pipeline.compute_checked_asm().unwrap();
    let checked_asm = pipeline.checked_asm().unwrap().clone();

    let asm = pipeline.compute_analyzed_asm().unwrap().clone();
    let initial_memory =
        powdr::riscv::continuations::load_initial_memory(&asm, pipeline.initial_memory());

    println!("Running powdr-riscv executor in fast mode...");
    let start = Instant::now();

    let (trace_len, label_freq) = powdr::riscv_executor::execute(
        &asm,
        initial_memory,
        pipeline.data_callback().unwrap(),
        &powdr::riscv::continuations::bootloader::default_input(&[]),
        None,
        Default::default(),
    );

    let duration = start.elapsed();
    println!("Fast executor took: {duration:?}");
    println!("Trace length: {trace_len}");

    let blocks = powdr_analysis::collect_basic_blocks(&checked_asm);
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

    let dont_eq = vec!["__data_init", "main", "halt"];
    let dont_contain = vec!["powdr_riscv_runtime", "page_ok"];
    let selected: HashSet<String> = blocks
        .iter()
        .skip(0)
        .filter(|(name, _, _, _)| {
            !dont_eq.contains(&name.as_str()) && !dont_contain.iter().any(|s| name.contains(s))
        })
        .take(10)
        .map(|block| block.0.clone())
        .into_iter()
        .collect();
    let auto_asm = powdr_analysis::analyze_precompiles(checked_asm.clone(), &selected);

    println!("New auto_asm:\n{auto_asm}");

    println!("Selected blocks: {selected:?}");

    let selected_blocks: HashMap<_, _> = blocks
        .into_iter()
        .filter(|(name, _, _, _)| selected.contains(name))
        .map(|(name, block, _, _)| (name, block))
        .collect();

    pipeline.rollback_from_checked_asm();
    pipeline.set_checked_asm(auto_asm);
    let asm = pipeline.compute_analyzed_asm().unwrap().clone();
    let initial_memory =
        powdr::riscv::continuations::load_initial_memory(&asm, pipeline.initial_memory());

    println!("Running powdr-riscv executor in fast mode with autoprecomiles...");
    let start = Instant::now();

    let (trace_len, _) = powdr::riscv_executor::execute(
        &asm,
        initial_memory,
        pipeline.data_callback().unwrap(),
        &powdr::riscv::continuations::bootloader::default_input(&[]),
        None,
        selected_blocks,
    );

    let duration = start.elapsed();
    println!("Fast executor with autoprecompiles took: {duration:?}");
    println!("Trace length with autoprecompiles: {trace_len}");

    /*
        pipeline.compute_witness()?;
        pipeline.compute_proof()?;
    */

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn execute<F: FieldElement>(
    file_name: &Path,
    inputs: Vec<F>,
    output_dir: &Path,
    continuations: bool,
    executor_csv: bool,
    profiling: Option<ProfilerOptions>,
) -> Result<(), Vec<String>> {
    let mut pipeline = Pipeline::<F>::default()
        .from_asm_file(file_name.to_path_buf())
        .with_prover_inputs(inputs)
        .with_output(output_dir.into(), true);

    let generate_witness = |pipeline: &mut Pipeline<F>| -> Result<(), Vec<String>> {
        pipeline.compute_witness().unwrap();
        Ok(())
    };

    if continuations {
        let dry_run =
            powdr::riscv::continuations::rust_continuations_dry_run(&mut pipeline, profiling);
        powdr::riscv::continuations::rust_continuations(&mut pipeline, generate_witness, dry_run)?;
    } else {
        let fixed = pipeline.compute_fixed_cols().unwrap().clone();
        let asm = pipeline.compute_analyzed_asm().unwrap().clone();
        let pil = pipeline.compute_optimized_pil().unwrap();

        let start = Instant::now();

        let (execution, _) = powdr::riscv_executor::execute_with_trace::<F>(
            &asm,
            &pil,
            fixed,
            powdr::riscv_executor::MemoryState::new(),
            pipeline.data_callback().unwrap(),
            &[],
            None,
            profiling,
        );

        let duration = start.elapsed();
        log::info!("Executor done in: {:?}", duration);
        log::info!("Execution trace length: {}", execution.trace_len);

        let witness_cols: Vec<_> = pil
            .committed_polys_in_source_order()
            .flat_map(|(s, _)| s.array_elements().map(|(name, _)| name))
            .collect();

        let trace: Vec<_> = execution.trace.into_iter().collect();

        if executor_csv {
            let file_name = format!(
                "{}_executor.csv",
                file_name.file_stem().unwrap().to_str().unwrap()
            );
            write_executor_csv(file_name, &trace, Some(&witness_cols));
        }

        pipeline = pipeline.add_external_witness_values(trace);

        generate_witness(&mut pipeline)?;
    }

    Ok(())
}

fn coprocessors_to_options(coprocessors: Option<String>) -> Result<RuntimeLibs, Vec<String>> {
    let mut libs = RuntimeLibs::new();
    if let Some(list) = coprocessors {
        let names = list.split(',').collect::<Vec<_>>();
        for name in names {
            match name {
                "poseidon2_gl" => libs = libs.with_poseidon2(),
                "keccakf" => libs = libs.with_keccak(),
                "arith" => libs = libs.with_arith(),
                _ => return Err(vec![format!("Invalid co-processor specified: {name}")]),
            }
        }
    }
    Ok(libs)
}

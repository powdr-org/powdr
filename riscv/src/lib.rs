//! A RISC-V frontend for powdr
#![deny(clippy::print_stdout)]

use std::{
    borrow::Cow,
    ffi::OsStr,
    path::{Path, PathBuf},
    process::Command,
};

use powdr_number::KnownField;
use std::fs;

mod code_gen;
pub mod continuations;
pub mod elf;
pub mod large_field;
pub mod runtime;
pub mod small_field;

static TARGET_STD: &str = "riscv32im-risc0-zkvm-elf";
static TARGET_NO_STD: &str = "riscv32imac-unknown-none-elf";

#[derive(Copy, Default, Clone)]
pub struct RuntimeLibs {
    pub arith: bool,
    pub keccak: bool,
    pub poseidon: bool,
}

impl RuntimeLibs {
    pub fn new() -> Self {
        Self {
            arith: false,
            keccak: false,
            poseidon: false,
        }
    }

    pub fn with_arith(self) -> Self {
        Self {
            arith: true,
            ..self
        }
    }

    pub fn with_keccak(self) -> Self {
        Self {
            keccak: true,
            ..self
        }
    }

    pub fn with_poseidon(self) -> Self {
        Self {
            poseidon: true,
            ..self
        }
    }
}
#[derive(Copy, Clone)]
pub struct CompilerOptions {
    pub field: KnownField,
    pub libs: RuntimeLibs,
    pub continuations: bool,
    pub min_degree_log: Option<u8>,
    pub max_degree_log: Option<u8>,
}

impl CompilerOptions {
    pub fn new(field: KnownField, libs: RuntimeLibs, continuations: bool) -> Self {
        Self {
            field,
            libs,
            continuations,
            min_degree_log: None,
            max_degree_log: None,
        }
    }

    pub fn new_bb() -> Self {
        Self {
            field: KnownField::BabyBearField,
            libs: RuntimeLibs::new(),
            continuations: false,
            min_degree_log: None,
            max_degree_log: None,
        }
    }

    pub fn new_gl() -> Self {
        Self {
            field: KnownField::GoldilocksField,
            libs: RuntimeLibs::new(),
            continuations: false,
            min_degree_log: None,
            max_degree_log: None,
        }
    }

    pub fn with_min_degree_log(self, log_min_degree: u8) -> Self {
        Self {
            min_degree_log: Some(log_min_degree),
            ..self
        }
    }

    pub fn with_max_degree_log(self, log_max_degree: u8) -> Self {
        Self {
            max_degree_log: Some(log_max_degree),
            ..self
        }
    }

    pub fn with_continuations(self) -> Self {
        Self {
            continuations: true,
            ..self
        }
    }

    pub fn with_arith(self) -> Self {
        Self {
            libs: self.libs.with_arith(),
            ..self
        }
    }

    pub fn with_keccak(self) -> Self {
        Self {
            libs: self.libs.with_keccak(),
            ..self
        }
    }

    pub fn with_poseidon(self) -> Self {
        Self {
            libs: self.libs.with_poseidon(),
            ..self
        }
    }
}

/// Compiles a rust file to Powdr asm.
#[allow(clippy::print_stderr)]
pub fn compile_rust(
    file_name: &str,
    options: CompilerOptions,
    output_dir: &Path,
    force_overwrite: bool,
    features: Option<Vec<String>>,
) -> Option<(PathBuf, String)> {
    if options.continuations {
        match options.field {
            KnownField::BabyBearField => {
                todo!()
            }
            KnownField::KoalaBearField => {
                todo!()
            }
            KnownField::Mersenne31Field => {
                todo!()
            }
            KnownField::GoldilocksField | KnownField::Bn254Field => {
                assert!(
                    options.libs.poseidon,
                    "Poseidon library is required for bootloader"
                );
            }
        }
    }

    let file_path = if file_name.ends_with("Cargo.toml") {
        Cow::Borrowed(file_name)
    } else if fs::metadata(file_name).unwrap().is_dir() {
        Cow::Owned(format!("{file_name}/Cargo.toml"))
    } else {
        panic!("input must be a crate directory or `Cargo.toml` file");
    };

    let elf_path = compile_rust_crate_to_riscv(&file_path, output_dir, features);

    compile_riscv_elf(file_name, &elf_path, options, output_dir, force_overwrite)
}

fn compile_program<P>(
    original_file_name: &str,
    input_program: P,
    options: CompilerOptions,
    output_dir: &Path,
    force_overwrite: bool,
    translator: impl FnOnce(P, CompilerOptions) -> String,
) -> Option<(PathBuf, String)> {
    let powdr_asm_file_name = output_dir.join(format!(
        "{}.asm",
        Path::new(original_file_name)
            .file_stem()
            .unwrap()
            .to_str()
            .unwrap()
    ));
    if powdr_asm_file_name.exists() && !force_overwrite {
        eprintln!(
            "Target file {} already exists. Not overwriting.",
            powdr_asm_file_name.to_str().unwrap()
        );
        return None;
    }

    let powdr_asm = translator(input_program, options);

    fs::write(powdr_asm_file_name.clone(), &powdr_asm).unwrap();
    log::info!("Wrote {}", powdr_asm_file_name.to_str().unwrap());

    Some((powdr_asm_file_name, powdr_asm))
}

/// Translates a RISC-V ELF file to powdr asm.
pub fn compile_riscv_elf(
    original_file_name: &str,
    input_file: &Path,
    options: CompilerOptions,
    output_dir: &Path,
    force_overwrite: bool,
) -> Option<(PathBuf, String)> {
    compile_program::<&Path>(
        original_file_name,
        input_file,
        options,
        output_dir,
        force_overwrite,
        elf::translate,
    )
}

/// Creates an array of references to a given type by calling as_ref on each
/// element.
macro_rules! as_ref [
    ($t:ty; $($x:expr),* $(,)?) => {
        [$(AsRef::<$t>::as_ref(&$x)),+]
    };
];

pub fn compile_rust_crate_to_riscv(
    input_dir: &str,
    output_dir: &Path,
    features: Option<Vec<String>>,
) -> PathBuf {
    const CARGO_TARGET_DIR: &str = "cargo_target";
    let target_dir = output_dir.join(CARGO_TARGET_DIR);

    let metadata = CargoMetadata::from_input_dir(input_dir);

    // Run build.
    let build_status =
        build_cargo_command(input_dir, &target_dir, metadata.use_std, features.clone())
            .status()
            .unwrap();
    assert!(build_status.success());

    let target = if metadata.use_std {
        TARGET_STD
    } else {
        TARGET_NO_STD
    };

    // TODO: support more than one executable per crate.
    assert_eq!(metadata.bins.len(), 1);
    target_dir
        .join(target)
        .join("release")
        .join(&metadata.bins[0])
}

#[derive(Debug)]
struct CargoMetadata {
    bins: Vec<String>,
    use_std: bool,
}

impl CargoMetadata {
    fn from_input_dir(input_dir: &str) -> Self {
        // Calls `cargo metadata --format-version 1 --no-deps --manifest-path <input_dir>` to determine
        // if the `std` feature is enabled in the dependency crate `powdr-riscv-runtime`.
        let metadata = Command::new("cargo")
            .args(as_ref![
                OsStr;
                "metadata",
                "--format-version",
                "1",
                "--no-deps",
                "--manifest-path",
                input_dir,
            ])
            .output()
            .unwrap();

        let metadata: serde_json::Value = serde_json::from_slice(&metadata.stdout).unwrap();
        let packages = metadata["packages"].as_array().unwrap();

        // Is the `std` feature enabled in the `powdr-riscv-runtime` crate?
        let use_std = packages.iter().any(|package| {
            package["dependencies"]
                .as_array()
                .unwrap()
                .iter()
                .any(|dependency| {
                    dependency["name"] == "powdr-riscv-runtime"
                        && dependency["features"]
                            .as_array()
                            .unwrap()
                            .contains(&"std".into())
                })
        });

        let bins = packages
            .iter()
            .flat_map(|package| {
                package["targets"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .filter_map(|target| {
                        target["kind"].as_array().and_then(|kind| {
                            if kind.contains(&"bin".into()) {
                                Some(target["name"].as_str().unwrap().to_string())
                            } else {
                                None
                            }
                        })
                    })
            })
            .collect();

        Self { bins, use_std }
    }
}

fn build_cargo_command(
    input_dir: &str,
    target_dir: &Path,
    use_std: bool,
    features: Option<Vec<String>>,
) -> Command {
    /*
        The explanation for the more exotic options we are using to build the user code:

        `-C link-arg=-Tpowdr.x`: tells the linker to use the `powdr.x` linker script,
        provided by `powdr-riscv-runtime` crate. It configures things like memory layout
        of the program and the entry point function.

        `-C link-arg=--emit-relocs`: this is a requirement from Powdr ELF translator, it
        tells the linker to leave in the final executable the linkage relocation tables.
        The ELF translator uses this information to lift references to text address into
        labels in the Powdr assembly.

        `-C passes=loweratomic`: risc0 target does not support atomic instructions. When
        they are needed, LLVM makes calls to software emulation functions it expects to
        exist, such as `__atomic_fetch_add_4`, etc. This option adds an LLVM pass that
        converts atomic instructions into non-atomic variants, so that the atomic
        functions are not need anymore. It works because we have a single-threaded
        non-interrupting implementation. This is only needed for std support, that uses
        risc0 target, but it is probably beneficial to leave this on for no_std as well.

        `-Zbuild-std=std,panic_abort`: there are no pre-packaged builds of standard
        libraries for risc0 target, so we have to instruct cargo to build the ones we
        will be using.

        `-Zbuild-std-features=default,compiler-builtins-mem`: rust's `std` has features
        that can be enabled or disabled, like any normal rust crate. We are telling that
        we need the default features, but also we need to build and use the memory
        related functions from `compiler_builtins` crate, which provides `memcpy`,
        `memcmp`, etc, for systems that doesn't already have them, like ours, as LLVM
        assumes these functions to be available. We also use `compiler_builtins` for
        `#[no_std]` programs, but in there it is enabled by default.
    */

    let mut cmd = Command::new("cargo");
    cmd.env(
        "RUSTFLAGS",
        "-g -C link-arg=-Tpowdr.x -C link-arg=--emit-relocs -C passes=lower-atomic -C panic=abort",
    );
    // keep debug info for the profiler (callgrind/flamegraph)
    cmd.env("CARGO_PROFILE_RELEASE_DEBUG", "true");

    let mut args: Vec<&OsStr> = as_ref![
        OsStr;
        "+nightly-2024-08-01",
        "build",
        "--release",
        "--target-dir",
        target_dir,
        "--manifest-path",
        input_dir,
        "--target"
        // target is defined in the following if-else block
    ]
    .into();

    if use_std {
        args.extend(as_ref![
            OsStr;
            TARGET_STD,
            "-Zbuild-std=std,panic_abort",
            "-Zbuild-std-features=default,compiler-builtins-mem",
        ]);
    } else {
        args.push(OsStr::new(TARGET_NO_STD));
    };

    // we can't do this inside the if because we need to keep a reference to the string
    let feature_list = features.as_ref().map(|f| f.join(",")).unwrap_or_default();

    if let Some(features) = features {
        if !features.is_empty() {
            args.extend(as_ref![OsStr; "--features", feature_list]);
        }
    }

    cmd.args(args);
    cmd
}

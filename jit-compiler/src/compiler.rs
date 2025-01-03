use mktemp::Temp;
use std::{
    env,
    fs::{self},
    hash::{DefaultHasher, Hash, Hasher},
    path::PathBuf,
    process::Command,
    str::from_utf8,
    sync::Arc,
};

use powdr_ast::{
    analyzed::Analyzed,
    parsed::{
        display::format_type_scheme_around_name,
        types::{FunctionType, Type, TypeScheme},
    },
};
use powdr_number::{FieldElement, LargeInt};

use crate::{codegen::escape_symbol, CompiledPIL, FixedColFunction};

pub fn generate_glue_code<T: FieldElement>(
    symbols: &[(&str, String)],
    analyzed: &Analyzed<T>,
) -> Result<String, String> {
    if T::BITS > 64 {
        return Err(format!(
            "Fields with more than 64 bits not supported, requested {}",
            T::BITS,
        ));
    }
    let mut glue = String::new();
    let int_int_fun: TypeScheme = Type::Function(FunctionType {
        params: vec![Type::Int],
        value: Box::new(Type::Int),
    })
    .into();
    for (sym, access) in symbols {
        let ty = analyzed.type_of_symbol(sym);
        if ty != int_int_fun && ty.ty != Type::Col {
            return Err(format!(
                "Only (int -> int) functions and columns are supported, but requested{}",
                format_type_scheme_around_name(sym, &Some(ty)),
            ));
        }

        // TODO we should use big int instead of u64
        glue.push_str(&format!(
            r#"
            #[no_mangle]
            pub extern "C" fn {}(i: u64) -> u64 {{
                u64::try_from(({access}).call(ibig::IBig::from(i))).unwrap()
            }}
            "#,
            extern_symbol_name(sym)
        ));
    }

    Ok(format!(
        "{PREAMBLE}\n{}\n{glue}\n",
        field_specific_preamble::<T>()
    ))
}

const PREAMBLE: &str = r#"
#![allow(unused_parens, unused_variables)]

static DEGREE: std::sync::RwLock<Option<ibig::IBig>> = std::sync::RwLock::new(None);

#[no_mangle]
pub extern "C" fn __set_degree(degree: u64) {
    *DEGREE.write().unwrap() = Some(ibig::IBig::from(degree));
}

#[derive(Clone, Copy)]
struct FieldElement(u64);
impl From<FieldElement> for u64 {
    fn from(x: FieldElement) -> u64 {
        x.0
    }
}
impl From<ibig::IBig> for FieldElement {
    fn from(x: ibig::IBig) -> Self {
        FieldElement(u64::try_from(x).unwrap())
    }
}
impl From<FieldElement> for ibig::IBig {
    fn from(x: FieldElement) -> Self {
        ibig::IBig::from(x.0)
    }
}

#[derive(Clone)]
enum Callable<Args, Ret> {
    Fn(fn(Args) -> Ret),
    Closure(std::sync::Arc<dyn Fn(Args) -> Ret + Send + Sync>),
}
impl<Args, Ret> Callable<Args, Ret> {
    #[inline(always)]
    fn call(&self, args: Args) -> Ret {
        match self {
            Callable::Fn(f) => f(args),
            Callable::Closure(f) => f(args),
        }
    }
}

#[derive(Clone)]
struct PilVec<T>(std::sync::Arc<Vec<T>>);

impl<T> PilVec<T> {
    fn len(&self) -> usize {
        self.0.len()
    }
}
impl<T> From<Vec<T>> for PilVec<T> {
    fn from(v: Vec<T>) -> Self {
        PilVec(std::sync::Arc::new(v))
    }
}
impl<T> std::ops::Index<usize> for PilVec<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &T {
        &self.0[index]
    }
}
    

trait Add {
    fn add(a: Self, b: Self) -> Self;
}

impl Add for ibig::IBig {
    fn add(a: Self, b: Self) -> Self { a + b }
}

impl<T: Clone> Add for PilVec<T> {
    fn add(a: Self, b: Self) -> Self {
        // TODO for a regular "push" or array::map this is very slow.
        // We could optimize this by sharing a larger backing vector
        // across prefix instances, allowing to extend the backing vector if
        // our view is the full vector.
        PilVec(std::sync::Arc::new(
            a.0.as_ref().iter().chain(b.0.as_ref()).cloned().collect::<Vec<_>>()
        ))
    }
}

trait FromLiteral {
    fn from_u64(x: u64) -> Self;
}
impl FromLiteral for ibig::IBig {
    fn from_u64(x: u64) -> Self { ibig::IBig::from(x) }
}
impl FromLiteral for FieldElement {
    fn from_u64(x: u64) -> Self { FieldElement::from(x) }
}

"#;

fn field_specific_preamble<T: FieldElement>() -> String {
    let modulus = u64::try_from(T::modulus().to_arbitrary_integer()).unwrap();
    format!(
        r#"
        impl From<u64> for FieldElement {{
            fn from(x: u64) -> Self {{
                // TODO this is inefficient.
                FieldElement(x % {modulus}_u64)
            }}
        }}
        impl Add for FieldElement {{
            fn add(a: Self, b: Self) -> Self {{
                // TODO this is inefficient.
                Self(u64::try_from((u128::from(a.0) + u128::from(b.0)) % u128::from({modulus}_u64)).unwrap())
            }}
        }}
        "#
    )
}

const CARGO_TOML: &str = r#"
[package]
name = "powdr_jit_compiled"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["cdylib"]

[dependencies]
ibig = { version = "0.3.6", features = [], default-features = false }
lazy_static = "1.4.0"
"#;

pub struct PathInTempDir {
    #[allow(dead_code)]
    dir: Temp,
    /// The absolute path
    pub path: String,
}

fn cargo_toml() -> String {
    match env::var("POWDR_JIT_OPT_LEVEL") {
        Ok(opt_level) => {
            format!("{CARGO_TOML}\n\n[profile.release]\nopt-level = {opt_level}\n",)
        }
        Err(_) => CARGO_TOML.to_string(),
    }
}

fn hash_string(input: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    input.hash(&mut hasher);
    hasher.finish()
}

/// Compiles the given code and returns the path to the
/// temporary directory containing the compiled library
/// and the path to the compiled library.
pub fn call_cargo(code: &str) -> Result<PathInTempDir, String> {
    let tmp = mktemp::Temp::new_dir().unwrap();
    let dir = PathBuf::from(format!("../cargo_dir/{}", hash_string(code)));
    if !dir.exists() {
        log::debug!("Compiling JIT code with cargo. ({})", dir.display());
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join("Cargo.toml"), cargo_toml()).unwrap();
        fs::create_dir(dir.join("src")).unwrap();
        fs::write(dir.join("src").join("lib.rs"), code).unwrap();
        let output_asm = false;
        let out = Command::new("cargo")
            .env(
                "RUSTFLAGS",
                format!(
                    "-C target-cpu=native{}",
                    if output_asm { " --emit asm" } else { "" }
                ),
            )
            .arg("build")
            .arg("--release")
            .current_dir(dir.clone())
            .output()
            .unwrap();
        if !out.status.success() {
            if log::log_enabled!(log::Level::Debug) {
                let stderr = from_utf8(&out.stderr).unwrap_or("UTF-8 error in error message.");
                return Err(format!(
                "Rust compiler error when JIT-compiling. Will use interpreter instead. Error message:\n{stderr}."
            ));
            } else {
                return Err("Rust compiler error when JIT-compiling. Will use interpreter instead. Set log level to DEBUG for reason.".to_string());
            }
        }
        #[allow(clippy::print_stdout)]
        if output_asm {
            let asm_file = dir
                .join("target")
                .join("release")
                .join("deps")
                .join("powdr_jit_compiled.s");
            println!("{}", fs::read_to_string(&asm_file).unwrap());
        }
    } else {
        log::debug!("Reusing cached JIT code. ({})", dir.display());
    }
    let extension = if cfg!(target_os = "windows") {
        "dll"
    } else if cfg!(target_os = "macos") {
        "dylib"
    } else {
        "so"
    };
    let lib_path = dir
        .join("target")
        .join("release")
        .join(format!("libpowdr_jit_compiled.{extension}"));
    Ok(PathInTempDir {
        dir: tmp,
        path: lib_path.to_str().unwrap().to_string(),
    })
}

/// Loads the given library and functions.
pub fn load_library(path: &str, fixed_column_names: &[&str]) -> Result<CompiledPIL, String> {
    let library = Arc::new(
        unsafe { libloading::Library::new(path) }
            .map_err(|e| format!("Error loading library at {path}: {e}"))?,
    );
    let fixed_columns = fixed_column_names
        .iter()
        .map(|&sym| {
            let extern_sym = extern_symbol_name(sym);
            let function =
                *unsafe { library.get::<extern "C" fn(u64) -> u64>(extern_sym.as_bytes()) }
                    .map_err(|e| format!("Error accessing symbol {sym}: {e}"))?;
            let fun = FixedColFunction {
                library: library.clone(),
                function,
            };
            Ok((sym.to_string(), fun))
        })
        .collect::<Result<_, String>>()?;
    let set_degree_fun = *unsafe { library.get::<extern "C" fn(u64)>(b"__set_degree") }
        .map_err(|e| format!("Error accessing symbol __set_degree: {e}"))?;
    Ok(CompiledPIL {
        library,
        fixed_columns,
        set_degree_fun,
    })
}

fn extern_symbol_name(sym: &str) -> String {
    format!("extern_{}", escape_symbol(sym))
}

mod common;

use common::{verify_riscv_asm_file, verify_riscv_asm_string};
use mktemp::Temp;
use powdr_number::{BabyBearField, FieldElement, GoldilocksField, KnownField};
use powdr_pipeline::{
    test_util::{run_pilcom_with_backend_variant, BackendVariant},
    Pipeline,
};
use std::path::{Path, PathBuf};
use test_log::test;

use powdr_riscv::{
    continuations::{rust_continuations, rust_continuations_dry_run},
    CompilerOptions, RuntimeLibs,
};

/// Compiles and runs a rust program with continuations, runs the full
/// witness generation & verifies it using Pilcom.
pub fn test_continuations(case: &str) {
    let temp_dir = Temp::new_dir().unwrap();

    let executable = powdr_riscv::compile_rust_crate_to_riscv(
        &format!("tests/riscv_data/{case}/Cargo.toml"),
        &temp_dir,
        None,
    );

    // Test continuations from ELF file.
    let powdr_asm = powdr_riscv::elf::translate(
        &executable,
        CompilerOptions::new_gl()
            .with_poseidon()
            .with_continuations(),
    );
    run_continuations_test(case, powdr_asm);
}

fn run_continuations_test(case: &str, powdr_asm: String) {
    // Manually create tmp dir, so that it is the same in all chunks.
    let tmp_dir = mktemp::Temp::new_dir().unwrap();

    let mut pipeline = Pipeline::<GoldilocksField>::default()
        .from_asm_string(powdr_asm.clone(), Some(PathBuf::from(&case)))
        .with_prover_inputs(Default::default())
        .with_output(tmp_dir.to_path_buf(), false);
    let pipeline_callback = |pipeline: Pipeline<GoldilocksField>| -> Result<(), ()> {
        run_pilcom_with_backend_variant(pipeline, BackendVariant::Composite).unwrap();

        Ok(())
    };
    let bootloader_inputs =
        rust_continuations_dry_run::<GoldilocksField>(&mut pipeline, Default::default());
    rust_continuations::<GoldilocksField, _, _>(pipeline, pipeline_callback, bootloader_inputs)
        .unwrap();
}

#[test]
#[ignore = "Too slow"]
// TODO: this a temporary test so we at least go through the bn254 code path.
// Once we fully support it, the whole test suite here should probably be modified to take a generic field, and this can be removed.
fn bn254_sanity_check() {
    let case = "trivial";

    let temp_dir = Temp::new_dir().unwrap();
    let executable = powdr_riscv::compile_rust_crate_to_riscv(
        &format!("tests/riscv_data/{case}/Cargo.toml"),
        &temp_dir,
        None,
    );

    log::info!("Verifying {case} converted from ELF file");
    let options = CompilerOptions::new(KnownField::Bn254Field, RuntimeLibs::new(), false);
    let from_elf = powdr_riscv::elf::translate(&executable, options);

    let temp_dir = mktemp::Temp::new_dir().unwrap().release();

    let file_name = format!("{case}_from_elf.asm");
    let mut pipeline = Pipeline::default()
        .with_output(temp_dir.to_path_buf(), false)
        .from_asm_string(from_elf, Some(PathBuf::from(file_name)));

    let analyzed = pipeline.compute_analyzed_asm().unwrap().clone();
    powdr_riscv_executor::execute_ast(
        &analyzed,
        Default::default(),
        pipeline.data_callback().unwrap(),
        // Assume the RISC-V program was compiled without a bootloader, otherwise this will fail.
        &[],
        usize::MAX,
        powdr_riscv_executor::ExecMode::Fast,
        Default::default(),
    );
    run_pilcom_with_backend_variant(pipeline, BackendVariant::Composite).unwrap();
}

#[test]
#[ignore = "Too slow"]
fn trivial() {
    let case = "trivial";
    verify_riscv_crate(case, Default::default())
}

#[test]
#[ignore = "Too slow"]
fn halt() {
    let case = "halt";
    verify_riscv_crate(case, Default::default())
}

#[test]
#[ignore = "Too slow"]
fn zero_with_values() {
    let case = "zero_with_values";
    verify_riscv_crate(case, Default::default())
}

#[test]
#[ignore = "Too slow"]
fn runtime_poseidon_gl() {
    let case = "poseidon_gl_via_coprocessor";
    let options = CompilerOptions::new_gl().with_poseidon();
    verify_riscv_crate_gl_with_options(case, Default::default(), options);
}

#[test]
#[ignore = "Too slow"]
fn sum() {
    let case = "sum";
    verify_riscv_crate(case, &[16u64, 4, 1, 2, 8, 5]);
}

#[test]
#[ignore = "Too slow"]
fn byte_access() {
    let case = "byte_access";
    verify_riscv_crate(case, &[0u64, 104, 707]);
}

#[test]
#[ignore = "Too slow"]
fn double_word() {
    let case = "double_word";
    let a0 = 0x01000000u32;
    let a1 = 0x010000ffu32;
    let b0 = 0xf100b00fu32;
    let b1 = 0x0100f0f0u32;
    let c = ((a0 as u64) | ((a1 as u64) << 32)).wrapping_mul((b0 as u64) | ((b1 as u64) << 32));

    let v = [
        a0,
        a1,
        b0,
        b1,
        (c & 0xffffffff) as u32,
        ((c >> 32) & 0xffffffff) as u32,
    ];
    verify_riscv_crate_bb_with_data(case, Default::default(), vec![(1, v)]);
    verify_riscv_crate_gl_with_data(case, Default::default(), vec![(1, v)]);
}

#[test]
#[ignore = "Too slow"]
fn memfuncs() {
    let case = "memfuncs";
    verify_riscv_crate(case, Default::default());
}

#[test]
#[ignore = "Too slow"]
fn keccak() {
    let case = "keccak";
    verify_riscv_crate(case, Default::default());
}

#[cfg(feature = "estark-polygon")]
#[test]
#[ignore = "Too slow"]
fn vec_median_estark_polygon() {
    let case = "vec_median";
    verify_riscv_crate(case, &[5u64, 11, 15, 75, 6, 5, 1, 4, 7, 3, 2, 9, 2]);
}

#[test]
#[ignore = "Too slow"]
fn vec_median() {
    let case = "vec_median";
    verify_riscv_crate(case, &[5, 11, 15, 75, 6, 5, 1, 4, 7, 3, 2, 9, 2]);
}

#[test]
#[ignore = "Too slow"]
fn password() {
    let case = "password_checker";
    verify_riscv_crate(case, Default::default());
}

#[test]
#[ignore = "Too slow"]
fn std_hello_world() {
    let case = "std_hello_world";
    verify_riscv_crate(case, Default::default());
}

#[test]
#[ignore = "Too slow"]
fn function_pointer() {
    let case = "function_pointer";
    verify_riscv_crate(case, &[2734, 735, 1999]);
}

#[test]
#[ignore = "Too slow"]
fn runtime_ec_double() {
    let case = "ec_double";
    let options = CompilerOptions::new_gl().with_arith();
    verify_riscv_crate_gl_with_options(case, vec![], options);
}

#[test]
#[ignore = "Too slow"]
fn runtime_ec_add() {
    let case = "ec_add";
    let options = CompilerOptions::new_gl().with_arith();
    verify_riscv_crate_gl_with_options(case, vec![], options);
}

#[test]
#[ignore = "Too slow"]
fn runtime_affine_256() {
    let case = "affine_256";
    let options = CompilerOptions::new_gl().with_arith();
    verify_riscv_crate_gl_with_options(case, vec![], options);
}

#[test]
#[ignore = "Too slow"]
fn runtime_modmul_256() {
    let case = "modmul_256";
    let options = CompilerOptions::new_gl().with_arith();
    verify_riscv_crate_gl_with_options(case, vec![], options);
}

/*
mstore(0, 666)
return(0, 32)
*/
#[cfg(feature = "complex-tests")]
static BYTECODE: &str = "61029a60005260206000f3";

#[cfg(feature = "complex-tests")]
#[ignore = "Too slow"]
#[test]
fn evm() {
    let case = "evm";
    let bytes = hex::decode(BYTECODE).unwrap();

    verify_riscv_crate_bb_with_data(case, vec![], vec![(666, bytes.clone())]);
    verify_riscv_crate_gl_with_data(case, vec![], vec![(666, bytes)]);
}

#[ignore = "Too slow"]
#[test]
fn sum_serde() {
    let case = "sum_serde";

    let data: Vec<u32> = vec![1, 2, 8, 5];
    let answer = data.iter().sum::<u32>();

    verify_riscv_crate_bb_with_data(case, vec![answer.into()], vec![(42, data.clone())]);
    verify_riscv_crate_gl_with_data(case, vec![answer.into()], vec![(42, data)]);
}

#[test]
#[ignore = "Too slow"]
fn read_slice() {
    read_slice_with_options::<BabyBearField>(CompilerOptions::new_bb());
    read_slice_with_options::<GoldilocksField>(CompilerOptions::new_gl());
}

fn read_slice_with_options<T: FieldElement>(options: CompilerOptions) {
    let case = "read_slice";
    let temp_dir = Temp::new_dir().unwrap();
    let executable = powdr_riscv::compile_rust_crate_to_riscv(
        &format!("tests/riscv_data/{case}/Cargo.toml"),
        &temp_dir,
        None,
    );
    let powdr_asm = powdr_riscv::elf::translate(&executable, options);

    let data: Vec<u32> = vec![];
    let answer = data.iter().sum::<u32>();

    use std::collections::BTreeMap;
    let d: BTreeMap<u32, Vec<T>> = vec![(
        42,
        vec![
            0u32.into(),
            1u32.into(),
            2u32.into(),
            3u32.into(),
            4u32.into(),
            5u32.into(),
            6u32.into(),
            7u32.into(),
        ],
    )]
    .into_iter()
    .collect();

    let mut pipeline = Pipeline::<T>::default()
        .from_asm_string(powdr_asm, Some(PathBuf::from(case)))
        .with_prover_inputs(vec![answer.into()])
        .with_prover_dict_inputs(d);

    pipeline.compute_witness().unwrap();
}

#[ignore = "Too slow"]
#[test]
fn two_sums_serde() {
    let case = "two_sums_serde";

    let data1: Vec<u32> = vec![1, 2, 8, 5];
    let data2 = data1.clone();

    verify_riscv_crate_bb_with_data(case, vec![], vec![(42, data1.clone()), (43, data2.clone())]);
    verify_riscv_crate_gl_with_data(case, vec![], vec![(42, data1), (43, data2)]);
}

const DISPATCH_TABLE_S: &str = "tests/riscv_data/dispatch_table/dispatch_table.s";

/// Tests that the dispatch table is correctly relocated when PIE is enabled.
#[ignore = "Too slow"]
#[test]
fn dispatch_table_pie_relocation() {
    verify_riscv_asm_file(Path::new(DISPATCH_TABLE_S), CompilerOptions::new_bb(), true);
    verify_riscv_asm_file(Path::new(DISPATCH_TABLE_S), CompilerOptions::new_gl(), true);
}

/// Tests that the dispatch table is correctly relocated when PIE is disabled.
#[ignore = "Too slow"]
#[test]
fn dispatch_table_static_relocation() {
    verify_riscv_asm_file(
        Path::new(DISPATCH_TABLE_S),
        CompilerOptions::new_bb(),
        false,
    );
    verify_riscv_asm_file(
        Path::new(DISPATCH_TABLE_S),
        CompilerOptions::new_gl(),
        false,
    );
}

#[test]
#[ignore = "Too slow"]
#[should_panic(expected = "reached a fail instruction")]
fn print() {
    let case = "print";
    verify_riscv_crate(case, &[0]);
}

#[test]
#[ignore = "Too slow"]
// Test compiling a program with features.
// If no features are enabled, the expected input is 0.
// The test program has two features, "add_two" and "add_three".
// Enabling these features adds 2 and 3 to the expected input, respectively.
fn features() {
    features_with_options::<BabyBearField>(CompilerOptions::new_bb());
    features_with_options::<GoldilocksField>(CompilerOptions::new_gl());
}

fn features_with_options<T: FieldElement>(options: CompilerOptions) {
    let case = "features";

    let temp_dir = Temp::new_dir().unwrap();

    // no features
    let expected = 0;
    let executable = powdr_riscv::compile_rust_crate_to_riscv(
        &format!("tests/riscv_data/{case}/Cargo.toml"),
        &temp_dir,
        None,
    );

    log::info!("Verifying {case} converted from ELF file");
    let from_elf = powdr_riscv::elf::translate(&executable, options.clone());
    verify_riscv_asm_string::<T, usize>(
        &format!("{case}_from_elf.asm"),
        &from_elf,
        &[expected.into()],
        None,
    );

    // "add_two"
    let expected = 2;
    let executable = powdr_riscv::compile_rust_crate_to_riscv(
        &format!("tests/riscv_data/{case}/Cargo.toml"),
        &temp_dir,
        Some(vec!["add_two".to_string()]),
    );

    log::info!("Verifying {case} converted from ELF file");
    let from_elf = powdr_riscv::elf::translate(&executable, options.clone());
    verify_riscv_asm_string::<T, usize>(
        &format!("{case}_from_elf.asm"),
        &from_elf,
        &[expected.into()],
        None,
    );

    // "add_two" and "add_three"
    let expected = 5;
    let executable = powdr_riscv::compile_rust_crate_to_riscv(
        &format!("tests/riscv_data/{case}/Cargo.toml"),
        &temp_dir,
        Some(vec!["add_two".to_string(), "add_three".to_string()]),
    );

    log::info!("Verifying {case} converted from ELF file");
    let from_elf = powdr_riscv::elf::translate(&executable, options);
    verify_riscv_asm_string::<T, usize>(
        &format!("{case}_from_elf.asm"),
        &from_elf,
        &[expected.into()],
        None,
    );
}

#[test]
#[ignore = "Too slow"]
fn many_chunks_dry() {
    // Compiles and runs the many_chunks example with continuations, just computing
    // and validating the bootloader inputs.
    // Doesn't do a full witness generation, verification, or proving.
    let case = "many_chunks";
    let temp_dir = Temp::new_dir().unwrap();
    let executable = powdr_riscv::compile_rust_crate_to_riscv(
        &format!("tests/riscv_data/{case}/Cargo.toml"),
        &temp_dir,
        None,
    );
    let powdr_asm = powdr_riscv::elf::translate(
        &executable,
        CompilerOptions::new_gl()
            .with_poseidon()
            .with_continuations(),
    );

    let mut pipeline = Pipeline::default()
        .from_asm_string(powdr_asm, Some(PathBuf::from(case)))
        .with_prover_inputs(Default::default());
    rust_continuations_dry_run::<GoldilocksField>(&mut pipeline, Default::default());
}

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct Point {
    x: i32,
    y: i32,
}

#[test]
#[ignore = "Too slow"]
fn output_syscall() {
    output_syscall_with_options::<BabyBearField>(CompilerOptions::new_bb());
    output_syscall_with_options::<GoldilocksField>(CompilerOptions::new_gl());
}

fn output_syscall_with_options<T: FieldElement>(options: CompilerOptions) {
    let case = "output";
    let temp_dir = Temp::new_dir().unwrap();
    let executable = powdr_riscv::compile_rust_crate_to_riscv(
        &format!("tests/riscv_data/{case}/Cargo.toml"),
        &temp_dir,
        None,
    );
    let powdr_asm = powdr_riscv::elf::translate(&executable, options);

    let inputs = vec![1u32, 2, 3].into_iter().map(T::from).collect();
    let mut pipeline = Pipeline::<T>::default()
        .from_asm_string(powdr_asm, Some(PathBuf::from(case)))
        .with_prover_inputs(inputs);

    pipeline.compute_witness().unwrap();

    let ctx = &pipeline.host_context();
    // Need to put the lock in a separate scope, so that it is dropped before the next read.
    {
        let fs = &ctx.file_data.lock().unwrap();
        assert_eq!(fs[&42], vec![1]);
        assert_eq!(fs[&43], vec![1, 2, 3]);
    }

    let p: Point = ctx.read(44).unwrap();
    assert_eq!(p.x, 1);
    assert_eq!(p.y, 2);
}

#[test]
#[ignore = "Too slow"]
fn many_chunks() {
    test_continuations("many_chunks")
}

#[test]
#[ignore = "Too slow"]
fn many_chunks_memory() {
    test_continuations("many_chunks_memory")
}

fn verify_riscv_crate(case: &str, inputs: &[u64]) {
    verify_riscv_crate_bb(case, inputs.iter().map(|&x| x.into()).collect());
    verify_riscv_crate_gl(case, inputs.iter().map(|&x| x.into()).collect());
}

fn verify_riscv_crate_bb(case: &str, inputs: Vec<BabyBearField>) {
    let options = CompilerOptions::new_bb();
    verify_riscv_crate_impl::<BabyBearField, ()>(case, options, inputs, None)
}

fn verify_riscv_crate_gl(case: &str, inputs: Vec<GoldilocksField>) {
    let options = CompilerOptions::new_gl();
    verify_riscv_crate_impl::<GoldilocksField, ()>(case, options, inputs, None)
}

fn verify_riscv_crate_gl_with_options(
    case: &str,
    inputs: Vec<GoldilocksField>,
    options: CompilerOptions,
) {
    verify_riscv_crate_impl::<GoldilocksField, ()>(case, options, inputs, None)
}

fn verify_riscv_crate_bb_with_data<S: serde::Serialize + Send + Sync + 'static>(
    case: &str,
    inputs: Vec<BabyBearField>,
    data: Vec<(u32, S)>,
) {
    let options = CompilerOptions::new_bb();
    verify_riscv_crate_impl(case, options, inputs, Some(data))
}

fn verify_riscv_crate_gl_with_data<S: serde::Serialize + Send + Sync + 'static>(
    case: &str,
    inputs: Vec<GoldilocksField>,
    data: Vec<(u32, S)>,
) {
    let options = CompilerOptions::new_gl();
    verify_riscv_crate_impl(case, options, inputs, Some(data))
}

fn verify_riscv_crate_impl<T: FieldElement, S: serde::Serialize + Send + Sync + 'static>(
    case: &str,
    options: CompilerOptions,
    inputs: Vec<T>,
    data: Option<Vec<(u32, S)>>,
) {
    let temp_dir = Temp::new_dir().unwrap();
    let executable = powdr_riscv::compile_rust_crate_to_riscv(
        &format!("tests/riscv_data/{case}/Cargo.toml"),
        &temp_dir,
        None,
    );

    log::info!("Verifying {case}");
    let from_elf = powdr_riscv::elf::translate(&executable, options);
    verify_riscv_asm_string(
        &format!("{case}_from_elf.asm"),
        &from_elf,
        &inputs,
        data.as_deref(),
    );
}

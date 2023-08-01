use compiler::verify_asm_string;
use number::{Bn254Field, FieldElement, GoldilocksField};
use std::fs;
use test_log::test;

fn verify_asm<T: FieldElement>(file_name: &str, inputs: Vec<T>) {
    let contents = fs::read_to_string(format!("../test_data/asm/{file_name}")).unwrap();
    verify_asm_string(file_name, &contents, inputs)
}

#[cfg(feature = "halo2")]
fn gen_halo2_proof(file_name: &str, inputs: Vec<Bn254Field>) {
    compiler::compile_pil_or_asm(
        format!("../test_data/asm/{file_name}").as_str(),
        inputs,
        &mktemp::Temp::new_dir().unwrap(),
        true,
        Some(backend::BackendType::Halo2),
    );
}

#[cfg(not(feature = "halo2"))]
fn gen_halo2_proof(_file_name: &str, _inputs: Vec<Bn254Field>) {}

fn slice_to_vec<T: FieldElement>(arr: &[i32]) -> Vec<T> {
    arr.iter().cloned().map(|x| x.into()).collect()
}

#[test]
fn simple_sum_asm() {
    let f = "simple_sum.asm";
    let i = [16, 4, 1, 2, 8, 5];
    verify_asm::<GoldilocksField>(f, slice_to_vec(&i));
    gen_halo2_proof(f, slice_to_vec(&i));
}

#[test]
fn palindrome() {
    let f = "palindrome.asm";
    let i = [7, 1, 7, 3, 9, 3, 7, 1];
    verify_asm::<GoldilocksField>(f, slice_to_vec(&i));
    gen_halo2_proof(f, slice_to_vec(&i));
}

#[test]
fn test_mem_read_write() {
    let f = "mem_read_write.asm";
    verify_asm::<GoldilocksField>(f, Default::default());
    gen_halo2_proof(f, Default::default());
}

#[test]
fn test_multi_assign() {
    let f = "multi_assign.asm";
    let i = [7];
    verify_asm::<GoldilocksField>(f, slice_to_vec(&i));
    gen_halo2_proof(f, slice_to_vec(&i));
}

#[test]
fn test_bit_access() {
    let f = "bit_access.asm";
    let i = [20];
    verify_asm::<GoldilocksField>(f, slice_to_vec(&i));
    gen_halo2_proof(f, slice_to_vec(&i));
}

#[test]
fn functional_instructions() {
    let f = "functional_instructions.asm";
    let i = [20];
    verify_asm::<GoldilocksField>(f, slice_to_vec(&i));
    gen_halo2_proof(f, slice_to_vec(&i));
}

#[test]
fn full_pil_constant() {
    let f = "full_pil_constant.asm";
    verify_asm::<GoldilocksField>(f, Default::default());
    gen_halo2_proof(f, Default::default());
}

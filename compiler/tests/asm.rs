use compiler::{compile_pil_or_asm, verify_asm_string, Backend};
use number::{Bn254Field, FieldElement, GoldilocksField};
use std::fs;
use test_log::test;

fn verify_asm<T: FieldElement>(
    file_name: &str,
    inputs: Vec<T>,
    public_inputs: Vec<T>,
    public_outputs: Vec<T>,
) {
    let contents = fs::read_to_string(format!("../test_data/asm/{file_name}")).unwrap();
    let publics = [public_inputs, public_outputs].concat();
    assert!(verify_asm_string(file_name, &contents, inputs, publics).is_ok());
}

fn halo2_proof(file_name: &str, inputs: Vec<Bn254Field>, public_inputs: Vec<Bn254Field>) {
    compile_pil_or_asm(
        format!("../test_data/asm/{file_name}").as_str(),
        inputs,
        public_inputs,
        &mktemp::Temp::new_dir().unwrap(),
        true,
        Some(Backend::Halo2),
    );
}

fn slice_to_vec<T: FieldElement>(arr: &[i32]) -> Vec<T> {
    arr.iter().cloned().map(|x| x.into()).collect()
}

#[test]
fn simple_sum_asm() {
    let f = "simple_sum.asm";
    let i = [16, 4, 1, 2, 8, 5];
    verify_asm::<GoldilocksField>(f, slice_to_vec(&i), vec![], vec![]);
    halo2_proof(f, slice_to_vec(&i), vec![]);
}

#[test]
fn palindrome() {
    let f = "palindrome.asm";
    let i = [7, 1, 7, 3, 9, 3, 7, 1];
    verify_asm::<GoldilocksField>(f, slice_to_vec(&i), vec![], vec![]);
    halo2_proof(f, slice_to_vec(&i), vec![]);
}

#[test]
fn test_mem_read_write() {
    let f = "mem_read_write.asm";
    verify_asm::<GoldilocksField>(f, Default::default(), vec![], vec![]);
    halo2_proof(f, Default::default(), vec![]);
}

#[test]
fn test_multi_assign() {
    let f = "multi_assign.asm";
    let i = [7];
    verify_asm::<GoldilocksField>(f, slice_to_vec(&i), vec![], vec![]);
    halo2_proof(f, slice_to_vec(&i), vec![]);
}

#[test]
fn test_bit_access() {
    let f = "bit_access.asm";
    let i = [20];
    verify_asm::<GoldilocksField>(f, slice_to_vec(&i), vec![], vec![]);
    halo2_proof(f, slice_to_vec(&i), vec![]);
}

#[test]
fn functional_instructions() {
    let f = "functional_instructions.asm";
    let i = [20];
    verify_asm::<GoldilocksField>(f, slice_to_vec(&i), vec![], vec![]);
    halo2_proof(f, slice_to_vec(&i), vec![]);
}

#[test]
fn vm_to_block() {
    let f = "vm_to_block.asm";
    let i = [];
    verify_asm::<GoldilocksField>(f, slice_to_vec(&i), vec![1.into()], vec![]);
    halo2_proof(f, slice_to_vec(&i), vec![]);
}

#[test]
#[ignore = "this fails in witness generation"]
fn vm_to_vm() {
    let f = "vm_to_vm.asm";
    let i = [];
    verify_asm::<GoldilocksField>(f, slice_to_vec(&i), vec![], vec![]);
    halo2_proof(f, slice_to_vec(&i), vec![]);
}

#[test]
fn full_pil_constant() {
    let f = "full_pil_constant.asm";
    verify_asm::<GoldilocksField>(f, Default::default(), vec![], vec![]);
    halo2_proof(f, Default::default(), vec![]);
}

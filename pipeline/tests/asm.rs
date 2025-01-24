use std::collections::BTreeMap;

use powdr_executor::constant_evaluator;
use powdr_linker::{LinkerMode, LinkerParams};
use powdr_number::{BabyBearField, FieldElement, GoldilocksField, Mersenne31Field};
use powdr_pipeline::{
    test_util::{
        asm_string_to_pil, make_prepared_pipeline, make_simple_prepared_pipeline,
        regular_test_all_fields, regular_test_gl, resolve_test_file, test_mock_backend,
        test_pilcom, test_plonky3_pipeline, BackendVariant,
    },
    Pipeline,
};
use test_log::test;

fn slice_to_vec<T: FieldElement>(arr: &[i32]) -> Vec<T> {
    arr.iter().cloned().map(|x| x.into()).collect()
}

#[test]
fn sqrt_asm() {
    let f = "asm/sqrt.asm";
    let i = [3];
    let pipeline: Pipeline<GoldilocksField> =
        make_prepared_pipeline(f, slice_to_vec(&i), vec![], LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn block_machine_exact_number_of_rows_asm() {
    let f = "asm/block_machine_exact_number_of_rows.asm";
    // This test needs machines to be of unequal length. Also, this is mostly testing witgen, so
    // we just run one backend that supports variable-length machines.
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn challenges_asm() {
    let f = "asm/challenges.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline.clone());
    test_plonky3_pipeline(pipeline);
}

#[test]
fn simple_sum_asm() {
    let f = "asm/simple_sum.asm";
    let i = [16, 4, 1, 2, 8, 5];
    regular_test_all_fields(f, &i);
}

#[test]
#[should_panic = "Witness generation failed."]
fn secondary_machine_plonk() {
    // Currently fails because no copy constraints are expressed in PIL yet.
    let f = "asm/secondary_machine_plonk.asm";
    regular_test_all_fields(f, &[]);
}

#[test]
fn secondary_block_machine_add2() {
    let f = "asm/secondary_block_machine_add2.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn second_phase_hint() {
    let f = "asm/second_phase_hint.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline.clone());
    test_plonky3_pipeline(pipeline);
}

#[test]
fn mem_write_once() {
    let f = "asm/mem_write_once.asm";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn mem_write_once_external_write() {
    let f = "asm/mem_write_once_external_write.asm";
    let mut mem = vec![GoldilocksField::from(0); 256];
    mem[17] = GoldilocksField::from(42);
    mem[62] = GoldilocksField::from(123);
    mem[255] = GoldilocksField::from(-1);
    let mut pipeline = Pipeline::default()
        .with_tmp_output()
        .from_file(resolve_test_file(f))
        .add_external_witness_values(vec![("main_memory::value".to_string(), mem)])
        .with_linker_params(LinkerParams {
            degree_mode: powdr_linker::DegreeMode::Monolithic,
            ..Default::default()
        });
    pipeline.compute_witness().unwrap();
    test_pilcom(pipeline.clone());
    test_mock_backend(pipeline);
}

#[test]
fn block_machine_cache_miss() {
    let f = "asm/block_machine_cache_miss.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn palindrome() {
    let f = "asm/palindrome.asm";
    let i = [7, 1, 7, 3, 9, 3, 7, 1];
    let pipeline: Pipeline<GoldilocksField> =
        make_prepared_pipeline(f, slice_to_vec(&i), vec![], LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn single_function_vm() {
    let f = "asm/single_function_vm.asm";
    regular_test_all_fields(f, &[]);
}

#[test]
fn empty() {
    let f = "asm/empty.asm";
    regular_test_all_fields(f, &[]);
}

#[test]
// TODO: https://github.com/powdr-labs/powdr/issues/2292
#[should_panic = "No column references found: []"]
fn single_operation() {
    let f = "asm/single_operation.asm";
    regular_test_all_fields(f, &[]);
}

#[test]
fn empty_vm() {
    let f = "asm/empty_vm.asm";
    regular_test_all_fields(f, &[]);
}

#[test]
fn vm_to_block_unique_interface() {
    let f = "asm/vm_to_block_unique_interface.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn vm_to_block_to_block() {
    let f = "asm/vm_to_block_to_block.asm";
    regular_test_gl(f, &[]);
}

#[test]
fn block_to_block() {
    let f = "asm/block_to_block.asm";
    regular_test_all_fields(f, &[]);
}

#[test]
fn block_to_block_empty_submachine() {
    let f = "asm/block_to_block_empty_submachine.asm";
    let mut pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);

    let witness = pipeline.compute_witness().unwrap();
    let arith_size = witness
        .iter()
        .find(|(k, _)| k == "main_arith::x")
        .unwrap()
        .1
        .len();
    assert_eq!(arith_size, 0);

    test_mock_backend(pipeline.clone());
    test_plonky3_pipeline(pipeline);
}

#[test]
fn block_to_block_with_bus_monolithic() {
    let f = "asm/block_to_block_with_bus.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline.clone());
    test_plonky3_pipeline(pipeline);
    let pipeline = make_simple_prepared_pipeline::<BabyBearField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline.clone());
    test_plonky3_pipeline(pipeline);
    let pipeline = make_simple_prepared_pipeline::<Mersenne31Field>(f, LinkerMode::Bus);
    test_mock_backend(pipeline.clone());
    test_plonky3_pipeline(pipeline);
}

#[test]
fn block_to_block_with_bus_different_sizes() {
    let f = "asm/block_to_block_with_bus_different_sizes.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline.clone());
    test_plonky3_pipeline(pipeline);
}

#[cfg(feature = "halo2")]
#[test]
#[should_panic = "called `Result::unwrap()` on an `Err` value: [\"Circuit was not satisfied\"]"]
fn block_to_block_with_bus_composite() {
    // This currently fails because of #1608 ("Emulate shared challenges in CompositeBackend"):
    // - `CompositeBackend::prove` correctly gets the challenges of each machine and accumulates them.
    //   The shared challenges are used during witness generation.
    // - `CompositeBackend::verify` simply verifies each machine proof independently, using the local
    //   challenges. As a result, the challenges during verification differ and the constraints are
    //   not satisfied.

    use powdr_number::Bn254Field;
    use powdr_pipeline::test_util::test_halo2_with_backend_variant;
    let f = "asm/block_to_block_with_bus.asm";
    let pipeline = make_simple_prepared_pipeline::<Bn254Field>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);

    // Native linker mode, because bus constraints are exponential in Halo2
    let pipeline = make_simple_prepared_pipeline(f, LinkerMode::Native);
    test_halo2_with_backend_variant(pipeline, BackendVariant::Composite);
}

#[test]
fn vm_instr_param_mapping() {
    let f = "asm/vm_instr_param_mapping.asm";
    regular_test_all_fields(f, &[]);
}

#[test]
fn vm_to_block_multiple_interfaces() {
    let f = "asm/vm_to_block_multiple_interfaces.asm";
    regular_test_all_fields(f, &[]);
}

#[test]
fn vm_to_vm() {
    let f = "asm/vm_to_vm.asm";
    regular_test_all_fields(f, &[]);
}

#[test]
#[ignore = "Too slow"]
fn vm_to_vm_dynamic_trace_length() {
    let f = "asm/vm_to_vm_dynamic_trace_length.asm";
    regular_test_gl(f, &[]);
}

#[test]
fn vm_to_vm_to_block() {
    let f = "asm/vm_to_vm_to_block.asm";
    regular_test_all_fields(f, &[]);
}

#[test]
fn vm_to_block_array() {
    let f = "asm/vm_to_block_array.asm";
    regular_test_all_fields(f, &[]);
}

#[test]
#[ignore = "Too slow"]
fn dynamic_vadcop() {
    let f = "asm/dynamic_vadcop.asm";

    let mut pipeline_gl = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    let witness = pipeline_gl.compute_witness().unwrap();
    let witness_by_name = witness
        .iter()
        .map(|(k, v)| (k.as_str(), v))
        .collect::<BTreeMap<_, _>>();

    // Spot-check some witness columns to have the expected length.
    assert_eq!(witness_by_name["main::X"].len(), 128);
    assert_eq!(witness_by_name["main_arith::y"].len(), 32);
    assert_eq!(witness_by_name["main_memory::m_addr"].len(), 32);

    test_mock_backend(pipeline_gl.clone());
    test_plonky3_pipeline(pipeline_gl);
}

#[test]
fn vm_to_vm_to_vm() {
    let f = "asm/vm_to_vm_to_vm.asm";
    regular_test_all_fields(f, &[]);
}

#[test]
fn vm_to_block_multiple_links() {
    let f = "asm/permutations/vm_to_block_multiple_links.asm";
    regular_test_all_fields(f, &[]);
}

#[test]
fn mem_read_write() {
    let f = "asm/mem_read_write.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn mem_read_write_no_memory_accesses() {
    let f = "asm/mem_read_write_no_memory_accesses.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn mem_read_write_with_bootloader() {
    let f = "asm/mem_read_write_with_bootloader.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn mem_read_write_large_diffs() {
    let f = "asm/mem_read_write_large_diffs.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn multi_assign() {
    let f = "asm/multi_assign.asm";
    let i = [7];
    regular_test_all_fields(f, &i);
}

#[test]
fn multi_return() {
    let f = "asm/multi_return.asm";
    regular_test_all_fields(f, Default::default());
}

#[test]
#[should_panic = "called `Result::unwrap()` on an `Err` value: [\"Assignment register `Z` is incompatible with `square_and_double(3)`. Try using `<==` with no explicit assignment registers.\", \"Assignment register `Y` is incompatible with `square_and_double(3)`. Try using `<==` with no explicit assignment registers.\"]"]
fn multi_return_wrong_assignment_registers() {
    let f = "asm/multi_return_wrong_assignment_registers.asm";
    regular_test_all_fields(f, Default::default());
}

#[test]
#[should_panic = "Result::unwrap()` on an `Err` value: [\"Mismatched number of registers for assignment A, B <=Y= square_and_double(3);\"]"]
fn multi_return_wrong_assignment_register_length() {
    let f = "asm/multi_return_wrong_assignment_register_length.asm";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn bit_access() {
    let f = "asm/bit_access.asm";
    let i = [20];
    let pipeline: Pipeline<GoldilocksField> =
        make_prepared_pipeline(f, slice_to_vec(&i), vec![], LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn sqrt() {
    let f = "asm/sqrt.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn functional_instructions() {
    let f = "asm/functional_instructions.asm";
    let i = [20];
    let pipeline: Pipeline<GoldilocksField> =
        make_prepared_pipeline(f, slice_to_vec(&i), vec![], LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn full_pil_constant() {
    let f = "asm/full_pil_constant.asm";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn intermediate_nested() {
    let f = "asm/intermediate_nested.asm";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn pil_at_module_level() {
    let f = "asm/pil_at_module_level.asm";
    regular_test_all_fields(f, Default::default());
}

#[cfg(feature = "estark-starky")]
#[test]
fn read_poly_files() {
    use powdr_backend::BackendType;
    use powdr_executor::constant_evaluator::get_uniquely_sized;
    use powdr_linker::{DegreeMode, LinkerParams};
    use powdr_number::Bn254Field;
    use powdr_pipeline::util::{FixedPolySet, PolySet, WitnessPolySet};

    let asm_files = ["asm/vm_to_block_unique_interface.asm", "asm/empty.asm"];
    for f in asm_files {
        let tmp_dir = mktemp::Temp::new_dir().unwrap();

        // generate poly files
        let mut pipeline = Pipeline::<Bn254Field>::default()
            .from_file(resolve_test_file(f))
            .with_output(tmp_dir.to_path_buf(), true)
            .with_linker_params(LinkerParams {
                degree_mode: DegreeMode::Monolithic,
                ..Default::default()
            })
            .with_backend(BackendType::EStarkDump, None);
        pipeline.compute_witness().unwrap();
        let pil = pipeline.compute_optimized_pil().unwrap();
        pipeline.compute_proof().unwrap();

        // check fixed cols (may have no fixed cols)
        let fixed = FixedPolySet::<Bn254Field>::read(tmp_dir.as_path()).unwrap();
        let fixed = get_uniquely_sized(&fixed).unwrap();
        if !fixed.is_empty() {
            assert_eq!(pil.degree(), fixed[0].1.len() as u64);
        }

        // check witness cols (examples assumed to have at least one witness col)
        let witness = WitnessPolySet::<Bn254Field>::read(tmp_dir.as_path()).unwrap();
        assert_eq!(pil.degree(), witness[0].1.len() as u64);
    }
}

#[test]
fn enum_in_asm() {
    let f = "asm/enum_in_asm.asm";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn pass_range_constraints() {
    let f = "asm/pass_range_constraints.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn side_effects() {
    let f = "asm/side_effects.asm";
    regular_test_gl(f, Default::default());
}

#[test]
fn multiple_signatures() {
    let f = "asm/multiple_signatures.asm";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn permutation_simple() {
    let f = "asm/permutations/simple.asm";
    regular_test_gl(f, Default::default());
}

#[test]
fn permutation_to_block() {
    let f = "asm/permutations/vm_to_block.asm";
    regular_test_gl(f, Default::default());
}

#[test]
#[should_panic = "Column main_bin::pc is not stackable in a 1-row block, conflict in rows 0 and 1"]
fn permutation_to_vm() {
    // TODO: witgen issue: Machine incorrectly detected as block machine.
    let f = "asm/permutations/vm_to_vm.asm";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn permutation_to_block_to_block() {
    let f = "asm/permutations/block_to_block.asm";
    regular_test_gl(f, Default::default());
}

#[test]
#[should_panic = "has incoming permutations but doesn't declare call_selectors"]
fn permutation_incoming_needs_selector() {
    let f = "asm/permutations/incoming_needs_selector.asm";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn call_selectors_with_no_permutation() {
    let f = "asm/permutations/call_selectors_with_no_permutation.asm";
    regular_test_gl(f, Default::default());
}

#[test]
#[ignore = "Too slow"]
fn vm_args() {
    let f = "asm/vm_args.asm";
    regular_test_gl(f, Default::default());
}

#[test]
fn vm_args_memory() {
    let f = "asm/vm_args_memory.asm";
    regular_test_gl(f, Default::default());
}

#[test]
fn vm_args_relative_path() {
    let f = "asm/vm_args_relative_path.asm";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn vm_args_two_levels() {
    let f = "asm/vm_args_two_levels.asm";
    regular_test_gl(f, Default::default());
}

mod reparse {

    use powdr_pipeline::test_util::run_reparse_test_with_blacklist;
    use test_log::test;

    /// Files that we don't expect to parse, analyze, and optimize without error.
    const BLACKLIST: [&str; 4] = [
        "asm/failing_assertion.asm",
        "asm/multi_return_wrong_assignment_register_length.asm",
        "asm/multi_return_wrong_assignment_registers.asm",
        "asm/permutations/incoming_needs_selector.asm",
    ];

    fn run_reparse_test(file: &str) {
        run_reparse_test_with_blacklist(file, &BLACKLIST)
    }
    include!(concat!(env!("OUT_DIR"), "/asm_reparse_tests.rs"));
}

mod book {
    use super::*;
    use test_log::test;

    fn run_book_test(file: &str) {
        use powdr_pipeline::test_util::test_mock_backend;
        // passing 0 to all tests currently works as they either take no prover input or 0 works
        let pipeline = make_prepared_pipeline::<GoldilocksField>(
            file,
            vec![0.into()],
            vec![],
            LinkerMode::Bus,
        );
        test_mock_backend(pipeline);
    }

    include!(concat!(env!("OUT_DIR"), "/asm_book_tests.rs"));
}

#[test]
#[should_panic = "Witness generation failed."]
fn hello_world_asm_fail() {
    let f = "asm/book/hello_world.asm";
    let i = [2];
    let pipeline: Pipeline<GoldilocksField> =
        make_prepared_pipeline(f, slice_to_vec(&i), vec![], LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
#[should_panic = "FailedAssertion(\"This should fail.\")"]
fn failing_assertion() {
    let f = "asm/failing_assertion.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn keccak() {
    use powdr_ast::analyzed::Analyzed;
    use powdr_number::BigInt;
    use powdr_pil_analyzer::evaluator::Value;
    use powdr_pipeline::test_util::evaluate_function;
    use std::{fs, sync::Arc};

    // Set up the file to test
    let code_path = "../test_data/asm/keccakf.asm";
    let code = fs::read_to_string(code_path).unwrap();
    let mut pipeline = Pipeline::<GoldilocksField>::default().from_asm_string(code, None);
    let analyzed = pipeline.compute_analyzed_pil().unwrap().clone();

    // Helper
    fn array_argument<T>(values: Vec<u64>) -> Value<'static, T> {
        Value::Array(
            values
                .iter()
                .map(|x| Arc::new(Value::Integer(BigInt::from(*x))))
                .collect(),
        )
    }

    fn compare_integer_array_evaluations<T>(this: &Value<T>, other: &Value<T>) {
        if let (Value::Array(ref this), Value::Array(ref other)) = (this, other) {
            assert_eq!(this.len(), other.len());
            for (this_elem, other_elem) in this.iter().zip(other.iter()) {
                if let (Value::Integer(ref this_int), Value::Integer(ref other_int)) =
                    (this_elem.as_ref(), other_elem.as_ref())
                {
                    assert_eq!(this_int, other_int);
                } else {
                    panic!("Expected integer.");
                }
            }
        } else {
            panic!("Expected array.");
        }
    }

    // Test vectors for keccakf_inner and keccakf
    let padded_input: Vec<u64> = vec![
        0x7a6f6b7261746573,
        0x0100000000000000,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x80,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
    ];

    let padded_endianness_swapped_input = padded_input.iter().map(|x| x.swap_bytes()).collect();

    // Test keccakf_inner
    let keccakf_inner_result = evaluate_function(
        &analyzed,
        "keccakf_inner",
        vec![Arc::new(array_argument(padded_endianness_swapped_input))],
    );

    let keccakf_inner_expected: Vec<u64> = vec![
        0xb6dc406d97d185ca,
        0x836e59c6c8ec3bca,
        0x6a01cf85414f77c0,
        0x397fa356584f8305,
        0xc8ad140a950d0cba,
        0x3dacc584b36c843f,
        0x428a466fad758146,
        0xa68af9b0cfafaf4c,
        0xffbba567083af2a9,
        0xb880d631598051a4,
        0x683f441da93e7295,
        0xbb5b42d2641b17c6,
        0xf4ec07dc2064443c,
        0x21959efb97953f8b,
        0x31c5e9b638335876,
        0xaa95e01d2bf963ed,
        0x82117b4b8decd828,
        0xe2a255871d47f57f,
        0x659b271c81bf6d3b,
        0x680b15e3d98b97ee,
        0x58118ac68850970d,
        0xada41f9e251307e6,
        0xf9a0529a1f229355,
        0x17cf3d9d8026e97f,
        0xdf84d5da988117d2,
    ];

    compare_integer_array_evaluations(
        &keccakf_inner_result,
        &array_argument(keccakf_inner_expected.clone()),
    );

    // Test keccakf
    let keccakf_result = evaluate_function(
        &analyzed,
        "keccakf",
        vec![Arc::new(array_argument(padded_input))],
    );

    let keccakf_expected = keccakf_inner_expected
        .iter()
        .map(|x| x.swap_bytes())
        .collect();

    compare_integer_array_evaluations(&keccakf_result, &array_argument(keccakf_expected));

    // Helper for testing full keccak
    fn test_main(analyzed: &Analyzed<GoldilocksField>, input: Vec<u8>, expected: Vec<u8>) {
        let result = evaluate_function(
            analyzed,
            "main",
            vec![
                Arc::new(Value::Integer(BigInt::from(32))), // W = 32 (output bytes)
                Arc::new(Value::Array(
                    input
                        .iter()
                        .map(|x| Arc::new(Value::Integer(BigInt::from(*x))))
                        .collect(),
                )),
                Arc::new(Value::Integer(BigInt::from(0x01))), // delim = 0x01
            ],
        );

        compare_integer_array_evaluations(
            &result,
            &array_argument(expected.iter().map(|x| *x as u64).collect()),
        );
    }

    // Test full keccak
    let input: Vec<Vec<u8>> = vec![
        // The following three test vectors are from Zokrates
        // https://github.com/Zokrates/ZoKrates/blob/develop/zokrates_stdlib/tests/tests/hashes/keccak/keccak.zok
        vec![0x7a, 0x6f, 0x6b, 0x72, 0x61, 0x74, 0x65, 0x73],
        [0x2a; 135].to_vec(),
        [0x2a; 136].to_vec(),
        // This test vector tests input size greater than compression function (keccakf) output size (200 bytes)
        {
            let mut v = vec![0x2a; 399];
            v.push(0x01);
            v
        },
        // All zero input test vector
        [0x00; 256].to_vec(),
    ];

    let expected: Vec<Vec<u8>> = vec![
        "ca85d1976d40dcb6ca3becc8c6596e83c0774f4185cf016a05834f5856a37f39",
        "723e2ae02ca8d8fb45dca21e5f6369c4f124da72f217dca5e657a4bbc69b917d",
        "e60d5160227cb1b8dc8547deb9c6a2c5e6c3306a1ca155611a73ed2c2324bfc0",
        "cf54f48e5701fed7b85fa015ff3def02604863f68c585fcf6af54a86d42e1046",
        "d397b3b043d87fcd6fad1291ff0bfd16401c274896d8c63a923727f077b8e0b5",
    ]
    .into_iter()
    .map(|x| {
        (0..x.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&x[i..i + 2], 16).unwrap())
            .collect()
    })
    .collect();

    input
        .into_iter()
        .zip(expected.into_iter())
        .for_each(|(input, expected)| {
            test_main(&analyzed, input, expected);
        });
}

#[test]
fn connect_no_witgen() {
    let f = "asm/connect_no_witgen.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Native);
    // TODO Mock prover doesn't support this test yet.
    test_pilcom(pipeline);
}

#[test]
fn generics_preservation() {
    let f = "asm/generics_preservation.asm";
    make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    // No need to generate a proof here.
}

#[test]
fn trait_parsing() {
    // Should be expanded/renamed when traits functionality is fully implemented
    let f = "asm/trait_parsing.asm";
    make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    // No need to generate a proof here.
}

#[test]
fn dynamic_fixed_cols() {
    let f = "asm/dynamic_fixed_cols.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn type_vars_in_local_decl() {
    let f = "asm/type_vars_in_local_decl.asm";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn types_in_expressions() {
    let input = r#"
        enum O<X> {
            A(X),
            B,
        }
        let f: -> Constr = || {
            let g: expr[] = [1, 2];
            let h: expr -> O<expr> = |i| O::A::<expr>(i);
            match h(g[1]) {
                O::A(x) => x,
            } = 0
        };
        machine Main with degree: 64 {
            col witness w;
            f();
        }
        "#;
    let output = asm_string_to_pil::<GoldilocksField>(input).to_string();
    let expected = "    2 = 0;\n";
    assert_eq!(output, expected);
}

#[test]
fn set_hint() {
    let f = "asm/set_hint.asm";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn expand_fixed_jit() {
    // Test some more or less complicated code and see that it all JIT-compiles.
    let file_name = "asm/expand_fixed.asm";

    let mut pipeline = Pipeline::<GoldilocksField>::default()
        .with_tmp_output()
        .from_file(resolve_test_file(file_name));
    let pil = pipeline.compute_optimized_pil().unwrap();

    let fixed_cols = constant_evaluator::generate_only_via_jit(&pil);

    let fixed_col_names = fixed_cols
        .into_iter()
        .map(|(name, _)| name)
        .collect::<Vec<_>>();
    assert_eq!(fixed_col_names, vec!["main::LAST"]);
}

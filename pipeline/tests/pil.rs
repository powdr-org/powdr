use powdr_linker::LinkerMode;
use powdr_number::GoldilocksField;
use powdr_pipeline::{
    test_util::{
        assert_proofs_fail_for_invalid_witnesses, assert_proofs_fail_for_invalid_witnesses_estark,
        assert_proofs_fail_for_invalid_witnesses_mock,
        assert_proofs_fail_for_invalid_witnesses_pilcom,
        assert_proofs_fail_for_invalid_witnesses_stwo, make_prepared_pipeline,
        make_simple_prepared_pipeline, regular_test_all_fields, regular_test_gl,
        test_halo2_with_backend_variant, test_mock_backend, test_stwo, BackendVariant,
    },
    Pipeline,
};

use test_log::test;

#[test]
fn invalid_witness() {
    let f = "pil/trivial.pil";
    let witness = vec![("main::w".to_string(), vec![0; 4])];
    assert_proofs_fail_for_invalid_witnesses(f, &witness);
}

#[test]
fn lookup_with_selector() {
    // witness[0] and witness[2] have to be in {2, 4}

    // Valid witness
    let f = "pil/lookup_with_selector.pil";
    use powdr_pipeline::test_util::resolve_test_file;
    use powdr_pipeline::Pipeline;
    let witness = [2, 42, 4, 17];
    Pipeline::default()
        .from_file(resolve_test_file(f))
        .set_witness(vec![(
            "main::w".to_string(),
            witness.iter().cloned().map(GoldilocksField::from).collect(),
        )])
        .with_backend(powdr_backend::BackendType::Mock, None)
        .compute_proof()
        .unwrap();

    // Invalid witness: 0 is not in the set {2, 4}
    let witness = vec![("main::w".to_string(), vec![0, 42, 4, 17])];
    assert_proofs_fail_for_invalid_witnesses_mock(f, &witness);
    assert_proofs_fail_for_invalid_witnesses_pilcom(f, &witness);
}

#[test]
#[cfg(feature = "estark-starky")]
#[should_panic = "Number not included: F3G { cube: [Fr(0x0000000000000000), Fr(0x0000000000000000), Fr(0x0000000000000000)], dim: 3 }"]
fn lookup_with_selector_starky() {
    // witness[0] and witness[2] have to be in {2, 4}

    let f = "pil/lookup_with_selector.pil";

    // Invalid witness: 0 is not in the set {2, 4}
    let witness = vec![("main::w".to_string(), vec![0, 42, 4, 17])];
    // Unfortunately, eStark panics in this case. That's why the test is marked
    // as should_panic, with the error message that would be coming from eStark...
    assert_proofs_fail_for_invalid_witnesses_estark(f, &witness);
}

#[test]
fn permutation_with_selector() {
    // witness[0] and witness[2] have to be in {2, 4}

    // Valid witness
    let f = "pil/permutation_with_selector.pil";
    use powdr_pipeline::test_util::resolve_test_file;
    use powdr_pipeline::Pipeline;
    let witness = [2, 42, 4, 17];
    Pipeline::default()
        .from_file(resolve_test_file(f))
        .set_witness(vec![(
            "main::w".to_string(),
            witness.iter().cloned().map(GoldilocksField::from).collect(),
        )])
        .with_backend(powdr_backend::BackendType::Mock, None)
        .compute_proof()
        .unwrap();

    // Invalid witness: 0 is not in the set {2, 4}
    let witness = vec![("main::w".to_string(), vec![0, 42, 4, 17])];
    assert_proofs_fail_for_invalid_witnesses_mock(f, &witness);
    assert_proofs_fail_for_invalid_witnesses_pilcom(f, &witness);
}

#[test]
#[cfg(feature = "estark-starky")]
#[should_panic = "assertion failed: check_val._eq(&F::one())"]
fn permutation_with_selector_starky() {
    // witness[0] and witness[2] have to be in {2, 4}

    let f = "pil/permutation_with_selector.pil";

    // Invalid witness: 0 is not in the set {2, 4}
    let witness = vec![("main::w".to_string(), vec![0, 42, 4, 17])];
    // Unfortunately, eStark panics in this case. That's why the test is marked
    // as should_panic, with the error message that would be coming from eStark...
    assert_proofs_fail_for_invalid_witnesses_estark(f, &witness);
}

#[test]
fn fibonacci() {
    let f = "pil/fibonacci.pil";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn fibonacci_with_public() {
    // Public references are not supported by the backends yet, but we can test witness generation.
    let f = "pil/fibonacci_with_public.pil";
    let mut pipeline: Pipeline<GoldilocksField> =
        make_prepared_pipeline(f, vec![], vec![], LinkerMode::Bus);
    pipeline.compute_witness().unwrap();
}

#[test]
fn fibonacci_invalid_witness() {
    let f = "pil/fibonacci.pil";

    // Changed one value and then continued.
    // The following constraint should fail in row 1:
    //     (1-ISLAST) * (x' - y) = 0;
    let witness = vec![
        ("Fibonacci::x".to_string(), vec![1, 1, 10, 3]),
        ("Fibonacci::y".to_string(), vec![1, 2, 3, 13]),
    ];
    assert_proofs_fail_for_invalid_witnesses_mock(f, &witness);
    assert_proofs_fail_for_invalid_witnesses_pilcom(f, &witness);

    // All constraints are valid, except the initial row.
    // The following constraint should fail in row 3:
    //     ISLAST * (y' - 1) = 0;
    let witness = vec![
        ("Fibonacci::x".to_string(), vec![1, 2, 3, 5]),
        ("Fibonacci::y".to_string(), vec![2, 3, 5, 8]),
    ];
    assert_proofs_fail_for_invalid_witnesses_mock(f, &witness);
    assert_proofs_fail_for_invalid_witnesses_pilcom(f, &witness);
}

#[test]
fn constant_in_identity() {
    let f = "pil/constant_in_identity.pil";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn fib_arrays() {
    let f = "pil/fib_arrays.pil";
    regular_test_all_fields(f, Default::default());
}

#[test]
#[should_panic = "Witness generation failed."]
fn external_witgen_fails_if_none_provided() {
    let f = "pil/external_witgen.pil";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn external_witgen_a_provided() {
    let f = "pil/external_witgen.pil";
    let external_witness = vec![("main::a".to_string(), vec![GoldilocksField::from(3); 16])];
    let pipeline = make_prepared_pipeline(f, Default::default(), external_witness, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn external_witgen_b_provided() {
    let f = "pil/external_witgen.pil";
    let external_witness = vec![("main::b".to_string(), vec![GoldilocksField::from(4); 16])];
    let pipeline = make_prepared_pipeline(f, Default::default(), external_witness, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn external_witgen_both_provided() {
    let f = "pil/external_witgen.pil";
    let external_witness = vec![
        ("main::a".to_string(), vec![GoldilocksField::from(3); 16]),
        ("main::b".to_string(), vec![GoldilocksField::from(4); 16]),
    ];
    let pipeline = make_prepared_pipeline(f, Default::default(), external_witness, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
#[should_panic = "Witness generation failed."]
fn external_witgen_fails_on_conflicting_external_witness() {
    let f = "pil/external_witgen.pil";
    let external_witness = vec![
        ("main::a".to_string(), vec![GoldilocksField::from(3); 16]),
        // Does not satisfy b = a + 1
        ("main::b".to_string(), vec![GoldilocksField::from(3); 16]),
    ];
    let pipeline = make_prepared_pipeline(f, Default::default(), external_witness, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn sum_via_witness_query() {
    let f = "pil/sum_via_witness_query.pil";
    // Only 3 inputs -> Checks that if we return "None", the system still tries to figure it out on its own.
    let inputs = vec![7.into(), 8.into(), 2.into()];
    let pipeline =
        make_prepared_pipeline::<GoldilocksField>(f, inputs, Default::default(), LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn witness_lookup() {
    let f = "pil/witness_lookup.pil";
    let inputs = [3, 5, 2, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]
        .into_iter()
        .map(GoldilocksField::from)
        .collect::<Vec<_>>();
    let pipeline = make_prepared_pipeline(f, inputs, Default::default(), LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
#[should_panic(expected = "Witness generation failed.")]
fn underdetermined_zero_no_solution() {
    let f = "pil/underdetermined_zero_no_solution.pil";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn pair_lookup() {
    let f = "pil/pair_lookup.pil";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn block_lookup_or() {
    let f = "pil/block_lookup_or.pil";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
#[ignore = "Too slow"]
fn block_lookup_or_permutation() {
    let f = "pil/block_lookup_or_permutation.pil";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn halo_without_lookup() {
    let f = "pil/halo_without_lookup.pil";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn add() {
    let f = "pil/add.pil";
    regular_test_gl(f, Default::default());
}

#[test]
fn stwo_challenges() {
    let f = "pil/challenges.pil";
    test_stwo(f, Default::default());
}

#[test]
fn stwo_fibonacci() {
    let f = "pil/fibo_no_publics.pil";
    test_stwo(f, Default::default());
}

#[test]
fn stwo_fixed_columns() {
    let f = "pil/fixed_columns.pil";
    test_stwo(f, Default::default());
}

#[test]
fn stwo_incremental_one() {
    let f = "pil/incremental_one.pil";
    test_stwo(f, Default::default());
}

#[test]
fn stwo_constant_next_test() {
    let f = "pil/fixed_with_incremental.pil";
    test_stwo(f, Default::default());
}
#[test]
fn fibonacci_invalid_witness_stwo() {
    let f = "pil/fibo_no_publics.pil";

    // Changed one value and then continued.
    // The following constraint should fail in row 1:
    //     (1-ISLAST) * (x' - y) = 0;
    let witness = vec![
        ("Fibonacci::x".to_string(), vec![1, 1, 10, 3]),
        ("Fibonacci::y".to_string(), vec![1, 2, 3, 13]),
    ];
    assert_proofs_fail_for_invalid_witnesses_stwo(f, &witness);

    // All constraints are valid, except the initial row.
    // The following constraint should fail in row 3:
    //     ISLAST * (y' - 1) = 0;
    let witness = vec![
        ("Fibonacci::x".to_string(), vec![1, 2, 3, 5]),
        ("Fibonacci::y".to_string(), vec![2, 3, 5, 8]),
    ];
    assert_proofs_fail_for_invalid_witnesses_stwo(f, &witness);
}
#[test]
fn simple_div() {
    let f = "pil/simple_div.pil";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn single_line_blocks() {
    let f = "pil/single_line_blocks.pil";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn two_block_machine_functions() {
    let f = "pil/two_block_machine_functions.pil";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn fixed_columns() {
    let f = "pil/fixed_columns.pil";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn witness_via_let() {
    let f = "pil/witness_via_let.pil";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn conditional_fixed_constraints() {
    let f = "pil/conditional_fixed_constraints.pil";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn referencing_arrays() {
    let f = "pil/referencing_array.pil";
    regular_test_all_fields(f, Default::default());
}

#[test]
fn naive_byte_decomposition_bn254() {
    // This should pass, because BN254 is a field that can fit all 64-Bit integers.
    let f = "pil/naive_byte_decomposition.pil";

    // Native linker mode, because bus constraints are exponential in Halo2
    let pipeline = make_simple_prepared_pipeline(f, LinkerMode::Native);
    test_halo2_with_backend_variant(pipeline, BackendVariant::Composite);
}

#[test]
#[should_panic = "Witness generation failed."]
fn naive_byte_decomposition_gl() {
    // This should fail, because GoldilocksField is a field that cannot fit all 64-Bit integers.
    let f = "pil/naive_byte_decomposition.pil";
    let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(f, LinkerMode::Bus);
    test_mock_backend(pipeline);
}

#[test]
fn different_degrees() {
    let f = "pil/different_degrees.pil";
    // Because machines have different lengths, this can only be proven
    // with a composite proof.
    regular_test_gl(f, Default::default());
    test_stwo(f, Default::default());
}

#[test]
#[ignore = "Too slow"]
fn vm_to_block_dynamic_length() {
    let f = "pil/vm_to_block_dynamic_length.pil";
    // Because machines have different lengths, this can only be proven
    // with a composite proof.
    regular_test_gl(f, Default::default());
}

#[test]
fn serialize_deserialize_optimized_pil() {
    let f = "pil/fibonacci.pil";
    let path = powdr_pipeline::test_util::resolve_test_file(f);

    let optimized = powdr_pipeline::Pipeline::<powdr_number::Bn254Field>::default()
        .from_file(path)
        .compute_optimized_pil()
        .unwrap();

    let optimized_serialized = serde_cbor::to_vec(&optimized).unwrap();
    let optimized_deserialized: powdr_ast::analyzed::Analyzed<powdr_number::Bn254Field> =
        serde_cbor::from_slice(&optimized_serialized[..]).unwrap();

    let input_pil_file = format!("{optimized}");
    let output_pil_file = format!("{optimized_deserialized}");

    assert_eq!(input_pil_file, output_pil_file);
}

mod reparse {
    use powdr_pipeline::test_util::run_reparse_test;
    use test_log::test;
    include!(concat!(env!("OUT_DIR"), "/pil_reparse_tests.rs"));
}

mod book {
    use super::*;
    use test_log::test;

    fn run_book_test(file: &str) {
        let pipeline = make_simple_prepared_pipeline::<GoldilocksField>(file, LinkerMode::Bus);
        test_mock_backend(pipeline);
    }

    include!(concat!(env!("OUT_DIR"), "/pil_book_tests.rs"));
}

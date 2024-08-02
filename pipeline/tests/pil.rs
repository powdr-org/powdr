#[cfg(feature = "halo2")]
use powdr_number::Bn254Field;
use powdr_number::GoldilocksField;
use powdr_pipeline::test_util::{
    assert_proofs_fail_for_invalid_witnesses, assert_proofs_fail_for_invalid_witnesses_estark,
    assert_proofs_fail_for_invalid_witnesses_halo2,
    assert_proofs_fail_for_invalid_witnesses_pilcom, gen_estark_proof,
    gen_estark_proof_with_backend_variant, make_prepared_pipeline, make_simple_prepared_pipeline,
    regular_test, run_pilcom_with_backend_variant, test_halo2, test_halo2_with_backend_variant,
    test_pilcom, test_plonky3_with_backend_variant, BackendVariant,
};

use test_log::test;

#[test]
fn invalid_witness() {
    let f = "pil/trivial.pil";
    let witness = vec![("main.w".to_string(), vec![0; 4])];
    assert_proofs_fail_for_invalid_witnesses(f, &witness);
}

#[test]
#[should_panic = "Number not included: F3G { cube: [Fr(0x0000000000000000), Fr(0x0000000000000000), Fr(0x0000000000000000)], dim: 3 }"]
fn lookup_with_selector() {
    // witness[0] and witness[2] have to be in {2, 4}

    // Valid witness
    let f = "pil/lookup_with_selector.pil";
    #[cfg(feature = "halo2")]
    {
        use powdr_pipeline::test_util::resolve_test_file;
        use powdr_pipeline::Pipeline;
        let witness = [2, 42, 4, 17];
        Pipeline::default()
            .from_file(resolve_test_file(f))
            .set_witness(vec![(
                "main.w".to_string(),
                witness.iter().cloned().map(Bn254Field::from).collect(),
            )])
            .with_backend(powdr_backend::BackendType::Halo2Mock, None)
            .compute_proof()
            .unwrap();
    }

    // Invalid witness: 0 is not in the set {2, 4}
    let witness = vec![("main.w".to_string(), vec![0, 42, 4, 17])];
    assert_proofs_fail_for_invalid_witnesses_halo2(f, &witness);
    assert_proofs_fail_for_invalid_witnesses_pilcom(f, &witness);
    // Unfortunately, eStark panics in this case. That's why the test is marked
    // as should_panic, with the error message that would be coming from eStark...
    assert_proofs_fail_for_invalid_witnesses_estark(f, &witness);
}

#[test]
#[should_panic = "assertion failed: check_val._eq(&F::one())"]
fn permutation_with_selector() {
    // witness[0] and witness[2] have to be in {2, 4}

    // Valid witness
    let f = "pil/permutation_with_selector.pil";
    #[cfg(feature = "halo2")]
    {
        use powdr_pipeline::test_util::resolve_test_file;
        use powdr_pipeline::Pipeline;
        let witness = [2, 42, 4, 17];
        Pipeline::default()
            .from_file(resolve_test_file(f))
            .set_witness(vec![(
                "main.w".to_string(),
                witness.iter().cloned().map(Bn254Field::from).collect(),
            )])
            .with_backend(powdr_backend::BackendType::Halo2Mock, None)
            .compute_proof()
            .unwrap();
    }

    // Invalid witness: 0 is not in the set {2, 4}
    let witness = vec![("main.w".to_string(), vec![0, 42, 4, 17])];
    assert_proofs_fail_for_invalid_witnesses_halo2(f, &witness);
    assert_proofs_fail_for_invalid_witnesses_pilcom(f, &witness);
    // Unfortunately, eStark panics in this case. That's why the test is marked
    // as should_panic, with the error message that would be coming from eStark...
    assert_proofs_fail_for_invalid_witnesses_estark(f, &witness);
}

#[test]
fn fibonacci() {
    let f = "pil/fibonacci.pil";
    regular_test(f, Default::default());
    test_plonky3_with_backend_variant(f, Default::default(), BackendVariant::Monolithic);
}

#[test]
fn fibonacci_invalid_witness() {
    let f = "pil/fibonacci.pil";

    // Changed one value and then continued.
    // The following constraint should fail in row 1:
    //     (1-ISLAST) * (x' - y) = 0;
    let witness = vec![
        ("Fibonacci.x".to_string(), vec![1, 1, 10, 3]),
        ("Fibonacci.y".to_string(), vec![1, 2, 3, 13]),
    ];
    assert_proofs_fail_for_invalid_witnesses(f, &witness);

    // All constraints are valid, except the initial row.
    // The following constraint should fail in row 3:
    //     ISLAST * (y' - 1) = 0;
    let witness = vec![
        ("Fibonacci.x".to_string(), vec![1, 2, 3, 5]),
        ("Fibonacci.y".to_string(), vec![2, 3, 5, 8]),
    ];
    assert_proofs_fail_for_invalid_witnesses(f, &witness);
}

#[test]
fn constant_in_identity() {
    let f = "pil/constant_in_identity.pil";
    regular_test(f, Default::default());
}

#[test]
fn fib_arrays() {
    let f = "pil/fib_arrays.pil";
    regular_test(f, Default::default());
}

#[test]
#[should_panic = "Witness generation failed."]
fn external_witgen_fails_if_none_provided() {
    let f = "pil/external_witgen.pil";
    let pipeline = make_simple_prepared_pipeline(f);
    test_pilcom(pipeline);
}

#[test]
fn external_witgen_a_provided() {
    let f = "pil/external_witgen.pil";
    let external_witness = vec![("main.a".to_string(), vec![GoldilocksField::from(3); 16])];
    let pipeline = make_prepared_pipeline(f, Default::default(), external_witness);
    test_pilcom(pipeline);
}

#[test]
fn external_witgen_b_provided() {
    let f = "pil/external_witgen.pil";
    let external_witness = vec![("main.b".to_string(), vec![GoldilocksField::from(4); 16])];
    let pipeline = make_prepared_pipeline(f, Default::default(), external_witness);
    test_pilcom(pipeline);
}

#[test]
fn external_witgen_both_provided() {
    let f = "pil/external_witgen.pil";
    let external_witness = vec![
        ("main.a".to_string(), vec![GoldilocksField::from(3); 16]),
        ("main.b".to_string(), vec![GoldilocksField::from(4); 16]),
    ];
    let pipeline = make_prepared_pipeline(f, Default::default(), external_witness);
    test_pilcom(pipeline);
}

#[test]
#[should_panic = "Witness generation failed."]
fn external_witgen_fails_on_conflicting_external_witness() {
    let f = "pil/external_witgen.pil";
    let external_witness = vec![
        ("main.a".to_string(), vec![GoldilocksField::from(3); 16]),
        // Does not satisfy b = a + 1
        ("main.b".to_string(), vec![GoldilocksField::from(3); 16]),
    ];
    let pipeline = make_prepared_pipeline(f, Default::default(), external_witness);
    test_pilcom(pipeline);
}

#[test]
fn sum_via_witness_query() {
    let f = "pil/sum_via_witness_query.pil";
    // Only 3 inputs -> Checks that if we return "None", the system still tries to figure it out on its own.
    let inputs = vec![7.into(), 8.into(), 2.into()];
    let pipeline = make_prepared_pipeline(f, inputs, Default::default());
    test_pilcom(pipeline);
    // prover query string uses a different convention,
    // so we cannot directly use the halo2_proof and estark functions here.
}

#[test]
fn witness_lookup() {
    let f = "pil/witness_lookup.pil";
    let inputs = [3, 5, 2, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]
        .into_iter()
        .map(GoldilocksField::from)
        .collect::<Vec<_>>();
    let pipeline = make_prepared_pipeline(f, inputs, Default::default());
    test_pilcom(pipeline.clone());
    // halo2 fails with "gates must contain at least one constraint"
    gen_estark_proof(pipeline);
}

#[test]
#[should_panic(expected = "Witness generation failed.")]
fn underdetermined_zero_no_solution() {
    let f = "pil/underdetermined_zero_no_solution.pil";
    let pipeline = make_simple_prepared_pipeline(f);
    test_pilcom(pipeline);
}

#[test]
fn pair_lookup() {
    let f = "pil/pair_lookup.pil";
    let pipeline = make_simple_prepared_pipeline(f);
    test_pilcom(pipeline);
    // halo2 would take too long for this
    // starky would take too long for this in debug mode
}

#[test]
fn block_lookup_or() {
    let f = "pil/block_lookup_or.pil";
    let pipeline = make_simple_prepared_pipeline(f);
    test_pilcom(pipeline);
    // halo2 would take too long for this
    // starky would take too long for this in debug mode
}

#[test]
#[ignore = "Too slow"]
fn block_lookup_or_permutation() {
    let f = "pil/block_lookup_or_permutation.pil";
    test_pilcom(make_simple_prepared_pipeline(f));
    test_halo2(make_simple_prepared_pipeline(f));
    // starky would take too long for this in debug mode
}

#[test]
fn halo_without_lookup() {
    let f = "pil/halo_without_lookup.pil";
    regular_test(f, Default::default());
}

#[test]
fn add() {
    let f = "pil/add.pil";
    test_plonky3_with_backend_variant(f, Default::default(), BackendVariant::Monolithic);
}

#[test]
fn simple_div() {
    let f = "pil/simple_div.pil";
    let pipeline = make_simple_prepared_pipeline(f);
    test_pilcom(pipeline);
    // starky would take too long for this in debug mode
}

#[test]
fn single_line_blocks() {
    let f = "pil/single_line_blocks.pil";
    let pipeline = make_simple_prepared_pipeline(f);
    test_pilcom(pipeline.clone());
    gen_estark_proof(pipeline);
}

#[test]
fn two_block_machine_functions() {
    let f = "pil/two_block_machine_functions.pil";
    let pipeline = make_simple_prepared_pipeline(f);
    test_pilcom(pipeline.clone());
    gen_estark_proof(pipeline);
}

#[test]
fn witness_via_let() {
    let f = "pil/witness_via_let.pil";
    let pipeline = make_simple_prepared_pipeline(f);
    test_pilcom(pipeline.clone());
}

#[test]
fn conditional_fixed_constraints() {
    let f = "pil/conditional_fixed_constraints.pil";
    let pipeline = make_simple_prepared_pipeline(f);
    test_pilcom(pipeline.clone());
}

#[test]
fn referencing_arrays() {
    let f = "pil/referencing_array.pil";
    regular_test(f, Default::default());
}

#[test]
fn naive_byte_decomposition_bn254() {
    // This should pass, because BN254 is a field that can fit all 64-Bit integers.
    let f = "pil/naive_byte_decomposition.pil";
    let pipeline = make_simple_prepared_pipeline(f);
    test_halo2(pipeline);
}

#[test]
#[should_panic = "Witness generation failed."]
fn naive_byte_decomposition_gl() {
    // This should fail, because GoldilocksField is a field that cannot fit all 64-Bit integers.
    let f = "pil/naive_byte_decomposition.pil";
    let pipeline = make_simple_prepared_pipeline(f);
    test_pilcom(pipeline);
}

#[test]
fn different_degrees() {
    let f = "pil/different_degrees.pil";
    // Because machines have different lengths, this can only be proven
    // with a composite proof.
    run_pilcom_with_backend_variant(make_simple_prepared_pipeline(f), BackendVariant::Composite)
        .unwrap();
    test_halo2_with_backend_variant(make_simple_prepared_pipeline(f), BackendVariant::Composite);
    gen_estark_proof_with_backend_variant(
        make_simple_prepared_pipeline(f),
        BackendVariant::Composite,
    );
}

#[test]
#[ignore = "Too slow"]
fn vm_to_block_dynamic_length() {
    let f = "pil/vm_to_block_dynamic_length.pil";
    // Because machines have different lengths, this can only be proven
    // with a composite proof.
    run_pilcom_with_backend_variant(make_simple_prepared_pipeline(f), BackendVariant::Composite)
        .unwrap();
    test_halo2_with_backend_variant(make_simple_prepared_pipeline(f), BackendVariant::Composite);
    gen_estark_proof_with_backend_variant(
        make_simple_prepared_pipeline(f),
        BackendVariant::Composite,
    );
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
        test_pilcom(make_simple_prepared_pipeline(file));
    }

    include!(concat!(env!("OUT_DIR"), "/pil_book_tests.rs"));
}

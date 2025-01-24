use powdr_ast::analyzed::Analyzed;
use powdr_linker::{DegreeMode, LinkerMode, LinkerParams};
use powdr_number::{
    BabyBearField, BigInt, Bn254Field, FieldElement, GoldilocksField, KoalaBearField,
};
use powdr_pil_analyzer::evaluator::{self, SymbolLookup};
use std::env;
use std::path::PathBuf;

use std::sync::Arc;

use crate::pipeline::Pipeline;

#[cfg(feature = "estark-starky")]
use crate::verify::verify;
#[cfg(feature = "estark-starky")]
use std::fs;

pub fn resolve_test_file(file_name: &str) -> PathBuf {
    PathBuf::from(format!("../test_data/{file_name}"))
}

/// Makes a new pipeline for the given file. All steps until witness generation are
/// already computed, so that the test can branch off from there, without having to re-compute
/// these steps.
pub fn make_simple_prepared_pipeline<T: FieldElement>(
    file_name: &str,
    linker_mode: LinkerMode,
) -> Pipeline<T> {
    let linker_params = LinkerParams {
        mode: linker_mode,
        degree_mode: DegreeMode::Vadcop,
    };
    let mut pipeline = Pipeline::default()
        .with_tmp_output()
        .with_linker_params(linker_params)
        .from_file(resolve_test_file(file_name));
    pipeline.compute_witness().unwrap();
    pipeline
}

/// Makes a new pipeline for the given file and inputs. All steps until witness generation are
/// already computed, so that the test can branch off from there, without having to re-compute
/// these steps.
pub fn make_prepared_pipeline<T: FieldElement>(
    file_name: &str,
    inputs: Vec<T>,
    external_witness_values: Vec<(String, Vec<T>)>,
    linker_mode: LinkerMode,
) -> Pipeline<T> {
    let linker_params = LinkerParams {
        mode: linker_mode,
        degree_mode: DegreeMode::Vadcop,
    };
    let mut pipeline = Pipeline::default()
        .with_tmp_output()
        .with_linker_params(linker_params)
        .from_file(resolve_test_file(file_name))
        .with_prover_inputs(inputs)
        .add_external_witness_values(external_witness_values);
    pipeline.compute_witness().unwrap();
    pipeline
}

/// Tests witness generation, mock prover, pilcom and plonky3 with
/// Goldilocks, BabyBear and KoalaBear.
pub fn regular_test_all_fields(file_name: &str, inputs: &[i32]) {
    regular_test_gl(file_name, inputs);
    regular_test_small_field(file_name, inputs);
}

pub fn regular_test_small_field(file_name: &str, inputs: &[i32]) {
    regular_test_bb(file_name, inputs);
    regular_test_kb(file_name, inputs);
}

/// Tests witness generation, mock prover, pilcom and plonky3 with BabyBear.
pub fn regular_test_bb(file_name: &str, inputs: &[i32]) {
    let inputs_bb = inputs.iter().map(|x| BabyBearField::from(*x)).collect();
    // LinkerMode::Native because the bus is not implemented for small fields
    let pipeline_bb = make_prepared_pipeline(file_name, inputs_bb, vec![], LinkerMode::Native);
    test_mock_backend(pipeline_bb.clone());
    test_plonky3_pipeline(pipeline_bb);
}

/// Tests witness generation, mock prover, pilcom and plonky3 with BabyBear and KoalaBear.
pub fn regular_test_kb(file_name: &str, inputs: &[i32]) {
    let inputs_kb = inputs.iter().map(|x| KoalaBearField::from(*x)).collect();
    // LinkerMode::Native because the bus is not implemented for small fields
    let pipeline_kb = make_prepared_pipeline(file_name, inputs_kb, vec![], LinkerMode::Native);
    test_mock_backend(pipeline_kb.clone());
    test_plonky3_pipeline(pipeline_kb);
}

/// Tests witness generation, mock prover, pilcom and plonky3 with Goldilocks.
pub fn regular_test_gl(file_name: &str, inputs: &[i32]) {
    let inputs_gl = inputs
        .iter()
        .map(|x| GoldilocksField::from(*x))
        .collect::<Vec<_>>();

    let pipeline_gl_native =
        make_prepared_pipeline(file_name, inputs_gl.clone(), vec![], LinkerMode::Native);
    test_mock_backend(pipeline_gl_native.clone());
    run_pilcom_with_backend_variant(pipeline_gl_native, BackendVariant::Composite).unwrap();

    let pipeline_gl_bus =
        make_prepared_pipeline(file_name, inputs_gl.clone(), vec![], LinkerMode::Bus);
    test_mock_backend(pipeline_gl_bus.clone());
    test_plonky3_pipeline(pipeline_gl_bus);
}

pub fn test_pilcom(pipeline: Pipeline<GoldilocksField>) {
    run_pilcom_with_backend_variant(pipeline.clone(), BackendVariant::Monolithic).unwrap();
    run_pilcom_with_backend_variant(pipeline, BackendVariant::Composite).unwrap();
}

pub fn asm_string_to_pil<T: FieldElement>(contents: &str) -> Arc<Analyzed<T>> {
    Pipeline::default()
        .from_asm_string(contents.to_string(), None)
        .compute_optimized_pil()
        .unwrap()
}

#[cfg(not(feature = "estark-starky"))]
pub fn run_pilcom_with_backend_variant(
    _pipeline: Pipeline<GoldilocksField>,
    _backend_variant: BackendVariant,
) -> Result<(), String> {
    Ok(())
}

#[cfg(feature = "estark-starky")]
pub fn run_pilcom_with_backend_variant(
    pipeline: Pipeline<GoldilocksField>,
    backend_variant: BackendVariant,
) -> Result<(), String> {
    use powdr_backend::BackendType;

    let backend = match backend_variant {
        BackendVariant::Monolithic => BackendType::EStarkDump,
        BackendVariant::Composite => BackendType::EStarkDumpComposite,
    };
    let mut pipeline = pipeline.with_backend(backend, None);

    if pipeline.output_dir().is_none() {
        pipeline = pipeline.with_tmp_output();
    }

    pipeline.compute_proof().unwrap();

    let out_dir = pipeline.output_dir().as_ref().unwrap();
    match backend_variant {
        BackendVariant::Composite => {
            // traverse all subdirs of the given output dir and verify each subproof
            for entry in fs::read_dir(out_dir).unwrap() {
                let entry = entry.unwrap();
                let path = entry.path();
                // In the composite backend, the prover can choose to skip some machines,
                // which happens if they are empty.
                if path.is_dir() && fs::read_dir(&path).unwrap().count() > 0 {
                    verify(&path)?;
                }
            }
            Ok(())
        }
        BackendVariant::Monolithic => verify(out_dir),
    }
}

fn should_generate_proofs() -> bool {
    match env::var("POWDR_GENERATE_PROOFS") {
        Ok(value) => match value.as_str() {
            "true" => true,
            "false" => false,
            _ => panic!("Invalid value for environment variable POWDR_GENERATE_PROOFS: {value}. Set it either to \"true\" or to \"false\"."),
        },
        Err(_) => false,
    }
}

#[cfg(not(feature = "estark-starky"))]
pub fn gen_estark_proof_with_backend_variant(
    _pipeline: Pipeline<GoldilocksField>,
    _backend_variant: BackendVariant,
) {
}

#[cfg(feature = "estark-starky")]
pub fn gen_estark_proof_with_backend_variant(
    pipeline: Pipeline<GoldilocksField>,
    backend_variant: BackendVariant,
) {
    use powdr_backend::BackendType;
    use powdr_number::buffered_write_file;

    if !should_generate_proofs() {
        return;
    }

    let backend = match backend_variant {
        BackendVariant::Monolithic => BackendType::EStarkStarky,
        BackendVariant::Composite => BackendType::EStarkStarkyComposite,
    };
    let mut pipeline = pipeline.with_backend(backend, None);

    pipeline.clone().compute_proof().unwrap();

    // Repeat the proof generation, but with an externally generated verification key

    // Verification Key
    let output_dir = pipeline.output_dir().as_ref().unwrap();
    let vkey_file_path = output_dir.join("verification_key.bin");
    buffered_write_file(&vkey_file_path, |writer| {
        pipeline.export_verification_key(writer).unwrap()
    })
    .unwrap();

    // Create the proof before adding the vkey to the pipeline,
    // so that it's generated during the proof
    let proof: Vec<u8> = pipeline.compute_proof().unwrap().clone();

    let mut pipeline = pipeline.with_vkey_file(Some(vkey_file_path));

    let publics: Vec<GoldilocksField> = pipeline
        .publics()
        .unwrap()
        .iter()
        .map(|(_name, v)| v.expect("all publics should be known since we created a proof"))
        .collect();

    pipeline.verify(&proof, &[publics]).unwrap();
}

/// Whether to compute a monolithic or composite proof.
pub enum BackendVariant {
    Monolithic,
    Composite,
}

#[cfg(feature = "halo2")]
pub fn test_halo2_with_backend_variant(
    pipeline: Pipeline<Bn254Field>,
    backend_variant: BackendVariant,
) {
    use powdr_backend::BackendType;

    let backend = match backend_variant {
        BackendVariant::Monolithic => BackendType::Halo2Mock,
        BackendVariant::Composite => BackendType::Halo2MockComposite,
    };

    // Generate a mock proof (fast and has good error messages)
    pipeline
        .clone()
        .with_backend(backend, None)
        .compute_proof()
        .unwrap();

    // `gen_halo2_proof` is rather slow, because it computes two Halo2 proofs.
    // Therefore, we only run it in the nightly tests.
    let is_nightly_test = env::var("IS_NIGHTLY_TEST")
        .map(|v| v == "true")
        .unwrap_or(false);

    if is_nightly_test && should_generate_proofs() {
        gen_halo2_proof(pipeline, backend_variant);
    }
}

#[cfg(not(feature = "halo2"))]
pub fn test_halo2_with_backend_variant(
    _pipeline: Pipeline<Bn254Field>,
    _backend_variant: BackendVariant,
) {
}

#[cfg(feature = "halo2")]
pub fn gen_halo2_proof(pipeline: Pipeline<Bn254Field>, backend: BackendVariant) {
    use powdr_backend::BackendType;
    use powdr_number::buffered_write_file;

    let backend = match backend {
        BackendVariant::Monolithic => BackendType::Halo2,
        BackendVariant::Composite => BackendType::Halo2Composite,
    };

    let mut pipeline = pipeline.clone().with_backend(backend, None);

    // Generate a proof with the setup and verification key generated on the fly
    pipeline.clone().compute_proof().unwrap();

    // Repeat the proof generation, but with an externally generated setup and verification key
    let pil = pipeline.compute_optimized_pil().unwrap();

    // Setup
    let output_dir = pipeline.output_dir().clone().unwrap();
    let setup_file_path = output_dir.join("params.bin");
    let max_degree = pil
        .degree_ranges()
        .into_iter()
        .map(|range| range.max)
        .max()
        .unwrap();
    buffered_write_file(&setup_file_path, |writer| {
        powdr_backend::BackendType::Halo2
            .factory::<Bn254Field>()
            .generate_setup(max_degree, writer)
            .unwrap()
    })
    .unwrap();
    let mut pipeline = pipeline.with_setup_file(Some(setup_file_path));

    // Verification Key
    let vkey_file_path = output_dir.join("verification_key.bin");
    buffered_write_file(&vkey_file_path, |writer| {
        pipeline.export_verification_key(writer).unwrap()
    })
    .unwrap();

    // Create the proof before adding the setup and vkey to the backend,
    // so that they're generated during the proof
    let proof: Vec<u8> = pipeline.compute_proof().unwrap().clone();

    let mut pipeline = pipeline.with_vkey_file(Some(vkey_file_path));

    let publics: Vec<Bn254Field> = pipeline
        .publics()
        .unwrap()
        .iter()
        .map(|(_name, v)| v.expect("all publics should be known since we created a proof"))
        .collect();

    pipeline.verify(&proof, &[publics]).unwrap();
}

#[cfg(not(feature = "halo2"))]
pub fn gen_halo2_proof(_pipeline: Pipeline<Bn254Field>, _backend: BackendVariant) {}

#[cfg(feature = "plonky3")]
pub fn test_plonky3_with_backend_variant<T: FieldElement>(
    file_name: &str,
    inputs: Vec<T>,
    backend: BackendVariant,
) {
    use powdr_backend::BackendType;
    use powdr_number::buffered_write_file;

    let backend = match backend {
        BackendVariant::Monolithic => BackendType::Plonky3,
        BackendVariant::Composite => BackendType::Plonky3Composite,
    };
    let mut pipeline = Pipeline::default()
        .with_tmp_output()
        .from_file(resolve_test_file(file_name))
        .with_prover_inputs(inputs)
        .with_backend(backend, None);

    // Generate a proof
    let proof = pipeline.compute_proof().cloned().unwrap();

    let publics: Vec<T> = pipeline
        .publics()
        .clone()
        .unwrap()
        .iter()
        .map(|(_name, v)| v.expect("all publics should be known since we created a proof"))
        .collect();

    pipeline.verify(&proof, &[publics.clone()]).unwrap();

    if pipeline.optimized_pil().unwrap().constant_count() > 0 {
        // Export verification Key
        let output_dir = pipeline.output_dir().as_ref().unwrap();
        let vkey_file_path = output_dir.join("verification_key.bin");
        buffered_write_file(&vkey_file_path, |writer| {
            pipeline.export_verification_key(writer).unwrap()
        })
        .unwrap();

        let mut pipeline = pipeline.with_vkey_file(Some(vkey_file_path));

        // Verify the proof again
        pipeline.verify(&proof, &[publics]).unwrap();
    }
}

pub fn test_mock_backend<T: FieldElement>(pipeline: Pipeline<T>) {
    pipeline
        .with_backend(powdr_backend::BackendType::Mock, None)
        .compute_proof()
        .cloned()
        .unwrap();
}

#[cfg(feature = "plonky3")]
pub fn test_plonky3_pipeline<T: FieldElement>(pipeline: Pipeline<T>) {
    use powdr_number::buffered_write_file;

    let mut pipeline = pipeline.with_backend(powdr_backend::BackendType::Plonky3, None);

    pipeline.compute_witness().unwrap();

    if !should_generate_proofs() {
        return;
    }

    // Generate a proof
    let proof = pipeline.compute_proof().cloned().unwrap();

    let publics: Vec<T> = pipeline
        .publics()
        .clone()
        .unwrap()
        .iter()
        .map(|(_name, v)| v.expect("all publics should be known since we created a proof"))
        .collect();

    pipeline.verify(&proof, &[publics.clone()]).unwrap();

    if pipeline.optimized_pil().unwrap().constant_count() > 0 {
        // Export verification Key
        let output_dir = pipeline.output_dir().as_ref().unwrap();
        let vkey_file_path = output_dir.join("verification_key.bin");
        buffered_write_file(&vkey_file_path, |writer| {
            pipeline.export_verification_key(writer).unwrap()
        })
        .unwrap();

        let mut pipeline = pipeline.with_vkey_file(Some(vkey_file_path));

        // Verify the proof again
        pipeline.verify(&proof, &[publics]).unwrap();
    }
}

#[cfg(not(feature = "plonky3"))]
pub fn test_plonky3_with_backend_variant<T: FieldElement>(_: &str, _: Vec<T>, _: BackendVariant) {}

#[cfg(not(feature = "plonky3"))]
pub fn test_plonky3_pipeline<T: FieldElement>(_: Pipeline<T>) {}

#[cfg(not(feature = "plonky3"))]
pub fn gen_plonky3_proof<T: FieldElement>(_: &str, _: Vec<T>) {}

/// Returns the analyzed PIL containing only the std library.
pub fn std_analyzed<T: FieldElement>() -> Analyzed<T> {
    let mut pipeline = Pipeline::default().from_asm_string(String::new(), None);
    pipeline.compute_analyzed_pil().unwrap().clone()
}

/// Evaluates a function call.
pub fn evaluate_function<'a, T: FieldElement>(
    analyzed: &'a Analyzed<T>,
    function: &'a str,
    arguments: Vec<Arc<evaluator::Value<'a, T>>>,
) -> evaluator::Value<'a, T> {
    let mut symbols = evaluator::Definitions {
        definitions: &analyzed.definitions,
        solved_impls: &analyzed.solved_impls,
    };
    let function = symbols.lookup(function, &None).unwrap();
    evaluator::evaluate_function_call(function, arguments, &mut symbols)
        .unwrap()
        .as_ref()
        .clone()
}

/// Evaluates a function call assuming inputs and outputs are integers.
pub fn evaluate_integer_function<T: FieldElement>(
    analyzed: &Analyzed<T>,
    function: &str,
    arguments: Vec<BigInt>,
) -> BigInt {
    let arguments = arguments
        .into_iter()
        .map(|x| Arc::new(evaluator::Value::Integer(x)))
        .collect();
    if let evaluator::Value::Integer(x) = evaluate_function(analyzed, function, arguments) {
        x
    } else {
        panic!("Expected integer.");
    }
}

fn convert_witness<T: FieldElement>(witness: &[(String, Vec<u64>)]) -> Vec<(String, Vec<T>)> {
    witness
        .iter()
        .map(|(k, v)| (k.clone(), v.iter().cloned().map(T::from).collect()))
        .collect()
}

pub fn assert_proofs_fail_for_invalid_witnesses_mock(
    file_name: &str,
    witness: &[(String, Vec<u64>)],
) {
    assert!(Pipeline::<GoldilocksField>::default()
        .with_tmp_output()
        .from_file(resolve_test_file(file_name))
        .set_witness(convert_witness(witness))
        .with_backend(powdr_backend::BackendType::Mock, None)
        .compute_proof()
        .is_err());
}

#[cfg(feature = "estark-starky")]
pub fn assert_proofs_fail_for_invalid_witnesses_pilcom(
    file_name: &str,
    witness: &[(String, Vec<u64>)],
) {
    let mut pipeline = Pipeline::<GoldilocksField>::default()
        .with_tmp_output()
        .from_file(resolve_test_file(file_name))
        .set_witness(convert_witness(witness));
    pipeline.compute_witness().unwrap();

    assert!(run_pilcom_with_backend_variant(pipeline.clone(), BackendVariant::Monolithic).is_err());
    assert!(run_pilcom_with_backend_variant(pipeline, BackendVariant::Composite).is_err());
}

#[cfg(not(feature = "estark-starky"))]
pub fn assert_proofs_fail_for_invalid_witnesses_pilcom(
    _file_name: &str,
    _witness: &[(String, Vec<u64>)],
) {
}

#[cfg(not(feature = "estark-starky"))]
pub fn assert_proofs_fail_for_invalid_witnesses_estark(
    _file_name: &str,
    _witness: &[(String, Vec<u64>)],
) {
}

#[cfg(feature = "estark-starky")]
pub fn assert_proofs_fail_for_invalid_witnesses_estark(
    file_name: &str,
    witness: &[(String, Vec<u64>)],
) {
    let pipeline = Pipeline::<GoldilocksField>::default()
        .from_file(resolve_test_file(file_name))
        .set_witness(convert_witness(witness));

    assert!(pipeline
        .clone()
        .with_backend(powdr_backend::BackendType::EStarkStarky, None)
        .compute_proof()
        .is_err());
}

#[cfg(feature = "halo2")]
pub fn assert_proofs_fail_for_invalid_witnesses_halo2(
    file_name: &str,
    witness: &[(String, Vec<u64>)],
) {
    let pipeline = Pipeline::<Bn254Field>::default()
        .from_file(resolve_test_file(file_name))
        .set_witness(convert_witness(witness));

    assert!(pipeline
        .clone()
        .with_backend(powdr_backend::BackendType::Halo2Mock, None)
        .compute_proof()
        .is_err());

    assert!(pipeline
        .clone()
        .with_backend(powdr_backend::BackendType::Halo2, None)
        .compute_proof()
        .is_err());
}

#[cfg(not(feature = "halo2"))]
pub fn assert_proofs_fail_for_invalid_witnesses_halo2(
    _file_name: &str,
    _witness: &[(String, Vec<u64>)],
) {
}

pub fn assert_proofs_fail_for_invalid_witnesses(file_name: &str, witness: &[(String, Vec<u64>)]) {
    assert_proofs_fail_for_invalid_witnesses_mock(file_name, witness);
    assert_proofs_fail_for_invalid_witnesses_pilcom(file_name, witness);
    assert_proofs_fail_for_invalid_witnesses_estark(file_name, witness);
    #[cfg(feature = "halo2")]
    assert_proofs_fail_for_invalid_witnesses_halo2(file_name, witness);
    #[cfg(feature = "stwo")]
    assert_proofs_fail_for_invalid_witnesses_stwo(file_name, witness);
}

pub fn run_reparse_test(file: &str) {
    run_reparse_test_with_blacklist(file, &[]);
}

pub fn run_reparse_test_with_blacklist(file: &str, blacklist: &[&str]) {
    if blacklist.contains(&file) {
        return;
    }

    // Load file
    let pipeline = Pipeline::<GoldilocksField>::default();
    let mut pipeline = if file.ends_with(".asm") {
        pipeline.from_asm_file(resolve_test_file(file))
    } else {
        pipeline.from_pil_file(resolve_test_file(file))
    };

    // Compute the optimized PIL
    let optimized_pil = pipeline.compute_optimized_pil().unwrap();

    // Run the pipeline using the string serialization of the optimized PIL.
    // This panics if the re-parsing fails.
    Pipeline::<GoldilocksField>::default()
        .from_pil_string(optimized_pil.to_string())
        .compute_optimized_pil()
        .unwrap();
}

#[cfg(feature = "stwo")]
use powdr_number::Mersenne31Field;
#[cfg(feature = "stwo")]
pub fn test_stwo(file_name: &str, inputs: Vec<Mersenne31Field>) {
    let backend = powdr_backend::BackendType::Stwo;

    let mut pipeline = Pipeline::default()
        .with_tmp_output()
        .from_file(resolve_test_file(file_name))
        .with_prover_inputs(inputs)
        .with_backend(backend, None);

    let proof = pipeline.compute_proof().cloned().unwrap();
    let publics: Vec<Mersenne31Field> = pipeline
        .publics()
        .clone()
        .unwrap()
        .iter()
        .map(|(_name, v)| v.expect("all publics should be known since we created a proof"))
        .collect();
    pipeline.verify(&proof, &[publics]).unwrap();
}
#[cfg(feature = "stwo")]
pub fn assert_proofs_fail_for_invalid_witnesses_stwo(
    file_name: &str,
    witness: &[(String, Vec<u64>)],
) {
    let pipeline = Pipeline::<Mersenne31Field>::default()
        .from_file(resolve_test_file(file_name))
        .set_witness(convert_witness(witness));

    assert!(pipeline
        .clone()
        .with_backend(powdr_backend::BackendType::Stwo, None)
        .compute_proof()
        .is_err());
}

#[cfg(not(feature = "stwo"))]
pub fn assert_proofs_fail_for_invalid_witnesses_stwo(
    _file_name: &str,
    _witness: &[(String, Vec<u64>)],
) {
}

#[cfg(not(feature = "stwo"))]
pub fn test_stwo(_file_name: &str, _inputs: Vec<u32>) {}

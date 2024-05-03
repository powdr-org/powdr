use powdr_ast::analyzed::Analyzed;
use powdr_backend::BackendType;
use powdr_number::{buffered_write_file, BigInt, Bn254Field, FieldElement, GoldilocksField};
use powdr_pil_analyzer::evaluator::{self, SymbolLookup};
use std::path::PathBuf;

use std::sync::Arc;

use crate::pipeline::Pipeline;
use crate::verify::verify;

pub fn resolve_test_file(file_name: &str) -> PathBuf {
    PathBuf::from(format!(
        "{}/../test_data/{file_name}",
        env!("CARGO_MANIFEST_DIR")
    ))
}

pub fn verify_test_file(
    file_name: &str,
    inputs: Vec<GoldilocksField>,
    external_witness_values: Vec<(String, Vec<GoldilocksField>)>,
) -> Result<(), String> {
    let pipeline = Pipeline::default()
        .from_file(resolve_test_file(file_name))
        .with_prover_inputs(inputs)
        .add_external_witness_values(external_witness_values);
    verify_pipeline(pipeline, BackendType::EStarkDump)
}

pub fn verify_asm_string<S: serde::Serialize + Send + Sync + 'static>(
    file_name: &str,
    contents: &str,
    inputs: Vec<GoldilocksField>,
    external_witness_values: Vec<(String, Vec<GoldilocksField>)>,
    data: Option<Vec<(u32, S)>>,
) {
    let mut pipeline = Pipeline::default()
        .from_asm_string(contents.to_string(), Some(PathBuf::from(file_name)))
        .with_prover_inputs(inputs)
        .add_external_witness_values(external_witness_values);

    if let Some(data) = data {
        pipeline = pipeline.add_data_vec(&data);
    }

    verify_pipeline(pipeline, BackendType::EStarkDump).unwrap();
}

pub fn verify_pipeline(
    pipeline: Pipeline<GoldilocksField>,
    backend: BackendType,
) -> Result<(), String> {
    let mut pipeline = pipeline.with_backend(backend);

    let tmp_dir = mktemp::Temp::new_dir().unwrap();
    if pipeline.output_dir().is_none() {
        pipeline = pipeline.with_tmp_output(&tmp_dir);
    }

    pipeline.compute_proof().unwrap();

    verify(pipeline.output_dir().unwrap())
}

pub fn gen_estark_proof(file_name: &str, inputs: Vec<GoldilocksField>) {
    let tmp_dir = mktemp::Temp::new_dir().unwrap();
    let pipeline = Pipeline::default()
        .with_tmp_output(&tmp_dir)
        .from_file(resolve_test_file(file_name))
        .with_prover_inputs(inputs);

    // If enabled, prove with EStarkPolygon backend.
    #[cfg(feature = "estark-polygon")]
    pipeline
        .clone()
        .with_backend(powdr_backend::BackendType::EStarkPolygon)
        .compute_proof()
        .unwrap();

    // Prove with EStarkStarky backend.
    let mut pipeline = pipeline.with_backend(powdr_backend::BackendType::EStarkStarky);
    pipeline.clone().compute_proof().unwrap();

    // Repeat the proof generation, but with an externally generated verification key

    // Verification Key
    let vkey_file_path = tmp_dir.as_path().join("verification_key.bin");
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
        .map(|(_name, v)| *v)
        .collect();

    pipeline.verify(&proof, &[publics]).unwrap();
}

#[cfg(feature = "halo2")]
pub fn test_halo2(file_name: &str, inputs: Vec<Bn254Field>) {
    use std::env;

    // Generate a mock proof (fast and has good error messages)
    Pipeline::default()
        .from_file(resolve_test_file(file_name))
        .with_prover_inputs(inputs.clone())
        .with_backend(powdr_backend::BackendType::Halo2Mock)
        .compute_proof()
        .unwrap();

    // `gen_halo2_proof` is rather slow, because it computes two Halo2 proofs.
    // Therefore, we only run it in the nightly tests.
    let is_nightly_test = env::var("IS_NIGHTLY_TEST")
        .map(|v| v == "true")
        .unwrap_or(false);
    if is_nightly_test {
        gen_halo2_proof(file_name, inputs)
    }
}

#[cfg(not(feature = "halo2"))]
pub fn test_halo2(_file_name: &str, _inputs: Vec<Bn254Field>) {}

#[cfg(feature = "halo2")]
pub fn gen_halo2_proof(file_name: &str, inputs: Vec<Bn254Field>) {
    let tmp_dir = mktemp::Temp::new_dir().unwrap();
    let mut pipeline = Pipeline::default()
        .with_tmp_output(&tmp_dir)
        .from_file(resolve_test_file(file_name))
        .with_prover_inputs(inputs)
        .with_backend(powdr_backend::BackendType::Halo2);

    // Generate a proof with the setup and verification key generated on the fly
    pipeline.clone().compute_proof().unwrap();

    // Repeat the proof generation, but with an externally generated setup and verification key
    let pil = pipeline.compute_optimized_pil().unwrap();

    // Setup
    let setup_file_path = tmp_dir.as_path().join("params.bin");
    buffered_write_file(&setup_file_path, |writer| {
        powdr_backend::BackendType::Halo2
            .factory::<Bn254Field>()
            .generate_setup(pil.degree(), writer)
            .unwrap()
    })
    .unwrap();
    let mut pipeline = pipeline.with_setup_file(Some(setup_file_path));

    // Verification Key
    let vkey_file_path = tmp_dir.as_path().join("verification_key.bin");
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
        .map(|(_name, v)| *v)
        .collect();

    pipeline.verify(&proof, &[publics]).unwrap();
}

#[cfg(not(feature = "halo2"))]
pub fn gen_halo2_proof(_file_name: &str, _inputs: Vec<Bn254Field>) {}

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
    let mut symbols = evaluator::Definitions(&analyzed.definitions);
    let function = symbols.lookup(function, None).unwrap();
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

pub fn assert_proofs_fail_for_invalid_witnesses_pilcom(
    file_name: &str,
    witness: &[(String, Vec<u64>)],
) {
    let tmp_dir = mktemp::Temp::new_dir().unwrap();
    let pipeline = Pipeline::<GoldilocksField>::default()
        .with_tmp_output(&tmp_dir)
        .from_file(resolve_test_file(file_name))
        .set_witness(convert_witness(witness));

    assert!(verify_pipeline(pipeline.clone(), BackendType::EStarkDump).is_err());
}

pub fn assert_proofs_fail_for_invalid_witnesses_estark(
    file_name: &str,
    witness: &[(String, Vec<u64>)],
) {
    let pipeline = Pipeline::<GoldilocksField>::default()
        .from_file(resolve_test_file(file_name))
        .set_witness(convert_witness(witness));

    assert!(pipeline
        .clone()
        .with_backend(powdr_backend::BackendType::EStarkStarky)
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
        .with_backend(powdr_backend::BackendType::Halo2Mock)
        .compute_proof()
        .is_err());

    assert!(pipeline
        .clone()
        .with_backend(powdr_backend::BackendType::Halo2)
        .compute_proof()
        .is_err());
}

#[cfg(not(feature = "halo2"))]
pub fn assert_proofs_fail_for_invalid_witnesses_bn254(
    _file_name: &str,
    _witness: &[(String, Vec<u64>)],
) {
}

pub fn assert_proofs_fail_for_invalid_witnesses(file_name: &str, witness: &[(String, Vec<u64>)]) {
    assert_proofs_fail_for_invalid_witnesses_pilcom(file_name, witness);
    assert_proofs_fail_for_invalid_witnesses_estark(file_name, witness);
    #[cfg(feature = "halo2")]
    assert_proofs_fail_for_invalid_witnesses_halo2(file_name, witness);
}

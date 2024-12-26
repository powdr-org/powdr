use powdr::backend::BackendType;
use powdr::number::buffered_write_file;
use powdr::pipeline::pipeline::DegreeMode;
use powdr::pipeline::pipeline::LinkerParams;
use powdr::Bn254Field;
use powdr::Pipeline;

use std::path::Path;

pub fn halo2_pipeline(
    pil: &str,
    prover_inputs: Vec<Bn254Field>,
    publics: Vec<Bn254Field>,
    setup_size: u64,
) {
    // Straightforward case
    let _proof = Pipeline::<Bn254Field>::default()
        .with_linker_params(LinkerParams {
            degree_mode: DegreeMode::Monolithic,
            ..Default::default()
        })
        .from_file(pil.into())
        .with_prover_inputs(prover_inputs.clone())
        .with_backend(BackendType::Halo2, None)
        .compute_proof()
        .unwrap();

    // Step-by-step case

    // First we create the universal setup of size 8
    buffered_write_file(Path::new("params.bin"), |writer| {
        BackendType::Halo2
            .factory::<Bn254Field>()
            .generate_setup(setup_size, writer)
            .unwrap()
    })
    .unwrap();

    // Configure a pipeline
    let mut pipeline = Pipeline::<Bn254Field>::default()
        .with_linker_params(LinkerParams {
            degree_mode: DegreeMode::Monolithic,
            ..Default::default()
        })
        .from_file(pil.into())
        .with_prover_inputs(prover_inputs)
        .with_backend(BackendType::Halo2, None)
        .with_setup_file(Some("params.bin".into()));

    // Create the verification key
    buffered_write_file(Path::new("vkey.bin"), |w| {
        pipeline.export_verification_key(w).unwrap()
    })
    .unwrap();

    // Add the verification key to a fresh pipeline and create a proof
    let mut pipeline_fresh = pipeline.clone().with_vkey_file(Some("vkey.bin".into()));

    let proof = pipeline_fresh.compute_proof().unwrap();

    // Create yet another fresh pipeline only for proof verification
    let mut pipeline = pipeline
        .with_linker_params(LinkerParams {
            degree_mode: DegreeMode::Monolithic,
            ..Default::default()
        })
        .with_backend(BackendType::Halo2, None)
        .with_setup_file(Some("params.bin".into()))
        .with_vkey_file(Some("vkey.bin".into()));

    // Verify a proof created by a different Pipeline
    pipeline.verify(proof, &[publics]).unwrap();
}

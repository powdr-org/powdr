use std::sync::Arc;

use powdr_ast::analyzed::Analyzed;
use powdr_executor::witgen::WitgenCallback;

use super::circuit_builder::PowdrCircuit;

use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use powdr_number::{FieldElement, KnownField};

// Can't depend on compiler::pipeline::GeneratedWitness because of circular dependencies...
pub fn mock_prove<T: FieldElement>(
    pil: Arc<Analyzed<T>>,
    constants: &[(String, Vec<T>)],
    witness: &[(String, Vec<T>)],
    witgen_callback: WitgenCallback<T>,
) -> Result<(), String> {
    if !matches!(T::known_field(), Some(KnownField::Bn254Field)) {
        panic!("powdr modulus doesn't match halo2 modulus. Make sure you are using Bn254");
    }

    // double the row count in order to make space for the cells introduced by the backend
    // TODO: use a precise count of the extra rows needed to avoid using so many rows

    let circuit_row_count_log = usize::BITS - pil.degree().leading_zeros();
    let expanded_row_count_log = circuit_row_count_log + 1;

    let circuit = PowdrCircuit::new(pil, constants)
        .with_witness(witness)
        .with_witgen_callback(witgen_callback);
    let mock_prover = MockProver::<Fr>::run(
        expanded_row_count_log,
        &circuit,
        vec![circuit.instance_column()],
    )
    .unwrap();
    mock_prover.verify().map_err(|errs| {
        // Using err.emit() is the only way to get a pretty error message,
        // so we print it here even though the error might be caught by the caller.
        for err in errs {
            err.emit(&mock_prover);
            eprintln!();
        }
        "Circuit was not satisfied".to_string()
    })
}

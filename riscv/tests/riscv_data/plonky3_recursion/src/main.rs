extern crate powdr_riscv_runtime;
use powdr_number::GoldilocksField;

use powdr_riscv_runtime::io::read;

use powdr_plonky3::{verify2, FieldElementMap};

pub fn main() {
    let verifying_key = read(1);
    let split = read(2);
    let mut challenger = GoldilocksField::get_challenger();
    let proof = read(3);
    let public_inputs = read(4);

    let _ = verify2::<GoldilocksField>(
        Some(&verifying_key),
        &split,
        &mut challenger,
        &proof,
        &public_inputs,
    );
}

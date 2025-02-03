use std::utils::unchanged_until;
use std::field::modulus;
use std::check::require_field_bits;
use std::machines::binary::ByteBinary;

machine Binary(byte_binary: ByteBinary) with
    latch: latch,
    operation_id: operation_id,
    // Allow this machine to be connected via a permutation
    call_selectors: sel,
{
    require_field_bits(32, || "Binary requires a field that fits any 32-Bit value.");

    operation and<0> A, B -> C;

    operation or<1> A, B -> C;

    operation xor<2> A, B -> C;

    let operation_id;
    let latch = 1;

    // We do not range check the bytes because the inputs are assumed 32-bits.
    let A_byte0;
    let A_byte1;
    let A_byte2;
    let A_byte3;
    let B_byte0;
    let B_byte1;
    let B_byte2;
    let B_byte3;
    let C_byte0;
    let C_byte1;
    let C_byte2;
    let C_byte3;

    let A;
    A = A_byte0 + A_byte1 * 0x100 + A_byte2 * 0x10000 + A_byte3 * 0x1000000;
    let B;
    B = B_byte0 + B_byte1 * 0x100 + B_byte2 * 0x10000 + B_byte3 * 0x1000000;
    let C;
    C = C_byte0 + C_byte1 * 0x100 + C_byte2 * 0x10000 + C_byte3 * 0x1000000;

    link => C_byte0 = byte_binary.run(operation_id, A_byte0, B_byte0);
    link => C_byte1 = byte_binary.run(operation_id, A_byte1, B_byte1);
    link => C_byte2 = byte_binary.run(operation_id, A_byte2, B_byte2);
    link => C_byte3 = byte_binary.run(operation_id, A_byte3, B_byte3);
}

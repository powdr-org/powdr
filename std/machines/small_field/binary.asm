use std::utils::unchanged_until;
use std::machines::binary::ByteBinary;
use std::field::modulus;
use std::check::require_field_bits;

// Computes bitwise operations on two 32-bit numbers
// decomposed into 4 bytes each.
machine Binary8(byte_binary: ByteBinary) with
    latch: latch,
    operation_id: operation_id,
    // Allow this machine to be connected via a permutation
    call_selectors: sel,
{
    require_field_bits(8, || "Binary8 requires a field that fits any 8-Bit value.");

    operation and<0> A1, A2, A3, A4, B1, B2, B3, B4 -> C1, C2, C3, C4;

    operation or<1> A1, A2, A3, A4, B1, B2, B3, B4 -> C1, C2, C3, C4;

    operation xor<2> A1, A2, A3, A4, B1, B2, B3, B4 -> C1, C2, C3, C4;

    let operation_id;

    let latch: col = std::well_known::one;

    let A1;
    let A2;
    let A3;
    let A4;
    let B1;
    let B2;
    let B3;
    let B4;
    let C1; 
    let C2; 
    let C3; 
    let C4;

    link => C1 = byte_binary.run(operation_id, A1, B1);
    link => C2 = byte_binary.run(operation_id, A2, B2);
    link => C3 = byte_binary.run(operation_id, A3, B3);
    link => C4 = byte_binary.run(operation_id, A4, B4);
}

// Computes bitwise operations on two 32-bit numbers
// decomposed into two 16-bit limbs each.
machine Binary(byte_binary: ByteBinary) with
    latch: latch,
    operation_id: operation_id,
    // Allow this machine to be connected via a permutation
    call_selectors: sel,
{
    require_field_bits(16, || "Binary8 requires a field that fits any 16-Bit value.");

    operation and<0> I1, I2, I3, I4 -> O1, O2;
    operation or<1> I1, I2, I3, I4 -> O1, O2;
    operation xor<2> I1, I2, I3, I4 -> O1, O2;

    let operation_id;

    let latch: col = |i| { 1 };

    let I1: inter = A1 + 256 * A2;
    let I2: inter = A3 + 256 * A4;
    let I3: inter = B1 + 256 * B2;
    let I4: inter = B3 + 256 * B4;
    let O1: inter = C1 + 256 * C2;
    let O2: inter = C3 + 256 * C4;

    let A1;
    let A2;
    let A3;
    let A4;
    let B1;
    let B2;
    let B3;
    let B4;
    let C1; 
    let C2; 
    let C3; 
    let C4;

    link => C1 = byte_binary.run(operation_id, A1, B1);
    link => C2 = byte_binary.run(operation_id, A2, B2);
    link => C3 = byte_binary.run(operation_id, A3, B3);
    link => C4 = byte_binary.run(operation_id, A4, B4);
}

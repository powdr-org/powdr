use std::prelude::Query;
use super::ByteCompare;

// Splits an arbitrary field element into 8 u32s (in little endian order), on the BN254 field.
machine SplitBN254(byte_compare: ByteCompare) with
    latch: RESET,
    // Allow this machine to be connected via a permutation
    call_selectors: sel,
{
    operation split in_acc -> o1, o2, o3, o4, o5, o6, o7, o8;

    // Latch and operation ID
    col fixed RESET(i) { if i % 32 == 31 { 1 } else { 0 } };

    // 1. Decompose the input into bytes

    // The byte decomposition of the input, in little-endian order
    // and shifted forward by one (to use the last row of the
    // previous block)
    // A hint is provided because automatic witness generation does not
    // understand step 3 to figure out that the byte decomposition is unique.
    let select_byte: fe, int -> fe = |input, byte| std::convert::fe((std::convert::int(input) >> (byte * 8)) & 0xff);
    col witness bytes;
    query |i| {
        std::prover::provide_value(bytes, i, select_byte(std::prover::eval(in_acc'), (i + 1) % 32));
    };
    // Puts the bytes together to form the input
    col witness in_acc;
    // Factors to multiply the bytes by
    col fixed FACTOR(i) { 1 << (((i + 1) % 32) * 8) };

    in_acc' = (1 - RESET) * in_acc + bytes * FACTOR;

    // 2. Build the output, packing chunks of 4 bytes (i.e., 32 bit) into a field element
    col witness o1, o2, o3, o4, o5, o6, o7, o8;
    col fixed FACTOR_OUTPUT1 = [0x100, 0x10000, 0x1000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]*;
    col fixed FACTOR_OUTPUT2 = [0, 0, 0, 1, 0x100, 0x10000, 0x1000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]*;
    col fixed FACTOR_OUTPUT3 = [0, 0, 0, 0, 0, 0, 0, 1, 0x100, 0x10000, 0x1000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]*;
    col fixed FACTOR_OUTPUT4 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0x100, 0x10000, 0x1000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]*;
    col fixed FACTOR_OUTPUT5 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0x100, 0x10000, 0x1000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]*;
    col fixed FACTOR_OUTPUT6 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0x100, 0x10000, 0x1000000, 0, 0, 0, 0, 0, 0, 0, 0, 0]*;
    col fixed FACTOR_OUTPUT7 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0x100, 0x10000, 0x1000000, 0, 0, 0, 0, 0]*;
    col fixed FACTOR_OUTPUT8 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0x100, 0x10000, 0x1000000, 0]*;

    o1' = (1 - RESET) * o1 + bytes * FACTOR_OUTPUT1;
    o2' = (1 - RESET) * o2 + bytes * FACTOR_OUTPUT2;
    o3' = (1 - RESET) * o3 + bytes * FACTOR_OUTPUT3;
    o4' = (1 - RESET) * o4 + bytes * FACTOR_OUTPUT4;
    o5' = (1 - RESET) * o5 + bytes * FACTOR_OUTPUT5;
    o6' = (1 - RESET) * o6 + bytes * FACTOR_OUTPUT6;
    o7' = (1 - RESET) * o7 + bytes * FACTOR_OUTPUT7;
    o8' = (1 - RESET) * o8 + bytes * FACTOR_OUTPUT8;

    // 3. Check that the byte decomposition does not overflow
    //
    //    Skipping this step would work but it wouldn't be sound, because
    //    the 32-byte decomposition could overflow, since the BN254 scalar field
    //    prime is smaller than 2^256.
    //
    //    The approach is to compare the byte decomposition with that of
    //    the maximum possible value (p - 1) byte by byte,
    //    from most significant to least significant (i.e., going backwards).
    //    A byte can only be larger than that of the max value if any previous
    //    byte has been smaller.
    //    See wrap_gl.asm for an example.

    // Bytes of the maximum value, in little endian order, rotated by one
    // For BN254, p = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001,
    // so the maximum value is 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000.
    col fixed BYTES_MAX = [0x00, 0x00, 0xf0, 0x93, 0xf5, 0xe1, 0x43, 0x91, 0x70, 0xb9, 0x79, 0x48, 0xe8, 0x33, 0x28, 0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e, 0x64, 0x30, 0x00]*;

    // Compare the current byte with the corresponding byte of the maximum value.
    col witness lt;
    col witness gt;
    link => (lt, gt) = byte_compare.run(bytes, BYTES_MAX);

    // Compute whether the current or any previous byte has been less than
    // the corresponding byte of the maximum value.
    // This moves *backward* from the second to last row.
    col witness was_lt;
    was_lt = RESET' * lt + (1 - RESET') * (was_lt' + lt - was_lt' * lt);

    // If any byte is larger, but no previous byte was smaller, the byte
    // decomposition has overflowed and should be rejected.
    gt * (1 - was_lt) = 0;
}

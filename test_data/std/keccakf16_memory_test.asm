use std::machines::hash::keccakf16_memory::Keccakf16Memory;
use std::machines::small_field::memory::Memory;
use std::machines::range::Byte2;
use std::machines::range::Bit12;

let main_degree: int = 2**7;
let add_sub_degree: int = 2**9;
let memory_degree: int = 2**9;
let keccakf_memory_degree: int = 2**7;

machine Main with degree: main_degree {
    reg pc[@pc];

    reg X1[<=];
    reg X2[<=];

    reg Y1[<=];
    reg Y2[<=];

    Byte2 byte2;
    Bit12 bit12;
    Memory memory(bit12, byte2, memory_degree, memory_degree);

    Keccakf16Memory keccakf16_memory(memory, keccakf_memory_degree, keccakf_memory_degree);

    // Increase time step by 2 in each row, because keccakf16_memory reads in step `i` and writes in step `i + 1`.
    col fixed STEP(i) { 2 * i };

    // Big endian.
    // Usage: mstore addr_h, addr_l, val_h, val_l
    instr mstore X1, X2, Y1, Y2 -> link ~> memory.mstore(X1, X2, STEP, Y1, Y2);
    // Usage: keccakf16_memory input_addr_h, input_addr_l, output_addr_h, output_addr_l;
    instr keccakf16_memory X1, X2, Y1, Y2 -> link ~> keccakf16_memory.keccakf16_memory(X1, X2, Y1, Y2, STEP);

    col witness val_h, val_l;
    // Usage: assert_eq addr_h, addr_l, val_h, val_l
    instr assert_eq X1, X2, Y1, Y2 ->
        link ~> (val_h, val_l) = memory.mload(X1, X2, STEP)
    {
        val_h = Y1,
        val_l = Y2
    }

    function main {
        // Test 1: Input/output address computations have no carry.
        // 0 for all 25 64-bit inputs except setting the second 64-bit input to 1. All 64-bit inputs in chunks of 4 16-bit big endian limbs.
        mstore 0, 0, 0, 0;
        mstore 0, 4, 0, 0;
        mstore 0, 8, 0, 0;
        mstore 0, 12, 0, 1;
        mstore 0, 16, 0, 0;
        mstore 0, 20, 0, 0;
        mstore 0, 24, 0, 0;
        mstore 0, 28, 0, 0;
        mstore 0, 32, 0, 0;
        mstore 0, 36, 0, 0;
        mstore 0, 40, 0, 0;
        mstore 0, 44, 0, 0;
        mstore 0, 48, 0, 0;
        mstore 0, 52, 0, 0;
        mstore 0, 56, 0, 0;
        mstore 0, 60, 0, 0;
        mstore 0, 64, 0, 0;
        mstore 0, 68, 0, 0;
        mstore 0, 72, 0, 0;
        mstore 0, 76, 0, 0;
        mstore 0, 80, 0, 0;
        mstore 0, 84, 0, 0;
        mstore 0, 88, 0, 0;
        mstore 0, 92, 0, 0;
        mstore 0, 96, 0, 0;
        // Input address 0. Output address 200.
        keccakf16_memory 0, 0, 0, 200;
        // Selectively checking a few registers only.
        // Test vector generated from Tiny Keccak.
        assert_eq 0, 200, 0xfdbb, 0xbbdf;
        assert_eq 0, 204, 0x9001, 0x405f;
        assert_eq 0, 392, 0xeac9, 0xf006;
        assert_eq 0, 396, 0x664d, 0xeb35;

        // Test 2: Same as Test 1 but sets input and output addresses to be the same.
        // No need to rerun the mstores because input values from Test 1 should be intact.
        keccakf16_memory 0, 0, 0, 0;
        // Selectively checking a few registers only.
        // Test vector generated from Tiny Keccak.
        assert_eq 0, 0, 0xfdbb, 0xbbdf;
        assert_eq 0, 4, 0x9001, 0x405f;
        assert_eq 0, 192, 0xeac9, 0xf006;
        assert_eq 0, 196, 0x664d, 0xeb35;

        // Test 3: Input/output address computations have carry.
        // 0 for all 25 64-bit inputs except setting the second 64-bit input to 1. All 64-bit inputs in chunks of 4 16-bit big endian limbs.
        mstore 100, 65520, 0, 0;
        mstore 100, 65524, 0, 0;
        mstore 100, 65528, 0, 0;
        mstore 100, 65532, 0, 1;
        mstore 101, 0, 0, 0;
        mstore 101, 4, 0, 0;
        mstore 101, 8, 0, 0;
        mstore 101, 12, 0, 0;
        mstore 101, 16, 0, 0;
        mstore 101, 20, 0, 0;
        mstore 101, 24, 0, 0;
        mstore 101, 28, 0, 0;
        mstore 101, 32, 0, 0;
        mstore 101, 36, 0, 0;
        mstore 101, 40, 0, 0;
        mstore 101, 44, 0, 0;
        mstore 101, 48, 0, 0;
        mstore 101, 52, 0, 0;
        mstore 101, 56, 0, 0;
        mstore 101, 60, 0, 0;
        mstore 101, 64, 0, 0;
        mstore 101, 68, 0, 0;
        mstore 101, 72, 0, 0;
        mstore 101, 76, 0, 0;
        mstore 101, 80, 0, 0;

        // Input address (100 * 65536 + 65520). Output address (50000 * 65536 + 65528).
        keccakf16_memory 100, 65520, 50000, 65528;

        // Selectively checking a few registers only.
        // Test vector generated from Tiny Keccak.
        assert_eq 50000, 65528, 0xfdbb, 0xbbdf;
        assert_eq 50000, 65532, 0x9001, 0x405f;
        assert_eq 50001, 184, 0xeac9, 0xf006;
        assert_eq 50001, 188, 0x664d, 0xeb35;

        return;
    }
}

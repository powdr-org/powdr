use std::machines::hash::poseidon2_bb::Poseidon2BB;
use std::machines::range::Byte2;
use std::machines::range::Bit12;
use std::machines::small_field::memory::Memory;
use std::machines::split::ByteCompare;
use std::machines::split::split_bb::SplitBB;

let main_degree: int = 2**16;
let memory_degree: int = 2**16;
let poseidon2_degree: int = 2**16;
let split_bb_degree: int = 2**16;

machine Main with degree: main_degree {
    reg pc[@pc];
    reg X1[<=];
    reg X2[<=];
    reg ADDR1_LOW[<=];
    reg ADDR1_HIGH[<=];
    reg ADDR2_LOW[<=];
    reg ADDR2_HIGH[<=];

    ByteCompare byte_compare;
    SplitBB split(byte_compare, split_bb_degree, split_bb_degree);

    // Increase the time step by 2 in each row, so that the poseidon machine
    // can read in the given time step and write in the next time step.
    col fixed STEP(i) { 2 * i };
    Byte2 byte2;
    Bit12 bit12;
    Memory memory(bit12, byte2, memory_degree, memory_degree);
    instr mstore_le ADDR1_HIGH, ADDR1_LOW, X1, X2 ->
        link ~> memory.mstore(ADDR1_HIGH, ADDR1_LOW, STEP, X1, X2);

    Poseidon2BB poseidon2(memory, split, poseidon2_degree, poseidon2_degree);
    instr poseidon2 ADDR1_HIGH, ADDR1_LOW, ADDR2_HIGH, ADDR2_LOW ->
        link ~> poseidon2.poseidon2_permutation(
            ADDR1_HIGH, ADDR1_LOW,
            ADDR2_HIGH, ADDR2_LOW,
            STEP
        );

    col witness val_low, val_high;
    instr assert_eq ADDR1_HIGH, ADDR1_LOW, X1 ->
        link ~> (val_high, val_low) = memory.mload(ADDR1_HIGH, ADDR1_LOW, STEP)
    {
        val_low + 2**16 * val_high = X1
    }

    function main {

        // Test vectors generated by gen_poseidon2_bb_consts

        // All zeros:
        mstore_le 0, 0, 0, 0;
        mstore_le 0, 4, 0, 0;
        mstore_le 0, 8, 0, 0;
        mstore_le 0, 12, 0, 0;
        mstore_le 0, 16, 0, 0;
        mstore_le 0, 20, 0, 0;
        mstore_le 0, 24, 0, 0;
        mstore_le 0, 28, 0, 0;
        mstore_le 0, 32, 0, 0;
        mstore_le 0, 36, 0, 0;
        mstore_le 0, 40, 0, 0;
        mstore_le 0, 44, 0, 0;
        mstore_le 0, 48, 0, 0;
        mstore_le 0, 52, 0, 0;
        mstore_le 0, 56, 0, 0;
        mstore_le 0, 60, 0, 0;

        poseidon2 0, 0, 0, 0;

        assert_eq 0, 0, 248801356;
        assert_eq 0, 4, 1685558007;
        assert_eq 0, 8, 720497725;
        assert_eq 0, 12, 956335022;
        assert_eq 0, 16, 321739953;
        assert_eq 0, 20, 208179186;
        assert_eq 0, 24, 1631289420;
        assert_eq 0, 28, 1989448950;

        // All ones:
        mstore_le 0, 0, 0, 1;
        mstore_le 0, 4, 0, 1;
        mstore_le 0, 8, 0, 1;
        mstore_le 0, 12, 0, 1;
        mstore_le 0, 16, 0, 1;
        mstore_le 0, 20, 0, 1;
        mstore_le 0, 24, 0, 1;
        mstore_le 0, 28, 0, 1;
        mstore_le 0, 32, 0, 1;
        mstore_le 0, 36, 0, 1;
        mstore_le 0, 40, 0, 1;
        mstore_le 0, 44, 0, 1;
        mstore_le 0, 48, 0, 1;
        mstore_le 0, 52, 0, 1;
        mstore_le 0, 56, 0, 1;
        mstore_le 0, 60, 0, 1;

        poseidon2 0, 0, 0, 0;

        assert_eq 0, 0, 825643358;
        assert_eq 0, 4, 1347291127;
        assert_eq 0, 8, 575415694;
        assert_eq 0, 12, 739008160;
        assert_eq 0, 16, 1041909928;
        assert_eq 0, 20, 1744130887;
        assert_eq 0, 24, 1806932542;
        assert_eq 0, 28, 1046987717;

        // All elements are -1 (in BabyBear, 0x78000000)
        mstore_le 0, 0, 30720, 0;
        mstore_le 0, 4, 30720, 0;
        mstore_le 0, 8, 30720, 0;
        mstore_le 0, 12, 30720, 0;
        mstore_le 0, 16, 30720, 0;
        mstore_le 0, 20, 30720, 0;
        mstore_le 0, 24, 30720, 0;
        mstore_le 0, 28, 30720, 0;
        mstore_le 0, 32, 30720, 0;
        mstore_le 0, 36, 30720, 0;
        mstore_le 0, 40, 30720, 0;
        mstore_le 0, 44, 30720, 0;
        mstore_le 0, 48, 30720, 0;
        mstore_le 0, 52, 30720, 0;
        mstore_le 0, 56, 30720, 0;
        mstore_le 0, 60, 30720, 0;

        poseidon2 0, 0, 0, 0;

        assert_eq 0, 0, 1841881823;
        assert_eq 0, 4, 149754252;
        assert_eq 0, 8, 1077798821;
        assert_eq 0, 12, 1282588023;
        assert_eq 0, 16, 761789559;
        assert_eq 0, 20, 703958163;
        assert_eq 0, 24, 332297247;
        assert_eq 0, 28, 1325149063;

        // Some other values (ported from poseidon_gl test):
        mstore_le 0, 0, 14, 6474;
        mstore_le 0, 4, 3225, 31229;
        mstore_le 0, 8, 13499, 22633;
        mstore_le 0, 12, 1, 47334;
        mstore_le 0, 16, 26147, 51257;
        mstore_le 0, 20, 14081, 12102;
        mstore_le 0, 24, 25381, 5145;
        mstore_le 0, 28, 0, 2087;
        mstore_le 0, 32, 0, 0;
        mstore_le 0, 36, 0, 0;
        mstore_le 0, 40, 0, 0;
        mstore_le 0, 44, 0, 0;
        mstore_le 0, 48, 0, 0;
        mstore_le 0, 52, 0, 0;
        mstore_le 0, 56, 0, 0;
        mstore_le 0, 60, 0, 0;

        poseidon2 0, 0, 0, 0;

        assert_eq 0, 0, 117705446;
        assert_eq 0, 4, 1986873944;
        assert_eq 0, 8, 1758310750;
        assert_eq 0, 12, 562581070;
        assert_eq 0, 16, 1115248905;
        assert_eq 0, 20, 1754580351;
        assert_eq 0, 24, 757697741;
        assert_eq 0, 28, 971587237;

        // Repeat the first test, but be fancy with the memory pointers being passed:
        mstore_le 42, 65520, 0, 1;
        mstore_le 42, 65524, 0, 1;
        mstore_le 42, 65528, 0, 1;
        mstore_le 42, 65532, 0, 1;
        mstore_le 43, 0, 0, 1;
        mstore_le 43, 4, 0, 1;
        mstore_le 43, 8, 0, 1;
        mstore_le 43, 12, 0, 1;
        mstore_le 43, 16, 0, 1;
        mstore_le 43, 20, 0, 1;
        mstore_le 43, 24, 0, 1;
        mstore_le 43, 28, 0, 1;
        mstore_le 43, 32, 0, 1;
        mstore_le 43, 36, 0, 1;
        mstore_le 43, 40, 0, 1;
        mstore_le 43, 44, 0, 1;

        // This will read 64 bytes starting at address 0x002afff0 and
        // write the result to bytes starting at address 0x002afff4.
        // Both operations should overflow the lower 16 bits of the address.
        poseidon2 42, 65520, 42, 65524;

        assert_eq 42, 65524, 825643358;
        assert_eq 42, 65528, 1347291127;
        assert_eq 42, 65532, 575415694;
        assert_eq 43, 0, 739008160;
        assert_eq 43, 4, 1041909928;
        assert_eq 43, 8, 1744130887;
        assert_eq 43, 12, 1806932542;
        assert_eq 43, 16, 1046987717;

        return;
    }
}

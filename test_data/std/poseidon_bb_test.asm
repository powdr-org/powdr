use std::machines::hash::poseidon_bb::PoseidonBB;
use std::machines::range::Byte2;
use std::machines::memory_bb::Memory;
use std::machines::split::ByteCompare;
use std::machines::split::split_gl::SplitGL;

machine Main with degree: 65536 {
    reg pc[@pc];
    reg X1[<=];
    reg X2[<=];
    reg ADDR1[<=];
    reg ADDR2[<=];

    ByteCompare byte_compare;
    SplitGL split(byte_compare);

    // Increase the time step by 2 in each row, so that the poseidon machine
    // can read in the given time step and write in the next time step.
    col fixed STEP(i) { 2 * i };
    Byte2 byte2;
    Memory memory(byte2);
    instr mstore_le ADDR1, X1, X2 ->
        link ~> memory.mstore(ADDR1, STEP, X1, X2);

    PoseidonBB poseidon(memory, split);
    instr poseidon ADDR1, ADDR2 -> link ~> poseidon.poseidon_permutation(ADDR1, ADDR2, STEP);

    col witness val_low, val_high;
    instr assert_eq ADDR1, X1 ->
        link ~> (val_high, val_low) = memory.mload(ADDR1, STEP)
    {
        val_low + 2**16 * val_high = X1
    }

    function main {

        // Test vectors generated by gen_poseidon_bb_consts

        // All zeros:
        mstore_le 0, 0, 0;
        mstore_le 4, 0, 0;
        mstore_le 8, 0, 0;
        mstore_le 12, 0, 0;
        mstore_le 16, 0, 0;
        mstore_le 20, 0, 0;
        mstore_le 24, 0, 0;
        mstore_le 28, 0, 0;
        mstore_le 32, 0, 0;
        mstore_le 36, 0, 0;
        mstore_le 40, 0, 0;
        mstore_le 44, 0, 0;
        mstore_le 48, 0, 0;
        mstore_le 52, 0, 0;
        mstore_le 56, 0, 0;
        mstore_le 60, 0, 0;

        poseidon 0, 0;

        assert_eq 0, 1660083390;
        assert_eq 4, 822822994;
        assert_eq 8, 1459131013;
        assert_eq 12, 1160269290;
        assert_eq 16, 1288171012;
        assert_eq 20, 317805207;
        assert_eq 24, 737788224;
        assert_eq 28, 1834068177;

        // All ones:
        mstore_le 0, 0, 1;
        mstore_le 4, 0, 1;
        mstore_le 8, 0, 1;
        mstore_le 12, 0, 1;
        mstore_le 16, 0, 1;
        mstore_le 20, 0, 1;
        mstore_le 24, 0, 1;
        mstore_le 28, 0, 1;
        mstore_le 32, 0, 1;
        mstore_le 36, 0, 1;
        mstore_le 40, 0, 1;
        mstore_le 44, 0, 1;
        mstore_le 48, 0, 1;
        mstore_le 52, 0, 1;
        mstore_le 56, 0, 1;
        mstore_le 60, 0, 1;

        poseidon 0, 0;

        assert_eq 0, 1011739672;
        assert_eq 4, 1842770587;
        assert_eq 8, 597411354;
        assert_eq 12, 1738754754;
        assert_eq 16, 1241091968;
        assert_eq 20, 1909530106;
        assert_eq 24, 1537366805;
        assert_eq 28, 1323132177;

        // All elements are -1 (in BabyBear, 0x78000000)
        mstore_le 0, 30720, 0;
        mstore_le 4, 30720, 0;
        mstore_le 8, 30720, 0;
        mstore_le 12, 30720, 0;
        mstore_le 16, 30720, 0;
        mstore_le 20, 30720, 0;
        mstore_le 24, 30720, 0;
        mstore_le 28, 30720, 0;
        mstore_le 32, 30720, 0;
        mstore_le 36, 30720, 0;
        mstore_le 40, 30720, 0;
        mstore_le 44, 30720, 0;
        mstore_le 48, 30720, 0;
        mstore_le 52, 30720, 0;
        mstore_le 56, 30720, 0;
        mstore_le 60, 30720, 0;

        poseidon 0, 0;

        assert_eq 0, 1231911417;
        assert_eq 4, 1457704645;
        assert_eq 8, 482354127;
        assert_eq 12, 1107490518;
        assert_eq 16, 1908524417;
        assert_eq 20, 505286822;
        assert_eq 24, 872747879;
        assert_eq 28, 820943313;

        // Some other values (ported from poseidon_gl test):
        mstore_le 0, 14, 6474;
        mstore_le 4, 3225, 31229;
        mstore_le 8, 13499, 22633;
        mstore_le 12, 1, 47334;
        mstore_le 16, 26147, 51257;
        mstore_le 20, 14081, 12102;
        mstore_le 24, 25381, 5145;
        mstore_le 28, 0, 2087;
        mstore_le 32, 0, 0;
        mstore_le 36, 0, 0;
        mstore_le 40, 0, 0;
        mstore_le 44, 0, 0;
        mstore_le 48, 0, 0;
        mstore_le 52, 0, 0;
        mstore_le 56, 0, 0;
        mstore_le 60, 0, 0;

        poseidon 0, 0;

        assert_eq 0, 493586113;
        assert_eq 4, 1137126664;
        assert_eq 8, 283902149;
        assert_eq 12, 244408331;
        assert_eq 16, 1254081394;
        assert_eq 20, 268224531;
        assert_eq 24, 429035219;
        assert_eq 28, 1897473309;

        // Repeat the first test, but be fancy with the memory pointers being passed:
        mstore_le 100, 0, 0;
        mstore_le 104, 0, 0;
        mstore_le 108, 0, 0;
        mstore_le 112, 0, 0;
        mstore_le 116, 0, 0;
        mstore_le 120, 0, 0;
        mstore_le 124, 0, 0;
        mstore_le 128, 0, 0;
        mstore_le 132, 0, 0;
        mstore_le 136, 0, 0;
        mstore_le 140, 0, 0;
        mstore_le 144, 0, 0;
        mstore_le 148, 0, 0;
        mstore_le 152, 0, 0;
        mstore_le 156, 0, 0;
        mstore_le 160, 0, 0;

        // This will read bytes [100, 164) and write the result to bytes [104, 136)
        poseidon 100, 104;

        assert_eq 104, 1660083390;
        assert_eq 108, 822822994;
        assert_eq 112, 1459131013;
        assert_eq 116, 1160269290;
        assert_eq 120, 1288171012;
        assert_eq 124, 317805207;
        assert_eq 128, 737788224;
        assert_eq 132, 1834068177;

        return;
    }
}

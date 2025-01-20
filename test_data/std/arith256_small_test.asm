use std::machines::small_field::arith256::Arith256;

let main_degree: int = 2**7;
let arith_degree: int = 2**10;

machine Main with degree: main_degree {
    reg pc[@pc];
    reg A0[<=];
    reg A1[<=];
    reg A2[<=];
    reg A3[<=];
    reg A4[<=];
    reg A5[<=];
    reg A6[<=];
    reg A7[<=];
    reg A8[<=];
    reg A9[<=];
    reg A10[<=];
    reg A11[<=];
    reg A12[<=];
    reg A13[<=];
    reg A14[<=];
    reg A15[<=];
    reg B0[<=];
    reg B1[<=];
    reg B2[<=];
    reg B3[<=];
    reg B4[<=];
    reg B5[<=];
    reg B6[<=];
    reg B7[<=];
    reg B8[<=];
    reg B9[<=];
    reg B10[<=];
    reg B11[<=];
    reg B12[<=];
    reg B13[<=];
    reg B14[<=];
    reg B15[<=];
    reg C0[<=];
    reg C1[<=];
    reg C2[<=];
    reg C3[<=];
    reg C4[<=];
    reg C5[<=];
    reg C6[<=];
    reg C7[<=];
    reg C8[<=];
    reg C9[<=];
    reg C10[<=];
    reg C11[<=];
    reg C12[<=];
    reg C13[<=];
    reg C14[<=];
    reg C15[<=];
    reg D0[<=];
    reg D1[<=];
    reg D2[<=];
    reg D3[<=];
    reg D4[<=];
    reg D5[<=];
    reg D6[<=];
    reg D7[<=];
    reg D8[<=];
    reg D9[<=];
    reg D10[<=];
    reg D11[<=];
    reg D12[<=];
    reg D13[<=];
    reg D14[<=];
    reg D15[<=];
    reg E0[<=];
    reg E1[<=];
    reg E2[<=];
    reg E3[<=];
    reg E4[<=];
    reg E5[<=];
    reg E6[<=];
    reg E7[<=];
    reg E8[<=];
    reg E9[<=];
    reg E10[<=];
    reg E11[<=];
    reg E12[<=];
    reg E13[<=];
    reg E14[<=];
    reg E15[<=];
    reg F0[<=];
    reg F1[<=];
    reg F2[<=];
    reg F3[<=];
    reg F4[<=];
    reg F5[<=];
    reg F6[<=];
    reg F7[<=];
    reg F8[<=];
    reg F9[<=];
    reg F10[<=];
    reg F11[<=];
    reg F12[<=];
    reg F13[<=];
    reg F14[<=];
    reg F15[<=];
    
    reg t_0_0;
    reg t_0_1;
    reg t_0_2;
    reg t_0_3;
    reg t_0_4;
    reg t_0_5;
    reg t_0_6;
    reg t_0_7;
    reg t_0_8;
    reg t_0_9;
    reg t_0_10;
    reg t_0_11;
    reg t_0_12;
    reg t_0_13;
    reg t_0_14;
    reg t_0_15;
    reg t_1_0;
    reg t_1_1;
    reg t_1_2;
    reg t_1_3;
    reg t_1_4;
    reg t_1_5;
    reg t_1_6;
    reg t_1_7;
    reg t_1_8;
    reg t_1_9;
    reg t_1_10;
    reg t_1_11;
    reg t_1_12;
    reg t_1_13;
    reg t_1_14;
    reg t_1_15;

    Arith256 arith(arith_degree, arith_degree);

    instr affine_256 A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, C0, C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15 -> D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, E0, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15
        link ~> (D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, E0, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15) = arith.affine_256(A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, C0, C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15);

    instr assert_eq A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15 {
        A0 = B0,
        A1 = B1,
        A2 = B2,
        A3 = B3,
        A4 = B4,
        A5 = B5,
        A6 = B6,
        A7 = B7,
        A8 = B8,
        A9 = B9,
        A10 = B10,
        A11 = B11,
        A12 = B12,
        A13 = B13,
        A14 = B14,
        A15 = B15
    }

    function main {
        // 0x0000000011111111222222223333333344444444555555556666666677777777
        // * 0x8888888899999999aaaaaaaabbbbbbbbccccccccddddddddeeeeeeeeffffffff
        // + 0xaaaaaaaabbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbaaaaaaaa
        // == 0x91a2b3c579be024740da740e6f8091a38e38e38f258bf259be024691fdb97530da740da60b60b60907f6e5d369d0369ca8641fda1907f6e33333333
        // == 0x00000000_091a2b3c_579be024_740da740_e6f8091a_38e38e38_f258bf25_9be02469 * 2**256 + 0x1fdb9753_0da740da_60b60b60_907f6e5d_369d0369_ca8641fd_a1907f6e_33333333

        t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15 <== affine_256(
            0x7777, 0x7777, 0x6666, 0x6666, 0x5555, 0x5555, 0x4444, 0x4444, 0x3333, 0x3333, 0x2222, 0x2222, 0x1111, 0x1111, 0x0000, 0x0000,
            0xffff, 0xffff, 0xeeee, 0xeeee, 0xdddd, 0xdddd, 0xcccc, 0xcccc, 0xbbbb, 0xbbbb, 0xaaaa, 0xaaaa, 0x9999, 0x9999, 0x8888, 0x8888,
            0xaaaa, 0xaaaa, 0xbbbb, 0xbbbb, 0xbbbb, 0xbbbb, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xbbbb, 0xbbbb, 0xbbbb, 0xbbbb, 0xaaaa, 0xaaaa);
        
        assert_eq t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, 0x2469, 0x9be0, 0xbf25, 0xf258, 0x8e38, 0x38e3, 0x091a, 0xe6f8, 0xa740, 0x740d, 0xe024, 0x579b, 0x2b3c, 0x091a, 0x0000, 0x0000;
        assert_eq t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15, 0x3333, 0x3333, 0x7f6e, 0xa190, 0x41fd, 0xca86, 0x0369, 0x369d, 0x6e5d, 0x907f, 0x0b60, 0x60b6, 0x40da, 0x0da7, 0x9753, 0x1fdb;

        // Test vectors from: https://github.com/0xPolygonHermez/zkevm-proverjs/blob/a4006af3d7fe4a57a85500c01dc791fb5013cef0/test/sm/sm_arith.js

        // 2 * 3 + 5 = 11
        t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15 <== affine_256(
            2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
        assert_eq t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        assert_eq t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;

        // 256 * 256 + 1 = 65537
        t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15 <== affine_256(
            256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
        assert_eq t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        assert_eq t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;

        // 3000 * 2000 + 5000 = 6005000
        t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15 <== affine_256(
            3000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            2000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            5000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
        assert_eq t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        assert_eq t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15, 0xa108, 0x5b, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;

        // 3000000 * 2000000 + 5000000 = 6000005000000
        t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15 <== affine_256(
            0xc6c0, 0x2d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0x8480, 0x1e, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0x4b40, 0x4c, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
        assert_eq t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        assert_eq t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15, 0xab40, 0xfc2a, 0x574, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;


        // 3000 * 0 + 5000 = 5000
        t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15 <== affine_256(
            3000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            5000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
        assert_eq t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        assert_eq t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15, 5000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;

        // 2**255 * 2 + 0 = 2 ** 256
        t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15 <== affine_256(
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x8000,
            2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
        assert_eq t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        assert_eq t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;

        // (2**256 - 1) * (2**256 - 1) + (2**256 - 1) = 2 ** 256 * 115792089237316195423570985008687907853269984665640564039457584007913129639935
        // = 2 ** 256 * 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
        t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15 <== affine_256(
            0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
            0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
            0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff);
        assert_eq t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff;
        assert_eq t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;

        // (2**256 - 1) * 1 + (2**256 - 1) = 2 ** 256 + 115792089237316195423570985008687907853269984665640564039457584007913129639934
        // = 2 ** 256 + 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
        t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15 <== affine_256(
            0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff);
        assert_eq t_0_0, t_0_1, t_0_2, t_0_3, t_0_4, t_0_5, t_0_6, t_0_7, t_0_8, t_0_9, t_0_10, t_0_11, t_0_12, t_0_13, t_0_14, t_0_15, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        assert_eq t_1_0, t_1_1, t_1_2, t_1_3, t_1_4, t_1_5, t_1_6, t_1_7, t_1_8, t_1_9, t_1_10, t_1_11, t_1_12, t_1_13, t_1_14, t_1_15, 0xfffe, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff;
    }
}

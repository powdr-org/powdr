use std::machines::binary::ByteBinary;
use std::machines::large_field::binary::Binary;

let main_degree: int = 2**7;
let binary_degree: int = 2**5;

machine Main with degree: main_degree {
    reg pc[@pc];
    reg X0[<=];
    reg X1[<=];
    reg X2[<=];
    reg A;

    ByteBinary byte_binary;
    Binary binary(byte_binary, binary_degree, binary_degree);

    instr and X0, X1 -> X2 link ~> X2 = binary.and(X0, X1);
    instr or X0, X1 -> X2 link ~> X2 = binary.or(X0, X1);
    instr xor X0, X1 -> X2 link ~> X2 = binary.xor(X0, X1);

    instr assert_eq X0, X1 {
        X0 = X1
    }

    function main {

        // AND
        A <== and(0, 0);
        assert_eq A, 0;
        A <== and(0xffffffff, 0xffffffff);
        assert_eq A, 0xffffffff;
        A <== and(0xffffffff, 0xabcdef01);
        assert_eq A, 0xabcdef01;
        A <== and(0xabcdef01, 0xffffffff);
        assert_eq A, 0xabcdef01;
        A <== and(0, 0xabcdef01);
        assert_eq A, 0;
        A <== and(0xabcdef01, 0);
        assert_eq A, 0;

        // OR
        A <== or(0, 0);
        assert_eq A, 0;
        A <== or(0xffffffff, 0xffffffff);
        assert_eq A, 0xffffffff;
        A <== or(0xffffffff, 0xabcdef01);
        assert_eq A, 0xffffffff;
        A <== or(0xabcdef01, 0xffffffff);
        assert_eq A, 0xffffffff;
        A <== or(0, 0xabcdef01);
        assert_eq A, 0xabcdef01;
        A <== or(0xabcdef01, 0);
        assert_eq A, 0xabcdef01;

        // XOR
        A <== xor(0, 0);
        assert_eq A, 0;
        A <== xor(0xffffffff, 0xffffffff);
        assert_eq A, 0;
        A <== xor(0xffffffff, 0xabcdef01);
        assert_eq A, 0x543210fe;
        A <== xor(0xabcdef01, 0xffffffff);
        assert_eq A, 0x543210fe;
        A <== xor(0, 0xabcdef01);
        assert_eq A, 0xabcdef01;
        A <== xor(0xabcdef01, 0);
        assert_eq A, 0xabcdef01;

        return;
    }
}

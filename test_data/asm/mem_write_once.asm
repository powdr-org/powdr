// Write-once memory with key (ADDR1, ADDR2) and value (v1, v2)
// This is similar to std::machines::large_field::write_once_memory::WriteOnceMemory, but has
// two address and value columns.
machine WriteOnceMemory with
    latch: LATCH
{

    operation access ADDR1, ADDR2, v1, v2 ->;

    let LATCH = 1;

    let ADDR1: col = |i| i;
    let ADDR2: col = |i| i + 1;
    let v1;
    let v2;
}

machine Main with degree: 256 {
    reg pc[@pc];
    reg X1[<=];
    reg X2[<=];
    reg Y1[<=];
    reg Y2[<=];
    reg A;
    reg B;

    WriteOnceMemory memory;
    instr mstore X1, X2, Y1, Y2 -> link => memory.access(X1, X2, Y1, Y2);
    instr mload X1, X2 -> Y1, Y2 link => memory.access(X1, X2, Y1, Y2);

    instr assert_eq X1, Y1 { X1 = Y1 }

    function main {
        mstore 17, 18, 42, 43;
        mstore 62, 63, 123, 1234;
        mstore 255, 256, -1, -2;

        // Setting the same value twice is not a problem
        mstore 17, 18, 42, 43;

        A, B <== mload(17, 18);
        assert_eq A, 42;
        assert_eq B, 43;

        A, B <== mload(62, 63);
        assert_eq A, 123;
        assert_eq B, 1234;

        A, B <== mload(255, 256);
        assert_eq A, -1;
        assert_eq B, -2;

        return;
    }
}

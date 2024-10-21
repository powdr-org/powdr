use std::machines::large_field::write_once_memory::WriteOnceMemory;

// Uses a simple write-once memory, but without an mstore operation.
// As a result, this only works if the content of the `value` column has
// been provided externally.
machine Main with degree: 256 {
    WriteOnceMemory memory;

    reg pc[@pc];
    reg X[<=];
    reg Y[<=];
    reg A;

    instr mload X -> Y link => memory.access(X,Y);
    instr assert_eq X, Y { X = Y }

    function main {
        A <== mload(17);
        assert_eq A, 42;

        A <== mload(62);
        assert_eq A, 123;

        A <== mload(255);
        assert_eq A, -1;

        return;
    }
}

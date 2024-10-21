// Very simple write-once memory that let's you store any field element at
// an address from 0 to N-1. Any value can be written only once, writing two
// different values to the same address fails. If an uninitialized cell is
// read, the returned values is unconstrained.
// A typical use-case would be to pass the `value` column as an "external"
// witness. This way the prover can provide some input vector and the program
// can read the same input multiple times.
machine WriteOnceMemory with
	latch: LATCH
{

    // Accesses the memory cell at the given address. This can be used
    // both for reading and writing, e.g.:
    //   instr mload X -> YH, YL link => memory.access(X, YH, YL);
    //   instr mstore X, YH, YL -> link => memory.access(X, YH, YL);
    operation access ADDR, value1, value2 ->;

    let LATCH = 1;

    let ADDR: col = |i| i;
    let value1;
    let value2;
}

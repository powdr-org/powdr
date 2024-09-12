machine Main with degree: 16 {
    Arith arith;

    reg pc[@pc];
    reg X[<=];
    reg Y[<=];
    reg A;
    reg Z[<=]; // we declare this assignment register last to test that the ordering does not matter

    instr add X, Y -> Z link => Z = arith.add(X, Y);
    instr mul X, Y -> Z link => Z = arith.mul(X, Y);
    instr assert_eq X, Y { X = Y }

    function main {
        A <== add(2, 1);
        A <== mul(A, 9);
        assert_eq A, 27;
        return;
    }
}

machine Arith with
    latch: latch,
    operation_id: operation_id
{

    operation add<0> x[0], x[1] -> y;
    operation mul<1> x[0], x[1] -> y;

    let latch: col = |i| 1;
    let operation_id;
    let x: col[2];
    let y;

    y = operation_id * (x[0] * x[1]) + (1 - operation_id) * (x[0] + x[1]);
}

// ANCHOR: links
machine Main(operation_id, latch) {
    Arith adder;

    operation main<0> x, y -> z;

    // on every row, add in the Adder
    link 1 x, y -> z = adder.add;

    constraints {
        col fixed operation_id = [1]*;
        col fixed latch = [1]*;

        col witness x;
        col witness y;
        col witness z;
    }
}
// ANCHOR_END: links

// ANCHOR: operations
machine Adder(operation_id, latch) {
    operation add<0> a, b -> c;
    operation sub<1> a, b -> c;

    constraints {
        col fixed operation_id = [1]*;
        col fixed latch = [1]*;

        col witness a;
        col witness b;
        col witness c;

        c = (1 - operation_id) * (a + b) + operation_id * (a - b);
    }
}
// ANCHOR_END: operations
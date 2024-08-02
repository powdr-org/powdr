machine Main with degree: 16 {
    // ANCHOR: declare_and_define
    col fixed ONES = [1]*; // this is valid
    // col fixed ONES; // this is invalid
    // ANCHOR_END: declare_and_define

    // ANCHOR: repetitions
    // valid, as for a given total length, only one column fits this definition for a given `N`
    col fixed A = [1, 2] + [3, 4]* + [5];

    // invalid, as many columns fit this definition
    // col fixed A = [1, 2]* + [3, 4]*
    // ANCHOR_END: repetitions

    // ANCHOR: mapping
    col fixed B(i) { i + 1 };

    col fixed C(i) {match i {
        0 => 1,
        _ => 0
    }};
    // ANCHOR_END: mapping
    let w;
    w = B;
}
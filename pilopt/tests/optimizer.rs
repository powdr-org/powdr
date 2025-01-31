use powdr_number::GoldilocksField;
use powdr_pil_analyzer::analyze_string;

use powdr_pilopt::optimize;
use pretty_assertions::assert_eq;

#[test]
fn replace_fixed() {
    let input = r#"namespace N(65536);
    col fixed one = [1]*;
    col fixed zero = [0]*;
    col witness X;
    col witness Y;
    query |i| {
        let _ = one;
    };
    X * one = X * zero - zero + Y;
    one * Y = zero * Y + 7 * X;
"#;
    let expectation = r#"namespace N(65536);
    col witness X;
    query |i| {
        let _: expr = 1_expr;
    };
    N::X = 7 * N::X;
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn replace_intermediate() {
    let input = r#"namespace N(65536);
    col witness X;
    col intermediate = 1;
    col other_intermediate = (intermediate - 1) * X;
    X' = X + intermediate + other_intermediate;
"#;
    let expectation = r#"namespace N(65536);
    col witness X;
    N::X' = N::X + 1;
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn deduplicate_fixed() {
    let input = r#"namespace N(65536);
    col fixed first = [1, 32]*;
    col fixed second = [1, 32]*;
    col i = first * second;
    col witness X;
    col witness Y;
    X * first = Y * second + i;
    namespace M(65536);
    col fixed first = [1, 32]*;
    col fixed second = [1, 32]*;
    col witness X;
    col witness Y;
    X * first = Y * second;
"#;
    let expectation = r#"namespace N(65536);
    col fixed first = [1_fe, 32_fe]*;
    col i = N::first * N::first;
    col witness X;
    col witness Y;
    N::X * N::first = N::Y * N::first + N::i;
namespace M(65536);
    col fixed first = [1_fe, 32_fe]*;
    col witness X;
    col witness Y;
    M::X * M::first = M::Y * M::first;
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn replace_lookup() {
    let input = r#"namespace N(65536);
    col fixed one = [1]*;
    col fixed zero = [0]*;
    col fixed two = [2]*;
    col fixed cnt(i) { i };
    col witness X;
    col witness Y;
    col witness W;
    col witness Z;
    col witness A;
    (1 - A) $ [ X, Y, A ] in [ zero, one, cnt ];
    [ Y, W, Z, A ] in (1 + A) $ [ cnt, zero, two, one ];
    [ W, Z ] in (1 + A) $ [ zero, one ];
"#;
    let expectation = r#"namespace N(65536);
    col fixed cnt(i) { i };
    col witness X;
    col witness Y;
    col witness W;
    col witness Z;
    col witness A;
    1 - N::A $ [N::A] in [N::cnt];
    [N::Y, N::W, N::Z, N::A] in 1 + N::A $ [N::cnt, 0, 2, 1];
    [N::W, N::Z] in 1 + N::A $ [0, 1];
    (1 - N::A) * N::X = 0;
    (1 - N::A) * N::Y = 1;
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn intermediate() {
    let input = r#"namespace N(65536);
        col witness x;
        col intermediate = x;
        col int2 = intermediate * x;
        col int3 = int2;
        int3 = (3 * x) + x;
    "#;
    let expectation = r#"namespace N(65536);
    col witness x;
    col intermediate = N::x;
    col int2 = N::intermediate * N::x;
    col int3 = N::int2;
    N::int3 = 3 * N::x + N::x;
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn zero_sized_array() {
    let input = r#"
        namespace std::array(65536);
            let<T> len: T[] -> int = [];
        namespace N(65536);
            col witness x[1];
            col witness y[0];
            let t: col = |i| std::array::len(y);
            x[0] = t;
    "#;
    let expectation = r#"namespace std::array(65536);
    let<T> len: T[] -> int = [];
namespace N(65536);
    col witness x[1];
    col witness y[0];
    col fixed t(i) { std::array::len::<expr>(N::y) };
    N::x[0] = N::t;
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn remove_duplicates() {
    let input = r#"namespace N(65536);
        col witness x;
        col fixed cnt(i) { i };

        x * (x - 1) = 0;
        x * (x - 1) = 0;
        x * (x - 1) = 0;

        [ x ] in [ cnt ];
        [ x ] in [ cnt ];
        [ x ] in [ cnt ];

        [ x + 1 ] in [ cnt ];
        [ x ] in [ cnt + 1 ];
    "#;
    let expectation = r#"namespace N(65536);
    col witness x;
    col fixed cnt(i) { i };
    N::x * (N::x - 1) = 0;
    [N::x] in [N::cnt];
    [N::x + 1] in [N::cnt];
    [N::x] in [N::cnt + 1];
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn remove_unreferenced() {
    let input = r#"namespace N(65536);
        col witness x;
        col fixed cnt(i) { inc(i) };
        let inc = |x| x + 1;
        // these are removed
        col witness k;
        col k2 = k;
        let rec: -> int = || rec();
        let a: int -> int = |i| b(i + 1);
        let b: int -> int = |j| 8;
        // identity
        [ x ] in [ cnt ];

    "#;
    let expectation = r#"namespace N(65536);
    col witness x;
    col fixed cnt(i) { N::inc(i) };
    let inc: int -> int = |x| x + 1_int;
    [N::x] in [N::cnt];
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn remove_unreferenced_parts_of_arrays() {
    let input = r#"namespace N(65536);
        col witness x[5];
        let inte: inter[5] = x;
        x[2] = inte[4];
    "#;
    let expectation = r#"namespace N(65536);
    col witness x[5];
    col inte[5] = [N::x[0], N::x[1], N::x[2], N::x[3], N::x[4]];
    N::x[2] = N::inte[4];
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap());
    assert_eq!(optimized.intermediate_count(), 5);
    assert_eq!(optimized.to_string(), expectation);
}

#[test]
fn remove_unreferenced_keep_enums() {
    let input = r#"namespace N(65536);
        enum X { A, B, C }
        enum Y { D, E, F(R[]) }
        enum R { T }
        let t: X[] -> int = |r| 1;
        // This references Y::F but even after type checking, the type
        // Y is not mentioned anywhere.
        let f: col = |i| if i == 0 { t([]) } else { (|x| 1)(Y::F([])) };
        let x;
        x = f;
    "#;
    let expectation = r#"namespace N(65536);
    enum X {
        A,
        B,
        C,
    }
    enum Y {
        D,
        E,
        F(N::R[]),
    }
    enum R {
        T,
    }
    let t: N::X[] -> int = |r| 1_int;
    col fixed f(i) { if i == 0_int { N::t([]) } else { (|x| 1_int)(N::Y::F([])) } };
    col witness x;
    N::x = N::f;
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn test_trait_impl() {
    let input = r#"namespace N(65536);
        trait Default<T> { f: -> T, g: T -> T }
        impl Default<fe> {
            f: || 1,
            // This is unused but should not be removed, nor should its dependencies.
            g: |x| dep(x)
        }
        trait UnusedTrait<T> { f: -> T }
        let dep: fe -> fe = |x| x + 1;
        // this should be removed.
        impl Default<int> { f: || 1, g: |x| x }
        let x: col = |_| Default::f();
        let w;
        w = x;
    "#;
    let expectation = r#"namespace N(65536);
    trait Default<T> {
        f: -> T,
        g: T -> T,
    }
    impl N::Default<fe> {
        f: || 1_fe,
        g: |x| N::dep(x),
    }
    let dep: fe -> fe = |x| x + 1_fe;
    col fixed x(_) { N::Default::f::<fe>() };
    col witness w;
    N::w = N::x;
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn enum_ref_by_trait() {
    let input = r#"namespace N(65536);
        enum O<T> { X, Y(T) }
        enum Q<T> { A, B(T) }
        trait X<T> { f: T -> O<T>, g: -> T }
        impl X<fe> { f: |_| O::Y(1), g: || { let r = Q::B(1_int); 1 } }
        let x: col = |i| { match X::f(1_fe) { O::Y(y) => y, _ => 0 } };
        let w;
        w = x;
    "#;
    let expectation = r#"namespace N(65536);
    enum O<T> {
        X,
        Y(T),
    }
    enum Q<T> {
        A,
        B(T),
    }
    trait X<T> {
        f: T -> N::O<T>,
        g: -> T,
    }
    impl N::X<fe> {
        f: |_| N::O::Y::<fe>(1_fe),
        g: || {
            let r: N::Q<int> = N::Q::B::<int>(1_int);
            1_fe
        },
    }
    col fixed x(i) { match N::X::f::<fe>(1_fe) {
        N::O::Y(y) => y,
        _ => 0_fe,
    } };
    col witness w;
    N::w = N::x;
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn do_not_replace_selected_lookup() {
    let input = r#"namespace N(65536);
    col fixed one = [1]*;
    col fixed zero = [0]*;
    col fixed two = [2]*;
    col fixed cnt(i) { i };
    col fixed even = [0, 1]*;
    col witness X;
    col witness Y;
    col witness A;
    // We can only turn this into a polynomial identity if `even` is
    // not constant zero, but it is difficult to determine this, so we only
    // do it if it is a constant number.
    [ X, Y, A ] in even $ [ zero, one, cnt ];
"#;
    let expectation = r#"namespace N(65536);
    col fixed cnt(i) { i };
    col fixed even = [0_fe, 1_fe]*;
    col witness X;
    col witness Y;
    col witness A;
    [N::X, N::Y, N::A] in N::even $ [0, 1, N::cnt];
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn handle_array_references_in_prover_functions() {
    let input = r#"namespace N(8);
    col witness x[1];
    
    // non-trivial constraint so that `x[0]` does not get removed.
    x[0]' = x[0] + 1;
    {
        let intermediate = x[0] + 1;
        query |i| {
            // No-op, but references `x[0]`.
            let _ = intermediate;
        }
    };
    "#;
    let expectation = r#"namespace N(8);
    col witness x[1];
    N::x[0]' = N::x[0] + 1;
    {
        let intermediate = N::x[0_int] + 1_expr;
        query |i| {
            let _: expr = intermediate;
        }
    };
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn equal_constrained_array_elements_empty() {
    let input = r#"namespace N(65536);
        col witness w[20];
        w[4] = w[7];
    "#;
    let expectation = r#"namespace N(65536);
    col witness w[20];
    N::w[4] = N::w[7];
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn equal_constrained_array_elements_query() {
    let input = r#"namespace N(65536);
        col witness w[20];
        w[4] = w[7];
        query |i| {
            let _ = w[4] + w[7] - w[5];
        };
    "#;
    let expectation = r#"namespace N(65536);
    col witness w[20];
    N::w[4] = N::w[7];
    query |i| {
        let _: expr = N::w[4_int] + N::w[7_int] - N::w[5_int];
    };
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn equal_constrained_array_elements() {
    let input = r#"namespace N(65536);
        col witness w[20];
        col witness x;
        w[4] = w[7];
        w[3] = w[5];
        x = w[3];
        w[7] + w[1] + x = 5;
    "#;
    let expectation = r#"namespace N(65536);
    col witness w[20];
    N::w[4] = N::w[7];
    N::w[3] = N::w[5];
    N::w[7] + N::w[1] + N::w[3] = 5;
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

#[test]
fn equal_constrained_transitive() {
    let input = r#"namespace N(65536);
        col witness a;
        col witness b;
        col witness c;
        a = b;
        b = c;
        a + b + c = 5;
    "#;
    let expectation = r#"namespace N(65536);
    col witness a;
    N::a + N::a + N::a = 5;
"#;
    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}
#[test]
fn simplify_associative_operations() {
    let input = r#"namespace N(150);
        col witness x;
        col witness y;
        col witness z;
        col fixed c1 = [1]*;
        col fixed c2 = [2]*;
        col fixed c3 = [3]*;
        
        (x + c2) + c1 = y;
        (c2 + x) + c3 = y;
        (x - c2) + c1 = y;
        
        ((x + 3) - y) - 9 = z;
        (c3 + (x + 3)) - y = z;
        ((-x + 3) + y) + 9 = z;
        ((-x + 3) + c3) + 12 = z;
    "#;

    let expectation = r#"namespace N(150);
    col witness x;
    col witness y;
    col witness z;
    N::x + 3 = N::y;
    N::x + 5 = N::y;
    N::x - 2 + 1 = N::y;
    N::x + 3 - N::y - 9 = N::z;
    N::x + 6 - N::y = N::z;
    -N::x + N::y + 12 = N::z;
    -N::x + 18 = N::z;
"#;

    let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
    assert_eq!(optimized, expectation);
}

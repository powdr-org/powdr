use itertools::Itertools;
use powdr_ast::analyzed::Analyzed;
use powdr_number::GoldilocksField;
use test_log::test;

use pretty_assertions::assert_eq;

fn analyze_string(input: &str) -> Analyzed<GoldilocksField> {
    powdr_pil_analyzer::analyze_string(input)
        .map_err(|errors| {
            errors
                .into_iter()
                .map(|e| {
                    e.output_to_stderr();
                    e.to_string()
                })
                .format("\n")
        })
        .expect("Failed to analyze test input.")
}

#[test]
fn parse_print_analyzed() {
    // This is rather a test for the Display trait than for the analyzer.
    let input = r#"    let N: int = 65536;
public P = T::pc(2);
namespace Bin(65536);
    col witness bla;
namespace std::prover(65536);
    let eval: expr -> fe = [];
namespace std::convert(65536);
    let int = [];
namespace T(65536);
    col fixed first_step = [1] + [0]*;
    col fixed line(i) { i };
    let ops: int -> bool = |i| i < 7 && 6 >= -i;
    col witness pc;
    col witness XInv;
    col witness XIsZero;
    T::XIsZero = 1 - T::X * T::XInv;
    T::XIsZero * T::X = 0;
    T::XIsZero * (1 - T::XIsZero) = 0;
    col witness instr_jmpz;
    col witness instr_jmpz_param_l;
    col witness instr_jmp;
    col witness instr_jmp_param_l;
    col witness instr_dec_CNT;
    col witness instr_assert_zero;
    T::instr_assert_zero * (T::XIsZero - 1) = 0;
    col witness X;
    col witness X_const;
    col witness X_read_free;
    col witness A;
    col witness CNT;
    col witness read_X_A;
    col witness read_X_CNT;
    col witness reg_write_X_CNT;
    col witness read_X_pc;
    col witness reg_write_X_A;
    T::X = T::read_X_A * T::A + T::read_X_CNT * T::CNT + T::X_const + T::X_read_free * T::X_free_value;
    T::A' = T::first_step' * 0 + T::reg_write_X_A * T::X + (1 - (T::first_step' + T::reg_write_X_A)) * T::A;
    col witness X_free_value;
    std::prelude::set_hint(T::X_free_value, query |_| match std::prover::eval(T::pc) {
        0 => std::prelude::Query::Input(1),
        3 => std::prelude::Query::Input(std::convert::int::<fe>(std::prover::eval(T::CNT) + 1)),
        7 => std::prelude::Query::Input(0),
        _ => std::prelude::Query::None,
    });
    col fixed p_X_const = [0, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    col fixed p_X_read_free = [1, 0, 0, 1, 0, 0, 0, -1, 0] + [0]*;
    col fixed p_read_X_A = [0, 0, 0, 1, 0, 0, 0, 1, 1] + [0]*;
    col fixed p_read_X_CNT = [0, 0, 1, 0, 0, 0, 0, 0, 0] + [0]*;
    col fixed p_read_X_pc = [0, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    col fixed p_reg_write_X_A = [0, 0, 0, 1, 0, 0, 0, 1, 0] + [0]*;
    col fixed p_reg_write_X_CNT = [1, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    [T::pc, T::reg_write_X_A, T::reg_write_X_CNT] in 1 - T::first_step $ [T::line, T::p_reg_write_X_A, T::p_reg_write_X_CNT];
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(input, formatted);
}

#[test]
fn intermediate() {
    let input = r#"namespace N(65536);
    col witness x;
    col intermediate = x;
    intermediate = intermediate;
"#;
    let expected = r#"namespace N(65536);
    col witness x;
    col intermediate = N::x;
    N::intermediate = N::intermediate;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn intermediate_array() {
    let input = r#"namespace N(65536);
    col witness x;
    col intermediate[3] = [x, x + 2, x * x];
    intermediate[0] = intermediate[0];
    intermediate[1] = intermediate[1];
    intermediate[2] = intermediate[2];
"#;
    let expected = r#"namespace N(65536);
    col witness x;
    col intermediate[3] = [N::x, N::x + 2, N::x * N::x];
    N::intermediate[0] = N::intermediate[0];
    N::intermediate[1] = N::intermediate[1];
    N::intermediate[2] = N::intermediate[2];
"#;
    let analyzed = analyze_string(input);
    assert_eq!(analyzed.intermediate_count(), 3);
    let formatted = analyzed.to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn intermediate_nested() {
    let input = r#"namespace N(65536);
    col witness x;
    col intermediate = x;
    col int2 = intermediate;
    col int3 = int2 + intermediate;
    int3 = 2 * x;
"#;
    let expected = r#"namespace N(65536);
    col witness x;
    col intermediate = N::x;
    col int2 = N::intermediate;
    col int3 = N::int2 + N::intermediate;
    N::int3 = 2 * N::x;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn let_definitions() {
    let input = r#"let r: int = 65536;
namespace N(r);
    let x;
    let z: int = 2;
    let t: col = |i| i + z;
    let other = [1, z];
    let other_fun: int, fe -> (int, (int -> int)) = |i, j| (i + 7, (|k| k - i));
"#;
    let expected = r#"    let r: int = 65536;
namespace N(65536);
    col witness x;
    let z: int = 2;
    col fixed t(i) { i + N::z };
    let other: int[] = [1, N::z];
    let other_fun: int, fe -> (int, (int -> int)) = |i, j| (i + 7, |k| k - i);
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn reparse_arrays() {
    let input = r#"public out = N::y[1](2);
namespace N(16);
    col witness y[3];
    N::y[1] - 2 = 0;
    N::y[2]' - 2 = 0;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
#[should_panic = "Type expr[] does not satisfy trait Sub."]
fn no_direct_array_references() {
    let input = r#"namespace N(16);
    col witness y[3];
    (N::y - 2) = 0;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
#[should_panic = "Tried to access element 3 of array of size 3"]
fn no_out_of_bounds() {
    let input = r#"namespace N(16);
    col witness y[3];
    (N::y[3] - 2) = 0;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
fn namespaced_call() {
    let input = r#"namespace Assembly(2);
    let A: int -> int = |i| 0;
    let C = |i| (Assembly::A((i + 2)) + 3);
    let D = |i| Assembly::C((i + 3));
"#;
    let expected = r#"namespace Assembly(2);
    let A: int -> int = |i| 0;
    let C: int -> int = |i| Assembly::A(i + 2) + 3;
    let D: int -> int = |i| Assembly::C(i + 3);
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn if_expr() {
    let input = r#"namespace Assembly(2);
    col fixed A = [0]*;
    let c = (|i| if (i < 3) { i } else { (i + 9) });
    col fixed D(i) { if (Assembly::c(i) != 0) { 3 } else { 2 } };
"#;
    let expected = r#"namespace Assembly(2);
    col fixed A = [0]*;
    let c: int -> int = |i| if i < 3 { i } else { i + 9 };
    col fixed D(i) { if Assembly::c(i) != 0 { 3 } else { 2 } };
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn symbolic_functions() {
    let input = r#"namespace N(16);
    let last_row: int = 15;
    let ISLAST: col = |i| if i == last_row { 1 } else { 0 };
    let x;
    let y;
    let constrain_equal_expr = |A, B| A - B;
    let on_regular_row = |cond| (1 - ISLAST) * cond;
    on_regular_row(constrain_equal_expr(x', y)) = 0;
    on_regular_row(constrain_equal_expr(y', x + y)) = 0;
    "#;
    let expected = r#"namespace N(16);
    let last_row: int = 15;
    col fixed ISLAST(i) { if i == N::last_row { 1 } else { 0 } };
    col witness x;
    col witness y;
    let constrain_equal_expr: expr, expr -> expr = |A, B| A - B;
    let on_regular_row: expr -> expr = |cond| (1 - N::ISLAST) * cond;
    (1 - N::ISLAST) * (N::x' - N::y) = 0;
    (1 - N::ISLAST) * (N::y' - (N::x + N::y)) = 0;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn next_op_on_param() {
    let input = r#"namespace N(16);
    let x;
    let y;
    let next_is_seven = |t| t' - 7;
    next_is_seven(y) = 0;
    "#;
    let expected = r#"namespace N(16);
    col witness x;
    col witness y;
    let next_is_seven: expr -> expr = |t| t' - 7;
    N::y' - 7 = 0;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn fixed_symbolic() {
    let input = r#"namespace N(16);
    let last_row = 15;
    let islast = |i| if i == N::last_row { 1 } else { 0 };
    let ISLAST: col = |i| islast(i);
    let x;
    let y;
    x - ISLAST = 0;
    "#;
    let expected = r#"namespace N(16);
    let last_row: int = 15;
    let islast: int -> fe = |i| if i == N::last_row { 1 } else { 0 };
    col fixed ISLAST(i) { N::islast(i) };
    col witness x;
    col witness y;
    N::x - N::ISLAST = 0;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn parentheses_lambda() {
    let input = r#"namespace N(16);
    let w = || 2;
    let x: fe = (|i| || w())(w())();
    "#;
    let expected = r#"namespace N(16);
    let w: -> fe = || 2;
    let x: fe = (|i| (|| N::w()))(N::w())();
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn simple_type_resolution() {
    let input = r#"namespace N(16);
    let w: col[3 + 4];
    "#;
    let expected = r#"namespace N(16);
    col witness w[7];
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn complex_type_resolution() {
    let input = r#"namespace N(16);
    let f: int -> int = |i| i + 10;
    let x: (int -> int), int -> int = |k, i| k(2**i);
    let y: col[x(f, 2)];
    let z: (((int -> int), int -> int)[], expr) = ([x, x, x, x, x, x, x, x], y[0]);
    "#;
    let expected = r#"namespace N(16);
    let f: int -> int = |i| i + 10;
    let x: (int -> int), int -> int = |k, i| k(2 ** i);
    col witness y[14];
    let z: (((int -> int), int -> int)[], expr) = ([N::x, N::x, N::x, N::x, N::x, N::x, N::x, N::x], N::y[0]);
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn function_type_display() {
    let input = r#"namespace N(16);
    let f: (-> int)[] = [|| 10, || 12];
    let g: (int -> int) -> int = |f| f(0);
    let h: int -> (int -> int) = |x| (|i| x + i);
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
fn expr_and_identity() {
    let input = r#"namespace N(16);
    let f: expr, expr -> Constr[] = |x, y| [x = y];
    let g: expr -> Constr[] = |x| [x = 0];
    let x: col;
    let y: col;
    f(x, y);
    g((x));
    "#;
    let expected = r#"namespace N(16);
    let f: expr, expr -> std::prelude::Constr[] = |x, y| [x = y];
    let g: expr -> std::prelude::Constr[] = |x| [x = 0];
    col witness x;
    col witness y;
    N::x = N::y;
    N::x = 0;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
#[should_panic = "Expected type std::prelude::Constr but got type expr"]
fn expression_but_expected_constraint() {
    let input = r#"namespace N(16);
    col witness y;
    (N::y - 2);
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
#[should_panic = "Type std::prelude::Constr[] does not satisfy trait ToSelectedExprs."]
fn constraint_but_expected_expression() {
    let input = r#"namespace N(16);
    col witness y;
    [ (N::y - 2) = 0 ] in [ N::y ];
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
#[should_panic = "Type symbol not found: T"]
fn used_undeclared_type_var() {
    let input = r#"let x: T = 8;"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
#[should_panic = "Unused type variable(s) in declaration: T"]
fn declared_unused_type_var() {
    let input = r#"let<T> x: int = 8;"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
#[should_panic = "Type symbol not found: T"]
fn double_used_undeclared_type_var() {
    let input = r#"let<K> x: T = 8;"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
fn to_expr() {
    let input = r#"
    namespace std::convert(16);
        let expr = [];
    namespace N(16);
        let mul_two: int -> int = |i| i * 2;
        col witness y;
        y = y * std::convert::expr(mul_two(7));
"#;
    let formatted = analyze_string(input).to_string();
    let expected = r#"namespace std::convert(16);
    let expr = [];
namespace N(16);
    let mul_two: int -> int = |i| i * 2;
    col witness y;
    N::y = N::y * 14;
"#;
    assert_eq!(formatted, expected);
}

#[test]
fn col_array_is_array() {
    let input = "
    namespace std::convert(16);
        let expr = [];
    namespace std::array(16);
        let len = [];
    namespace main(16);
        pol commit x1[16];
        let x2: col[16];
        let t: int = std::array::len(x1);
        let r: int = std::array::len(x2);
        x1[0] * std::convert::expr(t) = x2[0] * std::convert::expr(r);
    ";
    let formatted = analyze_string(input).to_string();
    let expected = r#"namespace std::convert(16);
    let expr = [];
namespace std::array(16);
    let len = [];
namespace main(16);
    col witness x1[16];
    col witness x2[16];
    let t: int = std::array::len::<expr>(main::x1);
    let r: int = std::array::len::<expr>(main::x2);
    main::x1[0] * 16 = main::x2[0] * 16;
"#;
    assert_eq!(formatted, expected);
}

#[test]
fn stages() {
    let input = "    let N: int = 8;
namespace Main(8);
    col witness x;
    col witness stage(2) y;
    col witness stage(1) z[4];
    Main::x = Main::y;
    Main::z[0] = Main::x;
";
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
fn challenges() {
    let input = "
    namespace Main(8);
        col fixed first = [1] + [0]*;
        col witness x;
        col witness stage(2) y;
        let a: expr = challenge(2, 1);

        x' = (x + 1) * (1 - first);
        y' = (x + a) * (1 - first);
    ";
    let analyzed = analyze_string(input);
    assert_eq!(analyzed.intermediate_count(), 0);
    let formatted = analyzed.to_string();
    let expected = r#"namespace Main(8);
    col fixed first = [1] + [0]*;
    col witness x;
    col witness stage(2) y;
    let a: expr = std::prelude::challenge(2, 1);
    Main::x' = (Main::x + 1) * (1 - Main::first);
    Main::y' = (Main::x + std::prelude::challenge(2, 1)) * (1 - Main::first);
"#;
    assert_eq!(formatted, expected);
}

#[test]
fn let_inside_block() {
    let input = "
    namespace Main(8);
        let w;
        let t: int -> expr = constr |i| match i {
            0 => { let x; x },
            1 => w,
            _ => if i < 3 { let y; y } else { w },
        };
        {
            let z;
            z = 9
        };
    ";
    let formatted = analyze_string(input).to_string();
    let expected = "namespace Main(8);
    col witness w;
    let t: int -> expr = constr |i| match i {
        0 => {
            let x: col;
            x
        },
        1 => Main::w,
        _ => if i < 3 {
            let y: col;
            y
        } else { Main::w },
    };
    col witness z;
    Main::z = 9;
";
    assert_eq!(formatted, expected);
}

#[test]
fn let_inside_block_complex_type() {
    let input = "
    enum O<X> {
        A(X),
        B,
    }
    let<T> f: T -> O<T>[] = |i| [O::A(i)];
    let<Q> x: Q -> O<Q>[][] = constr |i| {
        let w;
        let y = f(i);
        [y]
    };
    ";
    let formatted = analyze_string(input).to_string();
    // Type inference should add the correct concrete
    // type for y and w.
    let expected = "    enum O<X> {
        A(X),
        B,
    }
    let<T> f: T -> O<T>[] = |i| [O::A::<T>(i)];
    let<Q> x: Q -> O<Q>[][] = constr |i| {
        let w: col;
        let y: O<Q>[] = f::<Q>(i);
        [y]
    };
";
    assert_eq!(formatted, expected);
}

#[test]
#[should_panic = "Variable already defined: t"]
fn let_inside_block_redefine() {
    let input = "
    namespace Main(8);
        let t: int -> int = |i| {
            let t = 2;
            let t = 3;
            t
        };
    ";
    analyze_string(input).to_string();
}

#[test]
fn let_inside_block_scoping_separate() {
    let input = "
    namespace Main(8);
        let t: int -> int = |i| {
            let t = {
                let w = 8;
                w
            };
            let r = {
                // New scope, so no name clash.
                let w = 8;
                w
            };
            t + r
        };
    ";
    analyze_string(input).to_string();
}

#[test]
#[should_panic = "Value symbol not found: w"]
fn let_inside_block_scoping_limited() {
    let input = "
    namespace Main(8);
        let t: int -> expr = |i| {
            let r = {
                let w = 8;
                w
            };
            // w is not available here any more.
            w
        };
    ";
    analyze_string(input).to_string();
}

#[test]
#[should_panic = "Function parameters must be irrefutable, but [x, y] is refutable."]
fn refutable_function_param() {
    let input = "
    namespace Main(8);
        let t = |[x, y], z| x;
    ";
    analyze_string(input).to_string();
}

#[test]
#[should_panic = "Let statement requires an irrefutable pattern, but [x, y] is refutable."]
fn refutable_let() {
    let input = "
    namespace Main(8);
        let t = {
            let [x, y] = [1, 2];
            x
        };
    ";
    analyze_string(input).to_string();
}

#[test]
fn patterns() {
    let input = "    let t: ((int, int), int[]) -> int = |i| match i {
        ((_, 6), []) => 2,
        ((2, _), [3, 4]) => 3,
        ((_, 6), x) => x[0],
        ((_, y), _) => y,
        (_, [2]) => 7,
    };
";
    assert_eq!(input, analyze_string(input).to_string());
}

#[test]
#[should_panic = "Variable already defined: x"]
fn patterns_shadowing() {
    let input = "
    let t: int, int -> expr = |i, j| match (i, j) {
        (x, x) => x,
    };
    ";
    assert_eq!(input, analyze_string(input).to_string());
}

#[test]
#[should_panic = "Variable already defined: x"]
fn block_shadowing() {
    let input = "
    let t = {
        let x = 2;
        let x = 3;
        x
    };
    ";
    assert_eq!(input, analyze_string(input).to_string());
}

#[test]
#[should_panic = "Variable already defined: x"]
fn sub_block_shadowing() {
    let input = "    let t = ({
        let x = 2;
        {
            let x = 3;
            x
        }
    });
";
    assert_eq!(input, analyze_string(input).to_string());
}

#[test]
fn disjoint_block_shadowing() {
    let input = "    let t: int = {
        let b: int = {
            let x: int = 2;
            x
        };
        {
            let x: int = 3;
            x + b
        }
    };
";
    assert_eq!(input, analyze_string(input).to_string());
}

#[test]
#[should_panic = "Variable already defined: x"]
fn sub_function_shadowing() {
    let input = "    let t: int -> int = (|x| (|x| x)(2));
";
    assert_eq!(input, analyze_string(input).to_string());
}

#[test]
#[should_panic = "Variable already defined: x"]
fn function_param_shadowing() {
    let input = "    let t: int, int -> int = (|x, x| (x + x));
";
    assert_eq!(input, analyze_string(input).to_string());
}

#[test]
fn match_shadowing() {
    let input = "    let t: (int, int) -> int = |i| match i {
        (_, x) => 2,
        (x, _) => 3,
    };
";
    assert_eq!(input, analyze_string(input).to_string());
}

#[test]
fn single_ellipsis() {
    let input = "    let t: int[] -> int = |i| match i {
        [1, .., 3] => 2,
        [..] => 3,
        [.., 1] => 9,
        [7, 8, ..] => 2,
        _ => -1,
    };
";
    assert_eq!(input, analyze_string(input).to_string());
}

#[test]
fn namespace_no_degree() {
    let input = "namespace X;
    let y: int = 7;
namespace T(8);
    let k = X::y;
";
    let expected = "namespace X;
    let y: int = 7;
namespace T(8);
    let k: int = X::y;
";
    let analyzed = analyze_string(input);
    assert_eq!(expected, analyzed.to_string());
}

#[test]
fn find_in_prelude() {
    let input = "namespace std::prelude;
    let y: int = 7;
namespace T(8);
    let k = y;
";
    let expected = "namespace std::prelude;
    let y: int = 7;
namespace T(8);
    let k: int = std::prelude::y;
";
    let analyzed = analyze_string(input);
    assert_eq!(expected, analyzed.to_string());
}

#[test]
fn trait_def() {
    let input = "trait Add<T, Q> {
        add: T, T -> Q,
    }
";

    let expected = "    trait Add<T, Q> {
        add: T, T -> Q,
    }
";

    let analyzed = analyze_string(input);
    assert_eq!(expected, analyzed.to_string())
}

#[test]
fn array_type_trait() {
    let input = "trait ArraySum<T> {
        array_sum: T[4 + 1] -> T,
    }
";

    let expected = "    trait ArraySum<T> {
        array_sum: T[5] -> T,
    }
";

    let analyzed = analyze_string(input);
    assert_eq!(expected, analyzed.to_string())
}

#[test]
#[should_panic = "Duplicate symbol definition: Add"]
fn trait_enum_collisions() {
    let input = "trait Add<T, Q> {
        add: T, T -> Q,
    }
    enum Add {
        X
    }";

    let _ = analyze_string(input);
}

#[test]
fn reparse_generic_function_call() {
    let input = r#"namespace X(16);
    let<T: Add + FromLiteral> inc: T -> T = |x| x + 1;
namespace N(16);
    let x: int = 7;
    let y: int = X::inc::<int>(N::x);
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
fn reparse_non_function_fixed_cols() {
    let input = r#"namespace X(16);
    let A: int -> int = |i| i;
    let B: col = X::A;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
fn reparse_array_typed_fixed_col() {
    let input = r#"namespace std::array(16);
    let<T> len: T[] -> int = 19;
namespace Main(16);
    let<T> make_array: int, (int -> T) -> T[] = |n, f| if n == 0 { [] } else { Main::make_array::<T>(n - 1, f) + [f(n - 1)] };
    let nth_clock: int -> (int -> int) = |k| (|i| if i % std::array::len::<expr>(Main::clocks) == k { 1 } else { 0 });
    let clocks: col[4] = Main::make_array::<(int -> int)>(4, Main::nth_clock);
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
fn reparse_array_typed_intermediate_col() {
    let input = r#"namespace Main(16);
    col witness w;
    col clocks[4] = [Main::w, Main::w, Main::w, Main::w];
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
fn reparse_type_args_generic_enum() {
    let input = r#"namespace X(16);
    enum Option<T> {
        None,
        Some(T),
    }
    let<T> consume: T -> () = |_| { };
    let p: int -> () = |i| X::consume::<(X::Option<int>)>(X::Option::Some::<int>(i));
"#;

    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
fn simple_struct() {
    let input = "    struct Point {
        x: int,
        y: int,
    }
    let f: int -> Point = |i| Point{ x: 0, y: i };
    let x: Point = f(0);
";
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
fn def_struct_and_field() {
    let input = "    struct Point {
        x: int,
        y: int,
    }
    let p: Point = Point{ x: 3, y: 4 };
    let f: Point -> int = |d| d->y;
    let res: int = f(p);
";

    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
fn struct_field_in_expr() {
    let input = "    struct X {
        x: int,
        y: int,
    }
    let v: int -> X = |i| match i {
        1 => X{ x: 1, y: 0 },
        2 => X{ x: 2, y: 2 },
        _ => X{ x: 0, y: 1 },
    };
    let x: int = v(1)->y;
";

    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, input);
}

#[test]
fn intermediate_syntax() {
    let input = r#"namespace X(16);
    let w;
    let a: inter = w;
    let b: inter[1] = [w];
    col c = w;
    col d[1] = [w];
"#;
    let expected = r#"namespace X(16);
    col witness w;
    col a = X::w;
    col b[1] = [X::w];
    col c = X::w;
    col d[1] = [X::w];
"#;
    let analyzed = analyze_string(input);
    assert_eq!(analyzed.intermediate_count(), 4);
    assert_eq!(analyzed.to_string(), expected);
}

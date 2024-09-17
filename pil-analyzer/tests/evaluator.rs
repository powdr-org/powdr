use powdr_ast::analyzed::{FunctionValueDefinition, TypedExpression};
use powdr_number::{FieldElement, GoldilocksField};
use powdr_pil_analyzer::{
    analyze_string,
    evaluator::{self, evaluate, Definitions, SymbolLookup, Value},
};
use test_log::test;

use pretty_assertions::assert_eq;

fn parse_and_evaluate_symbol(input: &str, symbol: &str) -> String {
    let analyzed = analyze_string::<GoldilocksField>(input).unwrap();
    let Some(FunctionValueDefinition::Expression(TypedExpression {
        e: symbol,
        type_scheme: _,
    })) = &analyzed.definitions[symbol].1
    else {
        panic!()
    };
    evaluate::<GoldilocksField>(
        symbol,
        &mut Definitions {
            definitions: &analyzed.definitions,
            solved_impls: &analyzed.solved_impls,
        },
    )
    .unwrap()
    .to_string()
}

pub fn evaluate_function<T: FieldElement>(input: &str, function: &str) -> T {
    let analyzed = analyze_string::<GoldilocksField>(input).unwrap();
    let mut symbols = evaluator::Definitions {
        definitions: &analyzed.definitions,
        solved_impls: &analyzed.solved_impls,
    };
    let function = symbols.lookup(function, &None).unwrap();
    let result = evaluator::evaluate_function_call(function, vec![], &mut symbols)
        .unwrap()
        .as_ref()
        .clone();
    match result {
        Value::FieldElement(fe) => fe,
        _ => panic!("Expected field element but got {result}"),
    }
}

#[test]
fn trivial() {
    let src = r#"namespace Main(16);
        let x: int = 1 + 20;
    "#;
    let result = parse_and_evaluate_symbol(src, "Main::x");
    assert_eq!(result, r#"21"#);
}

#[test]
fn recursion() {
    let src = r#"namespace Main(16);
        let x: int -> int = |i| match i { 0 => 0, _ => x(i - 1) + 1 };
        let y = x(4);
    "#;
    let result = parse_and_evaluate_symbol(src, "Main::y");
    assert_eq!(result, r#"4"#);
}

#[test]
fn arrays_and_strings() {
    let src = r#"namespace Main(16);
        let words = ["the", "quick", "brown", "fox"];
        let translate = |w| match w {
            "the" => "franz",
            "quick" => "jagt",
            "brown" => "mit",
            "fox" => "dem",
            _ => "?",
        };
        let map_array = |arr, f| [f(arr[0]), f(arr[1]), f(arr[2]), f(arr[3])];
        let translated = map_array(words, translate);
    "#;
    let result = parse_and_evaluate_symbol(src, "Main::translated");
    assert_eq!(result, r#"["franz", "jagt", "mit", "dem"]"#);
}

#[test]
fn fibonacci() {
    let src = r#"namespace Main(16);
        let fib: int -> int = |i| match i {
            0 => 0,
            1 => 1,
            _ => fib(i - 1) + fib(i - 2),
        };
        let result = fib(20);
    "#;
    assert_eq!(
        parse_and_evaluate_symbol(src, "Main::result"),
        "6765".to_string()
    );
}

#[test]
fn capturing() {
    let src = r#"namespace Main(16);
        let f: int, (int -> int) -> (int -> int) = |n, g| match n { 99 => |i| n, 1 => g };
        let result = f(1, f(99, |x| x + 3000))(0);
    "#;
    // If the lambda function returned by the expression f(99, ...) does not
    // properly capture the value of n in a closure, then f(1, ...) would return 1.
    assert_eq!(
        parse_and_evaluate_symbol(src, "Main::result"),
        "99".to_string()
    );
}

#[test]
fn array_len() {
    let src = r#"
        let N: int = 2;
        namespace std::array(N);
        let len = 123;
        namespace F(N);
        let x = std::array::len([1, N, 3]);
        let empty: int[] = [];
        let y = std::array::len(empty);
    "#;
    assert_eq!(parse_and_evaluate_symbol(src, "F::x"), "3".to_string());
    assert_eq!(parse_and_evaluate_symbol(src, "F::y"), "0".to_string());
}

#[test]
#[should_panic = r#"FailedAssertion("this text")"#]
fn panic_complex() {
    let src = r#"
        let N: int = 2;
        namespace std::check(N);
        let panic = 123;
        namespace F(N);
        let concat = |a, b| a + b;
        let arg: int = 1;
        let x: int[] = (|i| if i == 1 { std::check::panic(concat("this ", "text")) } else { [9] })(arg);
    "#;
    parse_and_evaluate_symbol(src, "F::x");
}

#[test]
#[should_panic = r#"FailedAssertion("text")"#]
fn panic_string() {
    let src = r#"
        let N: int = 2;
        namespace std::check(N);
        let panic = 123;
        namespace F(N);
        let x: int = std::check::panic("text");
    "#;
    parse_and_evaluate_symbol(src, "F::x");
}

#[test]
fn hex_number_outside_field() {
    // This tests that the parser does not lose precision when parsing large integers.
    let src = r#"
        let N: int = 0x9999999999999999999999999999999;
    "#;
    parse_and_evaluate_symbol(src, "N");
}

#[test]
fn decimal_number_outside_field() {
    // This tests that the parser does not lose precision when parsing large integers.
    let src = r#"
        let N: int = 9999999999999999999999999999999;
    "#;
    parse_and_evaluate_symbol(src, "N");
}

#[test]
#[should_panic = "Number literal 9999999999999999999999999999999 is too large for field element."]
fn decimal_number_outside_field_for_fe() {
    let src = r#"
        let N: fe = 9999999999999999999999999999999;
    "#;
    parse_and_evaluate_symbol(src, "N");
}

#[test]
fn zero_power_zero() {
    let src = r#"
    let zpz_int: int = 0**0;
    let zpz_fe: fe = 0**0;
    "#;
    assert_eq!(parse_and_evaluate_symbol(src, "zpz_int"), "1".to_string());
    assert_eq!(parse_and_evaluate_symbol(src, "zpz_fe"), "1".to_string());
}

#[test]
fn debug_print() {
    let src = r#"
        namespace std::debug(8);
        let print = 2;
        let N = std::debug::print("test output\n");
    "#;
    parse_and_evaluate_symbol(src, "std::debug::N");
}

#[test]
fn debug_print_complex() {
    let src = r#"
        namespace std::debug(8);
        let print = 2;
        let t: fe = 9;
        let x: int = 2;
        let N = {
            let _ = std::debug::print((t, [x, 3], "test output\n"));
            std::debug::print("\n")
        };
    "#;
    parse_and_evaluate_symbol(src, "std::debug::N");
}

#[test]
fn local_vars() {
    let src = r#"
        let f: int -> int = |i| {
            let x = i + 1;
            let y = x - 1;
            let z = y - i;
            z
        };
        let t = f(8);
    "#;
    assert_eq!(parse_and_evaluate_symbol(src, "t"), "0".to_string());
}

#[test]
fn match_pattern() {
    let src = r#"
        let f: int[] -> int = |arr| match arr {
            [] => 0,
            [x] => x,
            [_, x] => x + 9,
            [_, x, y] => x + y,
            _ => 99,
        };
        let t = [
            f([]), f([1]), f([1, 2]), f([1, 2, 3]), f([1, 2, 3, 4])
        ];
    "#;
    assert_eq!(
        parse_and_evaluate_symbol(src, "t"),
        "[0, 1, 11, 5, 99]".to_string()
    );
}

#[test]
fn match_pattern_complex() {
    let src = r#"
        let f: ((int, int), int[]) -> int = |q| match q {
            ((1, _), [x, 4]) => 1 + x,
            ((1, 2), [y]) => 2 + y,
            ((_, 2), [y, z]) => 3 + y + z,
            ((x, 3), _) => x,
            ((x, -1), _) => x,
            (t, [_, r]) => r
        };
        let res = [
            f(((1, 9), [20, 4])),
            f(((1, 2), [3])),
            f(((9, 2), [300, 4])),
            f(((9, 3), [900, 8])),
            f(((90, 3), [900, 8, 7])),
            f(((99, -1), [900, 8, 7])),
            f(((1, 1), [-3, -1]))
        ];
    "#;
    assert_eq!(
        parse_and_evaluate_symbol(src, "res"),
        "[21, 5, 307, 9, 90, 99, -1]".to_string()
    );
}

#[test]
fn match_skip_array() {
    let src = r#"
        let f: int[] -> int = |arr| match arr {
            [x, .., y] => x + y,
            [] => 19,
            _ => 99,
        };
        let t = [f([]), f([1]), f([1, 2]), f([1, 2, 3]), f([1, 2, 3, 4])];
    "#;
    assert_eq!(
        parse_and_evaluate_symbol(src, "t"),
        "[19, 99, 3, 4, 5]".to_string()
    );
}

#[test]
fn match_skip_array_2() {
    let src = r#"
        let f: int[] -> int = |arr| match arr {
            [.., y] => y,
            _ => 99,
        };
        let t = [f([]), f([1]), f([1, 2]), f([1, 2, 3]), f([1, 2, 3, 4])];
    "#;
    assert_eq!(
        parse_and_evaluate_symbol(src, "t"),
        "[99, 1, 2, 3, 4]".to_string()
    );
}

#[test]
fn match_skip_array_3() {
    let src = r#"
        let f: int[] -> int = |arr| match arr {
            [.., x, y] => x,
            [..] => 99,
        };
        let t = [f([]), f([1]), f([1, 2]), f([1, 2, 3]), f([1, 2, 3, 4])];
    "#;
    assert_eq!(
        parse_and_evaluate_symbol(src, "t"),
        "[99, 99, 1, 2, 3]".to_string()
    );
}

#[test]
fn match_skip_array_4() {
    let src = r#"
        let f: int[] -> int = |arr| match arr {
            [x, y, ..] => y,
            [..] => 99,
        };
        let t = [f([]), f([1]), f([1, 2]), f([1, 2, 3]), f([1, 2, 3, 4])];
    "#;
    assert_eq!(
        parse_and_evaluate_symbol(src, "t"),
        "[99, 99, 2, 2, 2]".to_string()
    );
}

#[test]
fn unpack_fun() {
    let src = r#"
        let t: (int, fe, int), int -> int[] = |(x, _, y), z| [x, y, z];
        let x: int[] = t((1, 2, 3), 4);
    "#;
    assert_eq!(parse_and_evaluate_symbol(src, "x"), "[1, 3, 4]".to_string());
}

#[test]
fn unpack_let() {
    let src = r#"
        let x: int[] = {
            let (a, (_, b), (c, _, _, d, _)) = (1, ((), 3), (4, (), (), 7, ()));
            [a, b, c, d]
        };
    "#;
    assert_eq!(
        parse_and_evaluate_symbol(src, "x"),
        "[1, 3, 4, 7]".to_string()
    );
}

#[test]
pub fn match_enum() {
    let src = r#"
        enum X {
            A,
            B(),
            C(int, int),
            D(int, X)
        }
        let f = |x| match x {
            X::A => 1,
            X::B() => 2,
            X::C(a, b) => a + b,
            X::D(0, X::A) => 10001,
            X::D(c, y) => c + f(y),
        };
        let t = [f(X::A), f(X::B()), f(X::C(3, 4)), f(X::D(0, X::A)), f(X::D(0, X::B())), f(X::D(100, X::C(4, 5)))];
    "#;
    assert_eq!(
        parse_and_evaluate_symbol(src, "t"),
        "[1, 2, 7, 10001, 2, 109]".to_string()
    );
}

#[test]
pub fn gigantic_stack() {
    let src = r#"
        let arr_new: int, (int -> int) -> int[] = |n, f| if n == 0 { [] } else { arr_new(n - 1, f) + [f(n - 1)] };
        let arr_rev: int[], int, int -> int[] = |a, i, n| if i >= n { [] } else { arr_rev(a, i + 1, n) + [a[i]] };
        let l = 10000;
        let t = arr_new(l, |i| i);
        let r = arr_rev(t, 0, l);
        let x = r[7];
    "#;
    assert_eq!(parse_and_evaluate_symbol(src, "x"), "9992".to_string());
}

#[test]
pub fn string_eq() {
    let src = r#"
        let yes = "abc" != "def";
        let no = "abc" == "def";
        let yes2 = "abc" == "abc";
        let no2 = "abc" != "abc";
        let yes3 = "ab" != "abc";
        let no3 = "ab" == "abc";
    "#;
    assert_eq!(parse_and_evaluate_symbol(src, "yes"), "true".to_string());
    assert_eq!(parse_and_evaluate_symbol(src, "yes2"), "true".to_string());
    assert_eq!(parse_and_evaluate_symbol(src, "yes3"), "true".to_string());
    assert_eq!(parse_and_evaluate_symbol(src, "no"), "false".to_string());
    assert_eq!(parse_and_evaluate_symbol(src, "no2"), "false".to_string());
    assert_eq!(parse_and_evaluate_symbol(src, "no3"), "false".to_string());
}

#[test]
pub fn eval_complex_expression() {
    let src = r#"
        namespace std::prover;
            let eval: expr -> fe = [];
        namespace main;
            // Put into query function, so we're allowed to use eval()
            let test = query || std::prover::eval(2 * (1 + 1 + 1) + 1);
    "#;
    assert_eq!(
        evaluate_function::<GoldilocksField>(src, "main::test"),
        7u64.into()
    );
}

#[test]
fn no_stmts_in_block() {
    let input = "
let f: int -> () = |i| ();
let g: int -> () = |i| {
    f(1)
};

let h: () = g(1);
";

    assert_eq!(parse_and_evaluate_symbol(input, "h"), "()".to_string());
}

#[test]
fn called_with_empty_block() {
    let input = "
let<T1, T2: FromLiteral> f: T1 -> T2 = |_| 7;
let g: int = f({ });
";

    assert_eq!(parse_and_evaluate_symbol(input, "g"), "7".to_string());
}

#[test]
fn traits_and_refs() {
    let input = "
    namespace std::convert(4);
        let fe = || fe();
    namespace F(4);
        trait Add<T> {
            add: T, T -> T,
        }

        impl Add<int> {
            add: |a, b| a + b,
        }

        trait Cast<T, U> {
            add: T -> U, // This name is wrong on purpose
        }

        impl Cast<int, fe> {
            add: |a| std::convert::fe(a), 
        }

        let x: int -> fe = |q| match Add::add(q, 2) {
                 v => std::convert::fe(v),
        };

        let y: int -> fe = |q| match Add::add(q, 4) {
                v => x(v) + Cast::add(v),
        };

        let r: fe = y(2);
    ";

    assert_eq!(parse_and_evaluate_symbol(input, "F::r"), "14".to_string());
}

#[test]
fn traits_multiple_fns() {
    let input = "
    namespace std::convert(4);
        let fe = || fe();
    namespace F(4);
        trait Do<T, Q> {
            add: T, T -> Q,
            sub: T, T -> Q,
            cast: T -> Q,
        }

        impl Do<int, fe> {
            add: |a, b| std::convert::fe(a + b),
            sub: |a, b| std::convert::fe(a - b),
            cast: |a| std::convert::fe(a),
        }

        let x: int -> fe = |q| match Do::sub(q, q) {
            v => {
                let one: int = 1;
                let two: int = 2 * 1;
                v + Do::add(one, two)
            },
        };

        let y: int -> fe = |q| match Do::cast(q) {
            v => { 
                let two: int = 2;
                x(two) + v
            },
        };

        let r: fe = y(2);
    ";

    assert_eq!(parse_and_evaluate_symbol(input, "F::r"), "5".to_string());
}

#[test]
fn traits_multiple_impls() {
    let input = "
    namespace std::convert(4);
        let fe = || fe();
    namespace F(4);
        trait Do<T, Q> {
            add: T, T -> Q,
            sub: T, T -> Q,
            cast: T -> Q,
        }

        impl Do<int, fe> {
            add: |a, b| std::convert::fe(a + b),
            sub: |a, b| std::convert::fe(a - b),
            cast: |a| std::convert::fe(a),
        }

        impl Do<int, int> {
            add: |a, b| a + b + 1,
            sub: |a, b| a - b + 1,
        }

        impl Do<fe, fe> {
            add: |a, b| a + b,
            sub: |a, b| a - b,
        }

        let x: int -> fe = |q| match Do::sub::<int, int>(q, q) {
            v => {
                let p1: fe = 3;
                let p2: fe = 2 * 1;
                Do::add(p1, p2)
            },
        };

        let y: int -> int = |q| match q {
            v => {
                let p1: int = 5 - v;
                let p2: int = 2 * 1;
                Do::add(p1, p2)
            },
        };

        let z: int = y(2); 
        let r: fe = x(2);
        ";

    assert_eq!(parse_and_evaluate_symbol(input, "F::r"), "5".to_string());
    assert_eq!(parse_and_evaluate_symbol(input, "F::z"), "6".to_string());
}

#[test]
fn test_trait_function_call_in_impl() {
    let input = "
    namespace std::convert(4);
        let fe = || fe();
    namespace F(4);
        trait Do<T, Q> {
            op1: T, T -> Q,
            cast: T -> Q,
        }
        impl Do<int, fe> {
            op1: |a, b| Do::cast(a + b),
            cast: |a| std::convert::fe(a),
        }

        let one: int = 1;
        let two: int = 2;
        let r: fe = Do::op1(one, two);

    ";

    assert_eq!(parse_and_evaluate_symbol(input, "F::r"), "3".to_string());
}

#[test]
fn test_trait_function_call_cross_impl() {
    let input = "
    namespace std::convert(4);
        let fe = || fe();
    namespace F(4);
        trait Do1<T, Q> {
            op1: T, T -> Q,
        }

        trait Cast<T, Q> {
            cast: T -> Q,
        }

        impl Do1<int, fe> {
            op1: |a, b| Cast::cast(a + b),
        }

        impl Cast<int, fe> {
            cast: |a| std::convert::fe(a),
        }

        let four: int = 4;
        let two: int = 2;
        let r: fe = Do1::op1(four, two);

    ";

    assert_eq!(parse_and_evaluate_symbol(input, "F::r"), "6".to_string());
}

#[test]
pub fn match_struct() {
    let src = r#"
            struct S3 {
                a: int,
                b: int,
                c: int,
            }
            let f: S3 -> int = |s| match s {
                S3{ a: 1, b: 2, c } => 1,
                S3{ a: 1, b: 4, c } => 2 + c,
                S3{ a, b, c } => a + b + c,
            };
            let t = [f(S3{ a: 1, b: 2, c: 3 }), f(S3{ a: 1, b: 4, c: 4 }), f(S3{ a: 1, b: 3, c: 5 })];
        "#;
    assert_eq!(parse_and_evaluate_symbol(src, "t"), "[1, 6, 9]".to_string());
}

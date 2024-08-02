use powdr_ast::parsed::display::format_type_scheme_around_name;
use powdr_number::GoldilocksField;
use powdr_parser::parse_type_scheme;
use powdr_pil_analyzer::analyze_string;

use pretty_assertions::assert_eq;

fn type_check(input: &str, expected: &[(&str, &str, &str)]) {
    let analyzed = analyze_string::<GoldilocksField>(input);
    for (name, bounds, ty) in expected {
        let type_scheme = analyzed.type_of_symbol(name);
        assert_eq!(
            (*bounds, *ty),
            (
                type_scheme.vars.to_string().as_str(),
                type_scheme.ty.to_string().as_str()
            ),
            "Failure for symbol {name}"
        );
    }
}

#[test]
fn type_scheme_simplify_type_vars_basic() {
    let ts = parse_type_scheme("A, B, C", "B -> (C -> (A, B))").simplify_type_vars();
    assert_eq!(
        format_type_scheme_around_name(&"x", &Some(ts)),
        "<T1, T2, T3> x: T2 -> (T3 -> (T1, T2))"
    );
}

#[test]
fn type_scheme_simplify_type_vars() {
    // Test conflicts between the old and new names.
    let ts = parse_type_scheme("T2: FromLiteral + Sum, T1", "T2 -> T1[]").simplify_type_vars();
    assert_eq!(
        format_type_scheme_around_name(&"x", &Some(ts)),
        "<T1: FromLiteral + Sum, T2> x: T1 -> T2[]"
    );
}

#[test]
#[should_panic = "Expected type: expr\\n"]
fn use_fun_in_expr_context() {
    let input = r#"namespace N(16);
    let id = |i| i;
    let w;
    w = id;
"#;
    analyze_string::<GoldilocksField>(input);
}

#[test]
fn single_literal() {
    let input = "let<T: FromLiteral> x: T[] = [1, 2];";
    type_check(input, &[("x", "T: FromLiteral", "T[]")]);
}

#[test]
fn assignment() {
    // This should derive a concrete type for x due to how it is used by y.
    let input = "let x = [|i| i]; let y: int[] = [x[0](2)];";
    type_check(input, &[("x", "", "(int -> int)[]"), ("y", "", "int[]")]);
}

#[test]
#[should_panic(expected = "Inferred: let<T: Add> x:")]
fn higher_order_too_specific() {
    // The type for x is too specific, it does not need 'FromLiteral"
    let input = "
        let<T: Add + FromLiteral> x: T -> ((T -> T) -> T) = |i| |f| i + f(i);
        let<T: Add + FromLiteral> y: T = x(2)(|k| k + 8);
    ";
    type_check(input, &[]);
}

#[test]
fn higher_order() {
    let input = "
        let<T: Add> x: T -> ((T -> T) -> T) = |i| |f| i + f(i);
        let<T: Add + FromLiteral> y: T = x(2)(|k| k + 8);
    ";
    type_check(
        input,
        &[
            ("x", "T: Add", "T -> ((T -> T) -> T)"),
            ("y", "T: Add + FromLiteral", "T"),
        ],
    );
}

#[test]
#[should_panic(expected = "Cannot unify types")]
fn invalid_recursive() {
    let input = "let x = |i| |f| x(i);";
    type_check(input, &[]);
}

#[test]
fn fold() {
    let input = "let<T1, T2> fold: int, (int -> T1), T2, (T2, T1 -> T2) -> T2 = |length, f, initial, folder|
        if length <= 0 {
            initial
        } else {
            folder(fold((length - 1), f, initial, folder), f((length - 1)))
        };";
    type_check(
        input,
        &[(
            "fold",
            "T1, T2",
            "int, (int -> T1), T2, (T2, T1 -> T2) -> T2",
        )],
    );
}

#[test]
#[should_panic(expected = "Inferred type scheme: <T: Add> sum: T, T -> T")]
fn sum() {
    let input = "let sum = |a, b| a + b;";
    type_check(input, &[]);
}

#[test]
fn sum_via_fold() {
    let input = "
    let<T1, T2> fold: int, (int -> T1), T2, (T2, T1 -> T2) -> T2 = |length, f, initial, folder|
        if length <= 0 {
            initial
        } else {
            folder(fold((length - 1), f, initial, folder), f((length - 1)))
        };
    let<T: Add + FromLiteral> sum: int, (int -> T) -> T = |n, f| fold(n, f, 0, |a, b| a + b);
    ";
    type_check(input, &[]);
}

#[test]
fn pow() {
    let input =
        "let<T: Pow> pow: T, int -> T = |a, b| a ** b; let<T: FromLiteral + Pow> x: T = pow(2, 3);";
    type_check(
        input,
        &[
            ("pow", "T: Pow", "T, int -> T"),
            ("x", "T: FromLiteral + Pow", "T"),
        ],
    );
}

#[test]
#[should_panic(expected = "Could not derive a concrete")]
fn generic_fixes_concrete() {
    // It is debatable whether this test should fail or not.
    // The signature of `y` could be seen as fixing the type of `x`,
    // but in order to do that, we have to unify the derived type of
    // `y` with the declared and this would maybe create problems in that
    // we would not derive the most generic type for generic functions.
    let input = "
        let x = || 8;
        let<T> y: T -> int = |k| x();
    ";
    type_check(input, &[]);
}

#[test]
fn generic_needs_concrete() {
    let input = "
        let x = || 8;
        let<T> y: T -> int = |k| x();
        let t: int = x();
    ";
    type_check(input, &[]);
}

#[test]
fn if_statement() {
    let input = "
        let g = || g();
        let x = |a, b| if g() { a } else { b + 2 };
        let c: int = 2;
        let y = [|i| x(c, i)];
    ";
    type_check(
        input,
        &[
            ("g", "", "-> bool"),
            ("x", "", "int, int -> int"),
            ("c", "", "int"),
            ("y", "", "(int -> int)[]"),
        ],
    );
}

#[test]
fn constraints() {
    let input = "
        let a;
        let BYTE: col = |i| std::convert::fe(i & 0xff);
        [ a + 1 ] in [BYTE];
        namespace std::convert(8);
        let fe = 18;
    ";
    type_check(input, &[("a", "", "col"), ("BYTE", "", "col")]);
}

#[test]
fn bottom() {
    let input = "
    namespace std::check(8);
        let panic: string -> ! = panic();
        let div: int, int -> int = |x, y| if y == 0 { panic(\"Division by zero\") } else { x / y };";
    type_check(input, &[("std::check::div", "", "int, int -> int")]);
}

#[test]
fn lambda() {
    let input = "
    let x: col[3];
    let y: col;
    let set_equal: expr, expr -> Constr = |a, b| a = b;
    let<T1, T2> array_map: int, T1[], (T1 -> T2) -> T2[] = |n, a, f| if n == 0 { [] } else { array_map(n - 1, a, f) + [f(a[n - 1])] };
    array_map(3, x, |i| set_equal(i, y));
    ";
    type_check(input, &[]);
}

#[test]
#[should_panic = "Unable to derive concrete type for literal 3"]
fn non_concrete_inner_type() {
    let input = "let x: int = (|i| 7)(3);";
    type_check(input, &[("x", "", "int")]);
}

#[test]
#[should_panic = "Unable to derive concrete type for reference to generic symbol std::array::len"]
fn non_concrete_inner_type_arr() {
    let input = "let x: int = std::array::len([]); namespace std::array(2); let len = 99;";
    type_check(input, &[("x", "", "int")]);
}

#[test]
fn type_check_arrays() {
    let input = "
        namespace X(2);
        let<T: FromLiteral + Mul + Add> bn: T, T -> T = |a, b| a * 0x100000000 + b;
    
        pol fixed x(i) { match i { 0 => bn(1, 2), 1 => bn(3, 4) } };
        let t: int = bn(5, 6);
    ";
    type_check(input, &[]);
}

#[test]
#[should_panic = "Expected either int -> int or int -> fe, but got: int -> (int, string).\\nCannot unify types (int, string) and fe"]
fn error_for_column_type() {
    let input = "
        let x: col = |i| (i, \"abc\");
    ";
    type_check(input, &[]);
}

#[test]
fn col_array_is_array() {
    let input = "
    namespace std::array(16);
        let len = [];
    namespace main(16);
        pol commit x1[16];
        let x2: col[16];
        let t: int = std::array::len(x1);
        let r: int = std::array::len(x2);
    ";
    type_check(input, &[]);
}

#[test]
fn enum_simple() {
    let input = "
    enum X { A, B(int), C(string[], int) }
    let v: X -> (X, int) = |x| (x, 2);
    ";
    type_check(input, &[]);
}

#[test]
fn enum_constr() {
    let input = "
    enum X { A, B(int), C(string[], int) }
    let v: int -> X = |i| match i {
        0 => X::A,
        1 => X::B(7),
        2 => X::C([\"abc\"], 9),
        _ => X::A
    };

    ";
    type_check(input, &[]);
}

#[test]
fn enum_constr_is_function() {
    let input = "
    enum X { A, B(int), C(string[], int) }
    let a = || X::A;
    let b = || X::B;
    let c = || X::C;
    ";
    type_check(
        input,
        &[
            ("a", "", "-> X"),
            ("b", "", "-> (int -> X)"),
            ("c", "", "-> (string[], int -> X)"),
        ],
    );
}

#[test]
#[should_panic = "Expected symbol of kind Value but got Type: X"]
fn enum_is_not_constr() {
    let input = "
    enum X { A, B(int), C(string[], int) }
    let v: int -> X = |i| X;
    ";
    type_check(input, &[]);
}

#[test]
#[should_panic = "Expected type int -> std::prover::Query"]
fn query_with_wrong_type() {
    let input = "col witness w(i) query i;";
    type_check(input, &[]);
}

#[test]
#[should_panic = "Type int[] does not satisfy trait"]
fn wrong_type_args() {
    let input = "
        let<T: FromLiteral + Mul + Add> bn: T, T -> T = |a, b| a * 0x100000000 + b;
        let t: int = bn::<int[]>(5, 6);
    ";
    type_check(input, &[]);
}

#[test]
#[should_panic = "Type symbol not found: T"]
fn specialization_non_declared_type_var() {
    let input = "
        let<T: FromLiteral> x: T = 1;
        let t: int = x::<T>;
    ";
    type_check(input, &[]);
}

#[test]
#[should_panic = "Expected 0 type arguments for symbol x, but got 1: int[]"]
fn specialization_of_non_generic_symbol() {
    let input = "
        let x: int = 1;
        let t: int = x::<int[]>;
    ";
    type_check(input, &[]);
}

#[test]
fn specialization_of_non_generic_symbol2() {
    let input = "
        let x: int = 1;
        let t: int = x::<>;
    ";
    type_check(input, &[]);
}

#[test]
fn partial_specialization() {
    let input = "
        let<T1, T2> fold: int, (int -> T1), T2, (T2, T1 -> T2) -> T2 = |length, f, initial, folder|
            if length <= 0 {
                initial
            } else {
                folder(fold((length - 1), f, initial, folder), f((length - 1)))
            };
        let<T> fold_to_int_arr: int, (int -> T), int[], (int[], T -> int[]) -> int[] = fold::<T, int[]>;
        let<T> fold_int: int, (int -> int), T, (T, int -> T) -> T = fold::<int, T>;
        let y = fold_to_int_arr(4, |i| i, [], |acc, x| acc + [x]);
        let z = fold_int(4, |i| i, 0, |acc, x| acc + x);
    ";
    type_check(input, &[("y", "", "int[]"), ("z", "", "int")]);
}

#[test]
fn partial_specialization2() {
    let input = "
        let<T1, T2> fold: int, (int -> T1), T2, (T2, T1 -> T2) -> T2 = |length, f, initial, folder|
            if length <= 0 {
                initial
            } else {
                folder(fold((length - 1), f, initial, folder), f((length - 1)))
            };
        // This just forces the two type vars to be the same.
        let<T> fold_to_same: int, (int -> T), T, (T, T -> T) -> T = fold::<T, T>;
        let y = fold_to_same(4, |i| i, 0, |acc, x| acc + x);
    ";
    type_check(input, &[("y", "", "int")]);
}

#[test]
fn generic_enum() {
    let input = "
        enum Option<T> {
            Some(T),
            None
        }
        let<T1, T2> map: Option<T1>, (T1 -> T2) -> Option<T2> = |o, f| match o {
            Option::Some(x) => Option::Some(f(x)),
            Option::None => Option::None
        };
        let<T> unwrap_or_else: Option<T>, (-> T) -> T = |o, default| match o {
            Option::Some(x) => x,
            Option::None => default()
        };
        let t = Option::Some(3);
        let u = map(t, |x| x + 1);
        let k: int = unwrap_or_else(u, || 7);
    ";
    type_check(input, &[("t", "", "Option<int>")]);
}

#[test]
#[should_panic = "Inferred type scheme: <T> x: Option<T>"]
fn simple_none() {
    let input = "
        enum Option<T> {
            Some(T),
            None
        }
        let x = Option::None;
    ";
    type_check(input, &[("x", "", "Option<int>")]);
}

#[test]
fn type_from_pattern() {
    let input = "
    let r: int -> int = |i| i;
    let f = |q| match q {
        (x, []) => r(x),
        (x, [a]) => r(a),
        _ => 8
    };
    ";
    type_check(input, &[("f", "", "(int, int[]) -> int")]);
}

#[test]
fn enum_pattern() {
    let input = "
    enum X { A(int[], int), B, C(int) }
    let f = |q| match q {
        X::A([x, ..], _) => |i| X::B,
        X::B => |i| q,
        X::C(_) => X::C,
        x => |i| x,
    };
    ";
    type_check(input, &[("f", "", "X -> (int -> X)")]);
}

#[test]
#[should_panic = "Only one \"..\"-item allowed in array pattern"]
fn multi_ellipsis() {
    let input = "    let t: int[] -> int = (|i| match i {
        [1, .., 3, ..] => 2,
        _ => -1,
    });
";
    type_check(input, &[]);
}

#[test]
#[should_panic = "Expected enum variant for pattern but got int -> X - maybe you forgot the parentheses?"]
fn enum_no_paren_for_paren() {
    let input = "
    enum X { A(int) }
    let f = |q| match q {
        X::A => 2,
        _ => 3,
    };
    ";
    type_check(input, &[]);
}

#[test]
#[should_panic = "Enum variant X::A does not have fields, but is used with parentheses in pattern"]
fn enum_paren_for_no_paren() {
    let input = "
    enum X { A }
    let f = |q| match q {
        X::A() => 2,
        _ => 3,
    };
    ";
    type_check(input, &[]);
}

#[test]
#[should_panic = "Invalid number of data fields for enum variant X::A. Expected 1 but got 2."]
fn enum_too_many_fields() {
    let input = "
    enum X { A(int) }
    let f = |q| match q {
        X::A(_, _) => 2,
        _ => 3,
    };
    ";
    type_check(input, &[]);
}

#[test]
fn empty_function() {
    let input = "
    let f: int -> () = |i| { };
    let g: int -> () = |i| {
        f(i);
    };
    
    let h: () = g(4);
    ";
    type_check(input, &[]);
}

#[test]
fn empty_match() {
    let input = "
    let h: int -> int = |i| i;
    let f: int -> () = |i| match i {
        5 => { 
            let _ = h(4);
        },
        _ => { }
    };

    let g: () = f(4);
    let k: () = f(5);
    ";
    type_check(input, &[]);
}

#[test]
fn empty_conditional() {
    let input = "
    let h: int -> int = |i| i;
    let f: int -> () = |i| if i == 5 {
        let _ = h(4);
    } else { };

    let g: () = f(4);
    let k: () = f(5);
    ";
    type_check(input, &[]);
}

#[test]
fn cols_in_func() {
    let input = "
    namespace Main(104);
    let h: -> () = constr || {
        let w: col;
        let f: col = |j| j + 1;
        w = f;
    };
    h();
    ";
    type_check(input, &[]);
}

#[test]
fn type_vars_in_block_let() {
    let input = "
    let<T> f: T -> T[] = |i| [i];
    let<Q> x: Q -> Q[][] = |i| {
        let y: Q[] = f(i);
        [y]
    };
    ";
    type_check(input, &[]);
}

#[test]
#[should_panic = "Expected type: int -> T\\nInferred type: int\\n"]
fn new_fixed_column_wrong_value_type() {
    let input = r#"namespace N(16);
        let f = constr |j| {
            let k: int = 2;
            let fi: col = k;
            fi
        };
        let ev = f(2);
        let x;
        x = ev;
    "#;
    type_check(input, &[]);
}

#[test]
#[should_panic = "Let-declared variables without value must have type 'col'"]
fn new_fixed_column_wrong_type() {
    let input = r#"namespace N(16);
        let f = constr || {
            let fi: int;
        };
        f();
    "#;
    type_check(input, &[]);
}

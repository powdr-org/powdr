use itertools::Itertools;
use powdr_ast::{
    analyzed::{Analyzed, Expression, Reference},
    parsed::visitor::AllChildren,
};
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
        .unwrap()
}

#[test]
fn new_witness_column() {
    let input = r#"namespace N(16);
    let even: col = |i| i * 2_int;
    let new_wit = constr || { let x; x };
    let new_wit_arr = constr || { let x; [x, x] };
    let x;
    let y;
    let z = new_wit();
    z = y;
    z $ [z] in [even];
    let t = new_wit_arr();
    t[0] = t[1];
    "#;
    let expected = r#"namespace N(16);
    col fixed even(i) { i * 2_int };
    let new_wit: -> expr = constr || {
        let x: col;
        x
    };
    let new_wit_arr: -> expr[] = constr || {
        let x: col;
        [x, x]
    };
    col witness x;
    col witness y;
    let z: expr = N::new_wit();
    col witness x_1;
    N::x_1 = N::y;
    N::x_1 $ [N::x_1] in [N::even];
    let t: expr[] = N::new_wit_arr();
    col witness x_2;
    N::x_2 = N::x_2;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn new_witness_column_name_clash() {
    let input = r#"namespace N(16);
    let new_wit = constr || { let x; x };
    new_wit() = new_wit() + new_wit();
    "#;
    let expected = r#"namespace N(16);
    let new_wit: -> expr = constr || {
        let x: col;
        x
    };
    col witness x;
    col witness x_1;
    col witness x_2;
    N::x = N::x_1 + N::x_2;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn create_constraints() {
    let input = r#"namespace N(16);
    let force_bool: expr -> Constr = |c| c * (1 - c) = 0;
    let new_bool: -> expr = constr || { let x; force_bool(x); x };
    let is_zero: expr -> expr = constr |x| {
        let x_is_zero;
        force_bool(x_is_zero);
        let x_inv;
        x_is_zero = 1 - x * x_inv;
        x_is_zero * x = 0;
        x_is_zero
    };
    let x;
    let x_is_zero = is_zero(x);
    let y;
    y = x_is_zero + 2;
    "#;
    let expected = r#"namespace N(16);
    let force_bool: expr -> std::prelude::Constr = |c| c * (1_expr - c) = 0_expr;
    let new_bool: -> expr = constr || {
        let x: col;
        N::force_bool(x);
        x
    };
    let is_zero: expr -> expr = constr |x| {
        let x_is_zero: col;
        N::force_bool(x_is_zero);
        let x_inv: col;
        x_is_zero = 1_expr - x * x_inv;
        x_is_zero * x = 0_expr;
        x_is_zero
    };
    col witness x;
    let x_is_zero: expr = N::is_zero(N::x);
    col witness y;
    col witness x_is_zero_1;
    col witness x_inv;
    N::x_is_zero_1 * (1 - N::x_is_zero_1) = 0;
    N::x_is_zero_1 = 1 - N::x * N::x_inv;
    N::x_is_zero_1 * N::x = 0;
    N::y = N::x_is_zero_1 + 2;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
pub fn degree() {
    let input = r#"
        namespace std::convert;
            let expr = [];
        namespace std::prover;
            let degree = [];
            let min_degree = [];
            let max_degree = [];
        namespace Main(8);
            let d = std::prover::degree();
            let w;
            w = std::convert::expr(d);
        namespace Other(32..64);
            let min = std::prover::min_degree();
            let max = std::prover::max_degree();
            col witness w;
            w = 8;
    "#;
    let formatted = analyze_string(input).to_string();
    let expected = r#"namespace std::convert;
    let expr = [];
namespace std::prover;
    let degree = [];
    let min_degree = [];
    let max_degree = [];
namespace Main(8);
    let d: int = std::prover::degree();
    col witness w;
    Main::w = 8;
namespace Other(32..64);
    let min: int = std::prover::min_degree();
    let max: int = std::prover::max_degree();
    col witness w;
    Other::w = 8;
"#;
    assert_eq!(formatted, expected);
}

#[test]
#[should_panic = "Error: DataNotAvailable"]
pub fn degree_unset() {
    let input = r#"
        namespace std::convert;
            let expr = [];
        namespace std::prover;
            let degree = [];
        namespace Main(32..63);
            let d = std::prover::degree();
            let w;
            w = std::convert::expr(d);
    "#;
    analyze_string(input);
}

#[test]
pub fn constructed_constraints() {
    let input = r#"
        namespace Main(1024);
            let x;
            let y;
            let z;
            Constr::Identity(x, y);
            Constr::Lookup((Option::Some(1), Option::None), [(x, y), (3, z)]);
            Constr::Permutation((Option::None, Option::Some(x)), [(x, y), (3, z)]);
            Constr::Connection([(x, z), (y, 3)]);
    "#;
    let formatted = analyze_string(input).to_string();
    let expected = r#"namespace Main(1024);
    col witness x;
    col witness y;
    col witness z;
    Main::x = Main::y;
    [Main::x, 3] in [Main::y, Main::z];
    [Main::x, 3] is Main::x $ [Main::y, Main::z];
    [Main::x, Main::y] connect [Main::z, 3];
"#;
    assert_eq!(formatted, expected);
}

#[test]
fn next() {
    let input = r#"namespace N(16);
        col witness x;
        col witness y;
        x * y = 1';
        x * y = (1 + x)';
    "#;
    let formatted = analyze_string(input).to_string();
    let expected = r#"namespace N(16);
    col witness x;
    col witness y;
    N::x * N::y = 1;
    N::x * N::y = 1 + N::x';
"#;
    assert_eq!(formatted, expected);
}

#[test]
#[should_panic = "Double application of \\\"'\\\" on: N::x"]
fn double_next() {
    let input = r#"namespace N(16);
        col witness x;
        col witness y;
        x * y = (1 + x')';
    "#;
    analyze_string(input).to_string();
}

#[test]
fn new_fixed_column() {
    let input = r#"
    namespace std::convert;
        let fe = 9;
    namespace N(16);
        let f = constr || {
            let even: col = |i| std::convert::fe(i * 2_int);
            even
        };
        let ev = f();
        let x;
        x = ev;
    "#;
    let formatted = analyze_string(input).to_string();
    let expected = r#"namespace std::convert;
    let fe = 9;
namespace N(16);
    let f: -> expr = constr || {
        let even: col = std::prelude::ToCol::to_col::<(int -> fe)>(|i| std::convert::fe::<int>(i * 2_int));
        even
    };
    let ev: expr = N::f();
    col witness x;
    col fixed even(i) { std::convert::fe::<int>(i * 2_int) };
    N::x = N::even;
"#;
    assert_eq!(formatted, expected);
}

#[test]
fn new_fixed_column_as_closure() {
    let input = r#"namespace N(16);
        let f = constr |j| {
            let fi: col = |i| (i + j) * 2;
            fi
        };
        let ev = f(2);
        let x;
        x = ev;
    "#;
    let formatted = analyze_string(input).to_string();
    let expected = r#"namespace N(16);
    let f: int -> expr = constr |j| {
        let fi: col = |i| (i + j) * 2_int;
        fi
    };
    let ev: expr = N::f(2_int);
    col witness x;
    let fi = {
        let j = 2_int;
        |i| (i + j) * 2_int
    };
    N::x = N::fi;
"#;
    assert_eq!(formatted, expected);
}

#[test]
fn set_hint() {
    let input = r#"
    namespace std::prover;
        let eval = 8;
        enum Query { Hint(fe), None, }
    namespace N(16);
        let x;
        let y;
        std::prelude::set_hint(y, |i| std::prelude::Query::Hint(std::prover::eval(x)));
        {
            let z;
            std::prelude::set_hint(z, query |_| std::prelude::Query::Hint(1));
        };
    "#;
    let expected = r#"namespace std::prover;
    let eval = 8;
    enum Query {
        Hint(fe),
        None,
    }
namespace N(16);
    col witness x;
    col witness y;
    std::prelude::set_hint(N::y, query |i| std::prelude::Query::Hint(std::prover::eval(N::x)));
    col witness z;
    std::prelude::set_hint(N::z, query |_| std::prelude::Query::Hint(1_fe));
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
#[should_panic = "Expected type: int -> std::prelude::Query"]
fn set_hint_invalid_function() {
    let input = r#"
    namespace std::prover;
        let eval = 8;
        enum Query { Hint(fe), None, }
    namespace N(16);
        let x;
        std::prelude::set_hint(x, query |_, _| std::prelude::Query::Hint(1));
    "#;
    analyze_string(input);
}

#[test]
#[should_panic = "Array elements are not supported for std::prelude::set_hint (called on N::x[0])."]
fn set_hint_array_element() {
    let input = r#"
    namespace std::prover;
        enum Query { Hint(fe), None, }
    namespace N(16);
        let x: col[2];
        std::prelude::set_hint(x[0], query |_| std::prelude::Query::Hint(1));
    "#;
    let expected = r#"namespace std::prover;
    let set_hint = 8;
    let eval = 8;
    enum Query {
        Hint(fe),
        None,
    }
namespace N(16);
    col witness x(_) query std::prelude::Query::Hint(1);
    col witness y(i) query std::prelude::Query::Hint(std::prover::eval(N::x));
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
#[should_panic = "Expected reference to witness column as first argument for std::prelude::set_hint, but got intermediate column N::y."]
fn set_hint_no_col() {
    let input = r#"
    namespace std::prover;
        enum Query { Hint(fe), None, }
    namespace N(16);
        let x;
        let y: inter = x;
        std::prelude::set_hint(y, query |_| std::prelude::Query::Hint(1));
    "#;
    analyze_string(input);
}

#[test]
#[should_panic = "Column N::x already has a hint set, but tried to add another one."]
fn set_hint_twice() {
    let input = r#"
    namespace std::prover;
        enum Query { Hint(fe), None, }
    namespace N(16);
        let x;
        std::prelude::set_hint(x, query |_| std::prelude::Query::Hint(1));
        std::prelude::set_hint(x, query |_| std::prelude::Query::Hint(2));
    "#;
    analyze_string(input);
}

#[test]
#[should_panic = "Column N::x already has a hint set, but tried to add another one."]
fn set_hint_twice_in_constr() {
    let input = r#"
    namespace std::prover;
        enum Query { Hint(fe), None, }
    namespace N(16);
        let y;
        {
            let x;
            std::prelude::set_hint(x, query |_| std::prelude::Query::Hint(1));
            std::prelude::set_hint(x, query |_| std::prelude::Query::Hint(2));
        };
    "#;
    analyze_string(input);
}

#[test]
fn set_hint_outside() {
    let input = r#"
    namespace std::prover;
        let eval = 8;
        enum Query { Hint(fe), None, }
    namespace N(16);
        let x;
        let y;
        let create_wit = constr || { let w; w };
        let z = create_wit();
        let set_hint = constr |c| { std::prelude::set_hint(c, query |_| std::prelude::Query::Hint(8)); };
        set_hint(x);
        set_hint(y);
        (|| { set_hint(z); })();
    "#;
    let expected = r#"namespace std::prover;
    let eval = 8;
    enum Query {
        Hint(fe),
        None,
    }
namespace N(16);
    col witness x;
    std::prelude::set_hint(N::x, query |_| std::prelude::Query::Hint(8_fe));
    col witness y;
    std::prelude::set_hint(N::y, query |_| std::prelude::Query::Hint(8_fe));
    let create_wit: -> expr = constr || {
        let w: col;
        w
    };
    let z: expr = N::create_wit();
    let set_hint: expr -> () = constr |c| {
        std::prelude::set_hint(c, query |_| std::prelude::Query::Hint(8_fe));
    };
    col witness w;
    std::prelude::set_hint(N::w, query |_| std::prelude::Query::Hint(8_fe));
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn intermediate_syntax() {
    let input = r#"namespace N(65536);
    col witness x[5];
    let inter: inter = x[2];
    let inter_arr: inter[5] = x;
"#;
    let analyzed = analyze_string(input);
    assert_eq!(analyzed.intermediate_count(), 6);
    let expected = r#"namespace N(65536);
    col witness x[5];
    col inter = N::x[2];
    col inter_arr[5] = [N::x[0], N::x[1], N::x[2], N::x[3], N::x[4]];
"#;
    assert_eq!(analyzed.to_string(), expected);
}

#[test]
fn intermediate_dynamic() {
    let input = r#"namespace N(65536);
    col witness x[5];
    {
        let inte: inter = x[2];
        let inter_arr: inter[5] = x;
        inte = 8;
        inter_arr[3] = 9;
    };
"#;
    let analyzed = analyze_string(input);
    assert_eq!(analyzed.intermediate_count(), 6);
    let expected = r#"namespace N(65536);
    col witness x[5];
    col inte = N::x[2];
    col inter_arr[5] = [N::x[0], N::x[1], N::x[2], N::x[3], N::x[4]];
    N::inte = 8;
    N::inter_arr[3] = 9;
"#;
    assert_eq!(analyzed.to_string(), expected);
}

#[test]
fn intermediate_arr_no_length() {
    let input = r#"namespace N(65536);
    col witness x[5];
    {
        let inte: inter[] = x;
    };
"#;
    let analyzed = analyze_string(input);
    assert_eq!(analyzed.intermediate_count(), 5);
    let expected = r#"namespace N(65536);
    col witness x[5];
    col inte[5] = [N::x[0], N::x[1], N::x[2], N::x[3], N::x[4]];
"#;
    assert_eq!(analyzed.to_string(), expected);
}

#[test]
#[should_panic = "Error creating intermediate column array N::inte: Expected array of length 6 as value but it has 2 elements."]
fn intermediate_arr_wrong_length() {
    let input = r#"namespace N(65536);
    col witness x[2];
    {
        let inte: inter[6] = x;
    };
"#;
    analyze_string(input);
}

#[test]
fn closure() {
    let input = r#"
    namespace std::prover;
        let eval = 8;
    namespace N(16);
        col witness x;
        let y = |a, b, c| Query::Hint(a + c());
        {
            let r = 9;
            set_hint(x, |i| y(1, i, || 9 + r));
        };
"#;
    let analyzed = analyze_string(input);
    let expected = r#"namespace std::prover;
    let eval = 8;
namespace N(16);
    col witness x;
    std::prelude::set_hint(N::x, {
        let r = 9_fe;
        |i| N::y(1_fe, i, || 9_fe + r)
    });
    let y: fe, int, (-> fe) -> std::prelude::Query = |a, b, c| std::prelude::Query::Hint(a + c());
"#;
    assert_eq!(analyzed.to_string(), expected);
}

#[test]
fn closure_complex() {
    let input = r#"
    namespace std::prover;
        let eval = 8;
    namespace std::convert;
        let fe = 9;
    namespace N(16);
        col witness x;
        let y = |a, b, c| Query::Hint(a + c());
        {
            let r = 9;
            let k: int[] = [-2];
            let v: int = 9; // not captured
            let q = "" != "";
            let b = (|a, s, t| || "" == s)("a", "", "t");
            set_hint(x, |i| {
                y(1, i, || if b() && q { 9 + r } else { std::convert::fe(k[0]) })
            });
        };
"#;
    let analyzed = analyze_string(input);
    let expected = r#"namespace std::prover;
    let eval = 8;
namespace std::convert;
    let fe = 9;
namespace N(16);
    col witness x;
    std::prelude::set_hint(N::x, {
        let r = 9_fe;
        let k = [-2_int];
        let q = std::prelude::false;
        let b = {
            let s = "";
            || "" == s
        };
        |i| { N::y(1_fe, i, || if b() && q { 9_fe + r } else { std::convert::fe::<int>(k[0_int]) }) }
    });
    let y: fe, int, (-> fe) -> std::prelude::Query = |a, b, c| std::prelude::Query::Hint(a + c());
"#;
    assert_eq!(analyzed.to_string(), expected);

    let expected_analyzed = analyze_string(expected);
    // Check that the LocalVar ref IDs are assigned correctly. This cannot be tested by printing
    // since the IDs are ignored. Another way to test would be to execute, but it is difficult
    // to execute code where values are turned into expressions like that.
    // We extract the IDs of the analized and the re-parsed expected PIL.
    // They should both match.
    let refs = [analyzed, expected_analyzed]
        .into_iter()
        .map(|a| {
            let def = a.definitions.get("N::x").as_ref().unwrap().1.as_ref();
            def.unwrap()
                .all_children()
                .filter_map(|e| match e {
                    Expression::Reference(_, Reference::LocalVar(id, name)) => Some((id, name)),
                    _ => None,
                })
                .map(|(id, name)| format!("{name}: {id}"))
                .format(", ")
                .to_string()
        })
        .format("\n")
        .to_string();
    let expected_ids = "s: 3, i: 4, b: 3, q: 2, r: 0, k: 1";
    assert_eq!(refs, format!("{expected_ids}\n{expected_ids}"));
}

#[test]
fn simple_lookup() {
    let input = r#"namespace N(16);
    let x;
    let y;
    let a = [x];
    let b = [y]; 
    a in b;
    "#;
    let expected = r#"namespace N(16);
    col witness x;
    col witness y;
    let a: expr[] = [N::x];
    let b: expr[] = [N::y];
    [N::x] in [N::y];
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn selected_lookup() {
    let input = r#"namespace N(16);
    let a;
    let b;
    let x;
    let y;
    let k = [x];
    let t = a $ k;
    t in b $ [y];
    "#;
    let expected = r#"namespace N(16);
    col witness a;
    col witness b;
    col witness x;
    col witness y;
    let k: expr[] = [N::x];
    let t: std::prelude::SelectedExprs = N::a $ N::k;
    N::a $ [N::x] in N::b $ [N::y];
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn prover_functions() {
    let input = "
    namespace std::convert;
        let fe = 8;
    namespace std::prover;
        let provide_value = 9;
    namespace N(16);
        let x;
        let y;
        x = y;
        query |i| {
            std::prover::provide_value(x, i, std::convert::fe(i % 2));
            std::prover::provide_value(y, i, std::convert::fe(i % 2));
        };
    ";
    let analyzed = analyze_string(input);
    let expected = r#"namespace std::convert;
    let fe = 8;
namespace std::prover;
    let provide_value = 9;
namespace N(16);
    col witness x;
    col witness y;
    N::x = N::y;
    query |i| {
        std::prover::provide_value(N::x, i, std::convert::fe::<int>(i % 2_int));
        std::prover::provide_value(N::y, i, std::convert::fe::<int>(i % 2_int));
    };
"#;
    assert_eq!(analyzed.to_string(), expected);
}

#[test]
fn prover_functions_dynamic() {
    let input = "
    namespace std::convert;
        let fe = 8;
    namespace std::prover;
        let provide_value = 9;
    namespace N(16);
        let gen = constr || {
            let x;
            let y;
            x = y;
            query |i| {
                std::prover::provide_value(x, i, std::convert::fe(i % 2));
                std::prover::provide_value(y, i, std::convert::fe(i % 2));
            };
        };
        gen();
    ";
    let analyzed = analyze_string(input);
    let expected = r#"namespace std::convert;
    let fe = 8;
namespace std::prover;
    let provide_value = 9;
namespace N(16);
    let gen: -> () = constr || {
        let x: col;
        let y: col;
        x = y;
        query |i| {
            std::prover::provide_value(x, i, std::convert::fe::<int>(i % 2_int));
            std::prover::provide_value(y, i, std::convert::fe::<int>(i % 2_int));
        };
    };
    col witness x;
    col witness y;
    N::x = N::y;
    {
        let x = N::x;
        let y = N::y;
        query |i| {
            std::prover::provide_value(x, i, std::convert::fe::<int>(i % 2_int));
            std::prover::provide_value(y, i, std::convert::fe::<int>(i % 2_int));
        }
    };
"#;
    assert_eq!(analyzed.to_string(), expected);
}

#[test]
fn new_cols_at_stage() {
    let input = r#"
    namespace std::prover;
        let new_witness_col_at_stage: string, int -> expr = [];
    namespace N(16);
        let x;
        let r = std::prover::new_witness_col_at_stage("x", 0);
        let s = std::prover::new_witness_col_at_stage("x", 1);
        let t = std::prover::new_witness_col_at_stage("x", 2);
        let u = std::prover::new_witness_col_at_stage("y", 1);
        let v = std::prover::new_witness_col_at_stage("y", 2);
        let unused = std::prover::new_witness_col_at_stage("z", 10);
        let y;
        r + s + t + u + v = y;
    "#;
    let expected = r#"namespace std::prover;
    let new_witness_col_at_stage: string, int -> expr = [];
namespace N(16);
    col witness x;
    let r: expr = std::prover::new_witness_col_at_stage("x", 0_int);
    let s: expr = std::prover::new_witness_col_at_stage("x", 1_int);
    let t: expr = std::prover::new_witness_col_at_stage("x", 2_int);
    let u: expr = std::prover::new_witness_col_at_stage("y", 1_int);
    let v: expr = std::prover::new_witness_col_at_stage("y", 2_int);
    let unused: expr = std::prover::new_witness_col_at_stage("z", 10_int);
    col witness y;
    col witness x_1;
    col witness stage(1) x_2;
    col witness stage(2) x_3;
    col witness stage(1) y_1;
    col witness stage(2) y_2;
    N::x_1 + N::x_2 + N::x_3 + N::y_1 + N::y_2 = N::y;
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
}

#[test]
fn capture_enums() {
    let input = r#"
    namespace N(16);
        enum E<T> { A(T), B, C(T, int), D() }
        (|| {
            let x = E::A("abc");
            let y = E::B::<int[][]>;
            let z: E<int[]> = E::C([1, 2], 9);
            let w: E<fe> = E::D();
            query |_| {
                let t = (x, y, z, w);
            }
        })();

    "#;
    let expected = r#"namespace N(16);
    enum E<T> {
        A(T),
        B,
        C(T, int),
        D(),
    }
    {
        let x = N::E::A("abc");
        let y = N::E::B;
        let z = N::E::C([1_int, 2_int], 9_int);
        let w = N::E::D();
        query |_| {
            let t: (N::E<string>, N::E<int[][]>, N::E<int[]>, N::E<fe>) = (x, y, z, w);
        }
    };
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
    let re_analyzed = analyze_string(&formatted);
    assert_eq!(re_analyzed.to_string(), expected);
}

#[test]
fn capture_challenges_and_numbers() {
    let input = r#"
    namespace std::prelude;
        let challenge = 8;
    namespace std::prover;
        let provide_value = 9;
        let eval = -1;
    namespace N(16);
        (constr || {
            let x = std::prelude::challenge(0, 4);
            let y;
            let t = 2;
            query |i| {
                std::prover::provide_value(y, i, std::prover::eval(x) + t);
            }
        })();

    "#;
    let expected = r#"namespace std::prelude;
    let challenge = 8;
namespace std::prover;
    let provide_value = 9;
    let eval = -1;
    col witness y;
    {
        let x = std::prelude::challenge(0, 4);
        let y = std::prover::y;
        let t = 2_fe;
        query |i| {
            std::prover::provide_value(y, i, std::prover::eval(x) + t);
        }
    };
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
    let re_analyzed = analyze_string(&formatted);
    assert_eq!(re_analyzed.to_string(), expected);
}

#[test]
fn capture_binary_operations() {
    let input = r#"namespace std::prelude;
    namespace std::prover;
    let provide_value = 9;
    let eval = -1;
    namespace N(16);
        (constr || {
            let x;
            let y;
            let t = x + y;
            query |i| {
                let _ = std::prover::eval(t);
            }
        })();

    "#;
    let expected = r#"namespace std::prover;
    let provide_value = 9;
    let eval = -1;
    col witness x;
    col witness y;
    {
        let t = std::prover::x + std::prover::y;
        query |i| {
            let _: fe = std::prover::eval(t);
        }
    };
"#;
    let formatted = analyze_string(input).to_string();
    assert_eq!(formatted, expected);
    let re_analyzed = analyze_string(&formatted);
    assert_eq!(re_analyzed.to_string(), expected);
}

#[test]
pub fn capture_constraints_empty() {
    let input = r#"
        namespace std::prover;
            let capture_constraints: (-> ()) -> Constr[] = 9;

        namespace Main;
            let gen = || { };
            let a;
            let b;
            a = 1;
            std::prover::capture_constraints(gen);
            b = 2;
    "#;
    let formatted = analyze_string(input).to_string();
    let expected = "namespace std::prover;
    let capture_constraints: (-> ()) -> std::prelude::Constr[] = 9;
namespace Main;
    let gen: -> () = || { };
    col witness a;
    col witness b;
    Main::a = 1;
    Main::b = 2;
";
    assert_eq!(formatted, expected);
}

#[test]
pub fn capture_constraints_new_col_and_constr() {
    let input = r#"
        namespace std::prover;
            let capture_constraints: (-> ()) -> Constr[] = 9;

        namespace Main;
            let gen = constr || {
                let x;
                [x = 1, x = 2];
                x = 3;
            };
            let a;
            let b;
            a = 1;
            let constrs = std::prover::capture_constraints(gen);
            // Ignore the second constraint
            [constrs[0], constrs[2]];
            b = 2;
    "#;
    let formatted = analyze_string(input).to_string();
    let expected = "namespace std::prover;
    let capture_constraints: (-> ()) -> std::prelude::Constr[] = 9;
namespace Main;
    let gen: -> () = constr || {
        let x: col;
        [x = 1_expr, x = 2_expr];
        x = 3_expr;
    };
    col witness a;
    col witness b;
    Main::a = 1;
    let constrs: std::prelude::Constr[] = std::prover::capture_constraints(Main::gen);
    col witness x;
    Main::x = 1;
    Main::x = 3;
    Main::b = 2;
";
    assert_eq!(formatted, expected);
}

#[test]
pub fn capture_constraints_recursive() {
    let input = r#"
        namespace std::prover;
            let capture_constraints: (-> ()) -> Constr[] = 9;

        namespace Main;
            let a;
            [a] in [b];
            let constrs = std::prover::capture_constraints(constr || {
                let x;
                [x = 1, x = 2];
                std::prover::capture_constraints(constr || {
                    let y;
                    [y = 1, [y] in [x]];
                    y = 3;
                })[1];
                x = 3;
            });
            // Ignore the second constraint
            [constrs[0], constrs[2], constrs[3]];
            let b;
            b = 2;
    "#;
    let formatted = analyze_string(input).to_string();
    let expected = "namespace std::prover;
    let capture_constraints: (-> ()) -> std::prelude::Constr[] = 9;
namespace Main;
    col witness a;
    [Main::a] in [Main::b];
    let constrs: std::prelude::Constr[] = std::prover::capture_constraints(constr || {
        let x: col;
        [x = 1_expr, x = 2_expr];
        std::prover::capture_constraints(constr || {
            let y: col;
            [y = 1_expr, [y] in [x]];
            y = 3_expr;
        })[1_int];
        x = 3_expr;
    });
    col witness x;
    col witness y;
    Main::x = 1;
    [Main::y] in [Main::x];
    Main::x = 3;
    col witness b;
    Main::b = 2;
";
    assert_eq!(formatted, expected);
}

#[test]
pub fn at_next_stage() {
    let input = r#"
        namespace std::prover;
            let at_next_stage: (-> ()) -> () = 9;

        namespace Main;
            let a;
            std::prover::at_next_stage(constr || {
                let x;
                std::prover::at_next_stage(constr || {
                    let y;
                    x = 1;
                    y = 2;
                });
                let c;
                x = a + c;
            });
            let b;
    "#;
    let formatted = analyze_string(input).to_string();
    let expected = "namespace std::prover;
    let at_next_stage: (-> ()) -> () = 9;
namespace Main;
    col witness a;
    col witness stage(1) x;
    col witness stage(2) y;
    col witness stage(1) c;
    Main::x = 1;
    Main::y = 2;
    Main::x = Main::a + Main::c;
    col witness b;
";
    assert_eq!(formatted, expected);
}

#[test]
pub fn at_next_stage_intermediate_and_fixed() {
    let input = r#"
        namespace std::prover;
            let at_next_stage: (-> ()) -> () = 9;

        namespace Main;
            let a;
            std::prover::at_next_stage(constr || {
                let b: inter = a * a;
                let c;
                let first: col = |i| if i == 0_int { 1_fe } else { 0 };
                let d: inter = a + c;
                c' = first;
            });
            let x;
    "#;
    let formatted = analyze_string(input).to_string();
    let expected = "namespace std::prover;
    let at_next_stage: (-> ()) -> () = 9;
namespace Main;
    col witness a;
    col b = Main::a * Main::a;
    col witness stage(1) c;
    col fixed first(i) { if i == 0_int { 1_fe } else { 0_fe } };
    col d = Main::a + Main::c;
    Main::c' = Main::first;
    col witness x;
";
    assert_eq!(formatted, expected);
}

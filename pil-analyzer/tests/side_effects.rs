use itertools::Itertools;
use powdr_ast::analyzed::Analyzed;
use powdr_number::GoldilocksField;
use test_log::test;

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
#[should_panic = "Tried to create a witness column in a pure context: let x;"]
fn new_wit_in_pure() {
    let input = r#"namespace N(16);
    let new_col = || { let x; x };
    "#;
    analyze_string(input);
}

#[test]
#[should_panic = "Tried to create a fixed column in a pure context: let x: col = |i| i;"]
fn new_fixed_in_pure() {
    let input = r#"namespace N(16);
    let new_col = || { let x: col = |i| i + 0_int; x };
    "#;
    analyze_string(input);
}

#[test]
#[should_panic = "Expected type () but got type std::prelude::Constr"]
fn constr_in_pure() {
    let input = r#"namespace N(16);
    let new_col = |x| { x = 7; [] };
    "#;
    analyze_string(input);
}

#[test]
fn return_constr_in_pure() {
    let input = r#"namespace N(16);
    let new_col = |x| x = 7;
    "#;
    analyze_string(input);
}

#[test]
#[should_panic = "Referenced the query function std::prover::eval inside a pure context."]
fn call_eval_in_pure() {
    let input = r#"
    namespace std::prover(16);
        let eval = [];
    namespace N(16);
        let val_of_x = |x| std::prover::eval(x);
    "#;
    analyze_string(input);
}

#[test]
fn call_eval_in_query() {
    let input = r#"
    namespace std::prover(16);
        let eval = [];
    namespace N(16);
        let val_of_x = query |x| std::prover::eval(x);
    "#;
    analyze_string(input);
}

#[test]
#[should_panic = "Referenced the constr function N::new_wit inside a query context."]
fn call_constr_in_query() {
    let input = r#"
    namespace std::prover(16);
        let eval = [];
    namespace N(16);
        let new_wit = constr || { let x; x };
        let val_of_x = query |x| std::prover::eval(new_wit());
    "#;
    analyze_string(input);
}

#[test]
#[should_panic = "Used a constr lambda function inside a pure context"]
fn constr_lambda_in_pure() {
    let input = r#"namespace N(16);
    let f = |x| {
        let new_wit = constr || { x = 7; 0};
        8
    };
    "#;
    analyze_string(input);
}

#[test]
#[should_panic = "Expected type () but got type std::prelude::Constr"]
fn reset_context() {
    let input = r#"namespace N(16);
    let new_col = |x| { x = 7; [] };
    "#;
    analyze_string(input);
}

#[test]
#[should_panic = "Used a constr lambda function inside a pure context"]
fn fixed_with_constr_type() {
    let input = "let x: col = constr |i| 2;";
    analyze_string(input);
}

#[test]
fn set_hint() {
    let input = r#"
    namespace std::prover;
        enum Query { Hint(fe), None, }
    namespace N(16);
        let x;
        std::prelude::set_hint(x, query |i| std::prelude::Query::Hint(1));
    "#;
    analyze_string(input);
}

#[test]
fn set_hint_can_use_query() {
    let input = r#"
    namespace std::prover;
        let eval = 7;
        enum Query { Hint(fe), None, }
    namespace N(16);
        let x;
        let y;
        std::prelude::set_hint(x, query |_| std::prelude::Query::Hint(std::prover::eval(y)));
    "#;
    analyze_string(input);
}

#[test]
fn set_hint_pure() {
    let input = r#"
    namespace std::prover;
        enum Query { Hint(fe), None, }
    namespace N(16);
        let x;
        std::prelude::set_hint(x, |i| std::prelude::Query::Hint(1));
    "#;
    analyze_string(input);
}

#[test]
#[should_panic = "Used a constr lambda function inside a query context"]
fn set_hint_constr() {
    let input = r#"
    namespace std::prover;
        enum Query { Hint(fe), None, }
    namespace N(16);
        let x;
        std::prelude::set_hint(x, constr |i| std::prelude::Query::Hint(1));
    "#;
    analyze_string(input);
}

#[test]
#[should_panic = "Tried to create a fixed column in a pure context: let y: col = constr |i| 2;"]
fn constr_lambda_in_impl() {
    let input = r#"namespace N(16);
    trait Impure<T> {
            f: T -> T,
        }
    impl Impure<int> {
        f: |x| {
            let y: col = constr |i| 2;
            8
        },
    }
    let result: int = Impure::f(5);
    "#;
    analyze_string(input);
}

#[test]
fn query_in_constr() {
    let input = r#"namespace N(16);
    query |i| { };
    let f = constr || { query |i| { } };
    f();
    "#;
    analyze_string(input);
}

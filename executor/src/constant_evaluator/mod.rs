pub use data_structures::{get_uniquely_sized, get_uniquely_sized_cloned, VariablySizedColumn};
use itertools::Itertools;
use powdr_ast::analyzed::Analyzed;
use powdr_number::FieldElement;

mod data_structures;
mod interpreter;
mod jit_compiler;

/// Generates the fixed column values for all fixed columns that are defined (and not just declared).
///
/// @returns the names (in source order) and the values for the columns.
/// Arrays of columns are flattened, the name of the `i`th array element
/// is `name[i]`.
pub fn generate<T: FieldElement>(analyzed: &Analyzed<T>) -> Vec<(String, VariablySizedColumn<T>)> {
    let max_degree = analyzed
        .constant_polys_in_source_order()
        .map(|(poly, _)| poly.degree.unwrap().max)
        .max()
        .unwrap_or_default();

    let mut fixed_cols = Default::default();
    if max_degree > (1 << 18) {
        fixed_cols = jit_compiler::generate_values(analyzed);
    }
    let mut used_interpreter = false;
    for (poly, value) in analyzed.constant_polys_in_source_order() {
        if let Some(value) = value {
            // For arrays, generate values for each index,
            // for non-arrays, set index to None.
            for (index, (name, id)) in poly.array_elements().enumerate() {
                fixed_cols.entry((name.clone(), id)).or_insert_with(|| {
                    let index = poly.is_array().then_some(index as u64);
                    let range = poly.degree.unwrap();
                    range
                        .iter()
                        .map(|degree| {
                            used_interpreter = true;
                            interpreter::generate_values(analyzed, degree, &name, value, index)
                        })
                        .collect::<Vec<_>>()
                        .into()
                });
            }
        }
    }
    if !used_interpreter && !fixed_cols.is_empty() {
        log::info!("All columns were genrated using JIT-code.");
    }

    fixed_cols
        .into_iter()
        .sorted_by_key(|((_, id), _)| *id)
        .map(|((name, _), values)| (name, values))
        .collect()
}

/// Generates the fixed column values only using JIT-compiled code.
/// Might not return all fixed columns.
pub fn generate_only_via_jit<T: FieldElement>(
    analyzed: &Analyzed<T>,
) -> Vec<(String, VariablySizedColumn<T>)> {
    jit_compiler::generate_values(analyzed)
        .into_iter()
        .sorted_by_key(|((_, id), _)| *id)
        .map(|((name, _), values)| (name, values))
        .collect()
}

#[cfg(test)]
mod test {
    use itertools::Itertools;
    use powdr_ast::analyzed::Analyzed;
    use powdr_number::GoldilocksField;
    use pretty_assertions::assert_eq;
    use test_log::test;

    use crate::constant_evaluator::{
        data_structures::get_uniquely_sized, generate as generate_variably_sized,
    };

    fn convert(input: Vec<i32>) -> Vec<GoldilocksField> {
        input.into_iter().map(|x| x.into()).collect()
    }

    fn generate(analyzed: &Analyzed<GoldilocksField>) -> Vec<(String, Vec<GoldilocksField>)> {
        get_uniquely_sized(&generate_variably_sized(analyzed))
            .unwrap()
            .into_iter()
            .map(|(name, values)| (name, values.clone()))
            .collect()
    }

    fn analyze_string<T: powdr_number::FieldElement>(src: &str) -> Analyzed<T> {
        powdr_pil_analyzer::analyze_string::<T>(src)
            .map_err(|errors| {
                eprintln!("Error analyzing test input:");
                errors
                    .into_iter()
                    .map(|e| {
                        e.output_to_stderr();
                        e.to_string()
                    })
                    .format("\n")
                    .to_string()
            })
            .unwrap()
    }

    #[test]
    fn last() {
        let src = r#"
            let N = 8;
            namespace F(N);
            col fixed LAST(i) { if i == N - 1_int { 1_fe } else { 0_fe } };
            "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 8);
        let constants = generate(&analyzed);
        assert_eq!(
            constants,
            vec![("F::LAST".to_string(), convert(vec![0, 0, 0, 0, 0, 0, 0, 1]))]
        );
    }

    #[test]
    fn counter() {
        let src = r#"
            let N: int = 8;
            namespace std::convert;
            let fe = [];
            namespace F(N);
            pol constant EVEN(i) { std::convert::fe(2 * (i - 1) + 4_int) };
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 8);
        let constants = generate(&analyzed);
        assert_eq!(
            constants,
            vec![(
                "F::EVEN".to_string(),
                convert(vec![2, 4, 6, 8, 10, 12, 14, 16])
            )]
        );
    }

    #[test]
    fn xor() {
        let src = r#"
            let N: int = 8;
            namespace std::convert;
            let fe = [];
            namespace F(N);
            pol constant X(i) { std::convert::fe(i ^ (i + 17) | 3_int) };
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 8);
        let constants = generate(&analyzed);
        assert_eq!(
            constants,
            vec![(
                "F::X".to_string(),
                convert((0..8).map(|i| i ^ (i + 17) | 3).collect())
            )]
        );
    }

    #[test]
    fn match_expression() {
        let src = r#"
            let N: int = 8;
            namespace std::convert;
            let fe = [];
            namespace F(N);
            let x: int -> fe = |i| std::convert::fe(match i {
                0 => 7,
                3 => 9,
                5 => 2,
                _ => 4,
            } + 1_int);
            pol constant X(i) { x(i) };
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 8);
        let constants = generate(&analyzed);
        assert_eq!(
            constants,
            vec![("F::X".to_string(), convert(vec![8, 5, 5, 10, 5, 3, 5, 5]))]
        );
    }

    #[test]
    fn if_expression() {
        let src = r#"
            let N: int = 8;
            namespace F(N);
            let X: col = |i| if i < 3_int { 7_fe } else { 9 };
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 8);
        let constants = generate(&analyzed);
        assert_eq!(
            constants,
            vec![("F::X".to_string(), convert(vec![7, 7, 7, 9, 9, 9, 9, 9]))]
        );
    }

    #[test]
    fn macro_directive() {
        let src = r#"
            let N: int = 8;
            namespace std::convert;
            let fe = [];
            namespace F(N);
            let minus_one: int -> int = |x| x - 1;
            pol constant EVEN(i) { std::convert::fe(2 * minus_one(i) + 2) };
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 8);
        let constants = generate(&analyzed);
        assert_eq!(
            constants,
            vec![(
                "F::EVEN".to_string(),
                convert(vec![0, 2, 4, 6, 8, 10, 12, 14])
            )]
        );
    }

    #[test]
    fn poly_call() {
        let src = r#"
            let N = 16;
            namespace std::convert(N);
            let int = [];
            let fe = [];
            namespace F(N);
            let seq_f: int -> int = |i| i;
            col fixed seq(i) { std::convert::fe(seq_f(i)) };
            col fixed double_plus_one(i) { std::convert::fe(std::convert::int(seq_f((2 * i) % N)) + 1) };
            let half_nibble_f = |i| i & 0x7;
            col fixed half_nibble(i) { std::convert::fe(half_nibble_f(i)) };
            col fixed doubled_half_nibble(i) { std::convert::fe(half_nibble_f(i / 2)) };
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 16);
        let constants = generate(&analyzed);
        assert_eq!(constants.len(), 4);
        assert_eq!(
            constants[0],
            (
                "F::seq".to_string(),
                convert((0..=15i32).collect::<Vec<_>>())
            )
        );
        assert_eq!(
            constants[1],
            (
                "F::double_plus_one".to_string(),
                convert([1i32, 3, 5, 7, 9, 11, 13, 15, 1, 3, 5, 7, 9, 11, 13, 15].to_vec())
            )
        );
        assert_eq!(
            constants[2],
            (
                "F::half_nibble".to_string(),
                convert([0i32, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7].to_vec())
            )
        );
        assert_eq!(
            constants[3],
            (
                "F::doubled_half_nibble".to_string(),
                convert([0i32, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7].to_vec())
            )
        );
    }

    #[test]
    fn arrays() {
        let src = r#"
            let N: int = 8;
            let n: fe = 10;
            namespace F(N);
            let f = |i| i  + 20;
            col fixed alt = [0, 1, 0, 1, 0, 1] + [0]*;
            col fixed empty = [] + [0]*;
            col fixed ref_other = [n-1, f(1), 8] + [0]*;
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 8);
        let constants = generate(&analyzed);
        assert_eq!(constants.len(), 3);
        assert_eq!(
            constants[0],
            (
                "F::alt".to_string(),
                convert([0i32, 1, 0, 1, 0, 1, 0, 0].to_vec())
            )
        );
        assert_eq!(
            constants[1],
            ("F::empty".to_string(), convert([0i32; 8].to_vec()))
        );
        assert_eq!(
            constants[2],
            (
                "F::ref_other".to_string(),
                convert([9i32, 21, 8, 0, 0, 0, 0, 0].to_vec())
            )
        );
    }

    #[test]
    fn repetition_front() {
        let src = r#"
            let N: int = 8;
            namespace F(N);
            col fixed arr = [0, 1, 2]* + [7];
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 8);
        let constants = generate(&analyzed);
        assert_eq!(constants.len(), 1);
        assert_eq!(
            constants[0],
            (
                "F::arr".to_string(),
                convert([0i32, 1, 2, 0, 1, 2, 0, 7].to_vec())
            )
        );
    }

    #[test]
    fn comparisons() {
        let src = r#"
            let N: int = 8;
            namespace std::convert(N);
            let int = 9;
            let fe = 8;
            namespace F(N);
            let id = |i| i;
            let inv = |i| N - i;
            let a: int -> int = |i| [0, 1, 0, 1, 2, 1, 1, 1][i];
            let b: int -> int = |i| [0, 0, 1, 1, 0, 5, 5, 5][i];
            col fixed or(i) { if (a(i) != 0) || (b(i) != 0) { 1_fe } else { 0_fe } };
            col fixed and(i) { if (a(i) != 0) && (b(i) != 0) { 1_fe } else { 0_fe } };
            col fixed not(i) { if !(a(i) != 0) { 1_fe } else { 0_fe } };
            col fixed less(i) { if id(i) < inv(i) { 1_fe } else { 0_fe } };
            col fixed less_eq(i) { if id(i) <= inv(i) { 1_fe } else { 0_fe } };
            col fixed eq(i) { if id(i) == inv(i) { 1_fe } else { 0_fe } };
            col fixed not_eq(i) { if id(i) != inv(i) { 1_fe } else { 0_fe } };
            col fixed greater(i) { if id(i) > inv(i) { 1_fe } else { 0_fe } };
            col fixed greater_eq(i) { if id(i) >= inv(i) { 1_fe } else { 0_fe } };
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 8);
        let constants = generate(&analyzed);
        assert_eq!(
            constants[0],
            (
                "F::or".to_string(),
                convert([0, 1, 1, 1, 1, 1, 1, 1].to_vec())
            )
        );
        assert_eq!(
            constants[1],
            (
                "F::and".to_string(),
                convert([0, 0, 0, 1, 0, 1, 1, 1].to_vec())
            )
        );
        assert_eq!(
            constants[2],
            (
                "F::not".to_string(),
                convert([1, 0, 1, 0, 0, 0, 0, 0].to_vec())
            )
        );
        assert_eq!(
            constants[3],
            (
                "F::less".to_string(),
                convert([1, 1, 1, 1, 0, 0, 0, 0].to_vec())
            )
        );
        assert_eq!(
            constants[4],
            (
                "F::less_eq".to_string(),
                convert([1, 1, 1, 1, 1, 0, 0, 0].to_vec())
            )
        );
        assert_eq!(
            constants[5],
            (
                "F::eq".to_string(),
                convert([0, 0, 0, 0, 1, 0, 0, 0].to_vec())
            )
        );
        assert_eq!(
            constants[6],
            (
                "F::not_eq".to_string(),
                convert([1, 1, 1, 1, 0, 1, 1, 1].to_vec())
            )
        );
        assert_eq!(
            constants[7],
            (
                "F::greater".to_string(),
                convert([0, 0, 0, 0, 0, 1, 1, 1].to_vec())
            )
        );
        assert_eq!(
            constants[8],
            (
                "F::greater_eq".to_string(),
                convert([0, 0, 0, 0, 1, 1, 1, 1].to_vec())
            )
        );
    }

    #[test]
    #[should_panic = "got `expr` when calling function F::w"]
    fn calling_witness() {
        let src = r#"
            let N: int = 10;
            namespace F(N);
            let w;
            let x: col = |i| w(i) + 1;
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 10);
        generate(&analyzed);
    }

    #[test]
    #[should_panic = "Value symbol not found: w"]
    fn symbol_not_found() {
        let src = r#"
            let N: int = 10;
            namespace F(N);
            let x = |i| w(i) + 1;
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 10);
        generate(&analyzed);
    }

    #[test]
    #[should_panic = "got `expr` when calling function F::y"]
    fn forward_reference_to_array() {
        let src = r#"
            let N: int = 10;
            namespace F(N);
            let x: col = |i| { let t = y(i) + 1; 1_fe };
            col fixed y = [1, 2, 3]*;
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 10);
        generate(&analyzed);
    }

    #[test]
    fn forward_reference_to_function() {
        let src = r#"
            let N: int = 4;
            namespace std::convert(N);
            let int = [];
            let fe = [];
            namespace F(N);
            let x: int -> fe = |i| std::convert::fe(y(i) + 1);
            let y: int -> fe = |i| std::convert::fe(i + 20);
            let X: col = x;
            let Y: col = y;
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 4);
        let constants = generate(&analyzed);
        assert_eq!(
            constants[0],
            ("F::X".to_string(), convert([21, 22, 23, 24].to_vec()))
        );
        assert_eq!(
            constants[1],
            ("F::Y".to_string(), convert([20, 21, 22, 23].to_vec()))
        );
    }

    #[test]
    fn bigint_arith() {
        let src = r#"
            let N: int = 4;
            namespace std::convert(N);
            let int = [];
            let fe = [];
            namespace F(N);
            let x: col = |i| std::convert::fe((1 << (2000 + i)) >> 2000);
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 4);
        let constants = generate(&analyzed);
        assert_eq!(
            constants[0],
            ("F::x".to_string(), convert([1, 2, 4, 8].to_vec()))
        );
    }

    #[test]
    fn modulo_negative() {
        let src = r#"
            let N: int = 4;
            namespace std::convert(N);
            let int = [];
            let fe = [];
            namespace F(N);
            let x_arr = [ 3 % 4, (-3) % 4, 3 % (-4), (-3) % (-4)];
            let x: col = |i| std::convert::fe(100 + x_arr[i]);
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 4);
        let constants = generate(&analyzed);
        // Semantics of p % q involving negative numbers:
        // sgn(p) * |p| % |q|
        assert_eq!(
            constants[0],
            ("F::x".to_string(), convert([103, 97, 103, 97].to_vec()))
        );
    }

    #[test]
    fn arrays_of_fixed() {
        let src = r#"
            namespace F(4);
                let x: fe -> (int -> fe) = |k| |i| std::convert::fe(i) + k;
                let y: col[2] = [x(0), x(1)];
            namespace std::convert(4);
                let fe = || fe();
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 4);
        let constants = generate(&analyzed);
        assert_eq!(
            constants[0],
            ("F::y[0]".to_string(), convert([0, 1, 2, 3].to_vec()))
        );
        assert_eq!(
            constants[1],
            ("F::y[1]".to_string(), convert([1, 2, 3, 4].to_vec()))
        );
    }

    #[test]
    fn generic_cache() {
        // Tests that the evaluation cache stores symbols with their
        // generic arguments.
        let src = r#"
            namespace std::convert(4);
                let fe = || fe();
            namespace F(4);
                let<T: FromLiteral> seven: T = 7;
                let a: col = |i| std::convert::fe(i + seven + 0_int) + seven;
        "#;
        let analyzed = analyze_string(src);
        assert_eq!(analyzed.degree(), 4);
        let constants = generate(&analyzed);
        assert_eq!(
            constants[0],
            ("F::a".to_string(), convert([14, 15, 16, 17].to_vec()))
        );
    }

    #[test]
    fn do_not_add_constraint_for_empty_tuple() {
        let input = r#"namespace N(4);
            let f: -> () = || ();
            let r: int -> fe = |i| {
                // This returns an empty tuple, we check that this does not lead to
                // a call to add_proof_items()
                f();
                7_fe
            };
            let g: col = r;
        "#;
        let analyzed = analyze_string(input);
        assert_eq!(analyzed.degree(), 4);
        let constants = generate(&analyzed);
        assert_eq!(
            constants[0],
            ("N::g".to_string(), convert([7, 7, 7, 7].to_vec()))
        );
    }
}

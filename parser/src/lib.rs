//! Parser for powdr assembly and PIL

#![deny(clippy::print_stdout)]

use lalrpop_util::*;
use powdr_ast::parsed::{
    asm::ASMProgram,
    types::{Type, TypeBounds, TypeScheme},
    Expression, SourceReference,
};
use powdr_parser_util::{handle_parse_error, Error, SourceRef};

use std::sync::Arc;

pub mod sugar;
pub mod test_utils;

lalrpop_mod!(
    #[allow(clippy::all)]
    #[allow(clippy::uninlined_format_args)]
    pub powdr,
    "/powdr.rs"
);

pub struct ParserContext {
    file_name: Option<Arc<str>>,
    file_contents: Option<Arc<str>>,
}

impl ParserContext {
    pub fn new(file_name: Option<&str>, input: &str) -> Self {
        Self {
            file_name: file_name.map(|s| s.into()),
            file_contents: Some(input.into()),
        }
    }

    pub fn source_ref(&self, start: usize, end: usize) -> SourceRef {
        SourceRef {
            file_name: self.file_name.clone(),
            file_contents: self.file_contents.clone(),
            start,
            end,
        }
    }

    pub fn to_expr_with_source_ref<T: Into<Expression>>(
        &self,
        inner_expr: T,
        start: usize,
        end: usize,
    ) -> Box<Expression> {
        let mut expr = inner_expr.into();
        *expr.source_reference_mut() = self.source_ref(start, end);
        Box::new(expr)
    }
}

lazy_static::lazy_static! {
    static ref PIL_FILE_PARSER: powdr::PILFileParser = powdr::PILFileParser::new();
    static ref ASM_MODULE_PARSER: powdr::ASMModuleParser = powdr::ASMModuleParser::new();
    static ref TYPE_PARSER: powdr::TypeExprParser = powdr::TypeExprParser::new();
    static ref TYPE_VAR_BOUNDS_PARSER: powdr::TypeVarBoundsParser = powdr::TypeVarBoundsParser::new();
}

pub fn parse(file_name: Option<&str>, input: &str) -> Result<powdr_ast::parsed::PILFile, Error> {
    let ctx = ParserContext::new(file_name, input);
    PIL_FILE_PARSER
        .parse(&ctx, input)
        .map_err(|err| handle_parse_error(err, file_name, input))
}

pub fn parse_asm(
    file_name: Option<&str>,
    input: &str,
) -> Result<powdr_ast::parsed::asm::ASMProgram, Error> {
    parse_module(file_name, input).map(|main| ASMProgram { main })
}

pub fn parse_module(
    file_name: Option<&str>,
    input: &str,
) -> Result<powdr_ast::parsed::asm::ASMModule, Error> {
    let ctx = ParserContext::new(file_name, input);
    ASM_MODULE_PARSER
        .parse(&ctx, input)
        .map_err(|err| handle_parse_error(err, file_name, input))
}

pub fn parse_type(input: &str) -> Result<Type<powdr_ast::parsed::Expression>, Error> {
    let ctx = ParserContext::new(None, input);
    TYPE_PARSER
        .parse(&ctx, input)
        .map_err(|err| handle_parse_error(err, None, input))
}

pub fn parse_type_var_bounds(input: &str) -> Result<TypeBounds, Error> {
    let ctx = ParserContext::new(None, input);
    // We use GoldilocksField here, because we need to specify a concrete type,
    // even though the grammar for TypeBounds does not depend on the field.
    TYPE_VAR_BOUNDS_PARSER
        .parse(&ctx, input)
        .map_err(|err| handle_parse_error(err, None, input))
}

pub fn parse_type_scheme(vars: &str, ty: &str) -> TypeScheme {
    let vars = parse_type_var_bounds(vars).unwrap();
    let mut ty = parse_type(ty).unwrap();
    ty.map_to_type_vars(&vars.vars().collect());
    TypeScheme {
        vars,
        ty: ty.into(),
    }
}

/// Parse an escaped string - used in the grammar.
pub fn unescape_string(s: &str) -> String {
    assert!(s.len() >= 2);
    assert!(s.starts_with('"') && s.ends_with('"'));
    let mut chars = s[1..s.len() - 1].chars();
    let mut result: String = Default::default();
    while let Some(c) = chars.next() {
        result.push(if c == '\\' {
            match chars.next().unwrap() {
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                'b' => 8 as char,
                'f' => 12 as char,
                other => other,
            }
        } else {
            c
        })
    }
    result
}

#[cfg(test)]
mod test {
    use super::*;
    use powdr_ast::parsed::{
        build::direct_reference, ArrayLiteral, PILFile, PilStatement, PolynomialName,
        SelectedExpressions,
    };
    use powdr_parser_util::UnwrapErrToStderr;
    use pretty_assertions::assert_eq;
    use similar::TextDiff;
    use test_log::test;
    use test_utils::ClearSourceRefs;
    use walkdir::WalkDir;

    #[test]
    fn empty() {
        let input = "";
        let ctx = ParserContext::new(None, input);
        assert!(powdr::PILFileParser::new().parse(&ctx, input).is_ok());
    }

    #[test]
    fn simple_include() {
        let input = "include \"x\";";
        let ctx = ParserContext::new(None, input);
        let parsed = powdr::PILFileParser::new().parse(&ctx, input).unwrap();
        assert_eq!(
            parsed,
            PILFile(vec![PilStatement::Include(
                SourceRef {
                    file_name: None,
                    file_contents: Some(input.into()),
                    start: 0,
                    end: 11,
                },
                "x".to_string()
            )])
        );
    }

    #[test]
    fn start_offsets() {
        let input = "include \"x\"; pol commit t;";
        let ctx = ParserContext::new(None, input);
        let parsed = powdr::PILFileParser::new().parse(&ctx, input).unwrap();
        assert_eq!(
            parsed,
            PILFile(vec![
                PilStatement::Include(
                    SourceRef {
                        file_name: None,
                        file_contents: Some(input.into()),
                        start: 0,
                        end: 11,
                    },
                    "x".to_string()
                ),
                PilStatement::PolynomialCommitDeclaration(
                    SourceRef {
                        file_name: None,
                        file_contents: Some(input.into()),
                        start: 13,
                        end: 25,
                    },
                    None,
                    vec![PolynomialName {
                        name: "t".to_string(),
                        array_size: None
                    }],
                    None
                )
            ])
        );
    }

    #[test]
    fn simple_plookup() {
        let input = "[f] in [g];";
        let ctx = ParserContext::new(None, input);
        let parsed = powdr::PILFileParser::new()
            .parse(&ctx, "[f] in [g];")
            .unwrap();
        assert_eq!(
            parsed,
            PILFile(vec![PilStatement::PlookupIdentity(
                SourceRef {
                    file_name: None,
                    file_contents: Some(input.into()),
                    start: 0,
                    end: 10,
                },
                SelectedExpressions {
                    selector: None,
                    expressions: Box::new(
                        ArrayLiteral {
                            items: vec![direct_reference("f")]
                        }
                        .into()
                    )
                },
                SelectedExpressions {
                    selector: None,
                    expressions: Box::new(
                        ArrayLiteral {
                            items: vec![direct_reference("g")]
                        }
                        .into()
                    )
                }
            )])
        );
    }

    fn find_files_with_ext(
        dir: std::path::PathBuf,
        ext: String,
    ) -> impl Iterator<Item = (String, String)> {
        WalkDir::new(dir).into_iter().filter_map(move |e| {
            let entry = e.unwrap();
            let path = entry.path();
            match path.extension() {
                Some(path_ext) if path_ext.to_str() == Some(&ext) => Some((
                    std::fs::canonicalize(path)
                        .unwrap()
                        .to_str()
                        .unwrap()
                        .into(),
                    std::fs::read_to_string(path).unwrap(),
                )),
                _ => None,
            }
        })
    }

    #[test]
    /// Test that (source -> AST -> source -> AST) works properly for asm files
    fn parse_write_reparse_asm() {
        let crate_dir = env!("CARGO_MANIFEST_DIR");
        let basedir = std::path::PathBuf::from(format!("{crate_dir}/../test_data/"));
        let asm_files = find_files_with_ext(basedir, "asm".into());
        for (file, orig_string) in asm_files {
            let mut orig_asm = parse_asm(Some(&file), &orig_string).unwrap_err_to_stderr();
            let orig_asm_to_string = format!("{orig_asm}");
            let mut reparsed_asm = parse_asm(
                Some((file.clone() + " reparsed").as_ref()),
                &orig_asm_to_string,
            )
            .unwrap_err_to_stderr();
            orig_asm.clear_source_refs();
            reparsed_asm.clear_source_refs();
            if orig_asm != reparsed_asm {
                let orig_ast = format!("{orig_asm:#?}");
                let reparsed_ast = format!("{reparsed_asm:#?}");
                let diff = TextDiff::from_lines(&orig_ast, &reparsed_ast);
                eprintln!("parsed and re-parsed ASTs differ:");
                for change in diff.iter_all_changes() {
                    let sign = match change.tag() {
                        similar::ChangeTag::Delete => "-",
                        similar::ChangeTag::Insert => "+",
                        similar::ChangeTag::Equal => " ",
                    };
                    eprint!("\t{sign}{change}");
                }
                panic!("parsed and re-parsed ASTs differ for file: {file}");
            }
        }
    }

    #[test]
    /// Test that (source -> AST -> source -> AST) works properly for pil files
    fn parse_write_reparse_pil() {
        use test_utils::ClearSourceRefs;
        let crate_dir = env!("CARGO_MANIFEST_DIR");
        let basedir = std::path::PathBuf::from(format!("{crate_dir}/../test_data/"));
        let pil_files = find_files_with_ext(basedir, "pil".into());
        for (file, orig_string) in pil_files {
            let mut orig_pil = parse(Some(&file), &orig_string).unwrap_err_to_stderr();
            let orig_pil_to_string = format!("{orig_pil}");
            let mut reparsed_pil = parse(
                Some((file.clone() + " reparsed").as_ref()),
                &orig_pil_to_string,
            )
            .unwrap_err_to_stderr();
            orig_pil.clear_source_refs();
            reparsed_pil.clear_source_refs();
            assert_eq!(orig_pil, reparsed_pil);
            if orig_pil != reparsed_pil {
                let orig_ast = format!("{orig_pil:#?}");
                let reparsed_ast = format!("{reparsed_pil:#?}");
                let diff = TextDiff::from_lines(&orig_ast, &reparsed_ast);
                eprintln!("parsed and re-parsed ASTs differ:");
                for change in diff.iter_all_changes() {
                    let sign = match change.tag() {
                        similar::ChangeTag::Delete => "-",
                        similar::ChangeTag::Insert => "+",
                        similar::ChangeTag::Equal => " ",
                    };
                    eprint!("\t{sign}{change}");
                }
                panic!("parsed and re-parsed ASTs differ for file: {file}");
            }
        }
    }

    use crate::parse;

    #[test]
    fn reparse() {
        let input = r#"
    let N: int = 16;
namespace Fibonacci(N);
    let last_row = N - 1;
    let bool: expr -> expr = (|X| X * (1 - X));
    let one_hot = (|i, which| match i {
        which => 1,
        _ => 0,
    });
    pol constant ISLAST(i) { one_hot(i, %last_row) };
    pol commit arr[8];
    pol commit x, y;
    [x + 2, y'] in [ISLAST, 7];
    y $ [x + 2, y'] is ISLAST $ [ISLAST, 7];
    (x - 2) * y = 8;
    public out = y(%last_row);"#;
        let printed = format!("{}", parse(Some("input"), input).unwrap());
        assert_eq!(input.trim(), printed.trim());
    }

    #[test]
    fn reparse_witness_query() {
        let input = r#"pol commit wit(i) query (x(i), y(i));"#;
        let printed = format!("{}", parse(Some("input"), input).unwrap());
        assert_eq!(input.trim(), printed.trim());
    }

    #[test]
    fn reparse_arrays() {
        let input =
            "    pol commit y[3];\n    y - 2 = 0;\n    y[2] - 2 = 0;\n    public out = y[1](2);";
        let printed = format!("{}", parse(Some("input"), input).unwrap());
        assert_eq!(input.trim(), printed.trim());
    }

    #[test]
    fn reparse_strings_and_tuples() {
        let input = r#"let N = ("abc", 3);"#;
        let printed = format!("{}", parse(Some("input"), input).unwrap());
        assert_eq!(input.trim(), printed.trim());
    }

    #[test]
    fn array_literals() {
        let input = r#"let x = [[1], [2], [3 + 7]];"#;
        let printed = format!("{}", parse(Some("input"), input).unwrap_err_to_stderr());
        assert_eq!(input.trim(), printed.trim());
    }

    #[test]
    fn type_names_simple() {
        let input = r#"
    let a: col;
    let b: int;
    let c: fe;
    let d: int[];
    let e: int[7];
    let f: (int, fe, fe[3])[2];"#;
        let printed = format!("{}", parse(Some("input"), input).unwrap());
        assert_eq!(input.trim(), printed.trim());
    }

    #[test]
    fn type_names_complex() {
        let input = r#"
    let a: int -> fe;
    let b: int -> ();
    let c: -> ();
    let d: int, int -> fe;
    let e: int, int -> (fe, int[2]);
    let f: ((int, fe), fe[2] -> (fe -> int))[];
    let g: (int -> fe) -> int;
    let h: int -> (fe -> int);"#;
        let printed = format!("{}", parse(Some("input"), input).unwrap());
        assert_eq!(input.trim(), printed.trim());
    }

    #[test]
    fn enum_decls() {
        let input = r#"
namespace N(2);
    enum X {
    }
    enum Y {
        A,
        B(),
        C(int),
        D(int, (int -> fe)),
    }
"#;
        let printed = format!("{}", parse(Some("input"), input).unwrap());
        assert_eq!(input.trim(), printed.trim());
    }

    #[test]
    fn patterns() {
        let input = r#"
namespace N(2);
    let x = (|(x, y), [t, r, ..]| (x, y, t, r));
    {
        let (a, b, _, d) = x((1, 2), [3, 4]);
        b
    };
"#;
        let printed = format!("{}", parse(Some("input"), input).unwrap_err_to_stderr());
        assert_eq!(input.trim(), printed.trim());
    }

    #[test]
    fn type_args() {
        let input = r#"
namespace N(2);
    let<T: Ord> max: T, T -> T = (|a, b| if a < b { b } else { a });
    let<T1, T2> left: T1, T2 -> T1 = (|a, b| a);
    let seven = max::<int>(3, 7);
    let five = left::<int, fe[]>(5, [7]);
    let also_five = five::<>;
"#;
        let printed = format!("{}", parse(Some("input"), input).unwrap_err_to_stderr());
        assert_eq!(input.trim(), printed.trim());
    }

    #[test]
    fn type_args_with_space() {
        let input = r#"
namespace N(2);
    let<T: Ord> max: T, T -> T = (|a, b| if a < b { b } else { a });
    let seven = max :: <int>(3, 7);
"#;
        let expected = r#"
namespace N(2);
    let<T: Ord> max: T, T -> T = (|a, b| if a < b { b } else { a });
    let seven = max::<int>(3, 7);
"#;
        let printed = format!("{}", parse(Some("input"), input).unwrap_err_to_stderr());
        assert_eq!(expected.trim(), printed.trim());
    }

    #[test]
    fn parse_impl() {
        let input = r#"
    impl<T> Iterator<ArrayIterator<T>, T> {
        next: |it| if it.pos >= 7 { (it, none) } else { some((increment(it), it.arr[it.pos])) },
    }"#;

        let expected = r#"
    impl<T> Iterator<ArrayIterator<T>, T> {
        next: (|it| if it.pos >= 7 { (it, none) } else { some((increment(it), it.arr[it.pos])) }),
    }"#;

        let printed = format!("{}", parse(Some("input"), input).unwrap_err_to_stderr());
        assert_eq!(expected.trim(), printed.trim());
    }

    #[test]
    fn parse_impl2() {
        let input = r#"
    impl<A, B> Iterator<ArrayIterator<A>, B> {
        next: |it| if it.pos >= 7 { (it, it.pos) } else { (it, 0) },
    }"#;

        let expected = r#"
    impl<A, B> Iterator<ArrayIterator<A>, B> {
        next: (|it| if it.pos >= 7 { (it, it.pos) } else { (it, 0) }),
    }"#;

        let printed = format!("{}", parse(Some("input"), input).unwrap_err_to_stderr());
        assert_eq!(expected.trim(), printed.trim());
    }

    #[test]
    fn parse_trait() {
        let input = r#"
    trait Add<T> {
        add: T, T -> T,
    }"#;

        let expected = r#"
    trait Add<T> {
        add: T, T -> T,
    }"#;

        let printed = format!("{}", parse(Some("input"), input).unwrap_err_to_stderr());
        assert_eq!(expected.trim(), printed.trim());
    }

    #[test]
    fn parse_trait_multi_params() {
        let input = r#"
    trait Add<T, Q> {
        add: T, T -> Q,
    }"#;

        let expected = r#"
    trait Add<T, Q> {
        add: T, T -> Q,
    }"#;

        let printed = format!("{}", parse(Some("input"), input).unwrap_err_to_stderr());
        assert_eq!(expected.trim(), printed.trim());
    }

    #[test]
    #[should_panic = "Parse error"]
    fn parse_trait_no_type_vars() {
        let input = r#"
    trait Add {
        add: int, int -> int,
    }"#;

        let _ = format!("{}", parse(Some("input"), input).unwrap_err_to_stderr());
    }

    #[test]
    fn parse_trait_multi_params2() {
        let input = r#"
    trait Iterator<S, I> {
        next: S -> (S, Option<I>),
    }"#;

        let expected = r#"
    trait Iterator<S, I> {
        next: S -> (S, Option<I>),
    }"#;

        let printed = format!("{}", parse(Some("input"), input).unwrap_err_to_stderr());
        assert_eq!(expected.trim(), printed.trim());
    }

    #[test]
    fn empty_namespace() {
        let input = r#"
namespace(2);
    let x = 2;
namespace;
    let y = 4;
namespace N(8);
    let z = 8;
"#;
        let expected = r#"
namespace (2);
    let x = 2;
namespace;
    let y = 4;
namespace N(8);
    let z = 8;
"#;
        let printed = format!("{}", parse(Some("input"), input).unwrap_err_to_stderr());
        assert_eq!(expected.trim(), printed.trim());
    }
}

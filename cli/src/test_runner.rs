use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    str::FromStr,
};

use itertools::Itertools;

use powdr::ast::{
    analyzed::FunctionValueDefinition,
    parsed::{
        asm::SymbolPath,
        types::{FunctionType, Type},
    },
};
use powdr::pil_analyzer::evaluator::{self, SymbolLookup};
use powdr::{FieldElement, Pipeline};

/// Executes all functions in the given file that start with `test_` and are
/// inside a module called `test`.
///
/// @param include_std_tests: Whether to run the tests inside the standard library.
pub fn run<F: FieldElement>(input: &str, include_std_tests: bool) -> Result<(), Vec<String>> {
    let mut pipeline = Pipeline::<F>::default().from_file(PathBuf::from(&input));

    let analyzed = pipeline.compute_analyzed_pil()?;

    let mut symbols = evaluator::Definitions {
        definitions: &analyzed.definitions,
        solved_impls: &analyzed.solved_impls,
    };

    let mut errors = vec![];
    let tests: BTreeSet<&String> = analyzed
        .definitions
        .iter()
        .filter(|(n, _)| n.starts_with("test::test_") || n.contains("::test::test_"))
        .filter(|(n, _)| include_std_tests || !n.starts_with("std::"))
        .filter(|(n, _)| SymbolPath::from_str(n).unwrap().name().starts_with("test_"))
        .sorted_by_key(|(n, _)| *n)
        .filter_map(|(n, (_, val))| {
            let Some(FunctionValueDefinition::Expression(f)) = val else {
                return None;
            };
            // Require a plain `->()` type.
            (f.type_scheme.as_ref().unwrap().ty
                == (FunctionType {
                    params: vec![],
                    value: Box::new(Type::empty_tuple()),
                })
                .into())
            .then_some(n)
        })
        .collect();
    println!("Running {} tests...", tests.len());
    println!("{}", "-".repeat(85));
    for name in &tests {
        let name_len = name.len();
        let padding = if name_len >= 75 {
            " ".to_string()
        } else {
            " ".repeat(76 - name_len)
        };
        print!("{name}...");
        let function = symbols.lookup(name, &None).unwrap();
        match evaluator::evaluate_function_call::<F>(function, vec![], &mut symbols) {
            Err(e) => {
                let msg = e.to_string();
                println!("{padding}failed\n  {msg}");
                errors.push((name, msg));
            }
            Ok(_) => println!("{padding}ok"),
        }
    }

    println!("{}", "-".repeat(85));
    if errors.is_empty() {
        println!("All {} tests passed!", tests.len());
        Ok(())
    } else {
        println!(
            "Failed tests: {} / {}\n{}",
            errors.len(),
            tests.len(),
            errors.iter().map(|(n, e)| format!("  {n}: {e}")).join("\n")
        );
        Err(vec![format!("{} test(s) failed.", errors.len())])
    }
}

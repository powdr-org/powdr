use std::{
    collections::{HashMap, HashSet},
    vec,
};

use powdr_ast::parsed::{
    types::{ArrayType, TupleType, Type},
    Pattern,
};
use powdr_number::BigInt;

#[derive(Debug)]
pub struct MatchAnalysisReport {
    pub is_exhaustive: bool,
    pub redundant_patterns: Vec<usize>,
}
#[derive(Debug, Clone)]
enum PatternSpace {
    Any,
    Contained(Vec<PatternSpace>, bool), // ellipsis and variable-size array not implemented
    Finite(FinitePatternSpace),
    Infinite(InfinitePatternSpace, bool),
}

#[derive(Debug, Clone, PartialEq)]
enum FinitePatternSpace {
    Enum(HashMap<String, Option<Vec<PatternSpace>>>),
    //Bool(Option<bool>),
}

#[derive(Debug, Clone, PartialEq)]
enum InfinitePatternSpace {
    String(HashSet<String>),
    Number(HashSet<BigInt>),
}

impl PartialEq for PatternSpace {
    /// Checks if two PatternSpace instances are equal.
    /// PatternSpace::Any always returns false when compared with any other PatternSpace.
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Contained(a, b1), Self::Contained(c, b2)) => b1 == b2 && a == c,
            (Self::Finite(a), Self::Finite(b)) => a == b,
            (Self::Infinite(a, f1), Self::Infinite(b, f2)) => a == b && f1 == f2,
            _ => false,
        }
    }
}

type EnumDefinitions<'a> = HashMap<&'a str, Vec<(&'a str, Option<Vec<Type>>)>>;

impl PatternSpace {
    /// Subtracts the given pattern from the current pattern space, returning a new pattern space.
    fn substract(&self, other: &Pattern) -> Self {
        match (self, other) {
            (p, Pattern::CatchAll(_)) | (p, Pattern::Variable(_, _)) => p.cover_all_space(),
            (PatternSpace::Any, _) => self.clone(),
            (PatternSpace::Contained(ps, b), Pattern::Array(_, items))
            | (PatternSpace::Contained(ps, b), Pattern::Tuple(_, items)) => {
                let new_ps = ps.iter().zip(items).map(|(p, o)| p.substract(o)).collect();
                PatternSpace::Contained(new_ps, *b)
            }
            (
                PatternSpace::Finite(FinitePatternSpace::Enum(enums)),
                Pattern::Enum(_, symbol, variants),
            ) => {
                let result = enums
                    .iter()
                    .filter_map(|(name, inner)| {
                        if name == &symbol.to_string() {
                            match (inner, variants) {
                                (None, None) => None,
                                (Some(inner_spaces), Some(variant_patterns)) => {
                                    let subtracted: Vec<_> = inner_spaces
                                        .iter()
                                        .zip(variant_patterns)
                                        .map(|(space, pattern)| space.substract(pattern))
                                        .collect();
                                    if !subtracted.is_empty() {
                                        // TODO remove
                                        Some((name.clone(), Some(subtracted)))
                                    } else {
                                        None
                                    }
                                }
                                (Some(_), None) | (None, Some(_)) => unreachable!(),
                            }
                        } else {
                            Some((name.clone(), inner.clone()))
                        }
                    })
                    .collect();
                PatternSpace::Finite(FinitePatternSpace::Enum(result))
            }
            (
                PatternSpace::Infinite(InfinitePatternSpace::String(strings), full),
                Pattern::String(_, o_string),
            ) => {
                if *full {
                    self.clone()
                } else {
                    let mut new_strings = strings.clone(); // TODO Improve this
                    new_strings.insert(o_string.to_string());
                    PatternSpace::Infinite(InfinitePatternSpace::String(new_strings), *full)
                }
            }
            (
                PatternSpace::Infinite(InfinitePatternSpace::Number(numbers), full),
                Pattern::Number(_, o_number),
            ) => {
                if *full {
                    self.clone()
                } else {
                    let mut new_numbers = numbers.clone(); // TODO Improve this
                    new_numbers.insert(o_number.clone());
                    PatternSpace::Infinite(InfinitePatternSpace::Number(new_numbers), *full)
                }
            }
            (p1, p2) => {
                panic!("Cannot substract {p2:?} from {p1:?}");
            }
        }
    }

    /// Compute the union of two pattern spaces.
    fn union(self, other: &Self) -> Self {
        match (self, other) {
            (p, PatternSpace::Any) => p,
            (PatternSpace::Any, p) => p.clone(),
            (PatternSpace::Contained(ps, f1), PatternSpace::Contained(os, f2)) => {
                let mut new_ps = Vec::new();
                for (o, p) in os.iter().zip(ps.iter()) {
                    new_ps.push(p.clone().union(o));
                }

                PatternSpace::Contained(new_ps, f1 || *f2)
            }
            (
                PatternSpace::Infinite(InfinitePatternSpace::Number(ns), full1),
                PatternSpace::Infinite(InfinitePatternSpace::Number(ns2), full2),
            ) => {
                let new_ns: HashSet<_> = ns.union(ns2).cloned().collect();
                PatternSpace::Infinite(InfinitePatternSpace::Number(new_ns), full1 || *full2)
            }
            (
                PatternSpace::Infinite(InfinitePatternSpace::String(ss), full1),
                PatternSpace::Infinite(InfinitePatternSpace::String(ss2), full2),
            ) => {
                let new_ss = ss.union(ss2).cloned().collect(); // TODO More clone/collect
                PatternSpace::Infinite(InfinitePatternSpace::String(new_ss), full1 || *full2)
            }
            (s, _) => s.clone(), // enums are already merged
        }
    }

    /// Returns true if the pattern space is fully covered.
    fn all_covered(&self) -> bool {
        match self {
            PatternSpace::Any => false,
            PatternSpace::Infinite(_, covered) => *covered,
            PatternSpace::Finite(FinitePatternSpace::Enum(variants)) => {
                variants.is_empty()
                    || variants.iter().all(|(_, inner_space)| {
                        inner_space.as_ref().map_or(true, |spaces| {
                            spaces.iter().all(|space| space.all_covered())
                        })
                    })
            }
            PatternSpace::Contained(items, covered) => {
                *covered || items.iter().all(|item| item.all_covered())
            }
        }
    }

    /// Returns a new version of the pattern space with all the values covered.
    fn cover_all_space(&self) -> Self {
        match self {
            PatternSpace::Infinite(infinite, _) => PatternSpace::Infinite(infinite.clone(), true),

            PatternSpace::Finite(FinitePatternSpace::Enum(variants)) => {
                let mut new_variants = HashMap::new();
                for (name, inner_space) in variants.iter() {
                    let covered_inner_space = inner_space
                        .as_ref()
                        .map(|spaces| spaces.iter().map(|space| space.cover_all_space()).collect());
                    new_variants.insert(name.clone(), covered_inner_space);
                }
                PatternSpace::Finite(FinitePatternSpace::Enum(new_variants))
            }
            PatternSpace::Contained(spaces, b) => {
                let processed_spaces: Vec<PatternSpace> =
                    spaces.iter().map(|space| space.cover_all_space()).collect();
                PatternSpace::Contained(processed_spaces, *b)
            }
            _ => self.clone(),
        }
    }
}

/// Analyzes a list of match patterns for exhaustiveness and redundancy.
///
/// This function takes a slice of patterns and a map of enum definitions,
/// and determines whether the patterns cover all possible cases (exhaustiveness)
/// and if any patterns are unnecessary (redundancy).
///
/// It works by computing a representation of the covered pattern space
/// and then analyzing how each pattern affects this space.
///
/// The function returns a report containing:
/// - Whether the patterns are exhaustive (cover all possible cases)
/// - A list of indices of redundant patterns (if any)
pub fn analyze_match_patterns(
    patterns: &[Pattern],
    enums: &EnumDefinitions,
) -> MatchAnalysisReport {
    let mut redundant_patterns = Vec::new();
    let mut needed_patterns = Vec::new();
    let patterns = solve_ellipsis(patterns);

    let mut covered_space = compute_covered_space(&patterns, enums);
    for (pattern_index, pattern) in patterns.iter().enumerate() {
        let substracted_space = covered_space.substract(pattern);
        if substracted_space == covered_space {
            println!("Iguales: {:?} {:?}", covered_space, substracted_space);
            redundant_patterns.push(pattern_index);
        } else {
            println!("Desiguales: {:?} {:?}", covered_space, substracted_space);
            needed_patterns.push(pattern);
            covered_space = substracted_space;
        }

        if covered_space.all_covered() {
            // Add all remaining patterns as redundant
            redundant_patterns.extend((pattern_index + 1)..patterns.len());
            break;
        }
    }

    MatchAnalysisReport {
        is_exhaustive: covered_space.all_covered(),
        redundant_patterns,
    }
}

fn solve_ellipsis(patterns: &[Pattern]) -> Vec<Pattern> {
    let (max_size, has_ellipsis) =
        patterns
            .iter()
            .fold((0, false), |(max_size, has_ellipsis), p| match p {
                Pattern::Array(_, items) => {
                    let size = items.len();
                    let contains_ellipsis = items
                        .iter()
                        .any(|item| matches!(item, Pattern::Ellipsis(_)));
                    (max_size.max(size), has_ellipsis || contains_ellipsis)
                }
                _ => (max_size, has_ellipsis),
            });

    if max_size == 0 || !has_ellipsis {
        return patterns.to_vec();
    }

    let mut new_patterns = vec![];
    for p in patterns {
        let new_p = match p {
            Pattern::Array(sr, items) => {
                let items = expand_ellipsis(items, max_size);
                Pattern::Array(sr.clone(), items)
            }
            _ => p.clone(),
        };
        new_patterns.push(new_p);
    }

    new_patterns
}

fn expand_ellipsis(items: &[Pattern], max_size: usize) -> Vec<Pattern> {
    let mut new_items = Vec::new();
    let mut ellipsis_found = false;

    for (i, item) in items.iter().enumerate() {
        match item {
            Pattern::Ellipsis(sr) => {
                if ellipsis_found {
                    panic!("Multiple ellipsis patterns are not supported"); // TODO: Report error (if is not already cached before)
                }
                ellipsis_found = true;

                // Calculate remaining items after ellipsis
                let remaining_items = items.len() - (i + 1);
                // Calculate how many CatchAll patterns we need
                let catchall_count = max_size - (new_items.len() + remaining_items);

                // Add the required CatchAll patterns
                for _ in 0..catchall_count {
                    new_items.push(Pattern::CatchAll(sr.clone()));
                }
            }
            p => {
                new_items.push(p.clone());
            }
        }
    }

    new_items
}

/// Computes the PatternSpace representing the coverage of a given list of patterns.
///
/// This function takes a slice of patterns and a reference to enum definitions,
/// and calculates the total space covered by these patterns. It does this by:
/// 1. Creating a PatternSpace for each individual pattern
/// 2. Expanding these spaces (based on the provided enum definitions, if needed)
/// 3. Combining all expanded spaces into a single PatternSpace using union operations
fn compute_covered_space(patterns: &[Pattern], enums: &EnumDefinitions) -> PatternSpace {
    patterns
        .iter()
        .map(create_pattern_space)
        .flat_map(|processed| expand_pattern_space(processed, enums))
        .fold(PatternSpace::Any, |acc, space| acc.union(&space))
}

// Creates a PatternSpace for a given pattern.
fn create_pattern_space(pattern: &Pattern) -> PatternSpace {
    match pattern {
        Pattern::CatchAll(_) => PatternSpace::Any,
        Pattern::Ellipsis(_) => unreachable!(),
        Pattern::Number(_, _) => {
            PatternSpace::Infinite(InfinitePatternSpace::Number(HashSet::new()), false)
        }
        Pattern::String(_, _) => {
            PatternSpace::Infinite(InfinitePatternSpace::String(HashSet::new()), false)
        }
        Pattern::Variable(_, _) => PatternSpace::Any,
        Pattern::Tuple(_, p) => {
            let full = p
                .iter()
                .all(|pattern| matches!(pattern, Pattern::CatchAll(_) | Pattern::Variable(_, _)));
            let inner_space = p.iter().map(create_pattern_space).collect();
            PatternSpace::Contained(inner_space, full)
        }
        Pattern::Array(_, p) => {
            let full = p
                .iter()
                .all(|pattern| matches!(pattern, Pattern::CatchAll(_) | Pattern::Variable(_, _)));
            let inner_space = p.iter().map(create_pattern_space).collect();
            PatternSpace::Contained(inner_space, full)
        }
        Pattern::Enum(_, name, fields) => {
            let inner_space = fields
                .as_ref()
                .map(|patterns| patterns.iter().map(create_pattern_space).collect());
            PatternSpace::Finite(FinitePatternSpace::Enum(HashMap::from_iter(vec![(
                name.to_string(),
                inner_space,
            )])))
        }
    }
}

// Expands a pattern to cover all its variations.
fn expand_pattern_space(pattern: PatternSpace, enums: &EnumDefinitions) -> Vec<PatternSpace> {
    let vec = match pattern {
        PatternSpace::Contained(inner, full) => {
            // TODO: Check if when full is true, we can avoid expansion
            let mut expanded_enums = Vec::new();
            for inner_space in inner {
                let expanded = expand_pattern_space(inner_space, enums);
                expanded_enums.push(expanded);
            }
            let product = cartesian_product(expanded_enums);

            product
                .iter()
                .map(|p| PatternSpace::Contained(p.to_vec(), full))
                .collect()
        }
        PatternSpace::Finite(FinitePatternSpace::Enum(variants)) => {
            let (enum_name, _) = variants.keys().next().unwrap().rsplit_once("::").unwrap();
            let expanded_variants = enums
                .get(enum_name)
                .unwrap()
                .iter()
                .map(|(variant_name, types)| {
                    let processed_ty = process_variant_type(types, enums);
                    match processed_ty {
                        Some(spaces) => {
                            let expanded = spaces
                                .into_iter()
                                .flat_map(|space| expand_pattern_space(space, enums))
                                .collect::<Vec<_>>();

                            (format!("{enum_name}::{variant_name}"), Some(expanded))
                        }
                        None => (format!("{enum_name}::{variant_name}"), None),
                    }
                })
                .collect();

            vec![PatternSpace::Finite(FinitePatternSpace::Enum(
                expanded_variants,
            ))]
        }
        PatternSpace::Infinite(_, _) | PatternSpace::Any => vec![pattern],
    };

    vec
}

// Processes an enum variant type to generate its pattern space.
fn process_variant_type(
    variant: &Option<Vec<Type>>,
    enums: &EnumDefinitions,
) -> Option<Vec<PatternSpace>> {
    match variant {
        None => None,
        Some(types) => {
            let mut pattern_space = Vec::with_capacity(types.len());
            for ty in types {
                let new_pattern = match ty {
                    Type::Bottom
                    | Type::Col
                    | Type::Expr
                    | Type::Function(_)
                    | Type::Inter
                    | Type::Bool => {
                        unreachable!()
                    }
                    Type::Int | Type::Fe => {
                        PatternSpace::Infinite(InfinitePatternSpace::Number(HashSet::new()), false)
                    }
                    Type::String => {
                        PatternSpace::Infinite(InfinitePatternSpace::String(HashSet::new()), false)
                    }
                    Type::Array(ArrayType { base, length }) => {
                        let items = match length {
                            Some(length) => {
                                vec![base.as_ref().clone(); *length as usize]
                            }
                            None => {
                                vec![base.as_ref().clone()]
                            }
                        };

                        let expanded = process_variant_type(&Some(items), enums)?;
                        PatternSpace::Contained(expanded, false)
                    }
                    Type::Tuple(TupleType { items }) => {
                        let expanded = process_variant_type(&Some(items.to_vec()), enums)?;
                        PatternSpace::Contained(expanded, false)
                    }
                    Type::TypeVar(_) => PatternSpace::Any,
                    Type::NamedType(name, vars) => {
                        let single_enum = match vars {
                            None => PatternSpace::Finite(FinitePatternSpace::Enum(
                                HashMap::from_iter(vec![(name.to_string(), None)]),
                            )),
                            Some(_) => {
                                let new_vars = process_variant_type(vars, enums);
                                PatternSpace::Finite(FinitePatternSpace::Enum(HashMap::from_iter(
                                    vec![(name.to_string(), new_vars)],
                                )))
                            }
                        };

                        let expanded = expand_pattern_space(single_enum, enums);
                        expanded[0].clone()
                    }
                };

                pattern_space.push(new_pattern);
            }

            Some(pattern_space)
        }
    }
}

fn cartesian_product(patterns: Vec<Vec<PatternSpace>>) -> Vec<Vec<PatternSpace>> {
    patterns.into_iter().fold(vec![vec![]], |acc, patterns| {
        acc.into_iter()
            .flat_map(|v| {
                patterns.iter().map(move |p| {
                    let mut new_v = v.clone();
                    new_v.push(p.clone());
                    new_v
                })
            })
            .collect()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use powdr_ast::parsed::asm::{Part, SymbolPath};
    use powdr_parser_util::SourceRef;

    #[test]
    fn test_basic_match_analysis() {
        let patterns = vec![
            Pattern::String(SourceRef::unknown(), "A".to_string()),
            Pattern::String(SourceRef::unknown(), "B".to_string()),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(!report.is_exhaustive);
        assert!(report.redundant_patterns.is_empty());
    }

    #[test]
    fn test_match_analysis_repeated_pattern() {
        let patterns = vec![
            Pattern::String(SourceRef::unknown(), "A".to_string()),
            Pattern::String(SourceRef::unknown(), "A".to_string()),
            Pattern::String(SourceRef::unknown(), "A".to_string()),
        ];

        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(!report.is_exhaustive);
        assert_eq!(report.redundant_patterns, vec![1, 2]);
    }

    #[test]
    fn test_match_analysis_repeated_pattern_mixed() {
        let patterns = vec![
            Pattern::String(SourceRef::unknown(), "A".to_string()),
            Pattern::String(SourceRef::unknown(), "B".to_string()),
            Pattern::String(SourceRef::unknown(), "B".to_string()),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(!report.is_exhaustive);
        assert_eq!(report.redundant_patterns, vec![2]);
    }

    #[test]
    fn test_match_analysis_exhaustive_patterns() {
        let patterns = vec![
            Pattern::String(SourceRef::unknown(), "A".to_string()),
            Pattern::String(SourceRef::unknown(), "A".to_string()),
            Pattern::CatchAll(SourceRef::unknown()),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(report.is_exhaustive);
        assert_eq!(report.redundant_patterns, vec![1]);
    }

    #[test]
    fn test_match_analysis_tuples() {
        let patterns = vec![
            Pattern::Tuple(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ],
            ),
            Pattern::Tuple(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 9.into()),
                    Pattern::Number(SourceRef::unknown(), 8.into()),
                ],
            ),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(!report.is_exhaustive);
        assert!(report.redundant_patterns.is_empty());
    }

    #[test]
    fn test_match_analysis_catchall_array() {
        let patterns = vec![
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::CatchAll(SourceRef::unknown()),
                    Pattern::CatchAll(SourceRef::unknown()),
                ],
            ),
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 9.into()),
                    Pattern::Number(SourceRef::unknown(), 8.into()),
                ],
            ),
        ];

        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(report.is_exhaustive);
        assert_eq!(report.redundant_patterns, vec![1]);
    }

    #[test]
    fn test_match_analysis_double_catchall_array() {
        let patterns = vec![
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::CatchAll(SourceRef::unknown()),
                    Pattern::CatchAll(SourceRef::unknown()),
                ],
            ),
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::CatchAll(SourceRef::unknown()),
                    Pattern::CatchAll(SourceRef::unknown()),
                ],
            ),
        ];

        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(report.is_exhaustive);
        assert_eq!(report.redundant_patterns, vec![1]);
    }

    #[test]
    fn test_match_analysis_tuples_partial_catchall() {
        let patterns = vec![
            Pattern::Tuple(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 3.into()),
                ],
            ),
            Pattern::Tuple(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::CatchAll(SourceRef::unknown()),
                ],
            ),
            Pattern::Tuple(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 4.into()),
                ],
            ),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(!report.is_exhaustive);
        assert_eq!(report.redundant_patterns, vec![2]);
    }

    #[test]
    fn test_match_analysis_basic_enums() {
        let patterns = vec![
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("X".to_string()),
                ]),
                Some(vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ]),
            ),
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("Y".to_string()),
                ]),
                Some(vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ]),
            ),
        ];
        let enums = {
            let mut map = HashMap::new();
            map.insert(
                "A",
                vec![
                    ("X", Some(vec![Type::Int, Type::Int])),
                    ("Y", Some(vec![Type::Int, Type::Int])),
                ],
            );
            map
        };
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(!report.is_exhaustive);
        assert!(report.redundant_patterns.is_empty());
    }

    #[test]
    fn test_match_analysis_basic_enums_catchall() {
        let patterns = vec![
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("X".to_string()),
                ]),
                Some(vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ]),
            ),
            Pattern::CatchAll(SourceRef::unknown()),
        ];
        let enums = {
            let mut map = HashMap::new();
            map.insert(
                "A",
                vec![
                    ("X", Some(vec![Type::Int, Type::Int])),
                    ("Y", Some(vec![Type::Int, Type::Int])),
                ],
            );
            map
        };
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(report.is_exhaustive);
        assert!(report.redundant_patterns.is_empty());
    }

    #[test]
    fn test_match_analysis_no_variants() {
        let patterns = vec![
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("X".to_string()),
                ]),
                None,
            ),
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("Y".to_string()),
                ]),
                Some(vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ]),
            ),
        ];
        let enums = {
            let mut map = HashMap::new();
            map.insert(
                "A",
                vec![("X", None), ("Y", Some(vec![Type::Int, Type::Int]))],
            );
            map
        };
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(!report.is_exhaustive);
        assert!(report.redundant_patterns.is_empty());
    }

    #[test]
    fn test_match_analysis_enums_inner_catchall() {
        let patterns = vec![
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("X".to_string()),
                ]),
                Some(vec![
                    Pattern::CatchAll(SourceRef::unknown()),
                    Pattern::CatchAll(SourceRef::unknown()),
                ]),
            ),
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("X".to_string()),
                ]),
                Some(vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 3.into()),
                ]),
            ),
        ];
        let enums = {
            let mut map = HashMap::new();
            map.insert("A", vec![("X", Some(vec![Type::Int, Type::Int]))]);
            map
        };
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(report.is_exhaustive);
        assert_eq!(report.redundant_patterns, vec![1]);
    }

    #[test]
    fn test_usefullness_tuples_and_enums() {
        // ((_, None), _)
        // (_, (_, None))
        // (('l_short', Some('l_last')), ('r_short', Some('r_last'))
        let elem1 = Pattern::Tuple(
            SourceRef::unknown(),
            vec![
                Pattern::CatchAll(SourceRef::unknown()),
                Pattern::Enum(
                    SourceRef::unknown(),
                    SymbolPath::from_parts(vec![
                        Part::Named("Option".to_string()),
                        Part::Named("None".to_string()),
                    ]),
                    None,
                ),
            ],
        );
        let elem2 = Pattern::CatchAll(SourceRef::unknown());
        let arm1 = Pattern::Tuple(SourceRef::unknown(), vec![elem1, elem2]);

        let elem1 = Pattern::CatchAll(SourceRef::unknown());
        let elem2 = Pattern::Tuple(
            SourceRef::unknown(),
            vec![
                Pattern::CatchAll(SourceRef::unknown()),
                Pattern::Enum(
                    SourceRef::unknown(),
                    SymbolPath::from_parts(vec![
                        Part::Named("Option".to_string()),
                        Part::Named("None".to_string()),
                    ]),
                    None,
                ),
            ],
        );
        let arm2 = Pattern::Tuple(SourceRef::unknown(), vec![elem1, elem2]);

        let elem1 = Pattern::Tuple(
            SourceRef::unknown(),
            vec![
                Pattern::Variable(SourceRef::unknown(), "l_short".to_string()),
                Pattern::Enum(
                    SourceRef::unknown(),
                    SymbolPath::from_parts(vec![
                        Part::Named("Option".to_string()),
                        Part::Named("Some".to_string()),
                    ]),
                    Some(vec![Pattern::Variable(
                        SourceRef::unknown(),
                        "l_last".to_string(),
                    )]),
                ),
            ],
        );
        let elem2 = Pattern::Tuple(
            SourceRef::unknown(),
            vec![
                Pattern::Variable(SourceRef::unknown(), "r_short".to_string()),
                Pattern::Enum(
                    SourceRef::unknown(),
                    SymbolPath::from_parts(vec![
                        Part::Named("Option".to_string()),
                        Part::Named("Some".to_string()),
                    ]),
                    Some(vec![Pattern::Variable(
                        SourceRef::unknown(),
                        "r_last".to_string(),
                    )]),
                ),
            ],
        );
        let arm3 = Pattern::Tuple(SourceRef::unknown(), vec![elem1, elem2]);

        let patterns = vec![arm1, arm2, arm3];
        let mut enums = HashMap::new();
        enums.insert(
            "Option",
            vec![("None", None), ("Some", Some(vec![Type::String]))],
        );
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(!report.is_exhaustive);
        assert!(report.redundant_patterns.is_empty());
    }

    #[test]
    fn test_match_analysis_array_ellipsis() {
        let patterns: Vec<Pattern> = vec![
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Ellipsis(SourceRef::unknown()),
                ],
            ),
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 9.into()),
                    Pattern::Number(SourceRef::unknown(), 8.into()),
                ],
            ),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(!report.is_exhaustive);
        assert!(report.redundant_patterns.is_empty());
    }

    #[test]
    fn test_array_ellipsis_redundant_patterns() {
        let patterns = vec![
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::CatchAll(SourceRef::unknown()),
                    Pattern::Ellipsis(SourceRef::unknown()),
                ],
            ),
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Ellipsis(SourceRef::unknown()),
                ],
            ),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(report.is_exhaustive);
        assert_eq!(report.redundant_patterns, vec![1]);
    }

    #[test]
    fn test_array_ellipsis_exhaustive() {
        let patterns = vec![Pattern::Array(
            SourceRef::unknown(),
            vec![
                Pattern::CatchAll(SourceRef::unknown()),
                Pattern::Ellipsis(SourceRef::unknown()),
                Pattern::CatchAll(SourceRef::unknown()),
            ],
        )];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, &enums);
        assert!(report.is_exhaustive);
        assert!(report.redundant_patterns.is_empty());
    }

    // #[test]
    // fn test_array_ellipsis_non_exhaustive() {
    //     let patterns = vec![
    //         Pattern::Array(
    //             SourceRef::unknown(),
    //             vec![
    //                 Pattern::Number(SourceRef::unknown(), 1.into()),
    //                 Pattern::Ellipsis(SourceRef::unknown()),
    //                 Pattern::Number(SourceRef::unknown(), 2.into()),
    //             ],
    //         ),
    //         Pattern::Array(
    //             SourceRef::unknown(),
    //             vec![
    //                 Pattern::Number(SourceRef::unknown(), 1.into()),
    //                 Pattern::Ellipsis(SourceRef::unknown()),
    //                 Pattern::Number(SourceRef::unknown(), 2.into()),
    //             ],
    //         ),
    //     ];
    //     let enums = HashMap::new();
    //     let report = analyze_match_patterns(&patterns, &enums);
    //     assert!(!report.is_exhaustive);
    //     assert_eq!(report.redundant_patterns, vec![1]);
    // }
}

use std::collections::{BTreeMap, BTreeSet, HashSet};

use itertools::Itertools;

use crate::data_parser::DataValue;
use crate::parser::{Argument, Constant, Statement};

pub fn filter_reachable_from(
    label: &str,
    statements: &mut Vec<Statement>,
    objects: &mut BTreeMap<String, Vec<DataValue>>,
) {
    let replacements = extract_replacements(statements);
    let replacement_refs = replacements
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_str()))
        .collect();
    let referenced_labels = find_reachable_labels(label, statements, objects, &replacement_refs)
        .into_iter()
        .map(|s| s.to_owned())
        .collect::<HashSet<_>>();

    objects.retain(|name, _value| referenced_labels.contains(name));
    for (_name, value) in objects.iter_mut() {
        apply_replacement_to_object(value, &replacement_refs)
    }

    let mut active = false;
    *statements = std::mem::take(statements)
        .into_iter()
        .filter_map(|s| {
            let include = if active {
                if ends_control_flow(&s) {
                    active = false;
                }
                true
            } else {
                if let Statement::Label(l) = &s {
                    active = referenced_labels.contains(l) && !objects.contains_key(l);
                }
                active
            };
            include.then_some(apply_replacement_to_instruction(s, &replacement_refs))
        })
        .collect();
}

pub fn find_reachable_labels<'a>(
    label: &'a str,
    statements: &'a [Statement],
    objects: &'a mut BTreeMap<String, Vec<DataValue>>,
    replacements: &BTreeMap<&str, &'a str>,
) -> BTreeSet<&'a str> {
    let label_offsets = extract_label_offsets(statements);
    let mut queued_labels = BTreeSet::from([label]);
    let mut processed_labels = BTreeSet::<&str>::new();
    while let Some(l) = queued_labels.pop_first() {
        let l = *replacements.get(l).unwrap_or(&l);
        if !processed_labels.insert(l) {
            continue;
        }

        let new_references = if let Some(data_values) = objects.get(l) {
            data_values
                .iter()
                .filter_map(|v| {
                    if let DataValue::Reference(sym) = v {
                        Some(sym.as_str())
                    } else {
                        None
                    }
                })
                .collect()
        } else if let Some(offset) = label_offsets.get(l) {
            let (referenced_labels_in_block, seen_labels_in_block) =
                basic_block_references_starting_from(&statements[*offset..]);
            processed_labels.extend(seen_labels_in_block);
            referenced_labels_in_block
        } else {
            eprintln!("The RISCV assembly code references an external routine / label that is not available:");
            eprintln!("{l}");
            panic!();
        };
        for referenced in new_references {
            if !processed_labels.contains(referenced) {
                queued_labels.insert(referenced);
            }
        }
    }
    processed_labels
}

fn extract_replacements(statements: &[Statement]) -> BTreeMap<String, String> {
    let mut replacements = statements
        .iter()
        .filter_map(|s| match s {
            Statement::Directive(dir, args) if dir.as_str() == ".set" => {
                if let [Argument::Symbol(from), Argument::Symbol(to)] = &args[..] {
                    Some((from.to_string(), to.to_string()))
                } else {
                    panic!();
                }
            }
            _ => None,
        })
        .fold(BTreeMap::new(), |mut acc, (from, to)| {
            if acc.insert(from.to_string(), to).is_some() {
                panic!("Duplicate .set directive: {from}")
            }
            acc
        });

    // Replacements might have multiple indirections. Resolve to the last
    // indirection name:
    let keys = replacements.keys().cloned().collect::<Vec<_>>();
    for mut curr in keys {
        let mut seen = BTreeSet::new();
        while let Some(to) = replacements.get(&curr) {
            if !seen.insert(curr) {
                panic!(
                    "Cycle detected among .set directives involving:\n  {}",
                    seen.into_iter().format("\n  ")
                )
            }
            curr = to.to_string();
        }

        for key in seen {
            replacements.insert(key, curr.to_string());
        }
    }

    replacements
}

pub fn extract_label_offsets(statements: &[Statement]) -> BTreeMap<&str, usize> {
    statements
        .iter()
        .enumerate()
        .filter_map(|(i, s)| match s {
            Statement::Label(l) => Some((l.as_str(), i)),
            Statement::Directive(_, _) | Statement::Instruction(_, _) => None,
        })
        .fold(BTreeMap::new(), |mut acc, (n, i)| {
            if acc.insert(n, i).is_some() {
                panic!("Duplicate label: {n}")
            }
            acc
        })
}

pub fn references_in_statement(statement: &Statement) -> BTreeSet<&str> {
    match statement {
        Statement::Label(_) | Statement::Directive(_, _) => Default::default(),
        Statement::Instruction(_, args) => args
            .iter()
            .filter_map(|arg| match arg {
                Argument::Register(_) | Argument::StringLiteral(_) => None,
                Argument::Symbol(s) => Some(s.as_str()),
                Argument::RegOffset(_, c) | Argument::Constant(c) => match c {
                    Constant::Number(_) => None,
                    Constant::HiDataRef(s, _offset) | Constant::LoDataRef(s, _offset) => {
                        Some(s.as_str())
                    }
                },
                Argument::Difference(_, _) => todo!(),
            })
            .collect(),
    }
}

fn basic_block_references_starting_from(statements: &[Statement]) -> (Vec<&str>, Vec<&str>) {
    let mut seen_labels = vec![];
    let mut referenced_labels = BTreeSet::<&str>::new();
    iterate_basic_block(statements, |s| {
        if let Statement::Label(l) = s {
            seen_labels.push(l.as_str());
        } else {
            referenced_labels.extend(references_in_statement(s))
        }
    });
    (referenced_labels.into_iter().collect(), seen_labels)
}

fn iterate_basic_block<'a>(statements: &'a [Statement], mut fun: impl FnMut(&'a Statement)) {
    for s in statements {
        fun(s);
        if ends_control_flow(s) {
            break;
        }
    }
}

fn ends_control_flow(s: &Statement) -> bool {
    match s {
        Statement::Instruction(instruction, _) => match instruction.as_str() {
            "li" | "lui" | "la" | "mv" | "add" | "addi" | "sub" | "neg" | "mul" | "mulhu"
            | "xor" | "xori" | "and" | "andi" | "or" | "ori" | "not" | "slli" | "sll" | "srli"
            | "srl" | "srai" | "seqz" | "snez" | "slt" | "slti" | "sltu" | "sltiu" | "sgtz"
            | "beq" | "beqz" | "bgeu" | "bltu" | "blt" | "bge" | "bltz" | "blez" | "bgtz"
            | "bgez" | "bne" | "bnez" | "jal" | "jalr" | "call" | "ecall" | "ebreak" | "lw"
            | "lb" | "lbu" | "sw" | "sh" | "sb" | "nop" => false,
            "j" | "jr" | "tail" | "ret" | "unimp" => true,
            _ => {
                panic!("Unknown instruction: {instruction}");
            }
        },
        _ => false,
    }
}

fn apply_replacement_to_instruction(
    statement: Statement,
    replacements: &BTreeMap<&str, &str>,
) -> Statement {
    match statement {
        Statement::Label(_) | Statement::Directive(_, _) => statement,
        Statement::Instruction(instr, args) => Statement::Instruction(
            instr,
            args.into_iter()
                .map(|a| match a {
                    Argument::Register(_) | Argument::StringLiteral(_) => a,
                    Argument::Symbol(s) => Argument::Symbol(replace(s, replacements)),
                    Argument::RegOffset(reg, c) => {
                        Argument::RegOffset(reg, apply_replacement_to_constant(c, replacements))
                    }
                    Argument::Constant(c) => {
                        Argument::Constant(apply_replacement_to_constant(c, replacements))
                    }
                    Argument::Difference(l, r) => {
                        Argument::Difference(replace(l, replacements), replace(r, replacements))
                    }
                })
                .collect(),
        ),
    }
}

fn apply_replacement_to_constant(c: Constant, replacements: &BTreeMap<&str, &str>) -> Constant {
    match c {
        Constant::Number(_) => c,
        Constant::HiDataRef(s, off) => Constant::HiDataRef(replace(s, replacements), off),
        Constant::LoDataRef(s, off) => Constant::LoDataRef(replace(s, replacements), off),
    }
}

fn apply_replacement_to_object(object: &mut Vec<DataValue>, replacements: &BTreeMap<&str, &str>) {
    for value in object {
        if let DataValue::Reference(reference) = value {
            if let Some(replacement) = replacements.get(reference.as_str()) {
                *value = DataValue::Reference(replacement.to_string())
            }
        }
    }
}

fn replace(s: String, replacements: &BTreeMap<&str, &str>) -> String {
    match replacements.get(s.as_str()) {
        Some(r) => r.to_string(),
        None => s,
    }
}

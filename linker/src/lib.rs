#![deny(clippy::print_stdout)]

use lazy_static::lazy_static;
use powdr_analysis::utils::parse_pil_statement;
use powdr_ast::{
    asm_analysis::{combine_flags, MachineDegree},
    object::{Link, Location, MachineInstanceGraph},
    parsed::{
        asm::{AbsoluteSymbolPath, SymbolPath},
        build::{index_access, lookup, namespaced_reference, permutation, selected},
        ArrayLiteral, Expression, NamespaceDegree, PILFile, PilStatement,
    },
};
use powdr_parser_util::SourceRef;
use std::{collections::BTreeMap, iter::once};

const MAIN_OPERATION_NAME: &str = "main";
/// The log of the default minimum degree
pub const MIN_DEGREE_LOG: usize = 5;
lazy_static! {
    // The maximum degree can add a significant cost during setup, because
    // the fixed columns need to be committed to in all sizes up to the max degree.
    // This gives the user the possibility to overwrite the default value.
    /// The log of the default maximum degree
    pub static ref MAX_DEGREE_LOG: usize = {
        let default_max_degree_log = 22;

        let max_degree_log = match std::env::var("MAX_DEGREE_LOG") {
            Ok(val) => val.parse::<usize>().unwrap(),
            Err(_) => default_max_degree_log,
        };
        log::info!("For variably-sized machine, the maximum degree is 2^{max_degree_log}. \
            You can set the environment variable MAX_DEGREE_LOG to change this value.");
        max_degree_log
    };
}

/// Convert a [MachineDegree] into a [NamespaceDegree], setting any unset bounds to the relevant default values
fn to_namespace_degree(d: MachineDegree) -> NamespaceDegree {
    NamespaceDegree {
        min: d
            .min
            .unwrap_or_else(|| Expression::from(1 << MIN_DEGREE_LOG)),
        max: d
            .max
            .unwrap_or_else(|| Expression::from(1 << *MAX_DEGREE_LOG)),
    }
}

/// The optional degree of the namespace is set to that of the object if it's set, to that of the main object otherwise.
pub fn link(graph: MachineInstanceGraph) -> Result<PILFile, Vec<String>> {
    let main_machine = graph.main;
    let main_degree = graph
        .objects
        .get(&main_machine.location)
        .unwrap()
        .degree
        .clone();

    let mut pil = process_definitions(graph.statements);

    for (location, object) in graph.objects.into_iter() {
        // create a namespace for this object
        let degree = match main_degree.is_static() {
            true => main_degree.clone(),
            false => object.degree,
        };

        pil.push(PilStatement::Namespace(
            SourceRef::unknown(),
            SymbolPath::from_identifier(location.to_string()),
            Some(to_namespace_degree(degree)),
        ));

        pil.extend(object.pil);
        pil.extend(object.links.into_iter().map(process_link));

        if location == Location::main() {
            if let Some(main_operation) = graph
                .entry_points
                .iter()
                .find(|f| f.name == MAIN_OPERATION_NAME)
            {
                let main_operation_id = main_operation.id.clone();
                let operation_id = main_machine.operation_id.clone();
                match (operation_id, main_operation_id) {
                    (Some(operation_id), Some(main_operation_id)) => {
                        // call the main operation by initializing `operation_id` to that of the main operation
                        let linker_first_step = "_linker_first_step";
                        pil.extend([
                            parse_pil_statement(&format!(
                                "col fixed {linker_first_step}(i) {{ if i == 0_int {{ 1_fe }} else {{ 0_fe }} }};"
                            )),
                            parse_pil_statement(&format!(
                                "{linker_first_step} * ({operation_id} - {main_operation_id}) = 0;"
                            )),
                        ]);
                    }
                    (None, None) => {}
                    _ => unreachable!(),
                }
            }
        }
    }

    Ok(PILFile(pil))
}

// Extract the utilities and sort them into namespaces where possible.
fn process_definitions(
    mut definitions: BTreeMap<AbsoluteSymbolPath, Vec<PilStatement>>,
) -> Vec<PilStatement> {
    // definitions at the root do not require a namespace statement, so we put them first
    let root = definitions.remove(&Default::default());

    root.into_iter()
        .flatten()
        .chain(
            definitions
                .into_iter()
                .flat_map(|(module_path, statements)| {
                    once(PilStatement::Namespace(
                        SourceRef::unknown(),
                        module_path.relative_to(&Default::default()),
                        None,
                    ))
                    .chain(statements)
                }),
        )
        .collect()
}

fn process_link(link: Link) -> PilStatement {
    let from = link.from;
    let to = link.to;

    // the lhs is `instr_flag { operation_id, inputs, outputs }`
    let op_id = to.operation.id.iter().cloned().map(|n| n.into());

    let expr = if link.is_permutation {
        // permutation lhs is `flag { operation_id, inputs, outputs }`
        let lhs = selected(
            combine_flags(from.instr_flag, from.link_flag),
            ArrayLiteral {
                items: op_id
                    .chain(from.params.inputs)
                    .chain(from.params.outputs)
                    .collect(),
            }
            .into(),
        );

        // permutation rhs is `(latch * selector[idx]) { operation_id, inputs, outputs }`
        let to_namespace = to.machine.location.clone().to_string();
        let op_id = to
            .machine
            .operation_id
            .map(|oid| namespaced_reference(to_namespace.clone(), oid))
            .into_iter();

        let latch = namespaced_reference(to_namespace.clone(), to.machine.latch.unwrap());
        let rhs_selector = if let Some(call_selectors) = to.machine.call_selectors {
            let call_selector_array = namespaced_reference(to_namespace.clone(), call_selectors);
            let call_selector =
                index_access(call_selector_array, Some(to.selector_idx.unwrap().into()));
            latch * call_selector
        } else {
            latch
        };

        let rhs = selected(
            rhs_selector,
            ArrayLiteral {
                items: op_id
                    .chain(to.operation.params.inputs_and_outputs().map(|i| {
                        index_access(
                            namespaced_reference(to_namespace.clone(), &i.name),
                            i.index.clone(),
                        )
                    }))
                    .collect(),
            }
            .into(),
        );

        permutation(lhs, rhs)
    } else {
        // plookup lhs is `flag $ [ operation_id, inputs, outputs ]`
        let lhs = selected(
            combine_flags(from.instr_flag, from.link_flag),
            ArrayLiteral {
                items: op_id
                    .chain(from.params.inputs)
                    .chain(from.params.outputs)
                    .collect(),
            }
            .into(),
        );

        let to_namespace = to.machine.location.clone().to_string();
        let op_id = to
            .machine
            .operation_id
            .map(|oid| namespaced_reference(to_namespace.clone(), oid))
            .into_iter();

        let latch = namespaced_reference(to_namespace.clone(), to.machine.latch.unwrap());

        // plookup rhs is `latch $ [ operation_id, inputs, outputs ]`
        let rhs = selected(
            latch,
            ArrayLiteral {
                items: op_id
                    .chain(to.operation.params.inputs_and_outputs().map(|i| {
                        index_access(
                            namespaced_reference(to_namespace.clone(), &i.name),
                            i.index.clone(),
                        )
                    }))
                    .collect(),
            }
            .into(),
        );

        lookup(lhs, rhs)
    };

    PilStatement::Expression(SourceRef::unknown(), expr)
}

#[cfg(test)]
mod test {
    use std::{fs, path::PathBuf};

    use powdr_ast::object::MachineInstanceGraph;
    use powdr_number::{FieldElement, GoldilocksField};

    use powdr_analysis::convert_asm_to_pil;
    use powdr_parser::parse_asm;

    use pretty_assertions::assert_eq;

    use crate::{link, MAX_DEGREE_LOG, MIN_DEGREE_LOG};

    fn parse_analyze_and_compile_file<T: FieldElement>(file: &str) -> MachineInstanceGraph {
        let contents = fs::read_to_string(file).unwrap();
        let parsed = parse_asm(Some(file), &contents).unwrap_or_else(|e| {
            e.output_to_stderr();
            panic!();
        });
        let resolved =
            powdr_importer::load_dependencies_and_resolve(Some(PathBuf::from(file)), parsed)
                .unwrap();
        powdr_airgen::compile(convert_asm_to_pil::<T>(resolved).unwrap())
    }

    fn parse_analyze_and_compile<T: FieldElement>(input: &str) -> MachineInstanceGraph {
        let parsed = parse_asm(None, input).unwrap_or_else(|e| {
            e.output_to_stderr();
            panic!();
        });
        let resolved = powdr_importer::load_dependencies_and_resolve(None, parsed).unwrap();
        powdr_airgen::compile(convert_asm_to_pil::<T>(resolved).unwrap())
    }

    fn extract_main(code: &str) -> &str {
        let start = code.find("namespace main").unwrap();
        &code[start..]
    }

    #[test]
    fn compile_empty_vm() {
        let expectation = r#"namespace main(4 + 4);
    let _operation_id;
    query |__i| std::prover::provide_if_unknown(_operation_id, __i, || 2);
    pol constant _block_enforcer_last_step = [0]* + [1];
    let _operation_id_no_change = (1 - _block_enforcer_last_step) * (1 - instr_return);
    _operation_id_no_change * (_operation_id' - _operation_id) = 0;
    pol commit pc;
    pol commit instr__jump_to_operation;
    pol commit instr__reset;
    pol commit instr__loop;
    pol commit instr_return;
    pol constant first_step = [1] + [0]*;
    pol commit pc_update;
    pc_update = instr__jump_to_operation * _operation_id + instr__loop * pc + instr_return * 0 + (1 - (instr__jump_to_operation + instr__loop + instr_return)) * (pc + 1);
    pc' = (1 - first_step') * pc_update;
    1 $ [0, pc, instr__jump_to_operation, instr__reset, instr__loop, instr_return] in main__rom::latch $ [main__rom::operation_id, main__rom::p_line, main__rom::p_instr__jump_to_operation, main__rom::p_instr__reset, main__rom::p_instr__loop, main__rom::p_instr_return];
namespace main__rom(4 + 4);
    pol constant p_line = [0, 1, 2] + [2]*;
    pol constant p_instr__jump_to_operation = [0, 1, 0] + [0]*;
    pol constant p_instr__loop = [0, 0, 1] + [1]*;
    pol constant p_instr__reset = [1, 0, 0] + [0]*;
    pol constant p_instr_return = [0]*;
    pol constant operation_id = [0]*;
    pol constant latch = [1]*;
"#;

        let file_name = "../test_data/asm/empty_vm.asm";
        let graph = parse_analyze_and_compile_file::<GoldilocksField>(file_name);
        let pil = link(graph).unwrap();
        assert_eq!(extract_main(&format!("{pil}")), expectation);
    }

    #[test]
    fn compile_really_empty_vm() {
        let expectation = format!(
            r#"namespace main({}..{});
"#,
            1 << MIN_DEGREE_LOG,
            1 << *MAX_DEGREE_LOG
        );

        let graph = parse_analyze_and_compile::<GoldilocksField>("");
        let pil = link(graph).unwrap();
        assert_eq!(extract_main(&format!("{pil}")), expectation);
    }

    #[test]
    fn compile_pil_without_machine() {
        let input = "    let even = std::array::new(5, |i| 2 * i);";
        let graph = parse_analyze_and_compile::<GoldilocksField>(input);
        let pil = link(graph).unwrap().to_string();
        assert_eq!(&pil[0..input.len()], input);
    }

    #[test]
    fn compile_different_signatures() {
        let expectation = r#"namespace main(16);
    let _operation_id;
    query |__i| std::prover::provide_if_unknown(_operation_id, __i, || 4);
    pol constant _block_enforcer_last_step = [0]* + [1];
    let _operation_id_no_change = (1 - _block_enforcer_last_step) * (1 - instr_return);
    _operation_id_no_change * (_operation_id' - _operation_id) = 0;
    pol commit pc;
    pol commit X;
    pol commit Y;
    pol commit reg_write_X_A;
    pol commit reg_write_Y_A;
    pol commit A;
    pol commit instr_identity;
    pol commit instr_one;
    pol commit instr_nothing;
    pol commit instr__jump_to_operation;
    pol commit instr__reset;
    pol commit instr__loop;
    pol commit instr_return;
    pol commit X_const;
    pol commit X_read_free;
    pol commit read_X_A;
    pol commit read_X_pc;
    X = read_X_A * A + read_X_pc * pc + X_const + X_read_free * X_free_value;
    pol commit Y_const;
    pol commit Y_read_free;
    pol commit read_Y_A;
    pol commit read_Y_pc;
    Y = read_Y_A * A + read_Y_pc * pc + Y_const + Y_read_free * Y_free_value;
    pol constant first_step = [1] + [0]*;
    A' = reg_write_X_A * X + reg_write_Y_A * Y + instr__reset * 0 + (1 - (reg_write_X_A + reg_write_Y_A + instr__reset)) * A;
    pol commit pc_update;
    pc_update = instr__jump_to_operation * _operation_id + instr__loop * pc + instr_return * 0 + (1 - (instr__jump_to_operation + instr__loop + instr_return)) * (pc + 1);
    pc' = (1 - first_step') * pc_update;
    pol commit X_free_value;
    pol commit Y_free_value;
    1 $ [0, pc, reg_write_X_A, reg_write_Y_A, instr_identity, instr_one, instr_nothing, instr__jump_to_operation, instr__reset, instr__loop, instr_return, X_const, X_read_free, read_X_A, read_X_pc, Y_const, Y_read_free, read_Y_A, read_Y_pc] in main__rom::latch $ [main__rom::operation_id, main__rom::p_line, main__rom::p_reg_write_X_A, main__rom::p_reg_write_Y_A, main__rom::p_instr_identity, main__rom::p_instr_one, main__rom::p_instr_nothing, main__rom::p_instr__jump_to_operation, main__rom::p_instr__reset, main__rom::p_instr__loop, main__rom::p_instr_return, main__rom::p_X_const, main__rom::p_X_read_free, main__rom::p_read_X_A, main__rom::p_read_X_pc, main__rom::p_Y_const, main__rom::p_Y_read_free, main__rom::p_read_Y_A, main__rom::p_read_Y_pc];
    instr_identity $ [2, X, Y] in main_sub::instr_return $ [main_sub::_operation_id, main_sub::_input_0, main_sub::_output_0];
    instr_nothing $ [3] in main_sub::instr_return $ [main_sub::_operation_id];
    instr_one $ [4, Y] in main_sub::instr_return $ [main_sub::_operation_id, main_sub::_output_0];
    pol constant _linker_first_step(i) { if i == 0_int { 1_fe } else { 0_fe } };
    _linker_first_step * (_operation_id - 2) = 0;
namespace main__rom(16);
    pol constant p_line = [0, 1, 2, 3, 4] + [4]*;
    pol constant p_X_const = [0]*;
    pol constant p_X_read_free = [0]*;
    pol constant p_Y_const = [0]*;
    pol constant p_Y_read_free = [0, 0, 1, 0, 0] + [0]*;
    pol constant p_instr__jump_to_operation = [0, 1, 0, 0, 0] + [0]*;
    pol constant p_instr__loop = [0, 0, 0, 0, 1] + [1]*;
    pol constant p_instr__reset = [1, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_identity = [0]*;
    pol constant p_instr_nothing = [0]*;
    pol constant p_instr_one = [0, 0, 1, 0, 0] + [0]*;
    pol constant p_instr_return = [0, 0, 0, 1, 0] + [0]*;
    pol constant p_read_X_A = [0]*;
    pol constant p_read_X_pc = [0]*;
    pol constant p_read_Y_A = [0]*;
    pol constant p_read_Y_pc = [0]*;
    pol constant p_reg_write_X_A = [0]*;
    pol constant p_reg_write_Y_A = [0, 0, 1, 0, 0] + [0]*;
    pol constant operation_id = [0]*;
    pol constant latch = [1]*;
namespace main_sub(16);
    let _operation_id;
    query |__i| std::prover::provide_if_unknown(_operation_id, __i, || 5);
    pol constant _block_enforcer_last_step = [0]* + [1];
    let _operation_id_no_change = (1 - _block_enforcer_last_step) * (1 - instr_return);
    _operation_id_no_change * (_operation_id' - _operation_id) = 0;
    pol commit pc;
    pol commit _input_0;
    pol commit _output_0;
    pol commit instr__jump_to_operation;
    pol commit instr__reset;
    pol commit instr__loop;
    pol commit instr_return;
    pol commit _output_0_const;
    pol commit _output_0_read_free;
    pol commit read__output_0_pc;
    pol commit read__output_0__input_0;
    _output_0 = read__output_0_pc * pc + read__output_0__input_0 * _input_0 + _output_0_const + _output_0_read_free * _output_0_free_value;
    pol constant first_step = [1] + [0]*;
    (1 - instr__reset) * (_input_0' - _input_0) = 0;
    pol commit pc_update;
    pc_update = instr__jump_to_operation * _operation_id + instr__loop * pc + instr_return * 0 + (1 - (instr__jump_to_operation + instr__loop + instr_return)) * (pc + 1);
    pc' = (1 - first_step') * pc_update;
    pol commit _output_0_free_value;
    1 $ [0, pc, instr__jump_to_operation, instr__reset, instr__loop, instr_return, _output_0_const, _output_0_read_free, read__output_0_pc, read__output_0__input_0] in main_sub__rom::latch $ [main_sub__rom::operation_id, main_sub__rom::p_line, main_sub__rom::p_instr__jump_to_operation, main_sub__rom::p_instr__reset, main_sub__rom::p_instr__loop, main_sub__rom::p_instr_return, main_sub__rom::p__output_0_const, main_sub__rom::p__output_0_read_free, main_sub__rom::p_read__output_0_pc, main_sub__rom::p_read__output_0__input_0];
namespace main_sub__rom(16);
    pol constant p_line = [0, 1, 2, 3, 4, 5] + [5]*;
    pol constant p__output_0_const = [0, 0, 0, 0, 1, 0] + [0]*;
    pol constant p__output_0_read_free = [0]*;
    pol constant p_instr__jump_to_operation = [0, 1, 0, 0, 0, 0] + [0]*;
    pol constant p_instr__loop = [0, 0, 0, 0, 0, 1] + [1]*;
    pol constant p_instr__reset = [1, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_return = [0, 0, 1, 1, 1, 0] + [0]*;
    pol constant p_read__output_0__input_0 = [0, 0, 1, 0, 0, 0] + [0]*;
    pol constant p_read__output_0_pc = [0]*;
    pol constant operation_id = [0]*;
    pol constant latch = [1]*;
"#;
        let file_name = "../test_data/asm/different_signatures.asm";
        let graph = parse_analyze_and_compile_file::<GoldilocksField>(file_name);
        let pil = link(graph).unwrap();
        assert_eq!(extract_main(&format!("{pil}")), expectation);
    }

    #[test]
    fn compile_simple_sum() {
        let expectation = r#"namespace main(16);
    pol commit XInv;
    pol commit XIsZero;
    XIsZero = 1 - X * XInv;
    XIsZero * X = 0;
    XIsZero * (1 - XIsZero) = 0;
    let _operation_id;
    query |__i| std::prover::provide_if_unknown(_operation_id, __i, || 10);
    pol constant _block_enforcer_last_step = [0]* + [1];
    let _operation_id_no_change = (1 - _block_enforcer_last_step) * (1 - instr_return);
    _operation_id_no_change * (_operation_id' - _operation_id) = 0;
    pol commit pc;
    pol commit X;
    pol commit reg_write_X_A;
    pol commit A;
    pol commit reg_write_X_CNT;
    pol commit CNT;
    pol commit instr_jmpz;
    pol commit instr_jmpz_param_l;
    pol instr_jmpz_pc_update = XIsZero * instr_jmpz_param_l;
    pol instr_jmpz_pc_update_1 = (1 - XIsZero) * (pc + 1);
    pol commit instr_jmp;
    pol commit instr_jmp_param_l;
    pol commit instr_dec_CNT;
    pol commit instr_assert_zero;
    std::constraints::make_conditional(XIsZero = 1, instr_assert_zero);
    pol commit instr__jump_to_operation;
    pol commit instr__reset;
    pol commit instr__loop;
    pol commit instr_return;
    pol commit X_const;
    pol commit X_read_free;
    pol commit read_X_A;
    pol commit read_X_CNT;
    pol commit read_X_pc;
    X = read_X_A * A + read_X_CNT * CNT + read_X_pc * pc + X_const + X_read_free * X_free_value;
    pol constant first_step = [1] + [0]*;
    A' = reg_write_X_A * X + instr__reset * 0 + (1 - (reg_write_X_A + instr__reset)) * A;
    CNT' = reg_write_X_CNT * X + instr_dec_CNT * (CNT - 1) + instr__reset * 0 + (1 - (reg_write_X_CNT + instr_dec_CNT + instr__reset)) * CNT;
    pol commit pc_update;
    pc_update = instr_jmpz * (instr_jmpz_pc_update + instr_jmpz_pc_update_1) + instr_jmp * instr_jmp_param_l + instr__jump_to_operation * _operation_id + instr__loop * pc + instr_return * 0 + (1 - (instr_jmpz + instr_jmp + instr__jump_to_operation + instr__loop + instr_return)) * (pc + 1);
    pc' = (1 - first_step') * pc_update;
    pol commit X_free_value;
    query |__i| std::prover::handle_query(X_free_value, __i, match std::prover::eval(pc) {
        2 => std::prelude::Query::Input(0, 2),
        4 => std::prelude::Query::Input(0, std::convert::int(std::prover::eval(CNT) + 2)),
        7 => std::prelude::Query::Input(0, 1),
        _ => std::prelude::Query::None,
    });
    1 $ [0, pc, reg_write_X_A, reg_write_X_CNT, instr_jmpz, instr_jmpz_param_l, instr_jmp, instr_jmp_param_l, instr_dec_CNT, instr_assert_zero, instr__jump_to_operation, instr__reset, instr__loop, instr_return, X_const, X_read_free, read_X_A, read_X_CNT, read_X_pc] in main__rom::latch $ [main__rom::operation_id, main__rom::p_line, main__rom::p_reg_write_X_A, main__rom::p_reg_write_X_CNT, main__rom::p_instr_jmpz, main__rom::p_instr_jmpz_param_l, main__rom::p_instr_jmp, main__rom::p_instr_jmp_param_l, main__rom::p_instr_dec_CNT, main__rom::p_instr_assert_zero, main__rom::p_instr__jump_to_operation, main__rom::p_instr__reset, main__rom::p_instr__loop, main__rom::p_instr_return, main__rom::p_X_const, main__rom::p_X_read_free, main__rom::p_read_X_A, main__rom::p_read_X_CNT, main__rom::p_read_X_pc];
    pol constant _linker_first_step(i) { if i == 0_int { 1_fe } else { 0_fe } };
    _linker_first_step * (_operation_id - 2) = 0;
namespace main__rom(16);
    pol constant p_line = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] + [10]*;
    pol constant p_X_const = [0]*;
    pol constant p_X_read_free = [0, 0, 1, 0, 1, 0, 0, 18446744069414584320, 0, 0, 0] + [0]*;
    pol constant p_instr__jump_to_operation = [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr__loop = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] + [1]*;
    pol constant p_instr__reset = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_assert_zero = [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] + [0]*;
    pol constant p_instr_dec_CNT = [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_jmp = [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_jmp_param_l = [0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_jmpz = [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_jmpz_param_l = [0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_return = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] + [0]*;
    pol constant p_read_X_A = [0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0] + [0]*;
    pol constant p_read_X_CNT = [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_read_X_pc = [0]*;
    pol constant p_reg_write_X_A = [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0] + [0]*;
    pol constant p_reg_write_X_CNT = [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant operation_id = [0]*;
    pol constant latch = [1]*;
"#;
        let file_name = "../test_data/asm/simple_sum.asm";
        let graph = parse_analyze_and_compile_file::<GoldilocksField>(file_name);
        let pil = link(graph).unwrap();
        assert_eq!(extract_main(&format!("{pil}")), expectation);
    }

    #[test]
    fn compile_literal_number_args() {
        let source = r#"
machine Machine with min_degree: 32, max_degree: 64 {
    reg pc[@pc];
    reg fp;

    instr inc_fp amount: unsigned { fp' = fp + amount }
    instr adjust_fp amount: signed, t: label { fp' = fp + amount, pc' = t }

    function main {
        inc_fp 7;
        loop:
        adjust_fp -2, loop;
    }
}
"#;
        let expectation = r#"namespace main(32..64);
    let _operation_id;
    query |__i| std::prover::provide_if_unknown(_operation_id, __i, || 4);
    pol constant _block_enforcer_last_step = [0]* + [1];
    let _operation_id_no_change = (1 - _block_enforcer_last_step) * (1 - instr_return);
    _operation_id_no_change * (_operation_id' - _operation_id) = 0;
    pol commit pc;
    pol commit fp;
    pol commit instr_inc_fp;
    pol commit instr_inc_fp_param_amount;
    pol commit instr_adjust_fp;
    pol commit instr_adjust_fp_param_amount;
    pol commit instr_adjust_fp_param_t;
    pol commit instr__jump_to_operation;
    pol commit instr__reset;
    pol commit instr__loop;
    pol commit instr_return;
    pol constant first_step = [1] + [0]*;
    fp' = instr_inc_fp * (fp + instr_inc_fp_param_amount) + instr_adjust_fp * (fp + instr_adjust_fp_param_amount) + instr__reset * 0 + (1 - (instr_inc_fp + instr_adjust_fp + instr__reset)) * fp;
    pol commit pc_update;
    pc_update = instr_adjust_fp * instr_adjust_fp_param_t + instr__jump_to_operation * _operation_id + instr__loop * pc + instr_return * 0 + (1 - (instr_adjust_fp + instr__jump_to_operation + instr__loop + instr_return)) * (pc + 1);
    pc' = (1 - first_step') * pc_update;
    1 $ [0, pc, instr_inc_fp, instr_inc_fp_param_amount, instr_adjust_fp, instr_adjust_fp_param_amount, instr_adjust_fp_param_t, instr__jump_to_operation, instr__reset, instr__loop, instr_return] in main__rom::latch $ [main__rom::operation_id, main__rom::p_line, main__rom::p_instr_inc_fp, main__rom::p_instr_inc_fp_param_amount, main__rom::p_instr_adjust_fp, main__rom::p_instr_adjust_fp_param_amount, main__rom::p_instr_adjust_fp_param_t, main__rom::p_instr__jump_to_operation, main__rom::p_instr__reset, main__rom::p_instr__loop, main__rom::p_instr_return];
    pol constant _linker_first_step(i) { if i == 0_int { 1_fe } else { 0_fe } };
    _linker_first_step * (_operation_id - 2) = 0;
namespace main__rom(8);
    pol constant p_line = [0, 1, 2, 3, 4] + [4]*;
    pol constant p_instr__jump_to_operation = [0, 1, 0, 0, 0] + [0]*;
    pol constant p_instr__loop = [0, 0, 0, 0, 1] + [1]*;
    pol constant p_instr__reset = [1, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_adjust_fp = [0, 0, 0, 1, 0] + [0]*;
    pol constant p_instr_adjust_fp_param_amount = [0, 0, 0, 18446744069414584319, 0] + [0]*;
    pol constant p_instr_adjust_fp_param_t = [0, 0, 0, 3, 0] + [0]*;
    pol constant p_instr_inc_fp = [0, 0, 1, 0, 0] + [0]*;
    pol constant p_instr_inc_fp_param_amount = [0, 0, 7, 0, 0] + [0]*;
    pol constant p_instr_return = [0]*;
    pol constant operation_id = [0]*;
    pol constant latch = [1]*;
"#;
        let graph = parse_analyze_and_compile::<GoldilocksField>(source);
        let pil = link(graph).unwrap();
        assert_eq!(extract_main(&format!("{pil}")), expectation);
    }

    #[test]
    #[should_panic(expected = "Number passed to unsigned parameter is negative or too large")]
    fn negative_for_unsigned() {
        let source = r#"
machine NegativeForUnsigned {
    reg pc[@pc];
    reg fp;
    
    instr my_instr x: unsigned { pc' = pc + x }
    
    function main {
        my_instr 9223372034707292161;
    }
}
"#;
        let graph = parse_analyze_and_compile::<GoldilocksField>(source);
        let _ = link(graph);
    }

    #[test]
    fn instr_links_generated_pil() {
        let asm = r"
machine SubVM with latch: latch, operation_id: operation_id, min_degree: 64, max_degree: 128 {
    operation add5<0> x -> y;

    col witness operation_id;
    col fixed latch = [1]*;

    col witness x;
    col witness y;

    y = x + 5;
}

machine Main with min_degree: 32, max_degree: 64 {
    reg pc[@pc];
    reg X[<=];
    reg A;

    SubVM vm;

    instr add5_into_A X link => A' = vm.add5(X);

    function main {
        add5_into_A 10; // A <== 15
    }
}
";
        let expected = r#"namespace main(32..64);
    let _operation_id;
    query |__i| std::prover::provide_if_unknown(_operation_id, __i, || 3);
    pol constant _block_enforcer_last_step = [0]* + [1];
    let _operation_id_no_change = (1 - _block_enforcer_last_step) * (1 - instr_return);
    _operation_id_no_change * (_operation_id' - _operation_id) = 0;
    pol commit pc;
    pol commit X;
    pol commit reg_write_X_A;
    pol commit A;
    pol commit instr_add5_into_A;
    pol commit instr__jump_to_operation;
    pol commit instr__reset;
    pol commit instr__loop;
    pol commit instr_return;
    pol commit X_const;
    pol commit X_read_free;
    pol commit read_X_A;
    pol commit read_X_pc;
    X = read_X_A * A + read_X_pc * pc + X_const + X_read_free * X_free_value;
    pol constant first_step = [1] + [0]*;
    A' = reg_write_X_A * X + instr_add5_into_A * A' + instr__reset * 0 + (1 - (reg_write_X_A + instr_add5_into_A + instr__reset)) * A;
    pol commit pc_update;
    pc_update = instr__jump_to_operation * _operation_id + instr__loop * pc + instr_return * 0 + (1 - (instr__jump_to_operation + instr__loop + instr_return)) * (pc + 1);
    pc' = (1 - first_step') * pc_update;
    pol commit X_free_value;
    instr_add5_into_A $ [0, X, A'] in main_vm::latch $ [main_vm::operation_id, main_vm::x, main_vm::y];
    1 $ [0, pc, reg_write_X_A, instr_add5_into_A, instr__jump_to_operation, instr__reset, instr__loop, instr_return, X_const, X_read_free, read_X_A, read_X_pc] in main__rom::latch $ [main__rom::operation_id, main__rom::p_line, main__rom::p_reg_write_X_A, main__rom::p_instr_add5_into_A, main__rom::p_instr__jump_to_operation, main__rom::p_instr__reset, main__rom::p_instr__loop, main__rom::p_instr_return, main__rom::p_X_const, main__rom::p_X_read_free, main__rom::p_read_X_A, main__rom::p_read_X_pc];
    pol constant _linker_first_step(i) { if i == 0_int { 1_fe } else { 0_fe } };
    _linker_first_step * (_operation_id - 2) = 0;
namespace main__rom(4);
    pol constant p_line = [0, 1, 2, 3] + [3]*;
    pol constant p_X_const = [0, 0, 10, 0] + [0]*;
    pol constant p_X_read_free = [0]*;
    pol constant p_instr__jump_to_operation = [0, 1, 0, 0] + [0]*;
    pol constant p_instr__loop = [0, 0, 0, 1] + [1]*;
    pol constant p_instr__reset = [1, 0, 0, 0] + [0]*;
    pol constant p_instr_add5_into_A = [0, 0, 1, 0] + [0]*;
    pol constant p_instr_return = [0]*;
    pol constant p_read_X_A = [0]*;
    pol constant p_read_X_pc = [0]*;
    pol constant p_reg_write_X_A = [0]*;
    pol constant operation_id = [0]*;
    pol constant latch = [1]*;
namespace main_vm(64..128);
    pol commit operation_id;
    pol constant latch = [1]*;
    pol commit x;
    pol commit y;
    y = x + 5;
"#;
        let graph = parse_analyze_and_compile::<GoldilocksField>(asm);
        let pil = link(graph).unwrap();
        assert_eq!(extract_main(&(pil.to_string())), expected);
    }

    #[test]
    fn permutation_instructions() {
        let expected = r#"namespace main(128);
    let _operation_id;
    query |__i| std::prover::provide_if_unknown(_operation_id, __i, || 13);
    pol constant _block_enforcer_last_step = [0]* + [1];
    let _operation_id_no_change = (1 - _block_enforcer_last_step) * (1 - instr_return);
    _operation_id_no_change * (_operation_id' - _operation_id) = 0;
    pol commit pc;
    pol commit X;
    pol commit Y;
    pol commit Z;
    pol commit reg_write_X_A;
    pol commit reg_write_Y_A;
    pol commit reg_write_Z_A;
    pol commit A;
    pol commit reg_write_X_B;
    pol commit reg_write_Y_B;
    pol commit reg_write_Z_B;
    pol commit B;
    pol commit instr_or;
    pol commit instr_or_into_B;
    pol commit instr_assert_eq;
    std::constraints::make_conditional(X = Y, instr_assert_eq);
    pol commit instr__jump_to_operation;
    pol commit instr__reset;
    pol commit instr__loop;
    pol commit instr_return;
    pol commit X_const;
    pol commit X_read_free;
    pol commit read_X_A;
    pol commit read_X_B;
    pol commit read_X_pc;
    X = read_X_A * A + read_X_B * B + read_X_pc * pc + X_const + X_read_free * X_free_value;
    pol commit Y_const;
    pol commit Y_read_free;
    pol commit read_Y_A;
    pol commit read_Y_B;
    pol commit read_Y_pc;
    Y = read_Y_A * A + read_Y_B * B + read_Y_pc * pc + Y_const + Y_read_free * Y_free_value;
    pol commit Z_const;
    pol commit Z_read_free;
    pol commit read_Z_A;
    pol commit read_Z_B;
    pol commit read_Z_pc;
    Z = read_Z_A * A + read_Z_B * B + read_Z_pc * pc + Z_const + Z_read_free * Z_free_value;
    pol constant first_step = [1] + [0]*;
    A' = reg_write_X_A * X + reg_write_Y_A * Y + reg_write_Z_A * Z + instr__reset * 0 + (1 - (reg_write_X_A + reg_write_Y_A + reg_write_Z_A + instr__reset)) * A;
    B' = reg_write_X_B * X + reg_write_Y_B * Y + reg_write_Z_B * Z + instr_or_into_B * B' + instr__reset * 0 + (1 - (reg_write_X_B + reg_write_Y_B + reg_write_Z_B + instr_or_into_B + instr__reset)) * B;
    pol commit pc_update;
    pc_update = instr__jump_to_operation * _operation_id + instr__loop * pc + instr_return * 0 + (1 - (instr__jump_to_operation + instr__loop + instr_return)) * (pc + 1);
    pc' = (1 - first_step') * pc_update;
    pol commit X_free_value;
    pol commit Y_free_value;
    pol commit Z_free_value;
    instr_or_into_B $ [0, X, Y, B'] is main_bin::latch * main_bin::sel[0] $ [main_bin::operation_id, main_bin::A, main_bin::B, main_bin::C];
    1 $ [0, pc, reg_write_X_A, reg_write_Y_A, reg_write_Z_A, reg_write_X_B, reg_write_Y_B, reg_write_Z_B, instr_or, instr_or_into_B, instr_assert_eq, instr__jump_to_operation, instr__reset, instr__loop, instr_return, X_const, X_read_free, read_X_A, read_X_B, read_X_pc, Y_const, Y_read_free, read_Y_A, read_Y_B, read_Y_pc, Z_const, Z_read_free, read_Z_A, read_Z_B, read_Z_pc] in main__rom::latch $ [main__rom::operation_id, main__rom::p_line, main__rom::p_reg_write_X_A, main__rom::p_reg_write_Y_A, main__rom::p_reg_write_Z_A, main__rom::p_reg_write_X_B, main__rom::p_reg_write_Y_B, main__rom::p_reg_write_Z_B, main__rom::p_instr_or, main__rom::p_instr_or_into_B, main__rom::p_instr_assert_eq, main__rom::p_instr__jump_to_operation, main__rom::p_instr__reset, main__rom::p_instr__loop, main__rom::p_instr_return, main__rom::p_X_const, main__rom::p_X_read_free, main__rom::p_read_X_A, main__rom::p_read_X_B, main__rom::p_read_X_pc, main__rom::p_Y_const, main__rom::p_Y_read_free, main__rom::p_read_Y_A, main__rom::p_read_Y_B, main__rom::p_read_Y_pc, main__rom::p_Z_const, main__rom::p_Z_read_free, main__rom::p_read_Z_A, main__rom::p_read_Z_B, main__rom::p_read_Z_pc];
    instr_or $ [0, X, Y, Z] is main_bin::latch * main_bin::sel[1] $ [main_bin::operation_id, main_bin::A, main_bin::B, main_bin::C];
    pol constant _linker_first_step(i) { if i == 0_int { 1_fe } else { 0_fe } };
    _linker_first_step * (_operation_id - 2) = 0;
namespace main__rom(128);
    pol constant p_line = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] + [13]*;
    pol constant p_X_const = [0, 0, 2, 0, 1, 0, 3, 0, 2, 0, 1, 0, 0, 0] + [0]*;
    pol constant p_X_read_free = [0]*;
    pol constant p_Y_const = [0, 0, 3, 3, 2, 3, 4, 7, 3, 3, 2, 3, 0, 0] + [0]*;
    pol constant p_Y_read_free = [0]*;
    pol constant p_Z_const = [0]*;
    pol constant p_Z_read_free = [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr__jump_to_operation = [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr__loop = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] + [1]*;
    pol constant p_instr__reset = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_assert_eq = [0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0] + [0]*;
    pol constant p_instr_or = [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_or_into_B = [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0] + [0]*;
    pol constant p_instr_return = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] + [0]*;
    pol constant p_read_X_A = [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_read_X_B = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0] + [0]*;
    pol constant p_read_X_pc = [0]*;
    pol constant p_read_Y_A = [0]*;
    pol constant p_read_Y_B = [0]*;
    pol constant p_read_Y_pc = [0]*;
    pol constant p_read_Z_A = [0]*;
    pol constant p_read_Z_B = [0]*;
    pol constant p_read_Z_pc = [0]*;
    pol constant p_reg_write_X_A = [0]*;
    pol constant p_reg_write_X_B = [0]*;
    pol constant p_reg_write_Y_A = [0]*;
    pol constant p_reg_write_Y_B = [0]*;
    pol constant p_reg_write_Z_A = [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_reg_write_Z_B = [0]*;
    pol constant operation_id = [0]*;
    pol constant latch = [1]*;
namespace main_bin(128);
    pol commit operation_id;
    pol constant latch(i) { if i % 8 == 7 { 1 } else { 0 } };
    let sum_sel = std::array::sum(sel);
    pol constant FACTOR(i) { 1 << (i + 1) % 8 * 4 };
    let a = |i| i % 16;
    pol constant P_A(i) { a(i) };
    let b = |i| (i >> 4) % 16;
    pol constant P_B(i) { b(i) };
    pol constant P_C(i) { (a(i) | b(i)) & 15 };
    pol commit A_byte;
    pol commit B_byte;
    pol commit C_byte;
    pol commit A;
    pol commit B;
    pol commit C;
    A' = A * (1 - latch) + A_byte * FACTOR;
    B' = B * (1 - latch) + B_byte * FACTOR;
    C' = C * (1 - latch) + C_byte * FACTOR;
    [A_byte, B_byte, C_byte] in [P_A, P_B, P_C];
    pol commit sel[2];
    std::array::map(sel, std::utils::force_bool);
"#;
        let file_name = "../test_data/asm/permutations/vm_to_block.asm";
        let graph = parse_analyze_and_compile_file::<GoldilocksField>(file_name);
        let pil = link(graph).unwrap();
        assert_eq!(extract_main(&format!("{pil}")), expected);
    }

    #[test]
    fn link_merging() {
        let expected = r#"namespace main(32);
    pol commit tmp;
    let _operation_id;
    query |__i| std::prover::provide_if_unknown(_operation_id, __i, || 18);
    pol constant _block_enforcer_last_step = [0]* + [1];
    let _operation_id_no_change = (1 - _block_enforcer_last_step) * (1 - instr_return);
    _operation_id_no_change * (_operation_id' - _operation_id) = 0;
    pol commit pc;
    pol commit X;
    pol commit Y;
    pol commit Z;
    pol commit W;
    pol commit reg_write_X_A;
    pol commit reg_write_Y_A;
    pol commit reg_write_Z_A;
    pol commit reg_write_W_A;
    pol commit A;
    pol commit reg_write_X_B;
    pol commit reg_write_Y_B;
    pol commit reg_write_Z_B;
    pol commit reg_write_W_B;
    pol commit B;
    pol commit reg_write_X_C;
    pol commit reg_write_Y_C;
    pol commit reg_write_Z_C;
    pol commit reg_write_W_C;
    pol commit C;
    pol commit instr_add;
    pol commit instr_sub_with_add;
    pol commit instr_addAB;
    pol commit instr_add3;
    pol commit instr_add_to_A;
    pol commit instr_add_BC_to_A;
    pol commit instr_sub;
    pol commit instr_add_with_sub;
    pol commit instr_assert_eq;
    std::constraints::make_conditional(X = Y, instr_assert_eq);
    pol commit instr__jump_to_operation;
    pol commit instr__reset;
    pol commit instr__loop;
    pol commit instr_return;
    pol commit X_const;
    pol commit X_read_free;
    pol commit read_X_A;
    pol commit read_X_B;
    pol commit read_X_C;
    pol commit read_X_pc;
    X = read_X_A * A + read_X_B * B + read_X_C * C + read_X_pc * pc + X_const + X_read_free * X_free_value;
    pol commit Y_const;
    pol commit Y_read_free;
    pol commit read_Y_A;
    pol commit read_Y_B;
    pol commit read_Y_C;
    pol commit read_Y_pc;
    Y = read_Y_A * A + read_Y_B * B + read_Y_C * C + read_Y_pc * pc + Y_const + Y_read_free * Y_free_value;
    pol commit Z_const;
    pol commit Z_read_free;
    pol commit read_Z_A;
    pol commit read_Z_B;
    pol commit read_Z_C;
    pol commit read_Z_pc;
    Z = read_Z_A * A + read_Z_B * B + read_Z_C * C + read_Z_pc * pc + Z_const + Z_read_free * Z_free_value;
    pol commit W_const;
    pol commit W_read_free;
    pol commit read_W_A;
    pol commit read_W_B;
    pol commit read_W_C;
    pol commit read_W_pc;
    W = read_W_A * A + read_W_B * B + read_W_C * C + read_W_pc * pc + W_const + W_read_free * W_free_value;
    pol constant first_step = [1] + [0]*;
    A' = reg_write_X_A * X + reg_write_Y_A * Y + reg_write_Z_A * Z + reg_write_W_A * W + instr_add_to_A * A' + instr_add_BC_to_A * A' + instr__reset * 0 + (1 - (reg_write_X_A + reg_write_Y_A + reg_write_Z_A + reg_write_W_A + instr_add_to_A + instr_add_BC_to_A + instr__reset)) * A;
    B' = reg_write_X_B * X + reg_write_Y_B * Y + reg_write_Z_B * Z + reg_write_W_B * W + instr__reset * 0 + (1 - (reg_write_X_B + reg_write_Y_B + reg_write_Z_B + reg_write_W_B + instr__reset)) * B;
    C' = reg_write_X_C * X + reg_write_Y_C * Y + reg_write_Z_C * Z + reg_write_W_C * W + instr__reset * 0 + (1 - (reg_write_X_C + reg_write_Y_C + reg_write_Z_C + reg_write_W_C + instr__reset)) * C;
    pol commit pc_update;
    pc_update = instr__jump_to_operation * _operation_id + instr__loop * pc + instr_return * 0 + (1 - (instr__jump_to_operation + instr__loop + instr_return)) * (pc + 1);
    pc' = (1 - first_step') * pc_update;
    pol commit X_free_value;
    pol commit Y_free_value;
    pol commit Z_free_value;
    pol commit W_free_value;
    instr_add_to_A $ [0, X, Y, A'] in main_submachine::latch $ [main_submachine::operation_id, main_submachine::x, main_submachine::y, main_submachine::z];
    instr_add_BC_to_A $ [0, B, C, A'] in main_submachine::latch $ [main_submachine::operation_id, main_submachine::x, main_submachine::y, main_submachine::z];
    1 $ [0, pc, reg_write_X_A, reg_write_Y_A, reg_write_Z_A, reg_write_W_A, reg_write_X_B, reg_write_Y_B, reg_write_Z_B, reg_write_W_B, reg_write_X_C, reg_write_Y_C, reg_write_Z_C, reg_write_W_C, instr_add, instr_sub_with_add, instr_addAB, instr_add3, instr_add_to_A, instr_add_BC_to_A, instr_sub, instr_add_with_sub, instr_assert_eq, instr__jump_to_operation, instr__reset, instr__loop, instr_return, X_const, X_read_free, read_X_A, read_X_B, read_X_C, read_X_pc, Y_const, Y_read_free, read_Y_A, read_Y_B, read_Y_C, read_Y_pc, Z_const, Z_read_free, read_Z_A, read_Z_B, read_Z_C, read_Z_pc, W_const, W_read_free, read_W_A, read_W_B, read_W_C, read_W_pc] in main__rom::latch $ [main__rom::operation_id, main__rom::p_line, main__rom::p_reg_write_X_A, main__rom::p_reg_write_Y_A, main__rom::p_reg_write_Z_A, main__rom::p_reg_write_W_A, main__rom::p_reg_write_X_B, main__rom::p_reg_write_Y_B, main__rom::p_reg_write_Z_B, main__rom::p_reg_write_W_B, main__rom::p_reg_write_X_C, main__rom::p_reg_write_Y_C, main__rom::p_reg_write_Z_C, main__rom::p_reg_write_W_C, main__rom::p_instr_add, main__rom::p_instr_sub_with_add, main__rom::p_instr_addAB, main__rom::p_instr_add3, main__rom::p_instr_add_to_A, main__rom::p_instr_add_BC_to_A, main__rom::p_instr_sub, main__rom::p_instr_add_with_sub, main__rom::p_instr_assert_eq, main__rom::p_instr__jump_to_operation, main__rom::p_instr__reset, main__rom::p_instr__loop, main__rom::p_instr_return, main__rom::p_X_const, main__rom::p_X_read_free, main__rom::p_read_X_A, main__rom::p_read_X_B, main__rom::p_read_X_C, main__rom::p_read_X_pc, main__rom::p_Y_const, main__rom::p_Y_read_free, main__rom::p_read_Y_A, main__rom::p_read_Y_B, main__rom::p_read_Y_C, main__rom::p_read_Y_pc, main__rom::p_Z_const, main__rom::p_Z_read_free, main__rom::p_read_Z_A, main__rom::p_read_Z_B, main__rom::p_read_Z_C, main__rom::p_read_Z_pc, main__rom::p_W_const, main__rom::p_W_read_free, main__rom::p_read_W_A, main__rom::p_read_W_B, main__rom::p_read_W_C, main__rom::p_read_W_pc];
    instr_add + instr_add3 + instr_addAB + instr_sub_with_add $ [0, X * instr_add + X * instr_add3 + A * instr_addAB + Y * instr_sub_with_add, Y * instr_add + Y * instr_add3 + B * instr_addAB + Z * instr_sub_with_add, Z * instr_add + tmp * instr_add3 + X * instr_addAB + X * instr_sub_with_add] in main_submachine::latch $ [main_submachine::operation_id, main_submachine::x, main_submachine::y, main_submachine::z];
    instr_add3 $ [0, tmp, Z, W] in main_submachine::latch $ [main_submachine::operation_id, main_submachine::x, main_submachine::y, main_submachine::z];
    instr_add_with_sub + instr_sub $ [1, Z * instr_add_with_sub + X * instr_sub, X * instr_add_with_sub + Y * instr_sub, Y * instr_add_with_sub + Z * instr_sub] in main_submachine::latch $ [main_submachine::operation_id, main_submachine::z, main_submachine::x, main_submachine::y];
    pol constant _linker_first_step(i) { if i == 0_int { 1_fe } else { 0_fe } };
    _linker_first_step * (_operation_id - 2) = 0;
namespace main__rom(32);
    pol constant p_line = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] + [18]*;
    pol constant p_W_const = [0]*;
    pol constant p_W_read_free = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_X_const = [0, 0, 2, 0, 6, 0, 6, 0, 6, 0, 20, 0, 0, 1, 0, 1, 0, 0, 0] + [0]*;
    pol constant p_X_read_free = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_Y_const = [0, 0, 3, 5, 7, 13, 5, 1, 5, 1, 0, 0, 21, 2, 6, 2, 3, 0, 0] + [0]*;
    pol constant p_Y_read_free = [0]*;
    pol constant p_Z_const = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_Z_read_free = [0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] + [0]*;
    pol constant p_instr__jump_to_operation = [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr__loop = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] + [1]*;
    pol constant p_instr__reset = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_add = [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_add3 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_addAB = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_add_BC_to_A = [0]*;
    pol constant p_instr_add_to_A = [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_add_with_sub = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] + [0]*;
    pol constant p_instr_assert_eq = [0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0] + [0]*;
    pol constant p_instr_return = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] + [0]*;
    pol constant p_instr_sub = [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_instr_sub_with_add = [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_read_W_A = [0]*;
    pol constant p_read_W_B = [0]*;
    pol constant p_read_W_C = [0]*;
    pol constant p_read_W_pc = [0]*;
    pol constant p_read_X_A = [0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0] + [0]*;
    pol constant p_read_X_B = [0]*;
    pol constant p_read_X_C = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_read_X_pc = [0]*;
    pol constant p_read_Y_A = [0]*;
    pol constant p_read_Y_B = [0]*;
    pol constant p_read_Y_C = [0]*;
    pol constant p_read_Y_pc = [0]*;
    pol constant p_read_Z_A = [0]*;
    pol constant p_read_Z_B = [0]*;
    pol constant p_read_Z_C = [0]*;
    pol constant p_read_Z_pc = [0]*;
    pol constant p_reg_write_W_A = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_reg_write_W_B = [0]*;
    pol constant p_reg_write_W_C = [0]*;
    pol constant p_reg_write_X_A = [0]*;
    pol constant p_reg_write_X_B = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_reg_write_X_C = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] + [0]*;
    pol constant p_reg_write_Y_A = [0]*;
    pol constant p_reg_write_Y_B = [0]*;
    pol constant p_reg_write_Y_C = [0]*;
    pol constant p_reg_write_Z_A = [0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] + [0]*;
    pol constant p_reg_write_Z_B = [0]*;
    pol constant p_reg_write_Z_C = [0]*;
    pol constant operation_id = [0]*;
    pol constant latch = [1]*;
namespace main_submachine(32);
    pol commit operation_id;
    pol constant latch = [1]*;
    pol commit x;
    pol commit y;
    pol commit z;
    z = y + x;
"#;
        let file_name = "../test_data/asm/permutations/link_merging.asm";
        let graph = parse_analyze_and_compile_file::<GoldilocksField>(file_name);
        let pil = link(graph).unwrap();
        assert_eq!(extract_main(&format!("{pil}")), expected);
    }
}

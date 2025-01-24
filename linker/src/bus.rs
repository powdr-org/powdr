use powdr_analysis::utils::parse_pil_statement;
use powdr_ast::{
    asm_analysis::combine_flags,
    object::{Link, LinkTo, Location, MachineInstanceGraph, Object, Operation},
    parsed::{
        asm::SymbolPath,
        build::{index_access, namespaced_reference},
        ArrayLiteral, Expression, FunctionCall, PilStatement,
    },
};
use powdr_parser_util::SourceRef;
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, str::FromStr};

use crate::{
    call, try_into_namespace_degree, DegreeMode, InteractionType, LinkerBackend,
    MAIN_OPERATION_NAME,
};

/// Compute a unique identifier for an interaction
fn interaction_id(link_to: &LinkTo) -> u32 {
    let mut hasher = Sha256::default();
    hasher.update(format!("{}/{}", link_to.machine, link_to.operation));
    let result = hasher.finalize();
    let mut bytes = [0u8; 4];
    bytes.copy_from_slice(&result[..4]);
    u32::from_le_bytes(bytes)
}

pub struct BusLinker {
    /// the pil statements
    pil: Vec<PilStatement>,
    /// for each operation, whether we are in permutation mode or lookup mode
    operation_mode: BTreeMap<LinkTo, InteractionType>,
}

impl LinkerBackend for BusLinker {
    fn try_new(graph: &MachineInstanceGraph, degree_mode: DegreeMode) -> Result<Self, Vec<String>> {
        match degree_mode {
            DegreeMode::Monolithic => {
                Err(vec!["Monolithic degree mode is not supported".to_string()])
            }
            DegreeMode::Vadcop => Ok(()),
        }?;

        let operation_mode = graph
            .objects
            .iter()
            .flat_map(|(_, object)| {
                object.links.iter().map(|link| {
                    (
                        link.to.clone(),
                        if link.is_permutation {
                            InteractionType::Permutation
                        } else {
                            InteractionType::Lookup
                        },
                    )
                })
            })
            .fold(BTreeMap::default(), |mut acc, (to, interaction_type)| {
                let existing_value = acc.insert(to, interaction_type);
                assert!(
                    existing_value
                        .map(|v| v == interaction_type)
                        .unwrap_or(true),
                    "All links to the same operation must have the same permutation mode"
                );
                acc
            });

        Ok(Self {
            pil: Default::default(),
            operation_mode,
        })
    }

    fn process_link(&mut self, link: &Link, _: &Location, objects: &BTreeMap<Location, Object>) {
        let from = &link.from;
        let to = &link.to;

        let operation = &objects[&to.machine].operations[&to.operation];

        let interaction_id = interaction_id(to);

        let op_id = operation.id.clone().map(|operation_id| operation_id.into());

        // we send `flag $ { operation_id, inputs, outputs }`
        let selector = combine_flags(from.instr_flag.clone(), from.link_flag.clone());
        let tuple = ArrayLiteral {
            items: op_id
                .into_iter()
                .chain(from.params.inputs.clone())
                .chain(from.params.outputs.clone())
                .collect(),
        }
        .into();

        self.pil.push(PilStatement::Expression(
            SourceRef::unknown(),
            Expression::FunctionCall(
                SourceRef::unknown(),
                FunctionCall {
                    function: Box::new(Expression::Reference(
                        SourceRef::unknown(),
                        SymbolPath::from_str("std::protocols::bus::bus_send")
                            .unwrap()
                            .into(),
                    )),
                    arguments: vec![interaction_id.into(), tuple, selector],
                },
            ),
        ));
    }

    fn process_object(&mut self, location: &Location, objects: &BTreeMap<Location, Object>) {
        let object = &objects[location];

        let namespace_degree = try_into_namespace_degree(object.degree.clone())
            .unwrap_or_else(|| panic!("machine at {location} must have an explicit degree"));
        // create a namespace for this object
        self.pil.push(PilStatement::Namespace(
            SourceRef::unknown(),
            SymbolPath::from_identifier(location.to_string()),
            Some(namespace_degree),
        ));

        self.pil.extend(object.pil.clone());

        if let Some(call_selectors) = &object.call_selectors {
            // TODO: this is not optimal in the case where some operations are called via lookups or not called at all, but it will do for now.
            // If we used separate selector columns instead of an array, the optimizer could remove the unused ones better
            let count = object.operations.len();
            self.pil.extend([
                parse_pil_statement(&format!("col witness {call_selectors}[{count}];")),
                parse_pil_statement(&format!(
                    "std::array::map({call_selectors}, std::utils::force_bool);"
                )),
            ])
        }

        // process outgoing links
        for link in &object.links {
            self.process_link(link, location, objects);
        }
        // receive incoming links
        for (operation_index, (name, operation)) in object.operations.iter().enumerate() {
            self.process_operation(name, operation, operation_index, location, object);
        }

        // if this is the main object, call the main operation
        if *location == Location::main() {
            let operation_id = object.operation_id.clone();
            let main_operation_id = object
                .operations
                .get(MAIN_OPERATION_NAME)
                .and_then(|operation| operation.id.as_ref());

            if let (Some(operation_id_name), Some(operation_id_value)) =
                (operation_id, main_operation_id)
            {
                self.pil
                    .extend(call(&operation_id_name, operation_id_value));
            }
        }
    }

    fn into_pil(self) -> Vec<PilStatement> {
        self.pil
    }
}

impl BusLinker {
    /// Process an operation, which means receive from the bus with the correct [InteractionType]
    fn process_operation(
        &mut self,
        operation_name: &str,
        operation: &Operation,
        operation_index: usize,
        location: &Location,
        object: &Object,
    ) {
        let link_to = LinkTo {
            machine: location.clone(),
            operation: operation_name.to_string(),
        };

        let interaction_ty = self.operation_mode.get(&link_to);

        // By construction, all operations *which are called* have an [InteractionType]. The others can be safely ignored.
        if let Some(interaction_ty) = interaction_ty {
            // compute the unique interaction id
            let interaction_id = interaction_id(&link_to);

            let namespace = location.to_string();

            let op_id = object
                .operation_id
                .clone()
                .map(|oid| namespaced_reference(namespace.clone(), oid))
                .into_iter();

            let tuple = ArrayLiteral {
                items: op_id
                    .chain(operation.params.inputs_and_outputs().map(|i| {
                        index_access(
                            namespaced_reference(namespace.clone(), &i.name),
                            i.index.clone(),
                        )
                    }))
                    .collect(),
            }
            .into();

            let latch = namespaced_reference(namespace.clone(), object.latch.clone().unwrap());

            let (function, arguments) = match interaction_ty {
                InteractionType::Lookup => (
                    SymbolPath::from_str("std::protocols::lookup_via_bus::lookup_receive")
                        .unwrap()
                        .into(),
                    vec![interaction_id.into(), latch, tuple],
                ),
                InteractionType::Permutation => (
                    SymbolPath::from_str(
                        "std::protocols::permutation_via_bus::permutation_receive",
                    )
                    .unwrap()
                    .into(),
                    {
                        let call_selector_array = namespaced_reference(
                            location.to_string(),
                            object
                                .call_selectors
                                .as_ref()
                                .unwrap_or_else(|| panic!("{location} has incoming permutations but doesn't declare call_selectors")),
                            );
                        let call_selector =
                            index_access(call_selector_array, Some(operation_index.into()));
                        let rhs_selector = latch * call_selector;

                        vec![interaction_id.into(), rhs_selector, tuple]
                    },
                ),
            };

            // receive from the bus
            self.pil
                .push(PilStatement::Expression(SourceRef::unknown(), {
                    Expression::FunctionCall(
                        SourceRef::unknown(),
                        FunctionCall {
                            function: Box::new(Expression::Reference(
                                SourceRef::unknown(),
                                function,
                            )),
                            arguments,
                        },
                    )
                }));
        }
    }
}

#[cfg(test)]
mod test {
    use std::{fs, path::PathBuf};

    use powdr_ast::object::MachineInstanceGraph;
    use powdr_number::{FieldElement, GoldilocksField};

    use powdr_analysis::convert_asm_to_pil;
    use powdr_parser::parse_asm;

    use pretty_assertions::assert_eq;

    use crate::LinkerBackend;

    use super::BusLinker;

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

    fn extract_main(code: &str) -> &str {
        let start = code.find("namespace main").unwrap();
        &code[start..]
    }

    #[test]
    fn compile_empty_vm() {
        let expectation = r#"namespace main(8);
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
    pol commit call_selectors[0];
    std::array::map(call_selectors, std::utils::force_bool);
    std::protocols::bus::bus_send(1816473376, [0, pc, instr__jump_to_operation, instr__reset, instr__loop, instr_return], 1);
namespace main__rom(4);
    pol constant p_line = [0, 1, 2] + [2]*;
    pol constant p_instr__jump_to_operation = [0, 1, 0] + [0]*;
    pol constant p_instr__loop = [0, 0, 1] + [1]*;
    pol constant p_instr__reset = [1, 0, 0] + [0]*;
    pol constant p_instr_return = [0]*;
    pol constant operation_id = [0]*;
    pol constant latch = [1]*;
    std::protocols::lookup_via_bus::lookup_receive(1816473376, main__rom::latch, [main__rom::operation_id, main__rom::p_line, main__rom::p_instr__jump_to_operation, main__rom::p_instr__reset, main__rom::p_instr__loop, main__rom::p_instr_return]);
"#;

        let file_name = "../test_data/asm/empty_vm.asm";
        let graph = parse_analyze_and_compile_file::<GoldilocksField>(file_name);
        let pil = BusLinker::link(graph, crate::DegreeMode::Vadcop).unwrap();
        assert_eq!(extract_main(&format!("{pil}")), expectation);
    }
}

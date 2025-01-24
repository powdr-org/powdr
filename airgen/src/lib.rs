//! Compilation from powdr machines to AIRs

use std::collections::BTreeMap;

use powdr_ast::{
    asm_analysis::{
        self, combine_flags, AnalysisASMFile, LinkDefinition, MachineDegree, OperationSymbol,
    },
    object::{Link, LinkFrom, LinkTo, Location, MachineInstanceGraph, Object, Operation},
    parsed::{
        asm::{parse_absolute_path, AbsoluteSymbolPath, CallableRef, MachineParams},
        Expression, PilStatement,
    },
};

use itertools::Either;
use itertools::Itertools;

use powdr_number::BigUint;

const MAIN_MACHINE: &str = "::Main";

pub fn compile(input: AnalysisASMFile) -> MachineInstanceGraph {
    let main = Location::main();

    let non_std_non_rom_machines = input
        .machines()
        .filter(|(k, _)| k.parts().next() != Some("std"))
        .filter(|(k, _)| !k.parts().last().unwrap().ends_with("ROM"))
        .collect::<BTreeMap<_, _>>();

    // we start from the main machine
    let main_ty = match non_std_non_rom_machines.len() {
        0 => {
            // There is no machine. Create an empty main machine but retain
            // all PIL utility definitions.
            let zero_expr = Expression::from(BigUint::from(0u8));
            let degree = MachineDegree {
                min: Some(zero_expr.clone()),
                max: Some(zero_expr),
            };
            let obj: Object = Object {
                degree,
                ..Default::default()
            };
            return MachineInstanceGraph {
                main: main.clone(),
                objects: [(main, obj)].into(),
                statements: module_level_pil_statements(input),
            };
        }
        // if there is a single machine, treat it as main
        1 => (*non_std_non_rom_machines.keys().next().unwrap()).clone(),
        // otherwise, use the machine called `MAIN`
        _ => {
            let p = parse_absolute_path(MAIN_MACHINE);
            assert!(input.get_machine(&p).is_some());
            p
        }
    };

    // get a list of all machines to instantiate and their arguments. The order does not matter.
    let mut queue = vec![(
        main.clone(),
        Instance {
            machine_ty: main_ty.clone(),
            submachine_locations: vec![],
            min_degree: None,
            max_degree: None,
        },
    )];

    // map instance location to (type, arguments)
    let mut instances = BTreeMap::default();

    while let Some((
        location,
        Instance {
            machine_ty,
            submachine_locations,
            min_degree,
            max_degree,
        },
    )) = queue.pop()
    {
        let machine = &input.get_machine(&machine_ty).unwrap();

        queue.extend(machine.submachines.iter().map(|def| {
            let called_machine = &input.get_machine(&def.ty).unwrap();
            // we need to pass at least as many arguments as we have submachines
            assert!(def.args.len() >= called_machine.params.0.len());
            // and at most as many as submachines plus a min degree and a max degree
            assert!(def.args.len() <= called_machine.params.0.len() + 2);
            let mut def_args = def.args.clone().into_iter();
            let submachine_args: Vec<_> = (&mut def_args)
                .take(called_machine.params.0.len())
                .collect();
            let min_degree = def_args.next();
            let max_degree = def_args.next();

            (
                // get the absolute name for this submachine
                location.clone().join(def.name.clone()),
                Instance {
                    machine_ty: def.ty.clone(),
                    // resolve each given machine arg to a proper instance location
                    submachine_locations: submachine_args
                        .iter()
                        .map(|a| {
                            resolve_submachine_arg(&location, machine, &submachine_locations, a)
                        })
                        .collect(),
                    min_degree,
                    max_degree,
                },
            )
        }));

        instances.insert(
            location,
            Instance {
                machine_ty,
                submachine_locations,
                min_degree,
                max_degree,
            },
        );
    }

    // visit the tree compiling the machines
    let objects: BTreeMap<_, _> = instances
        .keys()
        .map(|location| {
            let object = ASMPILConverter::convert_machine(&instances, location, &input);
            (location.clone(), object)
        })
        .collect();

    MachineInstanceGraph {
        main,
        objects,
        statements: module_level_pil_statements(input),
    }
}

// resolve argument in a submachine declaration to a machine instance location
fn resolve_submachine_arg(
    location: &Location,
    machine: &asm_analysis::Machine,
    args: &[Location],
    submachine_arg: &Expression,
) -> Location {
    // We only support machine instances as arguments. This has already been checked before
    let id = submachine_arg.try_to_identifier().unwrap().clone();
    if let Some((_, arg)) = machine
        .params
        .0
        .iter()
        .zip(args.iter())
        .find(|(param, _)| param.name == id)
    {
        // argument is the name of a parameter, pass it forward
        arg.clone()
    } else {
        // argument is the name of another submachine, join with current location
        location.clone().join(id)
    }
}

/// Returns the pil statements at module level for each module.
fn module_level_pil_statements(
    asm_file: AnalysisASMFile,
) -> BTreeMap<AbsoluteSymbolPath, Vec<PilStatement>> {
    asm_file
        .modules
        .into_iter()
        .map(|(module_path, module)| (module_path, module.into_inner().1))
        .collect()
}

struct SubmachineRef {
    /// local name for this instance
    pub name: String,
    /// machine instance location
    pub location: Location,
    /// type of the submachine
    pub ty: AbsoluteSymbolPath,
}

struct Instance {
    machine_ty: AbsoluteSymbolPath,
    submachine_locations: Vec<Location>,
    min_degree: Option<Expression>,
    max_degree: Option<Expression>,
}

struct ASMPILConverter<'a> {
    /// Map of all machine instances to their type and passed arguments
    instances: &'a BTreeMap<Location, Instance>,
    /// Current machine instance
    location: &'a Location,
    /// Input definitions and machines.
    input: &'a AnalysisASMFile,
    /// Pil statements generated for the machine
    pil: Vec<PilStatement>,
    /// Submachine instances accessible to the machine (includes those passed as a parameter)
    submachines: Vec<SubmachineRef>,
}

impl<'a> ASMPILConverter<'a> {
    fn new(
        instances: &'a BTreeMap<Location, Instance>,
        location: &'a Location,
        input: &'a AnalysisASMFile,
    ) -> Self {
        Self {
            instances,
            location,
            input,
            pil: Default::default(),
            submachines: Default::default(),
        }
    }

    fn handle_pil_statement(&mut self, statement: PilStatement) {
        self.pil.push(statement);
    }

    fn convert_machine(
        instances: &'a BTreeMap<Location, Instance>,
        location: &'a Location,
        input: &'a AnalysisASMFile,
    ) -> Object {
        Self::new(instances, location, input).convert_machine_inner()
    }

    fn convert_machine_inner(mut self) -> Object {
        let instance = self.instances.get(self.location).unwrap();

        // TODO: This clone doubles the current memory usage
        let input = self
            .input
            .get_machine(&instance.machine_ty)
            .unwrap()
            .clone();

        // the passed degrees have priority over the ones defined in the machine type
        let min = instance.min_degree.clone().or(input.degree.min);
        let max = instance.max_degree.clone().or(input.degree.max);
        let degree = MachineDegree { min, max };

        self.submachines = input
            .submachines
            .into_iter()
            .map(|m| SubmachineRef {
                location: self.location.clone().join(m.name.clone()),
                name: m.name,
                ty: m.ty,
            })
            .collect();

        // machines should only have constraints, operations and links at this point
        assert!(input.instructions.is_empty());
        assert!(input.registers.is_empty());
        assert!(input.callable.is_only_operations());

        // process machine parameters
        self.handle_parameters(input.params, &instance.submachine_locations);

        for block in input.pil {
            self.handle_pil_statement(block);
        }

        let links = self.process_and_merge_links(&input.links[..]);

        Object {
            degree,
            pil: self.pil,
            links,
            latch: input.latch,
            call_selectors: input.call_selectors,
            operation_id: input.operation_id,
            operations: input
                .callable
                .into_iter()
                .map(|d| {
                    let operation_symbol: OperationSymbol = d.symbol.try_into().unwrap();

                    (
                        d.name.to_string(),
                        Operation {
                            id: operation_symbol.id.id.clone(),
                            params: operation_symbol.params.clone(),
                        },
                    )
                })
                .collect(),
        }
    }

    // Convert a link definition to a link, doing some basic checks in the process
    fn handle_link_def(
        &self,
        LinkDefinition {
            source: _,
            instr_flag,
            link_flag,
            to:
                CallableRef {
                    instance,
                    callable,
                    params,
                },
            is_permutation,
        }: LinkDefinition,
    ) -> Link {
        let from = LinkFrom {
            params,
            instr_flag,
            link_flag,
        };

        // get the type name for this submachine from the submachine declarations and parameters
        let instance = self
            .submachines
            .iter()
            .find(|s| s.name == instance)
            .unwrap_or_else(|| {
                let ty = &self.instances.get(self.location).unwrap().machine_ty;
                panic!("could not find submachine named `{instance}` in machine `{ty}`");
            });
        // get the machine type from the machine map
        let instance_ty = &self.input.get_machine(&instance.ty).unwrap();

        // check that the operation exists and that it has the same number of inputs/outputs as the link
        let operation = instance_ty
            .operation_definitions()
            .find(|o| o.name == callable)
            .unwrap_or_else(|| {
                panic!(
                    "function/operation not found: {}.{}",
                    &instance.name, callable
                )
            });
        assert_eq!(
            operation.operation.params.inputs.len(),
            from.params.inputs.len(),
            "link and operation have different number of inputs"
        );
        assert_eq!(
            operation.operation.params.outputs.len(),
            from.params.outputs.len(),
            "link and operation have different number of outputs"
        );

        Link {
            from,
            to: instance_ty
                .operation_definitions()
                .find(|o| o.name == callable)
                .map(|d| LinkTo {
                    machine: instance.location.clone(),
                    operation: d.name.to_string(),
                })
                .unwrap()
                .clone(),
            is_permutation,
        }
    }

    /// Process each link and then combine compatible links.
    /// Links can be merged iff:
    /// - they originate from the same machine instance
    /// - they target the same instance.operation
    /// - they are of the same kind (permutation/lookup)
    /// - their flags are mutually exclusive
    ///
    /// Right now we only consider links from different instructions,
    /// as a single instruction can be active at a time.
    fn process_and_merge_links(&self, defs: &[LinkDefinition]) -> Vec<Link> {
        /// Helper struct to group links that can potentially be merged.
        /// Besides these being equal, the links must be mutually exclusive (e.g., come from different instructions)
        #[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
        struct LinkInfo {
            from: Location,
            to: Location,
            operation: String,
            is_permutation: bool,
        }

        // process links, partitioning them into (mergeable, non-mergeable)
        let (mergeable_links, mut links): (Vec<_>, Vec<_>) = defs.iter().partition_map(|l| {
            let link = self.handle_link_def(l.clone());
            let info = LinkInfo {
                from: self.location.clone(),
                to: link.to.machine.clone(),
                operation: link.to.operation.clone(),
                is_permutation: link.is_permutation,
            };

            if link.from.instr_flag.is_none() {
                // only merge links that from instructions
                Either::Right(link)
            } else if link
                .from
                .params
                .inputs_and_outputs()
                .any(|p| p.contains_next_ref())
            {
                // TODO: links with next references can't be merged due to a witgen limitation.
                // This else if can be removed when witgen supports it.
                Either::Right(link)
            } else {
                // mergeable
                Either::Left((info, link))
            }
        });

        // group links into compatible sets, the idea here is:
        // - group by LinkInfo
        // - inside each group, separate links into sets of mutually exclusive flags (that is, from different instructions)
        let mut grouped_links: BTreeMap<LinkInfo, Vec<BTreeMap<Expression, Link>>> =
            Default::default();
        for (info, link) in mergeable_links {
            // add to an existing compatible set where the instr flag is not yet present
            let e = grouped_links.entry(info).or_default();
            if let Some(link_set) = e
                .iter_mut()
                .find(|link_set| !link_set.contains_key(link.from.instr_flag.as_ref().unwrap()))
            {
                link_set.insert(link.from.instr_flag.clone().unwrap(), link);
            } else {
                // otherwise, create a new set
                let mut new_set = BTreeMap::new();
                new_set.insert(link.from.instr_flag.clone().unwrap(), link);
                e.push(new_set);
            }
        }

        // merge link sets
        let merged_links = grouped_links
            .into_values()
            .flatten()
            .filter_map(|link_set| {
                // single link set, we don't need to combine the flag with inputs/outputs
                if link_set.len() == 1 {
                    return link_set.into_values().next();
                }

                // Merge links in set. Merging two links consists of adding their respective flags and inputs/outputs.
                // For example (asm and respective pil):
                //    instr foo X, Y -> Z link => Z = m.add(X, Y);
                //    instr_foo { 0, X, Y, Z } in m.latch { m.op_id, m.x, m.y, m.z };
                // and:
                //    instr bar X, Z -> Y link => Y = m.add(X, Z);
                //    instr_bar { 0, X, Z, Y } in m.latch { m.op_id, m.x, m.y, m.z };
                // would be combined into the following link:
                //    instr_foo + instr_bar { 0, X * instr_foo + X * instr_bar, Y * instr_foo + Z * instr_bar, Z * instr_bar + Y * instr_foo }
                //          in m.latch { m.op_id, m.x, m.y, m.z };
                link_set
                    .into_values()
                    .map(|mut link| {
                        // clear instruction flag by combining into the link flag, then combine it with inputs/outputs
                        link.from.link_flag =
                            combine_flags(link.from.instr_flag.take(), link.from.link_flag.clone());
                        link.from.params.inputs_and_outputs_mut().for_each(|p| {
                            *p = p.clone() * link.from.link_flag.clone();
                        });
                        link
                    })
                    .reduce(|mut a, b| {
                        // add flags and inputs/outputs of the two links
                        assert_eq!(a.from.params.inputs.len(), b.from.params.inputs.len());
                        assert_eq!(a.from.params.outputs.len(), b.from.params.outputs.len());
                        a.from.link_flag = a.from.link_flag + b.from.link_flag;
                        a.from
                            .params
                            .inputs_and_outputs_mut()
                            .zip(b.from.params.inputs_and_outputs())
                            .for_each(|(pa, pb)| {
                                *pa = pa.clone() + pb.clone();
                            });
                        a
                    })
            });
        links.extend(merged_links);
        links
    }

    // Process machine parameters (already resolved to machine instance locations)
    fn handle_parameters(&mut self, MachineParams(params): MachineParams, values: &Vec<Location>) {
        if params.len() != values.len() {
            panic!(
                "wrong number of arguments for machine `{}`: got {} expected {}",
                self.location,
                values.len(),
                params.len()
            );
        }

        for (param, value) in params.iter().zip(values) {
            let ty = AbsoluteSymbolPath::default().join(param.ty.clone().unwrap());
            match self.input.get_machine(&ty) {
                Some(_) => self.submachines.push(SubmachineRef {
                    location: value.clone(),
                    name: param.name.clone(),
                    ty,
                }),
                _ => unimplemented!("asm machines do not support non-machine parameters"),
            }
        }
    }
}

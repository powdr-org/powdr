use std::collections::{HashMap, HashSet};
use std::iter::once;

use powdr_ast::parsed::asm::{parse_absolute_path, AbsoluteSymbolPath};
use powdr_ast::{
    asm_analysis::{AnalysisASMFile, Machine},
    parsed::NamespacedPolynomialReference,
};
use powdr_pilopt::referenced_symbols::ReferencedSymbols;

type Expression = powdr_ast::asm_analysis::Expression<NamespacedPolynomialReference>;

const MAIN_MACHINE_STR: &str = "::Main";
const PC_REGISTER: &str = "pc";

pub fn optimize(mut analyzed_asm: AnalysisASMFile) -> AnalysisASMFile {
    // Optimizations assume the existence of a Main machine as an entry point.
    // If it doesn't exist, return the ASM as-is to prevent removing all machines,
    // which would break some examples.
    let main_machine_path = parse_absolute_path(MAIN_MACHINE_STR);
    if analyzed_asm
        .machines()
        .all(|(path, _)| path != main_machine_path)
    {
        return analyzed_asm;
    }

    asm_remove_unreferenced_machines(&mut analyzed_asm);
    asm_remove_unused_machine_components(&mut analyzed_asm);
    asm_remove_unreferenced_machines(&mut analyzed_asm);

    analyzed_asm
}

/// Remove all machines that are not referenced in any other machine.
/// This function traverses the dependency graph starting from ::Main to identify all reachable machines.
fn asm_remove_unreferenced_machines(asm_file: &mut AnalysisASMFile) {
    let deps = build_machine_dependencies(asm_file);
    let all_machines = collect_all_dependent_machines(&deps, MAIN_MACHINE_STR)
        .into_iter()
        .collect::<HashSet<_>>();
    asm_file.modules.iter_mut().for_each(|(path, module)| {
        let machines_in_module = machines_in_module(&all_machines, path);
        module.retain_machines(machines_in_module);
    });
}

/// Analyzes each machine and successively removes unnecessary components:
/// 1. Removes declarations of instructions that are never used.
/// 2. Removes instances of submachines that are never used, including those that became unused in the previous step.
/// 3. Removes unused registers.
fn asm_remove_unused_machine_components(asm_file: &mut AnalysisASMFile) {
    for (_, machine) in asm_file.machines_mut() {
        let submachine_to_decl: HashMap<String, String> = machine
            .submachines
            .iter()
            .map(|sub| (sub.name.clone(), sub.ty.to_string()))
            .collect();

        let symbols_in_callable: HashSet<String> = machine_callable_body_symbols(machine).collect();

        machine_remove_unused_instructions(machine, &symbols_in_callable);
        machine_remove_unused_submachines(machine, &symbols_in_callable, &submachine_to_decl);
        machine_remove_unused_registers(machine, &submachine_to_decl);
    }
}

fn machine_remove_unused_registers(
    machine: &mut Machine,
    submachine_to_decl: &HashMap<String, String>,
) {
    let used_symbols: HashSet<_> = once(PC_REGISTER.to_string())
        .chain(machine_callable_body_symbols(machine))
        .chain(machine_in_links(machine, submachine_to_decl))
        .chain(machine_instructions_symbols(machine))
        .chain(machine_links_symbols(machine))
        .collect();

    machine
        .registers
        .retain(|reg| used_symbols.contains(&reg.name));
}

fn machine_remove_unused_submachines(
    machine: &mut Machine,
    symbols: &HashSet<String>,
    submachine_to_decl: &HashMap<String, String>,
) {
    let visited_submachines = machine
        .instructions
        .iter()
        .filter(|ins| symbols.contains(&ins.name))
        .flat_map(|ins| {
            ins.instruction
                .links
                .iter()
                .filter_map(|link| submachine_to_decl.get(&link.link.instance))
        })
        .cloned();

    let used_submachines: HashSet<_> = visited_submachines
        .chain(machine_in_links(machine, submachine_to_decl))
        .chain(machine_in_args(machine, submachine_to_decl))
        .chain(symbols.iter().cloned())
        .collect();

    machine
        .submachines
        .retain(|sub| used_submachines.contains(&sub.ty.to_string()));
}

fn machine_remove_unused_instructions(machine: &mut Machine, symbols: &HashSet<String>) {
    machine
        .instructions
        .retain(|ins| symbols.contains(&ins.name));
}

/// Retrieves all machines defined within a specific module, relative to the given module path.
///
/// This function filters the provided set of all machine paths to include only those machines
/// that are defined within the module specified by `path`. It then strips the module path prefix from each
/// machine path to return the machine names relative to that module.
fn machines_in_module(
    all_machines: &HashSet<String>,
    path: &AbsoluteSymbolPath,
) -> HashSet<String> {
    let path_str = path.to_string();
    let path_prefix = if path_str == "::" {
        "::".to_string()
    } else {
        format!("{}{}", path_str, "::")
    };

    all_machines
        .iter()
        .filter(|machine_path| machine_path.starts_with(&path_prefix))
        .map(|machine_path| {
            machine_path
                .strip_prefix(&path_prefix)
                .unwrap_or(machine_path)
                .to_string()
        })
        .collect()
}

/// Creates a mapping between machine names and sets of paths for their instantiated submachines.
fn build_machine_dependencies(asm_file: &AnalysisASMFile) -> HashMap<String, HashSet<String>> {
    let mut dependencies = HashMap::new();

    for (path, machine) in asm_file.machines() {
        let submachine_to_decl: HashMap<String, String> = machine
            .submachines
            .iter()
            .map(|sub| (sub.name.clone(), sub.ty.to_string()))
            .collect();

        let submachine_names = dependencies_by_machine(machine, submachine_to_decl);
        dependencies.insert(path.to_string(), submachine_names);
    }

    dependencies
}

/// This function analyzes a given `Machine` and gathers all the submachines it depends on.
/// Dependencies are collected from various components of the machine:
///
/// 1. Instantiated Submachines: Submachines that are directly instantiated within the machine.
/// 2. Submachine Arguments: Submachines referenced in the arguments of the instantiated submachines.
/// 3. Parameters: Submachines specified in the machine's parameters.
/// 4. Links: Submachines that are used in links within the machine.
fn dependencies_by_machine(
    machine: &Machine,
    submachine_to_decl: HashMap<String, String>,
) -> HashSet<String> {
    let submachine_names: HashSet<String> = machine
        .submachines
        .iter()
        .map(|sub| sub.ty.to_string())
        .chain(machine.submachines.iter().flat_map(|sub| {
            sub.args.iter().filter_map(|expr| {
                expr_to_ref(expr).and_then(|ref_name| submachine_to_decl.get(&ref_name).cloned())
            })
        }))
        .chain(
            machine
                .params
                .0
                .iter()
                .map(|param| param.ty.as_ref().unwrap().to_string()),
        )
        .chain(
            machine
                .links
                .iter()
                .filter_map(|ld| submachine_to_decl.get(&ld.to.instance))
                .cloned(),
        )
        .collect();
    submachine_names
}

fn expr_to_ref(expr: &Expression) -> Option<String> {
    match expr {
        Expression::Reference(_, NamespacedPolynomialReference { path, .. }) => {
            Some(path.to_string())
        }
        Expression::PublicReference(_, pref) => Some(pref.clone()),
        _ => None,
    }
}

fn collect_all_dependent_machines(
    dependencies: &HashMap<String, HashSet<String>>,
    start: &str,
) -> HashSet<String> {
    let mut result = HashSet::new();
    let mut to_visit = vec![start.to_string()];
    let mut visited = HashSet::new();

    while let Some(machine) = to_visit.pop() {
        if visited.insert(machine.clone()) {
            result.insert(machine.clone());

            if let Some(submachines) = dependencies.get(&machine) {
                to_visit.extend(submachines.iter().cloned());
            }
        }
    }

    result
}

fn machine_callable_body_symbols(machine: &Machine) -> impl Iterator<Item = String> + '_ {
    machine.callable.function_definitions().flat_map(|def| {
        def.symbols()
            .map(|s| s.name.to_string())
            .collect::<Vec<_>>()
    })
}

fn machine_instructions_symbols(machine: &Machine) -> impl Iterator<Item = String> + '_ {
    machine
        .instructions
        .iter()
        .flat_map(|ins| ins.symbols().map(|s| s.name.to_string()))
}

fn machine_links_symbols(machine: &Machine) -> impl Iterator<Item = String> + '_ {
    machine
        .links
        .iter()
        .flat_map(|ld| ld.symbols().map(|s| s.name.to_string()))
}

fn machine_in_args<'a>(
    machine: &'a Machine,
    submachine_to_decl: &'a HashMap<String, String>,
) -> impl Iterator<Item = String> + 'a {
    machine
        .submachines
        .iter()
        .flat_map(|sm| sm.args.iter().filter_map(expr_to_ref))
        .filter_map(|ref_name| submachine_to_decl.get(&ref_name))
        .cloned()
}

fn machine_in_links<'a>(
    machine: &'a Machine,
    submachine_to_decl: &'a HashMap<String, String>,
) -> impl Iterator<Item = String> + 'a {
    machine
        .links
        .iter()
        .filter_map(move |ld| submachine_to_decl.get(&ld.to.instance))
        .cloned()
}

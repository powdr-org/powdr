use ibig::UBig;
use powdr_analysis::utils::parse_pil_statement;
use powdr_ast::{
    asm_analysis::MachineDegree,
    object::{Link, Location, MachineInstanceGraph, Object},
    parsed::{asm::AbsoluteSymbolPath, NamespaceDegree, PILFile, PilStatement},
};
use powdr_parser_util::SourceRef;
use std::{collections::BTreeMap, iter::once};
use strum::{Display, EnumString, EnumVariantNames};

/// A linker implementation using the bus
pub mod bus;
/// A linker implementation using native lookups and permutations
pub mod native;

const MAIN_OPERATION_NAME: &str = "main";
const LINKER_FIRST_STEP: &str = "_linker_first_step";

/// Link the objects into a single PIL file, using the specified parameters.
pub fn link(graph: MachineInstanceGraph, params: LinkerParams) -> Result<PILFile, Vec<String>> {
    match params.mode {
        LinkerMode::Native => native::NativeLinker::link(graph, params.degree_mode),
        LinkerMode::Bus => bus::BusLinker::link(graph, params.degree_mode),
    }
}

/// A trait for linker backends
trait LinkerBackend: Sized {
    /// Create a new linker instance from the given graph and degree mode.
    /// This can fail, for example if the linker does not support the given degree mode.
    fn try_new(graph: &MachineInstanceGraph, degree_mode: DegreeMode) -> Result<Self, Vec<String>>;

    /// Link the objects into a single PIL file.
    fn link(graph: MachineInstanceGraph, degree_mode: DegreeMode) -> Result<PILFile, Vec<String>> {
        let mut linker = Self::try_new(&graph, degree_mode)?;

        let common_definitions = process_definitions(graph.statements);

        for location in graph.objects.keys() {
            linker.process_object(location, &graph.objects);
        }

        Ok(PILFile(
            common_definitions
                .into_iter()
                .chain(linker.into_pil())
                .collect(),
        ))
    }

    /// Process an object at a given location.
    fn process_object(&mut self, location: &Location, objects: &BTreeMap<Location, Object>);

    /// Process a link between two machines, also passing the location at which the link is defined.
    fn process_link(&mut self, link: &Link, from: &Location, objects: &BTreeMap<Location, Object>);

    /// Convert the linker's internal state into PIL statements.
    fn into_pil(self) -> Vec<PilStatement>;
}

fn call(operation_id_name: &str, operation_id_value: &UBig) -> Vec<PilStatement> {
    // call the operation by initializing `operation_id` to that of the operation
    vec![
        parse_pil_statement(&format!(
            "col fixed {LINKER_FIRST_STEP}(i) {{ if i == 0 {{ 1 }} else {{ 0 }} }};"
        )),
        parse_pil_statement(&format!(
            "{LINKER_FIRST_STEP} * ({operation_id_name} - {operation_id_value}) = 0;"
        )),
    ]
}

#[derive(Clone, Copy, Default)]
pub struct LinkerParams {
    pub mode: LinkerMode,
    pub degree_mode: DegreeMode,
}

#[derive(Clone, EnumString, EnumVariantNames, Display, Copy, Default)]
/// Whether to link the machines natively or via a global bus.
pub enum LinkerMode {
    #[default]
    #[strum(serialize = "native")]
    Native,
    #[strum(serialize = "bus")]
    Bus,
}

#[derive(Clone, EnumString, EnumVariantNames, Display, Copy, Default)]
/// Whether to align the degrees of all machines to the main machine, or to use the degrees of the individual machines.
pub enum DegreeMode {
    #[strum(serialize = "monolithic")]
    Monolithic,
    #[default]
    #[strum(serialize = "vadcop")]
    Vadcop,
}

#[derive(Clone, Copy, PartialEq)]
enum InteractionType {
    Lookup,
    Permutation,
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

/// Convert a [MachineDegree] into a [NamespaceDegree]
fn try_into_namespace_degree(d: MachineDegree) -> Option<NamespaceDegree> {
    let min = d.min?;
    let max = d.max?;
    Some(NamespaceDegree { min, max })
}

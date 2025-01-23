use std::{
    borrow::Borrow,
    collections::HashMap,
    fmt::Display,
    fs,
    io::{self, BufReader, BufWriter, Write},
    path::{Path, PathBuf},
    rc::Rc,
    sync::Arc,
    time::Instant,
};

use crate::util::PolySet;
use log::Level;
use mktemp::Temp;
use powdr_ast::{
    analyzed::Analyzed,
    asm_analysis::AnalysisASMFile,
    object::MachineInstanceGraph,
    parsed::{asm::ASMProgram, PILFile},
};
use powdr_backend::{Backend, BackendOptions, BackendType, Proof};
use powdr_executor::{
    constant_evaluator::{self, VariablySizedColumn},
    witgen::{
        chain_callbacks, extract_publics, unused_query_callback, QueryCallback, WitgenCallback,
        WitgenCallbackContext, WitnessGenerator,
    },
};
pub use powdr_linker::{DegreeMode, LinkerMode, LinkerParams};
use powdr_number::{write_polys_csv_file, CsvRenderMode, FieldElement, ReadWrite};
use powdr_schemas::SerializedAnalyzed;

use crate::{
    dict_data_to_query_callback, handle_simple_queries_callback, inputs_to_query_callback,
    serde_data_to_query_callback,
    util::{FixedPolySet, WitnessPolySet},
};
use std::collections::BTreeMap;

pub type Columns<T> = Vec<(String, Vec<T>)>;
pub type VariablySizedColumns<T> = Vec<(String, VariablySizedColumn<T>)>;

#[derive(Default)]
pub struct Artifacts<T: FieldElement> {
    /// The path to a single .asm file.
    asm_file_path: Option<PathBuf>,
    /// The contents of a single .asm file, with an optional Path (for imports).
    asm_string: Option<(Option<PathBuf>, String)>,
    /// A parsed .asm file, with an optional Path (for imports).
    parsed_asm_file: Option<(Option<PathBuf>, ASMProgram)>,
    /// A tree of .asm modules (with all dependencies potentially imported
    /// from other files) with all references resolved to absolute symbol paths.
    resolved_module_tree: Option<ASMProgram>,
    /// The machine checked .asm file.
    checked_asm: Option<AnalysisASMFile>,
    /// The analyzed .asm file: Assignment registers are inferred, instructions
    /// are batched and some properties are checked.
    analyzed_asm: Option<AnalysisASMFile>,
    /// The optimized version of the analyzed ASM file.
    optimized_asm: Option<AnalysisASMFile>,
    /// A machine collection that only contains constrained machines.
    constrained_machine_collection: Option<AnalysisASMFile>,
    /// The airgen graph, i.e. a collection of constrained machines with resolved
    /// links between them.
    linked_machine_graph: Option<MachineInstanceGraph>,
    /// A single parsed pil file.
    parsed_pil_file: Option<PILFile>,
    /// The path to a single .pil file.
    pil_file_path: Option<PathBuf>,
    /// The contents of a single .pil file.
    pil_string: Option<String>,
    /// An analyzed .pil file, with all dependencies imported, potentially from other files.
    analyzed_pil: Option<Analyzed<T>>,
    /// An optimized .pil file.
    optimized_pil: Option<Arc<Analyzed<T>>>,
    /// Fully evaluated fixed columns.
    fixed_cols: Option<Arc<VariablySizedColumns<T>>>,
    /// Generated witnesses.
    witness: Option<Arc<Columns<T>>>,
    /// Instantiated backend.
    backend: Option<Box<dyn Backend<T>>>,
    /// The proof (if successful).
    proof: Option<Proof>,
}

/// Helper trait to make it prettier to get an `Option<&mut dyn io::Read>`` from
/// an `Option<F: io::Read>`.
trait AsIoRead {
    fn as_io_read(&mut self) -> Option<&mut dyn io::Read>;
}

impl<R: io::Read> AsIoRead for Option<R> {
    fn as_io_read(&mut self) -> Option<&mut dyn io::Read> {
        self.as_mut().map(|r| r as &mut dyn io::Read)
    }
}

/// Optional Arguments for various stages of the pipeline.
#[derive(Default, Clone)]
struct Arguments<T: FieldElement> {
    /// Externally computed witness values for witness generation.
    external_witness_values: Vec<(String, Vec<T>)>,
    /// Callback for queries for witness generation.
    query_callback: Option<Arc<dyn QueryCallback<T>>>,
    /// Backend to use for proving. If None, proving will fail.
    backend: Option<BackendType>,
    /// Backend options
    backend_options: BackendOptions,
    /// Linker options
    linker_params: LinkerParams,
    /// CSV render mode for witness generation.
    csv_render_mode: CsvRenderMode,
    /// Whether to export the witness as a CSV file.
    export_witness_csv: bool,
    /// Whether to export all columns (witness and constants) to a CSV file.
    export_all_columns_csv: bool,
    /// The optional setup file to use for proving.
    setup_file: Option<PathBuf>,
    /// The optional proving key file to use for proving.
    pkey_file: Option<PathBuf>,
    /// The optional verification key file to use for proving.
    vkey_file: Option<PathBuf>,
    /// The optional verification key file to use for recursive proving.
    vkey_app_file: Option<PathBuf>,
    /// The optional existing proof file to use for aggregation.
    existing_proof_file: Option<PathBuf>,
}

#[derive(Clone)]
pub struct Pipeline<T: FieldElement> {
    /// Stores all artifacts at the same time.
    artifact: Artifacts<T>,
    /// Output directory for intermediate files. If None, no files are written.
    output_dir: Option<PathBuf>,
    /// The temporary directory, owned by the pipeline (or any copies of it).
    /// This object is not used directly, but keeping it here ensures that the directory
    /// is not deleted until the pipeline is dropped.
    _tmp_dir: Option<Rc<Temp>>,
    /// The name of the pipeline. Used to name output files.
    name: Option<String>,
    /// Whether to overwrite existing files. If false, an error is returned if a file
    /// already exists.
    force_overwrite: bool,
    /// Whether to output the serialized pil object (.pilo)
    pilo: bool,
    /// The log level to use for this pipeline.
    log_level: Level,
    /// Optional arguments for various stages of the pipeline.
    arguments: Arguments<T>,
    /// The context for the host.
    host_context: HostContext,
    /// Initial memory given by the prover.
    initial_memory: Vec<Vec<u8>>,
}

impl<T: FieldElement> Clone for Artifacts<T> {
    fn clone(&self) -> Self {
        Artifacts {
            asm_file_path: self.asm_file_path.clone(),
            asm_string: self.asm_string.clone(),
            parsed_asm_file: self.parsed_asm_file.clone(),
            resolved_module_tree: self.resolved_module_tree.clone(),
            checked_asm: self.checked_asm.clone(),
            analyzed_asm: self.analyzed_asm.clone(),
            optimized_asm: self.optimized_asm.clone(),
            constrained_machine_collection: self.constrained_machine_collection.clone(),
            linked_machine_graph: self.linked_machine_graph.clone(),
            parsed_pil_file: self.parsed_pil_file.clone(),
            pil_file_path: self.pil_file_path.clone(),
            pil_string: self.pil_string.clone(),
            analyzed_pil: self.analyzed_pil.clone(),
            optimized_pil: self.optimized_pil.clone(),
            fixed_cols: self.fixed_cols.clone(),
            witness: self.witness.clone(),
            proof: self.proof.clone(),
            // Backend is not cloneable, so we clear it instead
            backend: None,
        }
    }
}

use super::HostContext;

impl<T> Default for Pipeline<T>
where
    T: FieldElement,
{
    fn default() -> Self {
        let (ctx, cb) = HostContext::new();
        Pipeline {
            artifact: Default::default(),
            output_dir: None,
            _tmp_dir: None,
            log_level: Level::Info,
            name: None,
            force_overwrite: false,
            pilo: false,
            arguments: Arguments::default(),
            host_context: ctx,
            initial_memory: vec![],
        }
        // We add the basic callback functionalities to support PrintChar and Hint.
        .add_query_callback(Arc::new(handle_simple_queries_callback()))
        .add_query_callback(cb)
    }
}

/// A Powdr pipeline, going from a PIL or ASM file to a proof.
///
/// The pipeline steps are:
/// ```mermaid
///  graph TD
///      AsmFilePath --> AsmString
///      AsmString --> ParsedAsmFile
///      ParsedAsmFile --> ResolvedModuleTree
///      ResolvedModuleTree --> AnalyzedAsm
///      AnalyzedAsm --> ConstrainedMachineCollection
///      ConstrainedMachineCollection --> LinkedMachineGraph
///      LinkedMachineGraph --> ParsedPilFile
///      ParsedPilFile --> AnalyzedPil
///      PilFilePath --> AnalyzedPil
///      PilString --> AnalyzedPil
///      AnalyzedPil --> OptimizedPil
///      OptimizedPil --> FixedCols
///      OptimizedPil && FixedCols --> Witness
///      OptimizedPil && FixedCols && Witness --> Proof
/// ```
///
/// # Example
/// ```rust
/// use powdr_pipeline::{Pipeline, verify, BackendType, test_util::resolve_test_file};
/// use std::path::PathBuf;
/// use powdr_number::GoldilocksField;
///
/// let mut pipeline = Pipeline::<GoldilocksField>::default()
///   .from_file(resolve_test_file("pil/fibonacci.pil"))
///   .with_output(PathBuf::from("."), true)
///   .with_backend(BackendType::EStarkDump, Some("stark_gl".to_string()));
///
/// // Get the result
/// let proof = pipeline.compute_proof().unwrap();
/// ```
impl<T: FieldElement> Pipeline<T> {
    /// Initializes the output directory to a temporary directory which lives as long
    /// the pipeline does.
    pub fn with_tmp_output(self) -> Self {
        let tmp_dir = Rc::new(mktemp::Temp::new_dir().unwrap());
        Pipeline {
            output_dir: Some(tmp_dir.to_path_buf()),
            force_overwrite: true,
            _tmp_dir: Some(tmp_dir),
            ..self
        }
    }

    pub fn with_output(self, output_dir: PathBuf, force_overwrite: bool) -> Self {
        Pipeline {
            output_dir: Some(output_dir),
            force_overwrite,
            ..self
        }
    }

    pub fn set_output(&mut self, output_dir: PathBuf, force_overwrite: bool) {
        self.output_dir = Some(output_dir);
        self.force_overwrite = force_overwrite;
    }

    pub fn add_external_witness_values(
        mut self,
        external_witness_values: Vec<(String, Vec<T>)>,
    ) -> Self {
        for (name, _) in &external_witness_values {
            assert!(
                !self
                    .arguments
                    .external_witness_values
                    .iter()
                    .any(|(n, _)| n == name),
                "Duplicate witness column name: {name}"
            );
        }
        self.arguments
            .external_witness_values
            .extend(external_witness_values);
        self
    }

    pub fn add_external_witness_values_mut(
        &mut self,
        external_witness_values: Vec<(String, Vec<T>)>,
    ) {
        for (name, _) in &external_witness_values {
            assert!(
                !self
                    .arguments
                    .external_witness_values
                    .iter()
                    .any(|(n, _)| n == name),
                "Duplicate witness column name: {name}"
            );
        }
        self.arguments
            .external_witness_values
            .extend(external_witness_values);
    }

    /// Control what is exported to CSV files by the pipeline.
    pub fn with_witness_csv_settings(
        mut self,
        export_witness_csv: bool,
        export_all_columns_csv: bool,
        csv_render_mode: CsvRenderMode,
    ) -> Self {
        self.arguments.export_witness_csv = export_witness_csv;
        self.arguments.export_all_columns_csv = export_all_columns_csv;
        self.arguments.csv_render_mode = csv_render_mode;
        self
    }

    pub fn add_query_callback(mut self, query_callback: Arc<dyn QueryCallback<T>>) -> Self {
        let query_callback = match self.arguments.query_callback {
            Some(old_callback) => Arc::new(chain_callbacks(old_callback, query_callback)),
            None => query_callback,
        };
        self.arguments.query_callback = Some(query_callback);
        self
    }

    /// Adds data to the initial memory given by the prover.
    /// This is a more efficient method of passing bytes from the host
    /// to the guest.
    pub fn add_to_initial_memory(mut self, data: Vec<u8>) -> Self {
        self.initial_memory.push(data);
        self
    }

    pub fn initial_memory(&self) -> &[Vec<u8>] {
        &self.initial_memory
    }

    pub fn add_data<S: serde::Serialize>(self, channel: u32, data: &S) -> Self {
        let bytes = serde_cbor::to_vec(&data).unwrap();
        self.add_query_callback(Arc::new(serde_data_to_query_callback(channel, bytes)))
    }

    pub fn add_data_vec<S: serde::Serialize + 'static>(self, data: &[(u32, S)]) -> Self {
        data.iter()
            .fold(self, |pipeline, data| pipeline.add_data(data.0, &data.1))
    }

    pub fn with_prover_inputs(self, inputs: Vec<T>) -> Self {
        self.add_query_callback(Arc::new(inputs_to_query_callback(inputs)))
    }

    pub fn with_prover_dict_inputs(self, inputs: BTreeMap<u32, Vec<T>>) -> Self {
        self.add_query_callback(Arc::new(dict_data_to_query_callback(inputs)))
    }

    pub fn with_linker_params(mut self, linker_params: LinkerParams) -> Self {
        self.arguments.linker_params = linker_params;
        self
    }

    pub fn with_backend(mut self, backend: BackendType, options: Option<BackendOptions>) -> Self {
        self.arguments.backend = Some(backend);
        self.arguments.backend_options = options.unwrap_or_default();
        self.artifact.backend = None;
        self
    }

    pub fn with_setup_file(mut self, setup_file: Option<PathBuf>) -> Self {
        self.arguments.setup_file = setup_file;
        self.artifact.backend = None;
        self
    }

    pub fn with_pkey_file(mut self, pkey_file: Option<PathBuf>) -> Self {
        self.arguments.pkey_file = pkey_file;
        self.artifact.backend = None;
        self
    }

    pub fn set_pkey_file(&mut self, pkey_file: PathBuf) {
        self.arguments.pkey_file = Some(pkey_file);
    }

    pub fn with_vkey_file(mut self, vkey_file: Option<PathBuf>) -> Self {
        self.arguments.vkey_file = vkey_file;
        self.artifact.backend = None;
        self
    }

    pub fn set_vkey_file(&mut self, vkey_file: PathBuf) {
        self.arguments.vkey_file = Some(vkey_file);
    }

    pub fn with_vkey_app_file(mut self, vkey_app_file: Option<PathBuf>) -> Self {
        self.arguments.vkey_app_file = vkey_app_file;
        self.artifact.backend = None;
        self
    }

    pub fn with_existing_proof_file(mut self, existing_proof_file: Option<PathBuf>) -> Self {
        self.arguments.existing_proof_file = existing_proof_file;
        self
    }

    pub fn with_pil_object(mut self) -> Self {
        self.pilo = true;
        self
    }

    pub fn from_file(self, asm_file: PathBuf) -> Self {
        match asm_file.extension() {
            Some(ext) if ext.to_str().unwrap() == "asm" => self.from_asm_file(asm_file),
            Some(ext) if ext.to_str().unwrap() == "pil" => self.from_pil_file(asm_file),
            _ => panic!("expected a .pil or .asm file"),
        }
    }

    pub fn from_asm_file(self, asm_file: PathBuf) -> Self {
        let name = self.name.or(Some(Self::name_from_path(&asm_file)));
        Pipeline {
            artifact: Artifacts {
                asm_file_path: Some(asm_file),
                ..Default::default()
            },
            name,
            ..self
        }
    }

    pub fn from_asm_string(self, asm_string: String, path: Option<PathBuf>) -> Self {
        let name = self.name.or(path.as_ref().map(|p| Self::name_from_path(p)));
        Pipeline {
            artifact: Artifacts {
                asm_string: Some((path, asm_string)),
                ..Default::default()
            },
            name,
            ..self
        }
    }

    pub fn from_pil_file(self, pil_file: PathBuf) -> Self {
        let name = self.name.or(Some(Self::name_from_path(&pil_file)));
        Pipeline {
            artifact: Artifacts {
                pil_file_path: Some(pil_file),
                ..Default::default()
            },
            name,
            ..self
        }
    }

    pub fn from_pil_string(self, pil_string: String) -> Self {
        Pipeline {
            artifact: Artifacts {
                pil_string: Some(pil_string),
                ..Default::default()
            },
            ..self
        }
    }

    pub fn from_maybe_pil_object(self, file: PathBuf) -> Result<Self, Vec<String>> {
        if file.extension().unwrap() == "pilo" {
            self.from_pil_object(file)
        } else {
            Ok(self.from_file(file))
        }
    }

    pub fn from_pil_object(self, pil_file: PathBuf) -> Result<Self, Vec<String>> {
        let name = self
            .name
            .or(Some(Self::name_from_path_with_suffix(&pil_file)));

        let analyzed: Analyzed<T> = SerializedAnalyzed::deserialize_from(pil_file)
            .map_err(|e| vec![format!("Error deserializing .pilo file: {}", e)])?
            .try_into()
            .map_err(|e| vec![e])?;

        Ok(Pipeline {
            artifact: Artifacts {
                optimized_pil: Some(Arc::new(analyzed)),
                ..Default::default()
            },
            name,
            ..self
        })
    }

    /// Reads previously generated fixed columns from the provided directory.
    pub fn read_constants(self, directory: &Path) -> Result<Self, String> {
        let fixed = FixedPolySet::<T>::read(directory)?;

        Ok(Pipeline {
            artifact: Artifacts {
                fixed_cols: Some(Arc::new(fixed)),
                ..self.artifact
            },
            ..self
        })
    }

    /// Reads previously generated fixed columns from the provided directory.
    pub fn read_constants_mut(&mut self, directory: &Path) -> Result<(), String> {
        let fixed = FixedPolySet::<T>::read(directory)?;

        self.artifact.fixed_cols = Some(Arc::new(fixed));

        Ok(())
    }

    /// Reads a previously generated witness from the provided directory.
    pub fn read_witness(self, directory: &Path) -> Result<Self, String> {
        let witness = WitnessPolySet::<T>::read(directory)?;

        Ok(Pipeline {
            artifact: Artifacts {
                witness: Some(Arc::new(witness)),
                // we're changing the witness, clear the current proof
                proof: None,
                ..self.artifact
            },
            ..self
        })
    }

    /// Sets the witness to the provided value.
    pub fn set_witness(mut self, witness: Vec<(String, Vec<T>)>) -> Self {
        if self.output_dir.is_some() {
            // Some future steps (e.g. Pilcom verification) require the witness to be persisted.
            let fixed_cols = self.compute_fixed_cols().unwrap();
            self.maybe_write_witness(&fixed_cols, &witness).unwrap();
        }
        Pipeline {
            artifact: Artifacts {
                witness: Some(Arc::new(witness)),
                // we're changing the witness, clear the current proof
                proof: None,
                ..self.artifact
            },
            ..self
        }
    }

    fn name_from_path(path: &Path) -> String {
        path.file_stem().unwrap().to_str().unwrap().to_string()
    }

    // This is used for parsing file names than ends with '_{suffix}'
    fn name_from_path_with_suffix(path: &Path) -> String {
        let file_name = Self::name_from_path(path);
        let mut split = file_name.split('_').collect::<Vec<_>>();
        split.pop();
        split.join("_")
    }

    fn log(&self, msg: &str) {
        log::log!(self.log_level, "{}", msg);
    }

    /// Returns the path to the output file if the output directory is set.
    /// Fails if the file already exists and `force_overwrite` is false.
    fn path_if_should_write<F: FnOnce(&str) -> String>(
        &self,
        file_name_from_pipeline_name: F,
    ) -> Result<Option<PathBuf>, Vec<String>> {
        self.output_dir
            .as_ref()
            .map(|output_dir| {
                let name = self
                    .name
                    .as_ref()
                    .expect("name must be set if output_dir is set");
                let path = output_dir.join(file_name_from_pipeline_name(name));
                if path.exists() && !self.force_overwrite {
                    Err(vec![format!(
                        "{} already exists! Use --force to overwrite.",
                        path.to_str().unwrap()
                    )])?;
                }
                log::info!("Writing {}.", path.to_str().unwrap());
                Ok(path)
            })
            .transpose()
    }

    fn maybe_write_pil<C: Display>(&self, content: &C, suffix: &str) -> Result<(), Vec<String>> {
        if let Some(path) = self.path_if_should_write(|name| format!("{name}{suffix}.pil"))? {
            fs::write(&path, format!("{content}"))
                .map_err(|e| vec![format!("Error writing {}: {e}", path.to_str().unwrap())])?;
        }
        Ok(())
    }

    fn maybe_write_pil_object(&self, pil: &Analyzed<T>, suffix: &str) -> Result<(), Vec<String>> {
        if self.pilo {
            if let Some(path) = self.path_if_should_write(|name| format!("{name}{suffix}.pilo"))? {
                SerializedAnalyzed::try_from(pil)
                    .map_err(|e| vec![e])?
                    .serialize_to(path)
                    .map_err(|e| vec![e])?;
            }
        }
        Ok(())
    }

    fn maybe_write_constants(
        &self,
        constants: &VariablySizedColumns<T>,
    ) -> Result<(), Vec<String>> {
        if let Some(path) = self.path_if_should_write(|_| "constants.bin".to_string())? {
            constants.write(&path).map_err(|e| vec![format!("{}", e)])?;
        }
        Ok(())
    }

    fn maybe_write_witness(
        &self,
        fixed: &VariablySizedColumns<T>,
        witness: &Columns<T>,
    ) -> Result<(), Vec<String>> {
        if let Some(path) = self.path_if_should_write(|_| "commits.bin".to_string())? {
            witness.write(&path).map_err(|e| vec![format!("{}", e)])?;
        }

        if self.arguments.export_witness_csv {
            if let Some(path) = self.path_if_should_write(|name| format!("{name}_witness.csv"))? {
                let columns = witness
                    .iter()
                    .map(|(name, values)| (name, values.as_ref()))
                    .collect::<Vec<_>>();

                let csv_file = fs::File::create(path).map_err(|e| vec![format!("{}", e)])?;
                write_polys_csv_file(csv_file, self.arguments.csv_render_mode, &columns);
            }
        }

        if self.arguments.export_all_columns_csv {
            if let Some(path) =
                self.path_if_should_write(|name| format!("{name}_all_columns.csv"))?
            {
                // get the column size for each namespace. This assumes all witness columns of the same namespace have the same size.
                let witness_sizes: HashMap<&str, u64> = witness
                    .iter()
                    .map(|(name, values)| {
                        let namespace = name.split("::").next().unwrap();
                        (namespace, values.len() as u64)
                    })
                    .collect();

                // choose the fixed column of the correct size. This assumes any namespace with no witness columns has a unique size
                let fixed_columns = fixed.iter().map(|(name, columns)| {
                    let namespace = name.split("::").next().unwrap();
                    let columns = witness_sizes
                        .get(&namespace)
                        // if we have witness columns, use their size
                        .map(|size| columns.get_by_size(*size).unwrap())
                        // otherwise, return the unique size
                        .unwrap_or_else(|| columns.get_uniquely_sized().unwrap());
                    (name, columns)
                });

                let columns = fixed_columns
                    .chain(witness.iter().map(|(name, values)| (name, values.as_ref())))
                    .collect::<Vec<_>>();

                let csv_file = fs::File::create(path).map_err(|e| vec![format!("{}", e)])?;
                write_polys_csv_file(csv_file, self.arguments.csv_render_mode, &columns);
            }
        }

        Ok(())
    }

    fn maybe_write_proof(&self, proof: &Proof) -> Result<(), Vec<String>> {
        let fname = if self.arguments.existing_proof_file.is_some() {
            "proof_aggr.bin"
        } else {
            "proof.bin"
        };
        if let Some(path) = self.path_if_should_write(|name| format!("{name}_{fname}"))? {
            fs::write(path, proof).unwrap();
        }

        Ok(())
    }

    // Removes artifacts related to witgen and proofs.
    // This is useful for when a single pipeline is used for several proofs.
    // In that case, we want to keep the fixed columns and backend setup unmodified,
    // but give it different witnesses and generate different proofs.
    // The previous alternative to this was cloning the entire pipeline.
    pub fn rollback_from_witness(&mut self) {
        self.artifact.witness = None;
        self.artifact.proof = None;
        self.arguments.external_witness_values.clear();
    }

    pub fn rollback_from_checked_asm(&mut self) {
        self.rollback_from_witness();
        self.artifact.analyzed_asm = None;
        self.artifact.optimized_asm = None;
        self.artifact.constrained_machine_collection = None;
        self.artifact.linked_machine_graph = None;
        self.artifact.parsed_pil_file = None;
        self.artifact.pil_file_path = None;
        self.artifact.pil_string = None;
        self.artifact.analyzed_pil = None;
        self.artifact.optimized_pil = None;
        self.artifact.fixed_cols = None;
    }

    // ===== Compute and retrieve artifacts =====

    pub fn asm_file_path(&self) -> Result<&PathBuf, Vec<String>> {
        match self.artifact.asm_file_path {
            Some(ref path) => Ok(path),
            None => Err(vec!["No asm file path available".to_string()]),
        }
    }

    pub fn compute_asm_string(&mut self) -> Result<&(Option<PathBuf>, String), Vec<String>> {
        if self.artifact.asm_string.is_none() {
            self.artifact.asm_string = Some({
                let path = self.asm_file_path();
                let path = path?;
                (
                    Some(path.clone()),
                    fs::read_to_string(path).map_err(|e| {
                        vec![format!("Error reading .asm file: {}\n{e}", path.display())]
                    })?,
                )
            });
        }

        Ok(self.artifact.asm_string.as_ref().unwrap())
    }

    pub fn asm_string(&self) -> Result<&(Option<PathBuf>, String), Vec<String>> {
        Ok(self.artifact.asm_string.as_ref().unwrap())
    }

    pub fn compute_parsed_asm_file(
        &mut self,
    ) -> Result<&(Option<PathBuf>, ASMProgram), Vec<String>> {
        if self.artifact.parsed_asm_file.is_none() {
            self.artifact.parsed_asm_file = Some({
                let (path, asm_string) = self.compute_asm_string()?;
                let path = path.clone();
                let path_str = path.as_ref().map(|p| p.to_str().unwrap());

                let parsed_asm =
                    powdr_parser::parse_asm(path_str, asm_string).unwrap_or_else(|err| {
                        eprintln!(
                            "Error parsing .asm file:{}",
                            path_str.map(|p| format!(" {p}")).unwrap_or_default()
                        );
                        err.output_to_stderr();
                        panic!();
                    });

                (path.clone(), parsed_asm)
            });
        }

        Ok(self.artifact.parsed_asm_file.as_ref().unwrap())
    }

    pub fn parsed_asm_file(&self) -> Result<&(Option<PathBuf>, ASMProgram), Vec<String>> {
        Ok(self.artifact.parsed_asm_file.as_ref().unwrap())
    }

    pub fn compute_resolved_module_tree(&mut self) -> Result<&ASMProgram, Vec<String>> {
        if self.artifact.resolved_module_tree.is_none() {
            self.artifact.resolved_module_tree = Some({
                self.compute_parsed_asm_file()?;
                let (path, parsed) = self.artifact.parsed_asm_file.take().unwrap();

                self.log("Loading dependencies and resolving references");
                powdr_importer::load_dependencies_and_resolve(path, parsed).map_err(|e| {
                    // TODO at some point, change the error type in Pipeline so that we can forward it here.
                    e.output_to_stderr();
                    vec![e.message().to_string()]
                })?
            });
        }

        Ok(self.artifact.resolved_module_tree.as_ref().unwrap())
    }

    pub fn resolved_module_tree(&self) -> Result<&ASMProgram, Vec<String>> {
        Ok(self.artifact.resolved_module_tree.as_ref().unwrap())
    }

    pub fn compute_checked_asm(&mut self) -> Result<&AnalysisASMFile, Vec<String>> {
        if self.artifact.checked_asm.is_none() {
            self.artifact.checked_asm = Some({
                self.compute_resolved_module_tree()?;
                let resolved = self.artifact.resolved_module_tree.take().unwrap();

                self.log("Run analysis machine check");
                let checked_asm = powdr_analysis::check(resolved)?;
                self.log("Analysis machine check done");
                log::trace!("{checked_asm}");

                checked_asm
            });
        }

        Ok(self.artifact.checked_asm.as_ref().unwrap())
    }

    pub fn checked_asm(&self) -> Result<&AnalysisASMFile, Vec<String>> {
        Ok(self.artifact.checked_asm.as_ref().unwrap())
    }

    pub fn set_checked_asm(&mut self, asm: AnalysisASMFile) {
        self.artifact.checked_asm = Some(asm);
    }

    pub fn compute_analyzed_asm(&mut self) -> Result<&AnalysisASMFile, Vec<String>> {
        if self.artifact.analyzed_asm.is_none() {
            self.artifact.analyzed_asm = Some({
                self.compute_checked_asm()?;
                let checked = self.artifact.checked_asm.take().unwrap();

                self.log("Run analysis");
                let analyzed_asm = powdr_analysis::analyze_only(checked)?;
                self.log("Analysis done");
                log::trace!("{analyzed_asm}");

                analyzed_asm
            });
        }

        Ok(self.artifact.analyzed_asm.as_ref().unwrap())
    }

    pub fn analyzed_asm(&self) -> Result<&AnalysisASMFile, Vec<String>> {
        Ok(self.artifact.analyzed_asm.as_ref().unwrap())
    }

    pub fn compute_optimized_asm(&mut self) -> Result<&AnalysisASMFile, Vec<String>> {
        if let Some(ref optimized_asm) = self.artifact.optimized_asm {
            return Ok(optimized_asm);
        }

        self.compute_analyzed_asm()?;
        let analyzed_asm = self.artifact.analyzed_asm.take().unwrap();

        self.log("Optimizing asm...");
        let optimized = powdr_asmopt::optimize(analyzed_asm);
        self.artifact.optimized_asm = Some(optimized);

        Ok(self.artifact.optimized_asm.as_ref().unwrap())
    }

    pub fn optimized_asm(&self) -> Result<&AnalysisASMFile, Vec<String>> {
        Ok(self.artifact.optimized_asm.as_ref().unwrap())
    }

    pub fn compute_constrained_machine_collection(
        &mut self,
    ) -> Result<&AnalysisASMFile, Vec<String>> {
        if self.artifact.constrained_machine_collection.is_none() {
            self.artifact.constrained_machine_collection = Some({
                self.compute_optimized_asm()?;
                let optimized_asm = self.artifact.optimized_asm.take().unwrap();
                powdr_asm_to_pil::compile::<T>(optimized_asm)
            });
        }

        Ok(self
            .artifact
            .constrained_machine_collection
            .as_ref()
            .unwrap())
    }

    pub fn constrained_machine_collection(&self) -> Result<&AnalysisASMFile, Vec<String>> {
        Ok(self
            .artifact
            .constrained_machine_collection
            .as_ref()
            .unwrap())
    }

    pub fn compute_linked_machine_graph(&mut self) -> Result<&MachineInstanceGraph, Vec<String>> {
        if self.artifact.linked_machine_graph.is_none() {
            self.artifact.linked_machine_graph = Some({
                self.compute_constrained_machine_collection()?;
                let analyzed_asm = self.artifact.constrained_machine_collection.take().unwrap();

                self.log("Run airgen");
                let graph = powdr_airgen::compile(analyzed_asm);
                self.log("Airgen done");
                log::trace!("{graph}");

                graph
            });
        }

        Ok(self.artifact.linked_machine_graph.as_ref().unwrap())
    }

    pub fn linked_machine_graph(&self) -> Result<&MachineInstanceGraph, Vec<String>> {
        Ok(self.artifact.linked_machine_graph.as_ref().unwrap())
    }

    pub fn compute_parsed_pil_file(&mut self) -> Result<&PILFile, Vec<String>> {
        if self.artifact.parsed_pil_file.is_none() {
            self.artifact.parsed_pil_file = Some({
                self.compute_linked_machine_graph()?;
                let graph = self.artifact.linked_machine_graph.take().unwrap();

                self.log("Run linker");
                let linked = powdr_linker::link(graph, self.arguments.linker_params)?;
                log::trace!("{linked}");
                self.maybe_write_pil(&linked, "")?;

                linked
            });
        }

        Ok(self.artifact.parsed_pil_file.as_ref().unwrap())
    }

    pub fn parsed_pil_file(&self) -> Result<&PILFile, Vec<String>> {
        Ok(self.artifact.parsed_pil_file.as_ref().unwrap())
    }

    fn compute_analyzed_pil_from_parsed_pil_file(&mut self) -> Result<Analyzed<T>, Vec<String>> {
        self.compute_parsed_pil_file()?;
        let linked = self.artifact.parsed_pil_file.take().unwrap();

        self.log("Analyzing PIL and computing constraints...");
        let analyzed =
            powdr_pil_analyzer::analyze_ast(linked).map_err(output_pil_analysis_errors)?;
        self.maybe_write_pil(&analyzed, "_analyzed")?;
        self.log("done.");

        Ok(analyzed)
    }

    fn compute_analyzed_pil_from_pil_file_path(&self) -> Result<Analyzed<T>, Vec<String>> {
        let pil_file = match self.artifact.pil_file_path {
            Some(ref path) => path,
            None => return Err(vec!["No pil file path available".to_string()]),
        };

        self.log("Analyzing PIL and computing constraints...");
        let analyzed =
            powdr_pil_analyzer::analyze_file(pil_file).map_err(output_pil_analysis_errors)?;
        self.maybe_write_pil(&analyzed, "_analyzed")?;
        self.log("done.");

        Ok(analyzed)
    }

    fn compute_analyzed_pil_from_pil_string(&self) -> Result<Analyzed<T>, Vec<String>> {
        let pil_string = match self.artifact.pil_string {
            Some(ref s) => s,
            None => return Err(vec!["No pil string available".to_string()]),
        };

        self.log("Analyzing PIL and computing constraints...");
        let analyzed =
            powdr_pil_analyzer::analyze_string(pil_string).map_err(output_pil_analysis_errors)?;
        self.maybe_write_pil(&analyzed, "_analyzed")?;
        self.log("done.");

        Ok(analyzed)
    }

    pub fn compute_analyzed_pil(&mut self) -> Result<&Analyzed<T>, Vec<String>> {
        if self.artifact.analyzed_pil.is_none() {
            let analyzed_pil =
                if self.artifact.asm_string.is_some() || self.artifact.asm_file_path.is_some() {
                    self.compute_analyzed_pil_from_parsed_pil_file()
                } else if self.artifact.pil_string.is_some() {
                    self.compute_analyzed_pil_from_pil_string()
                } else if self.artifact.pil_file_path.is_some() {
                    self.compute_analyzed_pil_from_pil_file_path()
                } else {
                    panic!()
                };
            self.artifact.analyzed_pil = Some(analyzed_pil?)
        }

        Ok(self.artifact.analyzed_pil.as_ref().unwrap())
    }

    pub fn analyzed_pil(&self) -> Result<&Analyzed<T>, Vec<String>> {
        Ok(self.artifact.analyzed_pil.as_ref().unwrap())
    }

    pub fn compute_optimized_pil(&mut self) -> Result<Arc<Analyzed<T>>, Vec<String>> {
        if let Some(ref optimized_pil) = self.artifact.optimized_pil {
            return Ok(optimized_pil.clone());
        }

        self.compute_analyzed_pil()?;
        let analyzed_pil = self.artifact.analyzed_pil.take().unwrap();

        self.log("Optimizing pil...");
        let optimized = powdr_pilopt::optimize(analyzed_pil);
        self.maybe_write_pil(&optimized, "_opt")?;
        self.maybe_write_pil_object(&optimized, "_opt")?;

        self.artifact.optimized_pil = Some(Arc::new(optimized));

        Ok(self.artifact.optimized_pil.as_ref().unwrap().clone())
    }

    pub fn optimized_pil(&self) -> Result<Arc<Analyzed<T>>, Vec<String>> {
        Ok(self.artifact.optimized_pil.as_ref().unwrap().clone())
    }

    pub fn compute_fixed_cols(&mut self) -> Result<Arc<VariablySizedColumns<T>>, Vec<String>> {
        if let Some(ref fixed_cols) = self.artifact.fixed_cols {
            return Ok(fixed_cols.clone());
        }

        let pil = self.compute_optimized_pil()?;

        self.log("Evaluating fixed columns...");
        let start = Instant::now();
        let fixed_cols = constant_evaluator::generate(&pil);
        self.log(&format!(
            "Fixed column generation took {}s",
            start.elapsed().as_secs_f32()
        ));
        self.maybe_write_constants(&fixed_cols)?;

        self.artifact.fixed_cols = Some(Arc::new(fixed_cols));

        Ok(self.artifact.fixed_cols.as_ref().unwrap().clone())
    }

    pub fn fixed_cols(&self) -> Result<Arc<VariablySizedColumns<T>>, Vec<String>> {
        Ok(self.artifact.fixed_cols.as_ref().unwrap().clone())
    }

    pub fn compute_witness(&mut self) -> Result<Arc<Columns<T>>, Vec<String>> {
        if let Some(ref witness) = self.artifact.witness {
            return Ok(witness.clone());
        }

        self.host_context.clear();

        let pil = self.compute_optimized_pil()?;
        let fixed_cols = self.compute_fixed_cols()?;

        assert_eq!(pil.constant_count(), fixed_cols.len());

        let witness_cols: Vec<_> = pil
            .committed_polys_in_source_order()
            .flat_map(|(s, _)| s.array_elements().map(|(name, _)| name))
            .collect();

        let mut external_witness_values =
            std::mem::take(&mut self.arguments.external_witness_values);
        // witgen needs external witness columns sorted by source order
        external_witness_values.sort_by_key(|(name, _)| {
            witness_cols
                .iter()
                .position(|n| n == name)
                .unwrap_or_else(|| {
                    panic!("external witness {name} does not exist in the optimized PIL")
                })
        });

        if witness_cols
            .iter()
            .all(|name| external_witness_values.iter().any(|(e, _)| e == name))
        {
            self.log("All witness columns externally provided, skipping witness generation.");
            self.artifact.witness = Some(Arc::new(external_witness_values));
        } else {
            self.log("Deducing witness columns...");
            let start = Instant::now();

            let query_callback = self
                .arguments
                .query_callback
                .clone()
                .unwrap_or_else(|| Arc::new(unused_query_callback()));
            let witness = WitnessGenerator::new(&pil, &fixed_cols, query_callback.borrow())
                .with_external_witness_values(&external_witness_values)
                .generate();

            self.log(&format!(
                "Witness generation took {}s",
                start.elapsed().as_secs_f32()
            ));

            self.maybe_write_witness(&fixed_cols, &witness)?;

            self.artifact.witness = Some(Arc::new(witness));
        }
        self.artifact.proof = None;

        Ok(self.artifact.witness.as_ref().unwrap().clone())
    }

    pub fn witness(&self) -> Result<Arc<Columns<T>>, Vec<String>> {
        Ok(self.artifact.witness.as_ref().unwrap().clone())
    }

    pub fn publics(&self) -> Result<Vec<(String, Option<T>)>, Vec<String>> {
        let pil = self.optimized_pil()?;
        let witness = self.witness()?;
        Ok(extract_publics(witness.iter().map(|(k, v)| (k, v)), &pil)
            .into_iter()
            .collect())
    }

    pub fn witgen_callback(&mut self) -> Result<WitgenCallback<T>, Vec<String>> {
        let ctx = WitgenCallbackContext::new(
            self.compute_fixed_cols()?,
            self.arguments.query_callback.as_ref().cloned(),
        );
        Ok(WitgenCallback::new(Arc::new(
            move |pil, current_witness, challenges, stage| {
                ctx.next_stage_witness(pil, current_witness, challenges, stage)
            },
        )))
    }

    pub fn backend(&mut self) -> Result<&mut dyn Backend<T>, Vec<String>> {
        Ok(self.artifact.backend.as_deref_mut().unwrap())
    }

    pub fn setup_backend(&mut self) -> Result<&mut dyn Backend<T>, Vec<String>> {
        if self.artifact.backend.is_some() {
            return Ok(self.artifact.backend.as_deref_mut().unwrap());
        }
        let pil = self.compute_optimized_pil()?;
        let fixed_cols = self.compute_fixed_cols()?;

        let backend = self.arguments.backend.expect("no backend selected!");
        let factory = backend.factory::<T>();

        // Opens the setup file, if set.
        let mut setup = self
            .arguments
            .setup_file
            .as_ref()
            .map(|path| BufReader::new(fs::File::open(path).unwrap()));

        // Opens the proving key file, if set.
        let mut pkey = self
            .arguments
            .pkey_file
            .as_ref()
            .map(|path| BufReader::new(fs::File::open(path).unwrap()));

        // Opens the verification key file, if set.
        let mut vkey = self
            .arguments
            .vkey_file
            .as_ref()
            .map(|path| BufReader::new(fs::File::open(path).unwrap()));

        // Opens the verification app key file, if set.
        let mut vkey_app = self
            .arguments
            .vkey_app_file
            .as_ref()
            .map(|path| BufReader::new(fs::File::open(path).unwrap()));

        // Create the backend
        let start = Instant::now();
        self.log(&format!("Backend setup for {backend}..."));
        let backend = factory
            .create(
                pil.clone(),
                fixed_cols.clone(),
                self.output_dir.clone(),
                setup.as_io_read(),
                pkey.as_io_read(),
                vkey.as_io_read(),
                vkey_app.as_io_read(),
                self.arguments.backend_options.clone(),
            )
            .unwrap();
        self.log(&format!("Setup took {}s", start.elapsed().as_secs_f32()));

        self.artifact.backend = Some(backend);
        Ok(self.artifact.backend.as_deref_mut().unwrap())
    }

    pub fn compute_proof(&mut self) -> Result<&Proof, Vec<String>> {
        if self.artifact.proof.is_some() {
            return Ok(self.artifact.proof.as_ref().unwrap());
        }

        let witness = self.compute_witness()?;
        let witgen_callback = self.witgen_callback()?;

        // Reads the existing proof file, if set.
        let existing_proof = self
            .arguments
            .existing_proof_file
            .as_ref()
            .map(|path| fs::read(path).unwrap());

        self.setup_backend()?;

        let start = Instant::now();
        let proof = {
            let backend = self.backend()?;
            match backend.prove(&witness, existing_proof, witgen_callback) {
                Ok(proof) => proof,
                Err(powdr_backend::Error::BackendError(e)) => {
                    return Err(vec![e.to_string()]);
                }
                Err(e) => panic!("{}", e),
            }
        };
        self.log(&format!(
            "Proof generation took {}s",
            start.elapsed().as_secs_f32()
        ));
        self.log(&format!("Proof size: {} bytes", proof.len()));

        self.maybe_write_proof(&proof)?;

        self.artifact.proof = Some(proof);

        Ok(self.artifact.proof.as_ref().unwrap())
    }

    pub fn proof(&self) -> Result<&Proof, Vec<String>> {
        Ok(self.artifact.proof.as_ref().unwrap())
    }

    pub fn output_dir(&self) -> &Option<PathBuf> {
        &self.output_dir
    }

    pub fn is_force_overwrite(&self) -> bool {
        self.force_overwrite
    }

    pub fn name(&self) -> &str {
        self.name.as_ref().unwrap()
    }

    pub fn data_callback(&self) -> Option<&dyn QueryCallback<T>> {
        self.arguments.query_callback.as_deref()
    }

    pub fn export_proving_key<W: io::Write>(&mut self, writer: W) -> Result<(), Vec<String>> {
        let backend = self.setup_backend()?;
        let mut bw = BufWriter::new(writer);
        let res = backend.export_proving_key(&mut bw).map_err(|e| match e {
            powdr_backend::Error::BackendError(e) => vec![e],
            _ => panic!(),
        });
        bw.flush().unwrap();
        res
    }

    pub fn export_verification_key<W: io::Write>(
        &mut self,
        mut writer: W,
    ) -> Result<(), Vec<String>> {
        let backend = self.setup_backend()?;
        backend
            .export_verification_key(&mut writer)
            .map_err(|e| match e {
                powdr_backend::Error::BackendError(e) => vec![e],
                _ => panic!(),
            })
    }

    pub fn export_ethereum_verifier<W: io::Write>(
        &mut self,
        mut writer: W,
    ) -> Result<(), Vec<String>> {
        let backend = self.setup_backend()?;

        match backend.export_ethereum_verifier(&mut writer) {
            Ok(()) => Ok(()),
            Err(powdr_backend::Error::NoEthereumVerifierAvailable) => {
                Err(vec!["No Ethereum verifier available".to_string()])
            }
            Err(powdr_backend::Error::BackendError(e)) => Err(vec![e]),
            _ => panic!(),
        }
    }

    pub fn verify(&mut self, proof: &[u8], instances: &[Vec<T>]) -> Result<(), Vec<String>> {
        let backend = self.setup_backend()?;

        let start = Instant::now();
        match backend.verify(proof, instances) {
            Ok(_) => {
                self.log(&format!(
                    "Verification took {}s",
                    start.elapsed().as_secs_f32()
                ));
                Ok(())
            }
            Err(powdr_backend::Error::BackendError(e)) => Err(vec![e]),
            _ => panic!(),
        }
    }

    pub fn export_backend_setup<W: io::Write>(&mut self, mut writer: W) -> Result<(), Vec<String>> {
        let backend = self.setup_backend()?;
        backend.export_setup(&mut writer).map_err(|e| match e {
            powdr_backend::Error::BackendError(e) => vec![e],
            _ => panic!(),
        })
    }

    pub fn host_context(&self) -> &HostContext {
        &self.host_context
    }
}

fn output_pil_analysis_errors(errors: Vec<powdr_parser_util::Error>) -> Vec<String> {
    eprintln!("Error analyzing PIL file:");
    errors
        .into_iter()
        .map(|e| {
            e.output_to_stderr();
            e.to_string()
        })
        .collect()
}

use std::{
    env,
    path::{Path, PathBuf},
};

use powdr_ast::parsed::{
    asm::{
        ASMModule, ASMProgram, Import, Module, ModuleStatement, Part, SymbolDefinition, SymbolPath,
        SymbolValue, TypeDeclaration,
    },
    folder::Folder,
};
use powdr_parser::parse_asm;

use crate::load_module_files;

static POWDR_STD_ENV: &str = "POWDR_STD";
static MOD_FILE: &str = "mod.asm";

/// Loads the standard library module from the location specified in the <POWDR_STD_ENV> environment variable
/// (or, if unset, <project_root>/std).
///
/// # Panics
/// If there is an error loading the standard library
fn load_std() -> ASMModule {
    let default_std_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("std");
    let std_path = env::var(POWDR_STD_ENV)
        .map(PathBuf::from)
        .unwrap_or(default_std_path);
    let std_path = std_path.join(MOD_FILE);

    match std::fs::read_to_string(&std_path) {
        Err(_) => {
            panic!(
                "Couldn't find the powdr standard library at {}. Set the {} environment variable.",
                std_path.display(),
                POWDR_STD_ENV
            )
        }
        Ok(std_source) => {
            let std_content = parse_asm(Some(std_path.as_path().to_str().unwrap()), &std_source)
                .unwrap_or_else(|err| {
                    eprintln!("Error parsing powdr standard library file:");
                    err.output_to_stderr();
                    panic!();
                });
            // This resolves all submodules and returns the standard library's main module
            load_module_files(Some(std_path), std_content).unwrap().main
        }
    }
}

pub fn add_std(program: ASMProgram) -> Result<ASMProgram, String> {
    StdAdder().fold_program(program)
}

struct StdAdder();

type Error = String;

impl Folder for StdAdder {
    type Error = Error;

    fn fold_program(&mut self, p: ASMProgram) -> Result<ASMProgram, Self::Error> {
        // Add `std` to the main module
        let mut main = p.main;
        main.statements
            .push(ModuleStatement::SymbolDefinition(SymbolDefinition {
                name: "std".to_string(),
                value: SymbolValue::Module(Module::Local(load_std())),
            }));

        // Recurse
        let main = self.fold_module_value(main)?;
        Ok(ASMProgram { main })
    }

    fn fold_module_value(&mut self, module: ASMModule) -> Result<ASMModule, Self::Error> {
        // This block is identical to Folder::fold_module_value.
        // Unfortunately, there is no way to call the super method from here.
        let mut statements = module
            .statements
            .into_iter()
            .map(|s| match s {
                ModuleStatement::SymbolDefinition(d) => match d.value {
                    SymbolValue::Machine(machine) => self.fold_machine(machine).map(From::from),
                    SymbolValue::Import(import) => {
                        StdAdder::fold_import(self, import).map(From::from)
                    }
                    SymbolValue::Module(module) => self.fold_module(module).map(From::from),
                    SymbolValue::Expression(e) => Ok(SymbolValue::Expression(e)),
                    SymbolValue::TypeDeclaration(TypeDeclaration::Enum(enum_decl)) => {
                        self.fold_enum_declaration(enum_decl).map(From::from)
                    }
                    SymbolValue::TypeDeclaration(TypeDeclaration::Struct(struct_decl)) => {
                        self.fold_struct_declaration(struct_decl).map(From::from)
                    }
                    SymbolValue::TraitDeclaration(trait_decl) => {
                        self.fold_trait_declaration(trait_decl).map(From::from)
                    }
                }
                .map(|value| ModuleStatement::SymbolDefinition(SymbolDefinition { value, ..d })),
                ModuleStatement::TraitImplementation(trait_impl) => {
                    self.fold_trait_implementation(trait_impl).map(From::from)
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Check whether the module already has a definition for `std`
        // (E.g. the main module)
        let has_std = statements
            .iter()
            .filter_map(|m| m.defined_names())
            .any(|n| n == "std");

        if !has_std {
            // If not, add `use super::std;`
            let std_import_path =
                SymbolPath::from_parts([Part::Super, Part::Named("std".to_string())]);
            statements.push(ModuleStatement::SymbolDefinition(SymbolDefinition {
                name: "std".to_string(),
                value: SymbolValue::Import(Import {
                    path: std_import_path,
                }),
            }));
        }

        Ok(ASMModule { statements })
    }
}

use super::{
    asm::{
        ASMModule, ASMProgram, Import, Machine, Module, ModuleStatement, SymbolDefinition,
        SymbolValue, TypeDeclaration,
    },
    EnumDeclaration, Expression, StructDeclaration, TraitDeclaration, TraitImplementation,
};

pub trait Folder {
    type Error;

    fn fold_program(&mut self, p: ASMProgram) -> Result<ASMProgram, Self::Error> {
        let main = self.fold_module_value(p.main)?;

        Ok(ASMProgram { main })
    }

    fn fold_module_value(&mut self, module: ASMModule) -> Result<ASMModule, Self::Error> {
        let statements = module
            .statements
            .into_iter()
            .map(|s| match s {
                ModuleStatement::SymbolDefinition(d) => match d.value {
                    SymbolValue::Machine(machine) => self.fold_machine(machine).map(From::from),
                    SymbolValue::Import(import) => self.fold_import(import).map(From::from),
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

        Ok(ASMModule { statements })
    }

    fn fold_module(&mut self, m: Module) -> Result<Module, Self::Error> {
        Ok(match m {
            Module::External(e) => Module::External(e),
            Module::Local(m) => Module::Local(self.fold_module_value(m)?),
        })
    }

    fn fold_machine(&mut self, machine: Machine) -> Result<Machine, Self::Error> {
        Ok(machine)
    }

    fn fold_import(&mut self, import: Import) -> Result<Import, Self::Error> {
        Ok(import)
    }

    fn fold_enum_declaration(
        &mut self,
        ty: EnumDeclaration<Expression>,
    ) -> Result<EnumDeclaration<Expression>, Self::Error> {
        Ok(ty)
    }

    fn fold_struct_declaration(
        &mut self,
        ty: StructDeclaration<Expression>,
    ) -> Result<StructDeclaration<Expression>, Self::Error> {
        Ok(ty)
    }

    fn fold_trait_implementation(
        &mut self,
        trait_impl: TraitImplementation<Expression>,
    ) -> Result<TraitImplementation<Expression>, Self::Error> {
        Ok(trait_impl)
    }

    fn fold_trait_declaration(
        &mut self,
        trait_decl: TraitDeclaration<Expression>,
    ) -> Result<TraitDeclaration<Expression>, Self::Error> {
        Ok(trait_decl)
    }
}

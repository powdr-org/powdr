#![deny(clippy::print_stdout)]

use std::collections::BTreeMap;

use powdr_ast::{
    asm_analysis::{
        AnalysisASMFile, AssignmentStatement, CallableSymbolDefinitions, DebugDirective,
        FunctionBody, FunctionStatements, FunctionSymbol, InstructionDefinitionStatement,
        InstructionStatement, Item, LabelStatement, LinkDefinition, Machine, MachineDegree,
        OperationSymbol, RegisterDeclarationStatement, RegisterTy, Return, SubmachineDeclaration,
    },
    parsed::{
        self,
        asm::{
            self, ASMModule, ASMProgram, AbsoluteSymbolPath, AssignmentRegister, FunctionStatement,
            Instruction, LinkDeclaration, MachineProperties, MachineStatement, ModuleStatement,
            RegisterFlag, SymbolDefinition, TypeDeclaration,
        },
    },
};

/// Verifies certain properties of each machine and constructs the Machine objects.
/// Also transfers generic PIL definitions but does not verify anything about them.
pub fn check(file: ASMProgram) -> Result<AnalysisASMFile, Vec<String>> {
    let ctx = AbsoluteSymbolPath::default();
    let machines = TypeChecker::default().check_module(file.main, &ctx)?;
    Ok(AnalysisASMFile {
        items: machines.into_iter().collect(),
    })
}

#[derive(Default)]
struct TypeChecker {}

impl TypeChecker {
    fn check_machine_type(
        &mut self,
        machine: asm::Machine,
        ctx: &AbsoluteSymbolPath,
    ) -> Result<Machine, Vec<String>> {
        let mut errors = vec![];

        let mut registers = vec![];
        let mut pil = vec![];
        let mut instructions = vec![];
        let mut links = vec![];
        let mut callable = CallableSymbolDefinitions::default();
        let mut submachines = vec![];

        for s in machine.statements {
            match s {
                MachineStatement::RegisterDeclaration(source, name, flag) => {
                    let ty = match flag {
                        Some(RegisterFlag::IsAssignment) => RegisterTy::Assignment,
                        Some(RegisterFlag::IsPC) => RegisterTy::Pc,
                        Some(RegisterFlag::IsReadOnly) => RegisterTy::ReadOnly,
                        None => RegisterTy::Write,
                    };
                    registers.push(RegisterDeclarationStatement { source, name, ty });
                }
                MachineStatement::InstructionDeclaration(source, name, instruction) => {
                    match self.check_instruction(&name, instruction) {
                        Ok(instruction) => instructions.push(InstructionDefinitionStatement {
                            source,
                            name,
                            instruction,
                        }),
                        Err(e) => errors.extend(e),
                    }
                }
                MachineStatement::LinkDeclaration(
                    source,
                    LinkDeclaration {
                        flag,
                        link,
                        is_permutation,
                    },
                ) => links.push(LinkDefinition {
                    source,
                    instr_flag: None,
                    link_flag: flag,
                    to: link,
                    is_permutation,
                }),
                MachineStatement::Pil(_source, statement) => {
                    pil.push(statement);
                }
                MachineStatement::Submachine(_, ty, name, args) => {
                    args.iter().for_each(|arg| {
                        if arg.try_to_identifier().is_none() {
                            errors
                                .push(format!("submachine argument not a machine instance: {arg}"))
                        }
                    });
                    submachines.push(SubmachineDeclaration {
                        name,
                        ty: AbsoluteSymbolPath::default().join(ty),
                        args,
                    });
                }
                MachineStatement::FunctionDeclaration(source, name, params, statements) => {
                    let mut function_statements = vec![];
                    for s in statements {
                        let statement_string = s.to_string();
                        match s {
                            FunctionStatement::Assignment(source, lhs, using_reg, rhs) => {
                                if let Some(using_reg) = &using_reg {
                                    if using_reg.len() != lhs.len() {
                                        errors.push(format!(
                                            "Mismatched number of registers for assignment {statement_string}"
                                        ));
                                    }
                                }
                                let using_reg = using_reg.unwrap_or_else(|| {
                                    vec![AssignmentRegister::Wildcard; lhs.len()]
                                });
                                let lhs_with_reg = lhs
                                    .into_iter()
                                    .zip(using_reg.into_iter())
                                    .collect::<Vec<_>>();
                                function_statements.push(
                                    AssignmentStatement {
                                        source,
                                        lhs_with_reg,
                                        rhs,
                                    }
                                    .into(),
                                );
                            }
                            FunctionStatement::Instruction(source, instruction, inputs) => {
                                function_statements.push(
                                    InstructionStatement {
                                        source,
                                        instruction,
                                        inputs,
                                    }
                                    .into(),
                                );
                            }
                            FunctionStatement::Label(source, name) => {
                                function_statements.push(LabelStatement { source, name }.into());
                            }
                            FunctionStatement::DebugDirective(source, directive) => {
                                function_statements
                                    .push(DebugDirective { source, directive }.into());
                            }
                            FunctionStatement::Return(source, values) => {
                                function_statements.push(Return { source, values }.into());
                            }
                        }
                    }
                    assert!(callable
                        .insert(
                            name,
                            FunctionSymbol {
                                source,
                                params,
                                body: FunctionBody {
                                    statements: FunctionStatements::new(function_statements),
                                },
                            },
                        )
                        .is_none());
                }
                MachineStatement::OperationDeclaration(source, name, id, params) => {
                    assert!(callable
                        .insert(name, OperationSymbol { source, id, params })
                        .is_none());
                }
            }
        }

        let MachineProperties {
            degree,
            min_degree,
            max_degree,
            latch,
            operation_id,
            call_selectors,
        } = machine.properties;

        let degree = match (degree, min_degree, max_degree) {
            (Some(d), None, None) => MachineDegree {
                min: Some(d.clone()),
                max: Some(d),
            },
            (Some(d), Some(_), _) => {
                errors.push("Machine {ctx} should not have a min_degree if it has a degree".into());
                MachineDegree {
                    min: Some(d.clone()),
                    max: Some(d),
                }
            }
            (Some(d), _, Some(_)) => {
                errors.push("Machine {ctx} should not have a max_degree if it has a degree".into());
                MachineDegree {
                    min: Some(d.clone()),
                    max: Some(d),
                }
            }
            (None, min, max) => MachineDegree { min, max },
        };

        if !registers.iter().any(|r| r.ty.is_pc()) {
            let operation_count = callable.operation_definitions().count();
            if operation_count > 0 && latch.is_none() {
                errors.push(format!(
                    "Machine {ctx} should have a latch column as it does not have a pc and has operations"
                ));
            }

            if operation_id.is_some() {
                for o in callable.operation_definitions() {
                    if o.operation.id.id.is_none() {
                        errors.push(format!(
                            "Operation `{}` in machine {ctx} needs an operation id because the machine has an operation id column",
                            o.name
                        ))
                    }
                }
            } else {
                // no operation id column
                if operation_count > 1 {
                    errors.push(format!(
                        "Machine {ctx} should have an operation id column as it does not have a pc and has more than one operation"
                    ));
                }
                if let Some(o) = callable.operation_definitions().next() {
                    if o.operation.id.id.is_some() {
                        errors.push(format!(
                            "Operation `{}` in machine {ctx} can't have an operation id because the machine does not have an operation id column",
                            o.name
                        ))
                    }
                }
            }

            for r in &registers {
                errors.push(format!(
                    "Machine {ctx} should not have registers as it does not have a pc, found `{}`",
                    r.name
                ));
            }

            for f in callable.function_definitions() {
                errors.push(format!(
                    "Machine {ctx} should not have functions as it does not have a pc, found `{}`",
                    f.name
                ))
            }

            for i in &instructions {
                errors.push(format!(
                    "Machine {ctx} should not have instructions as it does not have a pc, found `{}`",
                    i.name
                ))
            }
        } else {
            if latch.is_some() {
                errors.push(format!(
                    "Machine {ctx} should not have a latch column as it has a pc"
                ));
            }
            if operation_id.is_some() {
                errors.push(format!(
                    "Machine {ctx} should not have an operation id column as it has a pc"
                ));
            }
            if call_selectors.is_some() {
                errors.push(format!(
                    "Machine {ctx} should not have call_selectors as it has a pc"
                ));
            }
            for o in callable.operation_definitions() {
                errors.push(format!(
                    "Machine {ctx} should not have operations as it has a pc, found `{}`",
                    o.name
                ))
            }
        }

        if registers.iter().filter(|r| r.ty.is_pc()).count() > 1 {
            errors.push(format!("Machine {ctx} cannot have more than one pc"));
        }

        let machine = Machine {
            degree,
            latch,
            operation_id,
            call_selectors,
            params: machine.params,
            pc: registers
                .iter()
                .enumerate()
                .find_map(|(i, r)| (r.ty.is_pc()).then_some(i)),
            registers,
            links,
            instructions,
            pil,
            callable,
            submachines,
        };

        if !errors.is_empty() {
            Err(errors)
        } else {
            Ok(machine)
        }
    }

    fn check_module(
        &mut self,
        module: ASMModule,
        ctx: &AbsoluteSymbolPath,
    ) -> Result<BTreeMap<AbsoluteSymbolPath, Item>, Vec<String>> {
        let mut errors = vec![];

        let mut res: BTreeMap<AbsoluteSymbolPath, Item> = BTreeMap::default();

        for m in module.statements {
            match m {
                ModuleStatement::SymbolDefinition(SymbolDefinition { name, value }) => {
                    match value {
                        asm::SymbolValue::Machine(m) => {
                            match self.check_machine_type(m, &ctx.with_part(&name)) {
                                Err(e) => {
                                    errors.extend(e);
                                }
                                Ok(machine) => {
                                    res.insert(ctx.with_part(&name), Item::Machine(machine));
                                }
                            };
                        }
                        asm::SymbolValue::Import(_) => {
                            unreachable!("Imports should have been removed")
                        }
                        asm::SymbolValue::Module(m) => {
                            // add the name of this module to the context
                            let ctx = ctx.with_part(&name);

                            let m = match m {
                                asm::Module::External(_) => unreachable!(),
                                asm::Module::Local(m) => m,
                            };

                            match self.check_module(m, &ctx) {
                                Err(err) => {
                                    errors.extend(err);
                                }
                                Ok(m) => {
                                    res.extend(m);
                                }
                            };
                        }
                        asm::SymbolValue::Expression(e) => {
                            res.insert(ctx.clone().with_part(&name), Item::Expression(e));
                        }
                        asm::SymbolValue::TypeDeclaration(TypeDeclaration::Enum(enum_decl)) => {
                            res.insert(
                                ctx.clone().with_part(&name),
                                Item::TypeDeclaration(enum_decl.into()),
                            );
                        }
                        asm::SymbolValue::TypeDeclaration(TypeDeclaration::Struct(struct_decl)) => {
                            res.insert(
                                ctx.clone().with_part(&name),
                                Item::TypeDeclaration(struct_decl.into()),
                            );
                        }
                        asm::SymbolValue::TraitDeclaration(trait_decl) => {
                            res.insert(
                                ctx.clone().with_part(&name),
                                Item::TraitDeclaration(trait_decl),
                            );
                        }
                    }
                }
                ModuleStatement::TraitImplementation(trait_impl) => {
                    res.insert(ctx.clone(), Item::TraitImplementation(trait_impl));
                }
            }
        }

        if !errors.is_empty() {
            Err(errors)
        } else {
            Ok(res)
        }
    }

    fn check_instruction(
        &self,
        name: &str,
        instruction: parsed::asm::Instruction,
    ) -> Result<Instruction, Vec<String>> {
        if name == "return" {
            return Err(vec!["Instruction cannot use reserved name `return`".into()]);
        }

        let errors: Vec<_> = instruction
            .body
            .0
            .iter()
            .filter_map(|s| {
                // TODO this could be a function call that returns an identity including a selector in the future.
                if let powdr_ast::parsed::PilStatement::Expression(_, _) = s {
                    None
                } else {
                    Some(format!("Statement not allowed in instruction body: {s}"))
                }
            })
            .collect();
        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(Instruction {
            params: instruction.params,
            body: instruction.body,
            links: instruction.links,
        })
    }
}

#[cfg(test)]
mod tests {
    use powdr_importer::load_dependencies_and_resolve_str;

    use super::check;

    // A utility to test behavior of the type checker on source inputs
    // TODO: test returned values, not just success
    fn expect_check_str(src: &str, expected: Result<(), Vec<&str>>) {
        let resolved = load_dependencies_and_resolve_str(src);
        let checked = check(resolved);
        assert_eq!(
            checked.map(|_| ()),
            expected.map_err(|e| e.into_iter().map(|s| s.to_string()).collect())
        )
    }

    // TODO: remove `should_panic` below by detecting that `A` is not a `Machine`
    #[test]
    #[should_panic = "Ok"]
    fn submachine_is_not_a_machine() {
        let src = r#"
        mod A {
        }
        machine M with latch: l, operation_id: i {
            A a;
        }"#;
        expect_check_str(
            src,
            Err(vec![
                "Expected A to be of type Machine, but found type module",
            ]),
        );
    }

    #[test]
    fn constrained_machine_has_no_registers() {
        let src = r#"
machine Main with latch: latch, operation_id: id {
   reg A;
}
"#;
        expect_check_str(
            src,
            Err(vec![
                "Machine ::Main should not have registers as it does not have a pc, found `A`",
            ]),
        );
    }

    #[test]
    fn virtual_machine_with_links() {
        let src = r#"
machine Main {
   reg pc[@pc];
   reg A;
   reg B;

   link => B = submachine.foo(A);
}
"#;
        expect_check_str(src, Ok(()));
    }

    #[test]
    fn multiple_ops_need_op_id() {
        let src = r#"
machine Arith with latch: latch {
   operation add a, b -> c;
   operation sub a, b -> c;
}
"#;
        expect_check_str(src, Err(vec!["Machine ::Arith should have an operation id column as it does not have a pc and has more than one operation"]));
    }

    #[test]
    fn id_column_requires_op_id() {
        let src = r#"
machine Arith with latch: latch, operation_id: id  {
   operation add a, b -> c;
   operation sub a, b -> c;
}
"#;
        expect_check_str(src, Err(vec!["Operation `add` in machine ::Arith needs an operation id because the machine has an operation id column",
                                       "Operation `sub` in machine ::Arith needs an operation id because the machine has an operation id column"]));
    }

    #[test]
    fn id_op_id_requires_id_column() {
        let src = r#"
machine Arith with latch: latch {
   operation add<0> a, b -> c;
}
"#;
        expect_check_str(src, Err(vec!["Operation `add` in machine ::Arith can't have an operation id because the machine does not have an operation id column"]));
    }

    #[test]
    fn virtual_machine_has_no_call_selectors() {
        let src = r#"
machine Main with call_selectors: sel {
   reg pc[@pc];
}
"#;
        expect_check_str(
            src,
            Err(vec![
                "Machine ::Main should not have call_selectors as it has a pc",
            ]),
        );
    }
}

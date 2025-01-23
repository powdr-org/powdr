pub mod machine_check;
mod vm;

use std::collections::{HashMap, HashSet};
use std::ops::ControlFlow;

use powdr_ast::asm_analysis::InstructionDefinitionStatement;
use powdr_ast::parsed::asm::{
    parse_absolute_path, AbsoluteSymbolPath, CallableRef, Instruction, InstructionBody,
    LinkDeclaration, MachineParams, OperationId, Param, Params, Part, SymbolPath,
};
use powdr_ast::{asm_analysis::AnalysisASMFile, parsed::asm::ASMProgram};
use powdr_ast::{
    asm_analysis::{
        CallableSymbol, CallableSymbolDefinitions, FunctionStatement, FunctionStatements,
        InstructionStatement, LabelStatement, LinkDefinition, Machine, MachineDegree, Module,
        OperationSymbol, SubmachineDeclaration,
    },
    parsed::{
        visitor::{ExpressionVisitable, VisitOrder},
        BinaryOperator, FunctionCall, NamespacedPolynomialReference, Number, PilStatement,
    },
};
use powdr_number::BigUint;
use powdr_number::FieldElement;

type Expression = powdr_ast::asm_analysis::Expression<NamespacedPolynomialReference>;

const MAIN_MACHINE_STR: &str = "::Main";

pub fn convert_asm_to_pil<T: FieldElement>(
    file: ASMProgram,
) -> Result<AnalysisASMFile, Vec<String>> {
    let file = analyze(file)?;
    Ok(powdr_asm_to_pil::compile::<T>(file))
}

pub fn check(file: ASMProgram) -> Result<AnalysisASMFile, Vec<String>> {
    log::debug!("Run machine check analysis step");
    let file = machine_check::check(file)?;

    Ok(file)
}

pub fn analyze_precompiles(
    analyzed_asm: AnalysisASMFile,
    selected: &HashSet<String>,
) -> AnalysisASMFile {
    let main_machine_path = parse_absolute_path(MAIN_MACHINE_STR);
    if analyzed_asm
        .machines()
        .all(|(path, _)| path != main_machine_path)
    {
        return analyzed_asm;
    }

    create_precompiles(analyzed_asm, selected)
}

pub fn analyze_only(file: AnalysisASMFile) -> Result<AnalysisASMFile, Vec<String>> {
    // run analysis on virtual machines, batching instructions
    log::debug!("Start asm analysis");
    let file = vm::analyze(file)?;
    log::debug!("End asm analysis");

    Ok(file)
}

pub fn analyze(file: ASMProgram) -> Result<AnalysisASMFile, Vec<String>> {
    log::debug!("Run machine check analysis step");
    let file = machine_check::check(file)?;

    /*
        let mut blocks = collect_basic_blocks(&file);
        blocks.sort_by(|a, b| b.1.len().cmp(&a.1.len()));
        for (name, block) in &blocks {
            println!("Block {name} has {} instructions", block.len());
        }
    */
    let file = optimize(file);

    // run analysis on virtual machines, batching instructions
    log::debug!("Start asm analysis");
    let file = vm::analyze(file)?;
    log::debug!("End asm analysis");

    Ok(file)
}

pub mod utils {
    use powdr_ast::parsed::PilStatement;
    use powdr_parser::powdr;

    lazy_static::lazy_static! {
        static ref PIL_STATEMENT_PARSER: powdr::PilStatementParser = powdr::PilStatementParser::new();
    }

    pub fn parse_pil_statement(input: &str) -> PilStatement {
        let ctx = powdr_parser::ParserContext::new(None, input);
        PIL_STATEMENT_PARSER.parse(&ctx, input).unwrap()
    }
}

pub fn optimize(analyzed_asm: AnalysisASMFile) -> AnalysisASMFile {
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

    optimize_precompiles(analyzed_asm)
}

// Simplified: Replace "autoprecompile" blocks with a single synthetic instruction
pub fn simplify_autoprecompile_blocks(
    //program: &mut Vec<FunctionStatement>,
    program: &mut FunctionStatements,
) -> Vec<(String, Vec<FunctionStatement>)> {
    let mut blocks = Vec::new();
    let mut i = 0;

    let program = &mut program.inner;
    while i < program.len() {
        if let FunctionStatement::Label(LabelStatement { source, name }) = &program[i] {
            if name.starts_with("autoprecompile") {
                // Start collecting statements in this block
                let mut block_statements = Vec::new();
                let mut j = i + 1;

                // Collect until next label, branch, or return
                while j < program.len() {
                    match &program[j] {
                        FunctionStatement::Label(_) => break,
                        FunctionStatement::Instruction(InstructionStatement {
                            source: _,
                            instruction,
                            inputs: _,
                        }) if instruction.starts_with("branch")
                            || instruction.starts_with("jump") =>
                        {
                            break
                        }
                        FunctionStatement::Return(_) => break,
                        _ => {
                            block_statements.push(program[j].clone());
                            j += 1;
                        }
                    }
                }

                // Create a synthetic instruction
                //let synthetic_instruction_name = format!("synthetic_{}", name);
                let synthetic_instruction_name = name.clone();
                let synthetic_instruction = FunctionStatement::Instruction(InstructionStatement {
                    source: source.clone(),
                    instruction: synthetic_instruction_name.clone(),
                    inputs: vec![],
                });

                blocks.push((name.clone(), block_statements));

                /*
                                println!(
                                    "Replacing block '{}' with synthetic instruction '{}'",
                                    name, synthetic_instruction_name
                                );
                */

                // Replace the block contents
                program.splice(i + 1..j, std::iter::once(synthetic_instruction));

                // Adjust the index to continue after the synthetic instruction
                i += 1;
            } else {
                i += 1;
            }
        } else {
            i += 1;
        }
    }

    blocks
}

pub fn transform_autoprecompile_blocks(
    //program: &mut Vec<FunctionStatement>,
    program: &mut FunctionStatements,
    selected: &HashSet<String>,
) -> Vec<(String, Vec<FunctionStatement>)> {
    let mut blocks = Vec::new();
    let mut i = 0;

    let program = &mut program.inner;
    while i < program.len() {
        if let FunctionStatement::Label(LabelStatement { source, name }) = &program[i] {
            if selected.get(name).is_some() {
                // Start collecting statements in this block
                let mut block_statements = Vec::new();
                let mut j = i + 1;

                // Collect until next label, branch, or return
                while j < program.len() {
                    match &program[j] {
                        FunctionStatement::Label(_) => break,
                        FunctionStatement::Instruction(InstructionStatement {
                            source: _,
                            instruction,
                            inputs: _,
                        }) if instruction.starts_with("branch")
                            || instruction.starts_with("jump") =>
                        {
                            break
                        }
                        FunctionStatement::Return(_) => break,
                        _ => {
                            block_statements.push(program[j].clone());
                            j += 1;
                        }
                    }
                }

                // Create a synthetic instruction
                //let synthetic_instruction_name = format!("synthetic_{}", name);
                let synthetic_instruction_name = name.clone();
                let synthetic_instruction = FunctionStatement::Instruction(InstructionStatement {
                    source: source.clone(),
                    instruction: synthetic_instruction_name.clone(),
                    inputs: vec![],
                });

                blocks.push((name.clone(), block_statements));

                /*
                                println!(
                                    "Replacing block '{}' with synthetic instruction '{}'",
                                    name, synthetic_instruction_name
                                );
                */

                // Replace the block contents
                program.splice(i + 1..j, std::iter::once(synthetic_instruction));

                // Adjust the index to continue after the synthetic instruction
                i += 1;
            } else {
                i += 1;
            }
        } else {
            i += 1;
        }
    }

    blocks
}

pub fn generate_precompile(
    statements: &Vec<FunctionStatement>,
    instruction_map: &HashMap<String, Instruction>,
    degree: MachineDegree,
    wits: &[&PilStatement],
    identities: &[&PilStatement],
    main_links: &[LinkDefinition],
) -> Machine {
    let mut ssa_counter = 0;
    let mut constraints: Vec<PilStatement> = Vec::new();
    let mut links: Vec<LinkDefinition> = Vec::new();

    // let latch = 1;
    let latch = PilStatement::LetStatement(
        Default::default(),
        "latch".to_string(),
        None,
        Some(Expression::Number(
            Default::default(),
            Number {
                value: BigUint::from(1u32),
                type_: None,
            },
        )),
    );

    // let operation_id;
    //let op_id =
    //    PilStatement::LetStatement(Default::default(), "operation_id".to_string(), None, None);

    // let step;
    let step = PilStatement::LetStatement(Default::default(), "step".to_string(), None, None);

    // std::array::sum(sel)
    let sum_fun_symbol = SymbolPath::from_parts(
        ["std", "array", "sum"]
            .into_iter()
            .map(|p| Part::Named(p.to_string())),
    );
    let sum_fun: NamespacedPolynomialReference = sum_fun_symbol.into();
    let sum_fun: Expression = Expression::Reference(Default::default(), sum_fun);
    let sel_symbol = SymbolPath::from_identifier("sel".to_string());
    let sel: NamespacedPolynomialReference = sel_symbol.into();
    let sel = Expression::Reference(Default::default(), sel);
    let sum_sel = Expression::FunctionCall(
        Default::default(),
        FunctionCall {
            function: Box::new(sum_fun),
            arguments: vec![sel],
        },
    );

    // let used = std::array::sum(sel);
    let used =
        PilStatement::LetStatement(Default::default(), "used".to_string(), None, Some(sum_sel));

    // std::utils::force_bool(used);
    let bool_fun_symbol = SymbolPath::from_parts(
        ["std", "utils", "force_bool"]
            .into_iter()
            .map(|p| Part::Named(p.to_string())),
    );
    let bool_fun: NamespacedPolynomialReference = bool_fun_symbol.into();
    let bool_fun: Expression = Expression::Reference(Default::default(), bool_fun);
    let used_symbol = SymbolPath::from_identifier("used".to_string());
    let used_ref: NamespacedPolynomialReference = used_symbol.into();
    let used_ref = Expression::Reference(Default::default(), used_ref);
    let bool_used_ref = Expression::FunctionCall(
        Default::default(),
        FunctionCall {
            function: Box::new(bool_fun),
            arguments: vec![used_ref.clone()],
        },
    );
    let bool_used_ref = PilStatement::Expression(Default::default(), bool_used_ref);

    // operation run step;
    let op_param = Param {
        source: Default::default(),
        name: "step".to_string(),
        index: None,
        ty: None,
    };
    let run_symbol = OperationSymbol {
        source: Default::default(),
        id: OperationId { id: None },
        params: Params::<Param>::new(vec![op_param], vec![]),
    };
    let run_symbol = CallableSymbol::Operation(run_symbol);
    let callable_defs =
        CallableSymbolDefinitions([("run".to_string(), run_symbol)].into_iter().collect());

    constraints.push(step);
    constraints.push(latch);
    //constraints.push(op_id);
    constraints.push(used);
    constraints.push(bool_used_ref);

    let step_symbol = SymbolPath::from_identifier("step".to_string());
    let step_ref: NamespacedPolynomialReference = step_symbol.into();
    let step_ref = Expression::Reference(Default::default(), step_ref);

    let four = Expression::Number(
        Default::default(),
        Number {
            value: BigUint::from(4u32),
            type_: None,
        },
    );

    for stmt in statements {
        match stmt {
            FunctionStatement::Instruction(InstructionStatement {
                source: _,
                instruction,
                inputs,
            }) => {
                if let Some(instr_def) = instruction_map.get(instruction) {
                    let instr_inputs = instr_def
                        .params
                        .inputs
                        .iter()
                        .map(|p| p.name.clone())
                        .collect::<Vec<_>>();

                    // Create initial substitution map
                    let sub_map: HashMap<String, Expression> =
                        instr_inputs.into_iter().zip(inputs.clone()).collect();

                    // STEP_0 = step;
                    // STEP_i = STEP_{i-1} + 1;
                    let prev_step_ref = if ssa_counter == 0 {
                        step_ref.clone()
                    } else {
                        let prev_step_symbol =
                            SymbolPath::from_identifier(format!("STEP_{}", ssa_counter - 1));
                        let prev_step_ref: NamespacedPolynomialReference = prev_step_symbol.into();
                        let prev_step_ref =
                            Expression::Reference(Default::default(), prev_step_ref);
                        Expression::new_binary(
                            prev_step_ref.clone(),
                            BinaryOperator::Add,
                            four.clone(),
                        )
                    };

                    let step_i = PilStatement::LetStatement(
                        Default::default(),
                        format!("STEP_{ssa_counter}"),
                        None,
                        Some(prev_step_ref),
                    );

                    constraints.push(step_i);

                    // Witness columns from main
                    let local_wits = wits
                        .iter()
                        .map(|wit| {
                            if let PilStatement::PolynomialCommitDeclaration(
                                source,
                                stage,
                                names,
                                value,
                            ) = wit
                            {
                                PilStatement::PolynomialCommitDeclaration(
                                    source.clone(),
                                    *stage,
                                    names
                                        .iter()
                                        .map(|n| format!("{}_{}", n.clone(), ssa_counter).into())
                                        .collect::<Vec<_>>(),
                                    value.clone(),
                                )
                            } else {
                                panic!("Expected PolynomialCommitDeclaration")
                            }
                        })
                        .collect::<Vec<_>>();

                    // Constraints from main
                    let local_identities = identities
                        .iter()
                        .map(|id| {
                            if let PilStatement::Expression(source, expr) = id {
                                let mut expr = expr.clone();
                                append_suffix_mut(&mut expr, &ssa_counter.to_string());
                                PilStatement::Expression(source.clone(), expr)
                            } else {
                                panic!("Expected PolynomialCommitDeclaration")
                            }
                        })
                        .collect::<Vec<_>>();

                    constraints.extend(local_wits);
                    constraints.extend(local_identities);

                    // Links from main
                    for link in main_links {
                        let mut link = link.clone();
                        for e in &mut link.to.params.inputs_and_outputs_mut() {
                            substitute(e, &sub_map);
                            append_suffix_mut(e, &ssa_counter.to_string());
                        }
                        links.push(link);
                    }

                    // Process Links
                    for link in &instr_def.links {
                        let sub_inputs = link
                            .link
                            .params
                            .inputs
                            .clone()
                            .into_iter()
                            .map(|mut p| {
                                substitute(&mut p, &sub_map);
                                append_suffix_mut(&mut p, &ssa_counter.to_string());
                                p
                            })
                            .collect::<Vec<_>>();
                        let sub_outputs = link
                            .link
                            .params
                            .outputs
                            .clone()
                            .into_iter()
                            .map(|mut p| {
                                substitute(&mut p, &sub_map);
                                append_suffix_mut(&mut p, &ssa_counter.to_string());
                                p
                            })
                            .collect::<Vec<_>>();
                        let sub_link_link = CallableRef {
                            instance: link.link.instance.clone(),
                            callable: link.link.callable.clone(),
                            params: Params::<Expression>::new(sub_inputs, sub_outputs),
                        };

                        links.push(LinkDefinition {
                            source: Default::default(),
                            instr_flag: None,
                            link_flag: used_ref.clone(),
                            to: sub_link_link,
                            is_permutation: link.is_permutation,
                        });
                    }

                    // Process constraints
                    for pil_stmt in &instr_def.body.0 {
                        if let PilStatement::Expression(source, expr) = pil_stmt {
                            let mut expr = expr.clone();
                            substitute(&mut expr, &sub_map);
                            append_suffix_mut(&mut expr, &ssa_counter.to_string());
                            constraints.push(PilStatement::Expression(source.clone(), expr));
                        }
                    }

                    ssa_counter += 1;
                }
            }
            _ => {
                // Handle other statement types if necessary
            }
        }
    }

    let regs_param = Param {
        source: Default::default(),
        name: "regs".to_string(),
        index: None,
        ty: Some(SymbolPath::from_parts(
            ["std", "machines", "large_field", "memory", "Memory"]
                .iter()
                .map(|p| Part::Named(p.to_string())),
        )),
    };
    let mem_param = Param {
        source: Default::default(),
        name: "memory".to_string(),
        index: None,
        ty: Some(SymbolPath::from_parts(
            ["std", "machines", "large_field", "memory", "Memory"]
                .iter()
                .map(|p| Part::Named(p.to_string())),
        )),
    };
    let split_param = Param {
        source: Default::default(),
        name: "split_gl".to_string(),
        index: None,
        ty: Some(SymbolPath::from_parts(
            ["std", "machines", "split", "split_gl", "SplitGL"]
                .iter()
                .map(|p| Part::Named(p.to_string())),
        )),
    };
    let binary_param = Param {
        source: Default::default(),
        name: "binary".to_string(),
        index: None,
        ty: Some(SymbolPath::from_parts(
            ["std", "machines", "large_field", "binary", "Binary"]
                .iter()
                .map(|p| Part::Named(p.to_string())),
        )),
    };
    let shift_param = Param {
        source: Default::default(),
        name: "shift".to_string(),
        index: None,
        ty: Some(SymbolPath::from_parts(
            ["std", "machines", "large_field", "shift", "Shift"]
                .iter()
                .map(|p| Part::Named(p.to_string())),
        )),
    };
    let byte_param = Param {
        source: Default::default(),
        name: "byte".to_string(),
        index: None,
        ty: Some(SymbolPath::from_parts(
            ["std", "machines", "range", "Byte"]
                .iter()
                .map(|p| Part::Named(p.to_string())),
        )),
    };
    let bit2_param = Param {
        source: Default::default(),
        name: "bit2".to_string(),
        index: None,
        ty: Some(SymbolPath::from_parts(
            ["std", "machines", "range", "Bit2"]
                .iter()
                .map(|p| Part::Named(p.to_string())),
        )),
    };
    let bit6_param = Param {
        source: Default::default(),
        name: "bit6".to_string(),
        index: None,
        ty: Some(SymbolPath::from_parts(
            ["std", "machines", "range", "Bit6"]
                .iter()
                .map(|p| Part::Named(p.to_string())),
        )),
    };
    let bit7_param = Param {
        source: Default::default(),
        name: "bit7".to_string(),
        index: None,
        ty: Some(SymbolPath::from_parts(
            ["std", "machines", "range", "Bit7"]
                .iter()
                .map(|p| Part::Named(p.to_string())),
        )),
    };
    Machine {
        degree,
        latch: Some("latch".to_string()),
        //operation_id: Some("operation_id".to_string()),
        operation_id: None,
        call_selectors: Some("sel".to_string()),
        params: MachineParams(vec![
            regs_param,
            mem_param,
            split_param,
            binary_param,
            shift_param,
            byte_param,
            bit2_param,
            bit6_param,
            bit7_param,
        ]),
        registers: Vec::new(),
        pc: None,
        pil: constraints,
        instructions: Vec::new(),
        links,
        callable: callable_defs,
        submachines: Vec::new(),
    }
}

fn substitute(expr: &mut Expression, sub: &HashMap<String, Expression>) {
    expr.visit_expressions_mut(
        &mut |expr| {
            if let Expression::Reference(_, ref mut r) = expr {
                if let Some(sub_expr) = sub.get(&r.path.to_string()) {
                    *expr = sub_expr.clone();
                }
            }
            ControlFlow::Continue::<()>(())
        },
        VisitOrder::Pre,
    );
}

fn append_suffix_mut(expr: &mut Expression, suffix: &str) {
    expr.visit_expressions_mut(
        &mut |expr| match expr {
            Expression::FunctionCall(_, ref mut fun_call) => {
                for arg in &mut fun_call.arguments {
                    append_suffix_mut(arg, suffix);
                }
                ControlFlow::Break::<()>(())
            }
            Expression::Reference(_, ref mut r) => {
                let name = r.path.try_last_part().unwrap();
                let name = format!("{name}_{suffix}");
                *r.path.try_last_part_mut().unwrap() = name;
                ControlFlow::Continue::<()>(())
            }
            _ => ControlFlow::Continue::<()>(()),
        },
        VisitOrder::Pre,
    );
}

fn collect_columns(expr: &Expression) -> Vec<String> {
    let mut cols: Vec<_> = Vec::new();
    expr.visit_expressions(
        &mut |expr| match expr {
            Expression::FunctionCall(_, ref fun_call) => {
                for arg in &fun_call.arguments {
                    cols.extend(collect_columns(arg));
                }
                ControlFlow::Break::<()>(())
            }
            Expression::Reference(_, ref r) => {
                let name = r.path.try_last_part().unwrap();
                cols.push(name.clone());
                ControlFlow::Continue::<()>(())
            }
            _ => ControlFlow::Continue::<()>(()),
        },
        VisitOrder::Pre,
    );
    cols
}

fn optimize_precompiles(mut analyzed_asm: AnalysisASMFile) -> AnalysisASMFile {
    let machine = analyzed_asm
        .get_machine_mut(&parse_absolute_path("::Main"))
        .unwrap();
    let CallableSymbol::Function(ref mut main_function) =
        &mut machine.callable.0.get_mut("main").unwrap()
    else {
        panic!("main function missing")
    };

    let blocks = simplify_autoprecompile_blocks(&mut main_function.body.statements);
    let new_fs = FunctionStatements::new(main_function.body.statements.inner.clone());
    main_function.body.statements = new_fs.clone();
    //println!("new statements: {new_fs}");

    let wits = machine
        .pil
        .iter()
        .filter(|stmt| matches!(stmt, PilStatement::PolynomialCommitDeclaration(_, _, _, _)))
        .collect::<Vec<_>>();

    let identities = machine
        .pil
        .iter()
        .filter(|stmt| matches!(stmt, PilStatement::Expression(_, _)))
        .collect::<Vec<_>>();

    let name_to_instr: HashMap<String, Instruction> = machine
        .instructions
        .iter()
        .map(|instr| (instr.name.clone(), instr.instruction.clone()))
        .collect();

    if blocks.is_empty() {
        return analyzed_asm;
    }

    let precompile_module_name = blocks[0].0.clone();
    let precompile_machine_name = format!("Precompile_{precompile_module_name}");
    let precompile_submachine_name = format!("instance_{precompile_module_name}");
    let precompile_instr_name = precompile_module_name.clone();

    let precompile = generate_precompile(
        &blocks[0].1,
        &name_to_instr,
        machine.degree.clone(),
        &wits,
        &identities,
        &machine.links,
    );

    let precompile = optimize_precompile(precompile);
    println!("New precompile:\n{precompile}");

    let mut module = Module::new(Default::default(), Default::default(), Default::default());
    module.push_machine(precompile_machine_name.clone(), precompile);
    let module_path = parse_absolute_path(&format!("::{precompile_module_name}"));

    let mut submachine_path = module_path.clone();
    submachine_path.push(precompile_machine_name);

    let args = vec![
        "regs",
        "memory",
        "split_gl",
        "binary",
        "shift",
        "byte",
        "bit2",
        "bit6",
        "bit7",
        "MIN_DEGREE",
        "MAIN_MAX_DEGREE",
    ];
    let precompile_decl = SubmachineDeclaration {
        name: precompile_submachine_name.clone(),
        ty: submachine_path,
        args: args
            .into_iter()
            .map(|s| {
                Expression::Reference(
                    Default::default(),
                    NamespacedPolynomialReference::from_identifier(s.to_string()),
                )
            })
            .collect(),
    };
    machine.submachines.push(precompile_decl);

    let step = Expression::Reference(
        Default::default(),
        NamespacedPolynomialReference::from_identifier("STEP".to_string()),
    );

    let link_callable = CallableRef {
        instance: precompile_submachine_name,
        callable: "run".to_string(),
        params: Params::new(vec![step], vec![]),
    };
    let one = Expression::Number(
        Default::default(),
        Number {
            value: BigUint::from(1u32),
            type_: None,
        },
    );
    let link = LinkDeclaration {
        flag: one,
        link: link_callable,
        is_permutation: true,
    };
    let instruction = Instruction {
        params: Default::default(),
        links: vec![link],
        body: InstructionBody(vec![]),
    };
    let instr_decl = InstructionDefinitionStatement {
        source: Default::default(),
        name: precompile_instr_name,
        instruction,
    };
    machine.instructions.push(instr_decl);

    analyzed_asm.modules.insert(module_path.clone(), module);

    let main_module = analyzed_asm
        .modules
        .get_mut(&AbsoluteSymbolPath::default())
        .unwrap();
    main_module.push_module(precompile_module_name);

    println!("Optimized ASM:\n{analyzed_asm}");

    analyzed_asm
}

fn create_precompiles(
    mut analyzed_asm: AnalysisASMFile,
    selected: &HashSet<String>,
) -> AnalysisASMFile {
    let machine = analyzed_asm
        .get_machine_mut(&parse_absolute_path("::Main"))
        .unwrap();
    let CallableSymbol::Function(ref mut main_function) =
        &mut machine.callable.0.get_mut("main").unwrap()
    else {
        panic!("main function missing")
    };

    let blocks = transform_autoprecompile_blocks(&mut main_function.body.statements, selected);

    if blocks.is_empty() {
        return analyzed_asm;
    }

    let new_fs = FunctionStatements::new(main_function.body.statements.inner.clone());
    main_function.body.statements = new_fs.clone();
    //println!("new statements: {new_fs}");

    let wits = machine
        .pil
        .iter()
        .filter(|stmt| matches!(stmt, PilStatement::PolynomialCommitDeclaration(_, _, _, _)))
        .collect::<Vec<_>>();

    let identities = machine
        .pil
        .iter()
        .filter(|stmt| matches!(stmt, PilStatement::Expression(_, _)))
        .collect::<Vec<_>>();

    let name_to_instr: HashMap<String, Instruction> = machine
        .instructions
        .iter()
        .map(|instr| (instr.name.clone(), instr.instruction.clone()))
        .collect();

    let degree = machine.degree.clone();

    let mut module_names = Vec::new();
    let mut modules = Vec::new();

    for block in &blocks {
        let precompile_module_name = block.0.clone();
        let precompile_machine_name = format!("Precompile_{precompile_module_name}");
        let precompile_submachine_name = format!("instance_{precompile_module_name}");
        let precompile_instr_name = precompile_module_name.clone();

        let precompile = generate_precompile(
            &block.1,
            &name_to_instr,
            degree.clone(),
            &wits,
            &identities,
            &machine.links,
        );

        let precompile = optimize_precompile(precompile);
        println!("New precompile:\n{precompile}");

        let mut module = Module::new(Default::default(), Default::default(), Default::default());
        module.push_machine(precompile_machine_name.clone(), precompile);
        let module_path = parse_absolute_path(&format!("::{precompile_module_name}"));

        let mut submachine_path = module_path.clone();
        submachine_path.push(precompile_machine_name);

        let args = vec![
            "regs",
            "memory",
            "split_gl",
            "binary",
            "shift",
            "byte",
            "bit2",
            "bit6",
            "bit7",
            "MIN_DEGREE",
            "MAIN_MAX_DEGREE",
        ];
        let precompile_decl = SubmachineDeclaration {
            name: precompile_submachine_name.clone(),
            ty: submachine_path,
            args: args
                .into_iter()
                .map(|s| {
                    Expression::Reference(
                        Default::default(),
                        NamespacedPolynomialReference::from_identifier(s.to_string()),
                    )
                })
                .collect(),
        };
        machine.submachines.push(precompile_decl);

        let step = Expression::Reference(
            Default::default(),
            NamespacedPolynomialReference::from_identifier("STEP".to_string()),
        );

        let link_callable = CallableRef {
            instance: precompile_submachine_name,
            callable: "run".to_string(),
            params: Params::new(vec![step], vec![]),
        };
        let one = Expression::Number(
            Default::default(),
            Number {
                value: BigUint::from(1u32),
                type_: None,
            },
        );
        let link = LinkDeclaration {
            flag: one,
            link: link_callable,
            is_permutation: true,
        };
        let instruction = Instruction {
            params: Default::default(),
            links: vec![link],
            body: InstructionBody(vec![]),
        };
        let instr_decl = InstructionDefinitionStatement {
            source: Default::default(),
            name: precompile_instr_name,
            instruction,
        };
        machine.instructions.push(instr_decl);

        //analyzed_asm.modules.insert(module_path.clone(), module);

        //main_module.push_module(precompile_module_name);
        module_names.push(precompile_module_name);
        modules.push((module_path.clone(), module));
    }

    for module in modules {
        analyzed_asm.modules.insert(module.0, module.1);
    }

    let main_module = analyzed_asm
        .modules
        .get_mut(&AbsoluteSymbolPath::default())
        .unwrap();

    for module in module_names {
        main_module.push_module(module);
    }

    println!("Optimized ASM:\n{analyzed_asm}");

    analyzed_asm
}

fn optimize_precompile(mut machine: Machine) -> Machine {
    let mut scc: HashSet<String> = HashSet::new();

    // We use operation inputs/outputs as scc sources
    for callable in machine.callable.0.values() {
        match callable {
            CallableSymbol::Operation(symbol) => {
                symbol.params.inputs_and_outputs().for_each(|p| {
                    scc.insert(p.name.clone());
                });
            }
            CallableSymbol::Function(symbol) => {
                symbol.params.inputs_and_outputs().for_each(|p| {
                    scc.insert(p.name.clone());
                });
            }
        }
    }

    // Use args of mstore links as sources too
    for link in &machine.links {
        let callable = &link.to.callable;
        if callable == "mstore" {
            scc.extend(collect_columns(&link.link_flag));
            if let Some(ref flag) = &link.instr_flag {
                scc.extend(collect_columns(flag));
            }
            for p in link.to.params.inputs_and_outputs() {
                scc.extend(collect_columns(p));
            }
        }
    }

    //println!("Optimizer source SCC = {:?}", scc);

    // Collect connected items until we can't anymore.
    // This is ofc slower than a proper SCC algorithm, but it's fine for now.
    loop {
        let pre_len = scc.len();

        // Collect all cols in links.
        // For a given link, if one col is part of the SCC,
        // add all others.
        for link in &machine.links {
            //println!("Checking link {}", link);
            let mut local: HashSet<String> = HashSet::new();
            local.extend(collect_columns(&link.link_flag));
            if let Some(ref flag) = &link.instr_flag {
                local.extend(collect_columns(flag));
            }
            for p in link.to.params.inputs_and_outputs() {
                local.extend(collect_columns(p));
            }
            //println!("Local SCC = {:?}", local);
            if local.iter().any(|c| scc.contains(c)) {
                scc.extend(local);
            }
        }
        //println!("Extended SCC after links = {:?}", scc);

        // Collect all cols in identities.
        // For a given identity, if one col is part of the SCC,
        // add all others.
        for stmt in &machine.pil {
            let mut local: HashSet<String> = HashSet::new();
            if let PilStatement::Expression(_, ref expr) = stmt {
                local.extend(collect_columns(expr));
            }
            if local.iter().any(|c| scc.contains(c)) {
                scc.extend(local);
            }
        }
        //println!("Extended SCC after pils = {:?}", scc);

        let post_len = scc.len();
        if pre_len == post_len {
            break;
        }
    }

    //println!("Optimizer converged SCC = {:?}", scc);

    // Remove all links that are not part of the SCC
    machine.links.retain(|link| {
        let mut local: HashSet<String> = HashSet::new();
        local.extend(collect_columns(&link.link_flag));
        if let Some(ref flag) = &link.instr_flag {
            local.extend(collect_columns(flag));
        }
        for p in link.to.params.inputs_and_outputs() {
            local.extend(collect_columns(p));
        }
        local.iter().all(|c| scc.contains(c))
    });

    // Remove all identities that are not part of the SCC
    machine.pil.retain(|stmt| {
        if let PilStatement::Expression(_, ref expr) = stmt {
            let cols = collect_columns(expr);
            cols.iter().all(|c| scc.contains(c))
        } else {
            true
        }
    });

    println!("Optimized machine: before mloads\n{machine}");

    // Optimize mloads.
    let mut mem: HashMap<u64, Expression> = HashMap::new();
    machine.links.retain(|link| {
        let callable = &link.to.callable;
        if link.to.instance != "regs" || (callable != "mload" && callable != "mstore") {
            return true;
        }

        let inputs = &link.to.params.inputs;
        let outputs = &link.to.params.outputs;

        let reg: u64 = match &inputs[0] {
            Expression::Number(_, ref n) => n.value.clone().try_into().unwrap(),
            _ => panic!("Expected number"),
        };

        if callable == "mload" {
            assert_eq!(outputs.len(), 1);
            let cols = collect_columns(&outputs[0]);
            assert_eq!(cols.len(), 1);
            let output_col = &cols[0];

            if let Some(col) = mem.get(&reg) {
                machine.pil.push(PilStatement::Expression(
                    Default::default(),
                    Expression::new_binary(
                        Expression::Reference(
                            Default::default(),
                            NamespacedPolynomialReference::from_identifier(output_col.clone()),
                        ),
                        BinaryOperator::Identity,
                        col.clone(), /*
                                     Expression::Reference(
                                         Default::default(),
                                         NamespacedPolynomialReference::from_identifier(col.clone()),
                                     )*/
                    ),
                ));
                return false;
            } else {
                //mem.insert(reg, output_col.clone());
                mem.insert(reg, outputs[0].clone());
            }
        } else if callable == "mstore" {
            assert_eq!(inputs.len(), 3);

            //let cols = collect_columns(&inputs[2]);
            //println!("cols = {cols:?}");
            //assert_eq!(cols.len(), 1);
            //let value = &cols[0];

            //mem.insert(reg, value.clone());
            mem.insert(reg, inputs[2].clone());
        }
        true
    });

    // Optimize mstores.
    let mut last_store: HashMap<u64, usize> = HashMap::new();
    for (i, link) in machine.links.iter().enumerate() {
        let callable = &link.to.callable;
        if link.to.instance != "regs" || callable != "mstore" {
            continue;
        }

        let inputs = &link.to.params.inputs;

        let reg: u64 = match &inputs[0] {
            Expression::Number(_, ref n) => n.value.clone().try_into().unwrap(),
            _ => panic!("Expected number"),
        };

        last_store.insert(reg, i);
    }

    machine.links = machine
        .links
        .into_iter()
        .enumerate()
        .filter_map(|(i, link)| {
            let callable = &link.to.callable;
            if link.to.instance != "regs" || callable != "mstore" {
                // Retain non-mstore links
                return Some(link);
            }

            let inputs = &link.to.params.inputs;

            let reg: u64 = match &inputs[0] {
                Expression::Number(_, ref n) => n.value.clone().try_into().unwrap(),
                _ => panic!("Expected number"),
            };

            // Retain only if this index is the last `mstore` for this address
            if last_store
                .get(&reg)
                .is_some_and(|&last_index| last_index == i)
            {
                Some(link)
            } else {
                None
            }
        })
        .collect();

    // Move all memory links to the end because of witgen.
    let mut memory_links = vec![];
    machine.links.retain(|link| {
        if link.to.instance == "memory" || link.to.instance == "regs" {
            memory_links.push(link.clone());
            false
        } else {
            true
        }
    });
    machine.links.extend(memory_links);

    machine
}

pub fn collect_basic_blocks(
    analyzed_asm: &AnalysisASMFile,
) -> Vec<(String, Vec<FunctionStatement>)> {
    let machine = analyzed_asm
        .get_machine(&parse_absolute_path("::Main"))
        .unwrap();
    let CallableSymbol::Function(ref main_function) = &mut machine.callable.0.get("main").unwrap()
    else {
        panic!("main function missing")
    };

    let program = &main_function.body.statements.inner;

    let mut blocks = Vec::new();
    let mut ghost_labels = 0;
    let mut curr_label = format!("ghost_label_{ghost_labels}");
    let mut block_statements = Vec::new();

    for op in program {
        match &op {
            FunctionStatement::Label(LabelStatement { source: _, name }) => {
                blocks.push((curr_label.clone(), block_statements.clone()));
                block_statements.clear();
                curr_label = name.clone();
            }
            FunctionStatement::Instruction(InstructionStatement {
                source: _,
                instruction,
                inputs: _,
            }) if instruction.starts_with("branch") || instruction.starts_with("jump") => {
                blocks.push((curr_label.clone(), block_statements.clone()));
                block_statements.clear();
                ghost_labels += 1;
                curr_label = format!("ghost_label_{ghost_labels}");
            }
            FunctionStatement::Instruction(InstructionStatement {
                source: _,
                instruction: _,
                inputs: _,
            })
            | FunctionStatement::Assignment(_) => {
                block_statements.push(op.clone());
            }
            FunctionStatement::Return(_) => {
                blocks.push((curr_label.clone(), block_statements.clone()));
                block_statements.clear();
                ghost_labels += 1;
                curr_label = format!("ghost_label_{ghost_labels}");
            }
            _ => {}
        }
    }

    blocks
}

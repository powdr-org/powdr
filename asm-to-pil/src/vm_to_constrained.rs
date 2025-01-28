//! Compilation from powdr assembly to PIL

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    iter::once,
};

use powdr_ast::{
    asm_analysis::{
        combine_flags, AssignmentStatement, Batch, CallableSymbol, CallableSymbolDefinitions,
        DebugDirective, FunctionStatement, InstructionDefinitionStatement, InstructionStatement,
        LabelStatement, LinkDefinition, Machine, MachineDegree, OperationSymbol,
        RegisterDeclarationStatement, RegisterTy, Rom,
    },
    parsed::{
        self,
        asm::{
            CallableParams, CallableRef, InstructionBody, InstructionParams, LinkDeclaration,
            OperationId, Param, Params,
        },
        build::{self, absolute_reference, direct_reference, next_reference},
        visitor::ExpressionVisitable,
        ArrayExpression, BinaryOperation, BinaryOperator, Expression, FunctionCall,
        FunctionDefinition, FunctionKind, LambdaExpression, MatchArm, MatchExpression, Number,
        Pattern, PilStatement, PolynomialName, UnaryOperation, UnaryOperator,
    },
};
use powdr_number::{BigUint, FieldElement, LargeInt};
use powdr_parser_util::SourceRef;

use crate::{
    common::{instruction_flag, return_instruction, RETURN_NAME},
    utils::parse_pil_statement,
};

pub fn convert_machine<T: FieldElement>(
    machine: Machine,
    rom: Option<Rom>,
) -> (Machine, Option<Machine>) {
    let output_count = machine
        .operations()
        .map(|f| f.params.outputs.len())
        .max()
        .unwrap_or_default();
    VMConverter::<T>::with_output_count(output_count).convert_machine(machine, rom)
}

pub enum Input {
    Register(String),
    Literal(String, LiteralKind),
}

pub enum LiteralKind {
    Label,
    SignedConstant,
    UnsignedConstant,
}

const ROM_OPERATION_ID: &str = "operation_id";
const ROM_LATCH: &str = "latch";
pub const ROM_SUBMACHINE_NAME: &str = "_rom";
const ROM_ENTRY_POINT: &str = "get_line";
const CALL_SELECTORS: &str = "call_selectors";

fn rom_machine<'a>(
    degree: MachineDegree,
    mut pil: Vec<PilStatement>,
    mut line_lookup: impl Iterator<Item = &'a str>,
) -> Machine {
    Machine {
        degree,
        operation_id: Some(ROM_OPERATION_ID.into()),
        latch: Some(ROM_LATCH.into()),
        pil: {
            pil.extend([
                parse_pil_statement(&format!("pol fixed {ROM_OPERATION_ID} = [0]*;")),
                parse_pil_statement(&format!("pol fixed {ROM_LATCH} = [1]*;")),
            ]);
            pil
        },
        callable: CallableSymbolDefinitions(
            once((
                ROM_ENTRY_POINT.into(),
                CallableSymbol::Operation(OperationSymbol {
                    source: SourceRef::unknown(),
                    id: OperationId {
                        id: Some(0u32.into()),
                    },
                    params: Params {
                        inputs: (&mut line_lookup)
                            .take(1)
                            .map(|x| Param {
                                source: SourceRef::unknown(),
                                name: x.to_string(),
                                index: None,
                                ty: None,
                            })
                            .collect(),
                        outputs: line_lookup
                            .map(|x| Param {
                                source: SourceRef::unknown(),
                                name: x.to_string(),
                                index: None,
                                ty: None,
                            })
                            .collect(),
                    },
                }),
            ))
            .collect(),
        ),
        ..Default::default()
    }
}

/// Component that turns a virtual machine into a constrained machine.
/// TODO check if the conversion really depends on the finite field.
#[derive(Default)]
struct VMConverter<T> {
    pil: Vec<PilStatement>,
    rom_pil: Vec<PilStatement>,
    pc_name: Option<String>,
    assignment_register_names: Vec<String>,
    registers: BTreeMap<String, Register>,
    instructions: BTreeMap<String, Instruction>,
    code_lines: Vec<CodeLine<T>>,
    /// Pairs of columns that are used in the connecting plookup
    line_lookup: Vec<(String, String)>,
    /// Names of fixed columns that contain the rom.
    rom_constant_names: Vec<String>,
    /// the maximum number of inputs in all functions
    output_count: usize,
    _phantom: std::marker::PhantomData<T>,
}

impl<T: FieldElement> VMConverter<T> {
    fn with_output_count(output_count: usize) -> Self {
        Self {
            output_count,
            ..Default::default()
        }
    }

    fn convert_machine(
        mut self,
        mut input: Machine,
        rom: Option<Rom>,
    ) -> (Machine, Option<Machine>) {
        if !input.has_pc() {
            assert!(rom.is_none());
            return (input, None);
        }

        // store the names of all assignment registers: we need them to generate assignment columns for other registers.
        assert!(self.assignment_register_names.is_empty());
        self.assignment_register_names = input
            .assignment_register_names()
            .map(|s| s.to_string())
            .collect();

        // turn registers into columns and constraints
        for reg in input.registers.drain(..) {
            self.handle_register_declaration(reg);
        }

        // turn internal instructions into constraints and external ones into links
        for instr in std::mem::take(&mut input.instructions) {
            self.handle_instruction_def(&mut input, instr);
        }

        // introduce `return` instruction
        self.handle_instruction_def(
            &mut input,
            InstructionDefinitionStatement {
                source: SourceRef::unknown(),
                name: RETURN_NAME.into(),
                instruction: self.return_instruction(),
            },
        );

        let assignment_registers = self
            .assignment_register_names()
            .cloned()
            .collect::<Vec<_>>();
        for reg in assignment_registers {
            self.create_constraints_for_assignment_reg(reg);
        }

        // introduce `first_step` which is used for register updates
        self.pil.push(PilStatement::PolynomialConstantDefinition(
            SourceRef::unknown(),
            "first_step".to_string(),
            FunctionDefinition::Array(ArrayExpression::value(vec![1u32.into()]).pad_with_zeroes()),
        ));

        self.pil.extend(
            self.registers
                .iter()
                .filter_map(|(name, reg)| {
                    reg.update_expression().map(|rhs| {
                        let lhs = next_reference(name);
                        use RegisterTy::*;
                        match reg.ty {
                            // Force pc to zero on first row.
                            Pc => {
                                // introduce an intermediate witness polynomial to keep the degree of polynomial identities at 2
                                // this may not be optimal for backends which support higher degree constraints
                                let pc_update_name = format!("{name}_update");
                                vec![
                                    witness_column(
                                        SourceRef::unknown(),
                                        pc_update_name.clone(),
                                        None,
                                    ),
                                    PilStatement::Expression(
                                        SourceRef::unknown(),
                                        build::identity(
                                            direct_reference(pc_update_name.clone()),
                                            rhs,
                                        ),
                                    ),
                                    PilStatement::Expression(
                                        SourceRef::unknown(),
                                        build::identity(
                                            lhs,
                                            (Expression::from(1) - next_reference("first_step"))
                                                * direct_reference(pc_update_name),
                                        ),
                                    ),
                                ]
                            }
                            // Un-constrain read-only registers when calling `_reset`
                            ReadOnly => {
                                let not_reset: Expression =
                                    Expression::from(1) - direct_reference("instr__reset");
                                vec![PilStatement::Expression(
                                    SourceRef::unknown(),
                                    build::identity(not_reset * (lhs - rhs), 0.into()),
                                )]
                            }
                            _ => {
                                vec![PilStatement::Expression(
                                    SourceRef::unknown(),
                                    build::identity(lhs, rhs),
                                )]
                            }
                        }
                    })
                })
                .flatten(),
        );

        for batch in rom.unwrap().statements.into_iter_batches() {
            self.handle_batch(batch);
        }

        input.latch = Some(instruction_flag(RETURN_NAME));

        self.translate_code_lines();

        input.links.push(LinkDefinition {
            source: SourceRef::unknown(),
            instr_flag: None,
            link_flag: Expression::from(1u32),
            to: CallableRef {
                instance: ROM_SUBMACHINE_NAME.to_string(),
                callable: ROM_ENTRY_POINT.to_string(),
                params: CallableParams {
                    inputs: self.line_lookup[..1]
                        .iter()
                        .map(|x| direct_reference(&x.0))
                        .collect(),
                    outputs: self.line_lookup[1..]
                        .iter()
                        .map(|x| direct_reference(&x.0))
                        .collect(),
                },
            },
            is_permutation: false,
        });

        assert!(input.call_selectors.is_none());
        input.call_selectors = Some(CALL_SELECTORS.into());

        if !self.pil.is_empty() {
            input.pil.extend(self.pil);
        }

        let rom_degree = Expression::from(self.code_lines.len().next_power_of_two() as u32).into();

        (
            input,
            Some(rom_machine(
                rom_degree,
                self.rom_pil,
                self.line_lookup.iter().map(|(_, x)| x.as_ref()),
            )),
        )
    }

    fn handle_batch(&mut self, batch: Batch) {
        let code_line = batch
            .statements
            .into_iter()
            .map(|s| self.handle_statement(s))
            .reduce(|mut acc, e| {
                // we write to the union of the target registers.
                assert!(acc.write_regs.is_empty());
                acc.write_regs.extend(e.write_regs);
                // we write the union of the written values.
                assert!(acc.value.is_empty());
                acc.value.extend(e.value);
                // we use the union of the used instructions.
                assert!(acc.instructions.is_empty());
                acc.instructions.extend(e.instructions);
                // we use the union of the labels
                acc.labels.extend(e.labels);
                // we use the union of debug directives
                acc.debug_directives.extend(e.debug_directives);
                acc
            })
            .expect("unexpected empty batch");

        self.code_lines.push(code_line);
    }

    fn handle_statement(&mut self, statement: FunctionStatement) -> CodeLine<T> {
        match statement {
            FunctionStatement::Assignment(AssignmentStatement {
                source,
                lhs_with_reg,
                rhs,
            }) => {
                let lhs_with_reg = lhs_with_reg
                    .into_iter()
                    // All assignment registers should be inferred at this point.
                    .map(|(lhs, reg)| (lhs, reg.unwrap()))
                    .collect();

                match *rhs {
                    Expression::FunctionCall(_, c) => {
                        self.handle_functional_instruction(lhs_with_reg, *c.function, c.arguments)
                    }
                    _ => self.handle_non_functional_assignment(source, lhs_with_reg, *rhs),
                }
            }
            FunctionStatement::Instruction(InstructionStatement {
                instruction,
                inputs,
                ..
            }) => self.handle_instruction(instruction, inputs),
            FunctionStatement::Label(LabelStatement { name, .. }) => CodeLine {
                labels: [name].into(),
                ..Default::default()
            },
            FunctionStatement::DebugDirective(d) => CodeLine {
                debug_directives: vec![d],
                ..Default::default()
            },
            FunctionStatement::Return(r) => self.handle_instruction(RETURN_NAME.into(), r.values),
        }
    }

    fn handle_register_declaration(
        &mut self,
        RegisterDeclarationStatement { source, ty, name }: RegisterDeclarationStatement,
    ) {
        let mut conditioned_updates = vec![];
        let mut default_update = None;
        match ty {
            RegisterTy::Pc => {
                assert_eq!(self.pc_name, None);
                self.pc_name = Some(name.to_string());
                self.line_lookup
                    .push((name.to_string(), "p_line".to_string()));
                default_update = Some(direct_reference(&name) + 1.into());
            }
            RegisterTy::Assignment => {
                // no default update as this is transient
            }
            RegisterTy::ReadOnly => {
                // default update to be kept constant
                default_update = Some(direct_reference(&name))
            }
            RegisterTy::Write => {
                let assignment_regs = self
                    .assignment_register_names()
                    .cloned()
                    .collect::<Vec<_>>();
                // TODO do this at the same place where we set up the read flags.
                for reg in assignment_regs {
                    let write_flag = format!("reg_write_{reg}_{name}");
                    self.create_witness_fixed_pair(source.clone(), &write_flag);
                    conditioned_updates
                        .push((direct_reference(&write_flag), direct_reference(&reg)));
                }
                default_update = Some(direct_reference(&name));
            }
        };
        self.registers.insert(
            name.to_string(),
            Register {
                conditioned_updates,
                default_update,
                ty,
            },
        );
        self.pil.push(witness_column(source, name, None));
    }

    fn handle_instruction_def(&mut self, input: &mut Machine, s: InstructionDefinitionStatement) {
        let instruction_name = s.name.clone();
        let instruction_flag = format!("instr_{instruction_name}");
        self.create_witness_fixed_pair(s.source.clone(), &instruction_flag);

        let params = s.instruction.params;

        // validate instruction links and add to machine links
        input.links.extend(s.instruction.links.into_iter().map(|l| {
            self.handle_instruction_link(s.source.clone(), &instruction_flag, &params, l)
        }));

        // validate instruction body
        self.handle_instruction_body(
            s.source,
            &instruction_name,
            &instruction_flag,
            &params,
            s.instruction.body,
        );

        let inputs: Vec<_> = params
            .inputs
            .into_iter()
            .map(|param| {
                match param
                    .ty
                    .as_ref()
                    .map(|ty| ty.try_to_identifier().map(|s| s.as_str()))
                {
                    Some(Some("label")) => Input::Literal(param.name, LiteralKind::Label),
                    Some(Some("signed")) => Input::Literal(param.name, LiteralKind::SignedConstant),
                    Some(Some("unsigned")) => {
                        Input::Literal(param.name, LiteralKind::UnsignedConstant)
                    }
                    Some(_) => panic!("Invalid param type: {}", param.ty.as_ref().unwrap()),
                    None => Input::Register(param.name),
                }
            })
            .collect();

        let outputs = params.outputs.into_iter().map(|param| param.name).collect();

        let instruction = Instruction { inputs, outputs };
        self.instructions.insert(instruction_name, instruction);
    }

    /// check parameters are valid and extend PIL from the definition
    fn handle_instruction_body(
        &mut self,
        source: SourceRef,
        name: &str,
        flag: &str,
        params: &InstructionParams,
        mut body: InstructionBody,
    ) {
        // check inputs are literals or assignment registers
        let mut literal_arg_names = vec![];
        for param in &params.inputs {
            assert!(
                param.index.is_none(),
                "Cannot use array elements for instruction parameters."
            );
            match param
                .ty
                .as_ref()
                .map(|ty| ty.try_to_identifier().map(|s| s.as_str()))
            {
                Some(Some("label" | "signed" | "unsigned")) => literal_arg_names.push(&param.name),
                Some(_) => panic!("Invalid param type: {}", param.ty.as_ref().unwrap()),
                None => {
                    if !self
                        .registers
                        .get(&param.name)
                        .is_some_and(|r| r.ty.is_assignment())
                    {
                        panic!(
                            "Register '{}' used for instruction input is not an assignment register.",
                            &param.name
                        );
                    }
                }
            }
        }

        // check outputs are assignment registers
        for param in &params.outputs {
            assert!(
                param.index.is_none(),
                "Cannot use array elements for instruction outputs."
            );
            assert!(
                param.ty.is_none() && self.registers[&param.name].ty.is_assignment(),
                "Register '{}' used for instruction output is not an assignment register.",
                &param.name
            );
        }

        // generate PIL from instruction body

        let substitutions = literal_arg_names
            .into_iter()
            .map(|arg_name| {
                let param_col_name = format!("instr_{name}_param_{arg_name}");
                self.create_witness_fixed_pair(source.clone(), &param_col_name);
                (arg_name.clone(), param_col_name)
            })
            .collect::<HashMap<_, _>>();
        body.0.iter_mut().for_each(|s| {
            s.post_visit_expressions_mut(&mut |e| {
                if let Expression::Reference(_, r) = e {
                    if let Some(name) = r.try_to_identifier() {
                        if let Some(sub) = substitutions.get(name) {
                            *r.path.try_last_part_mut().unwrap() = sub.to_string();
                        }
                    }
                }
            });
        });

        let instr_flag = direct_reference(flag);
        for statement in body.0 {
            let PilStatement::Expression(source, expr) = statement else {
                panic!("Invalid statement for instruction body: {statement}");
            };
            if let Some((var, expr)) = try_extract_update(&expr) {
                // Try to reduce the update to linear by introducing intermediate variables.
                // We do this to keep the degree of the update expression low, but it is
                // not strictly necessary.
                let expr = self.linearize(&format!("{flag}_{var}_update"), expr);

                self.registers
                    .get_mut(&var)
                    .unwrap()
                    .conditioned_updates
                    .push((instr_flag.clone(), expr));
            } else {
                let fun_call = Expression::FunctionCall(
                    source.clone(),
                    FunctionCall {
                        function: absolute_reference("::std::constraints::make_conditional").into(),
                        arguments: vec![expr, instr_flag.clone()],
                    },
                );
                self.pil.push(PilStatement::Expression(source, fun_call))
            }
        }
    }

    /// validade instruction link params and transform it into a link definition
    fn handle_instruction_link(
        &mut self,
        source: SourceRef,
        instr_flag: &str,
        instr_params: &InstructionParams,
        link_decl: LinkDeclaration,
    ) -> LinkDefinition {
        let callable: CallableRef = link_decl.link;
        let lhs = instr_params;
        let rhs = &callable.params;

        let mut rhs_assignment_registers = BTreeSet::new();
        let mut rhs_next_write_registers = BTreeSet::new();

        // collect assignment registers and next references to write registers used on rhs
        for expr in rhs.inputs_and_outputs() {
            expr.pre_visit_expressions(&mut |e| match e {
                Expression::Reference(_, poly) => {
                    poly.try_to_identifier()
                        .and_then(|name| self.registers.get(name).map(|reg| (name, reg)))
                        .filter(|(_, reg)| reg.ty == RegisterTy::Assignment)
                        .map(|(name, _)| rhs_assignment_registers.insert(name.clone()));
                }
                Expression::UnaryOperation(
                    _,
                    UnaryOperation {
                        op: UnaryOperator::Next,
                        expr: e,
                    },
                ) => {
                    if let Expression::Reference(_, poly) = e.as_ref() {
                        poly.try_to_identifier()
                            .and_then(|name| self.registers.get(name).map(|reg| (name, reg)))
                            .filter(|(_, reg)| {
                                [RegisterTy::Write, RegisterTy::Pc].contains(&reg.ty)
                            })
                            .map(|(name, _)| rhs_next_write_registers.insert(name.clone()));
                    }
                }
                _ => {}
            })
        }

        // any assignment register present on the rhs (input or output) must be
        // present on the instruction params
        for name in &rhs_assignment_registers {
            assert!(
                lhs.inputs_and_outputs().any(|p_lhs| p_lhs.name == *name),
                "Assignment register '{name}' used in link definition must be present in instruction params"
            );
        }

        let instr_flag = direct_reference(instr_flag);

        // if a write register next reference (R') is used in the instruction link,
        // we must induce a tautology in the update clause (R' = R') when the
        // link is active, to allow the operation plookup to match.
        let flag = combine_flags(Some(instr_flag.clone()), link_decl.flag.clone());
        for name in rhs_next_write_registers {
            let reg = self.registers.get_mut(&name).unwrap();
            let value = next_reference(name);
            reg.conditioned_updates.push((flag.clone(), value));
        }

        LinkDefinition {
            source,
            instr_flag: Some(instr_flag),
            link_flag: link_decl.flag,
            to: callable,
            is_permutation: link_decl.is_permutation,
        }
    }

    fn handle_non_functional_assignment(
        &mut self,
        _source: SourceRef,
        lhs_with_reg: Vec<(String, String)>,
        value: Expression,
    ) -> CodeLine<T> {
        assert!(
            lhs_with_reg.len() == 1,
            "Multi assignments are only implemented for function calls."
        );
        let (write_regs, assign_reg) = lhs_with_reg.into_iter().next().unwrap();
        let value = self.process_assignment_value(value);
        CodeLine {
            write_regs: [(assign_reg.clone(), vec![write_regs])]
                .into_iter()
                .collect(),
            value: [(assign_reg, value)].into(),
            ..Default::default()
        }
    }

    fn handle_functional_instruction(
        &mut self,
        lhs_with_regs: Vec<(String, String)>,
        function: Expression,
        mut args: Vec<Expression>,
    ) -> CodeLine<T> {
        let Expression::Reference(_, reference) = function else {
            panic!("Expected instruction name");
        };
        let instr_name = reference.try_to_identifier().unwrap();
        let instr = &self
            .instructions
            .get(instr_name)
            .unwrap_or_else(|| panic!("Instruction not found: {instr_name}"));
        let output = instr.outputs.clone();

        for (o, (_, r)) in output.iter().zip(lhs_with_regs.iter()) {
            assert!(
                o == r,
                "The instruction {instr_name} uses the output register {o}, but the caller uses {r} to further process the value.",
            );
        }

        args.extend(lhs_with_regs.iter().map(|(lhs, _)| direct_reference(lhs)));
        self.handle_instruction(instr_name.clone(), args)
    }

    fn handle_instruction(&mut self, instr_name: String, args: Vec<Expression>) -> CodeLine<T> {
        let instr = &self
            .instructions
            .get(&instr_name)
            .unwrap_or_else(|| panic!("Instruction not found: {instr_name}"));
        assert_eq!(
            instr.inputs.len() + instr.outputs.len(),
            args.len(),
            "Called instruction {instr_name} with the wrong number of arguments"
        );

        let mut args = args.into_iter();

        let (value, instruction_literal_args): (BTreeMap<_, _>, Vec<_>) =
            instr.inputs.iter().zip(&mut args).fold(
                Default::default(),
                |(mut value, mut instruction_literal_arg), (input, a)| {
                    match input {
                        Input::Register(reg) => {
                            // We read a value into the assignment register "reg".
                            assert!(!value.contains_key(reg));
                            value.insert(reg.clone(), self.process_assignment_value(a));
                        }
                        Input::Literal(_, LiteralKind::Label) => {
                            if let Expression::Reference(_, r) = a {
                                instruction_literal_arg.push(InstructionLiteralArg::LabelRef(
                                    r.try_to_identifier().unwrap().clone(),
                                ));
                            } else {
                                panic!();
                            }
                        }
                        Input::Literal(_, LiteralKind::UnsignedConstant) => {
                            // TODO evaluate expression
                            if let Expression::Number(_, Number {value, ..}) = a {
                                let half_modulus = T::modulus().to_arbitrary_integer() / BigUint::from(2u64);
                                assert!(value < half_modulus, "Number passed to unsigned parameter is negative or too large: {value}");
                                instruction_literal_arg.push(InstructionLiteralArg::Number(
                                    T::from(value),
                                ));
                            } else {
                                panic!("expected unsigned number, received {a}");
                            }
                        }
                        Input::Literal(_, LiteralKind::SignedConstant) => {
                            // TODO evaluate expression
                            if let Expression::Number(_, Number {value, ..}) = a {
                                instruction_literal_arg.push(InstructionLiteralArg::Number(
                                    T::checked_from(value).unwrap(),
                                ));
                            } else if let Expression::UnaryOperation(_, UnaryOperation { op: UnaryOperator::Minus, expr }) = a
                            {
                                if let Expression::Number(_, Number {value, ..}) = *expr {
                                    instruction_literal_arg.push(InstructionLiteralArg::Number(
                                        -T::checked_from(value).unwrap(),
                                    ))
                                } else {
                                    panic!();
                                }
                            } else {
                                panic!();
                            }
                        }
                    };
                    (value, instruction_literal_arg)
                },
            );

        let write_regs: BTreeMap<_, _> = instr
            .outputs
            .iter()
            .zip(&mut args)
            .map(|(reg, a)| {
                // Output a value trough assignment register "reg"
                if let Expression::Reference(_, r) = a {
                    (reg.clone(), vec![r.try_to_identifier().unwrap().clone()])
                } else {
                    panic!("Expected direct register to assign to in instruction call.");
                }
            })
            .collect();

        assert_eq!(write_regs.len(), instr.outputs.len());

        CodeLine {
            write_regs,
            instructions: vec![(instr_name.to_string(), instruction_literal_args)],
            value,
            ..Default::default()
        }
    }

    fn process_assignment_value(&self, value: Expression) -> Vec<(T, AffineExpressionComponent)> {
        match value {
            Expression::PublicReference(_, _) => panic!(),
            Expression::IndexAccess(_, _) => panic!(),
            Expression::FunctionCall(_, _) => panic!(),
            Expression::Reference(_, reference) => {
                // TODO check it actually is a register
                let name = reference.try_to_identifier().unwrap();
                vec![(1.into(), AffineExpressionComponent::Register(name.clone()))]
            }
            Expression::Number(_, Number { value, .. }) => {
                vec![(T::from(value), AffineExpressionComponent::Constant)]
            }
            Expression::String(_, _) => panic!(),
            Expression::Tuple(_, _) => panic!(),
            Expression::ArrayLiteral(_, _) => panic!(),
            Expression::MatchExpression(_, _) => panic!(),
            Expression::IfExpression(_, _) => panic!(),
            Expression::BlockExpression(_, _) => panic!(),
            Expression::FreeInput(_, expr) => {
                vec![(1.into(), AffineExpressionComponent::FreeInput(*expr))]
            }
            Expression::LambdaExpression(_, _) => {
                unreachable!("lambda expressions should have been removed")
            }
            Expression::BinaryOperation(_, BinaryOperation { left, op, right }) => match op {
                BinaryOperator::Add => self.add_assignment_value(
                    self.process_assignment_value(*left),
                    self.process_assignment_value(*right),
                ),
                BinaryOperator::Sub => self.add_assignment_value(
                    self.process_assignment_value(*left),
                    self.negate_assignment_value(self.process_assignment_value(*right)),
                ),
                BinaryOperator::Mul => {
                    let left = self.process_assignment_value(*left);
                    let right = self.process_assignment_value(*right);
                    if let [(f, AffineExpressionComponent::Constant)] = &left[..] {
                        // TODO overflow?
                        right
                            .into_iter()
                            .map(|(coeff, comp)| (*f * coeff, comp))
                            .collect()
                    } else if let [(f, AffineExpressionComponent::Constant)] = &right[..] {
                        // TODO overflow?
                        left.into_iter()
                            .map(|(coeff, comp)| (*f * coeff, comp))
                            .collect()
                    } else {
                        panic!("Multiplication by non-constant.");
                    }
                }
                BinaryOperator::Pow => {
                    let left = self.process_assignment_value(*left);
                    let right = self.process_assignment_value(*right);
                    if let (
                        [(l, AffineExpressionComponent::Constant)],
                        [(r, AffineExpressionComponent::Constant)],
                    ) = (&left[..], &right[..])
                    {
                        // TODO overflow?
                        if r.to_arbitrary_integer() > (u32::MAX).into() {
                            panic!("Exponent too large");
                        }
                        vec![(l.pow(r.to_integer()), AffineExpressionComponent::Constant)]
                    } else {
                        panic!("Exponentiation of non-constants.");
                    }
                }
                BinaryOperator::Div
                | BinaryOperator::Mod
                | BinaryOperator::BinaryAnd
                | BinaryOperator::BinaryXor
                | BinaryOperator::BinaryOr
                | BinaryOperator::ShiftLeft
                | BinaryOperator::ShiftRight
                | BinaryOperator::LogicalOr
                | BinaryOperator::LogicalAnd
                | BinaryOperator::Less
                | BinaryOperator::LessEqual
                | BinaryOperator::Equal
                | BinaryOperator::Identity
                | BinaryOperator::NotEqual
                | BinaryOperator::GreaterEqual
                | BinaryOperator::Greater
                | BinaryOperator::Is
                | BinaryOperator::In
                | BinaryOperator::Select
                | BinaryOperator::Connect => {
                    panic!("Invalid operation in expression {left} {op} {right}")
                }
            },
            Expression::UnaryOperation(_, UnaryOperation { op, expr }) => {
                assert!(op == UnaryOperator::Minus);
                self.negate_assignment_value(self.process_assignment_value(*expr))
            }
            Expression::StructExpression(_, _) => panic!(),
        }
    }

    fn add_assignment_value(
        &self,
        mut left: Vec<(T, AffineExpressionComponent)>,
        right: Vec<(T, AffineExpressionComponent)>,
    ) -> Vec<(T, AffineExpressionComponent)> {
        // TODO combine (or at least check for) same components.
        left.extend(right);
        left
    }

    fn negate_assignment_value(
        &self,
        expr: Vec<(T, AffineExpressionComponent)>,
    ) -> Vec<(T, AffineExpressionComponent)> {
        expr.into_iter().map(|(v, c)| (-v, c)).collect()
    }

    fn create_constraints_for_assignment_reg(&mut self, register: String) {
        let assign_const = format!("{register}_const");
        self.create_witness_fixed_pair(SourceRef::unknown(), &assign_const);
        let read_free = format!("{register}_read_free");
        self.create_witness_fixed_pair(SourceRef::unknown(), &read_free);
        let free_value = format!("{register}_free_value");
        // we can read from write registers, pc and read-only registers
        let read_registers = self
            .write_register_names()
            .chain(self.pc_register_names())
            .chain(self.read_only_register_names())
            .cloned()
            .collect::<Vec<_>>();
        let assign_constraint: Expression = read_registers
            .iter()
            .map(|name| {
                let read_coefficient = format!("read_{register}_{name}");
                self.create_witness_fixed_pair(SourceRef::unknown(), &read_coefficient);
                direct_reference(read_coefficient) * direct_reference(name.clone())
            })
            .chain([
                direct_reference(assign_const),
                direct_reference(read_free) * direct_reference(free_value),
            ])
            .sum();
        self.pil.push(PilStatement::Expression(
            SourceRef::unknown(),
            build::identity(direct_reference(register), assign_constraint),
        ));
    }

    /// Translates the code lines to fixed column but also fills
    /// the query hints for the free inputs.
    fn translate_code_lines(&mut self) {
        self.rom_pil
            .push(PilStatement::PolynomialConstantDefinition(
                SourceRef::unknown(),
                "p_line".to_string(),
                FunctionDefinition::Array(
                    ArrayExpression::Value(
                        (0..self.code_lines.len())
                            .map(|i| BigUint::from(i as u64).into())
                            .collect(),
                    )
                    .pad_with_last()
                    .unwrap_or_else(|| ArrayExpression::RepeatedValue(vec![0.into()])),
                ),
            ));
        // TODO check that all of them are matched against execution trace witnesses.
        let mut rom_constants = self
            .rom_constant_names
            .iter()
            .map(|n| (n, vec![T::from(0); self.code_lines.len()]))
            .collect::<BTreeMap<_, _>>();
        let mut free_value_query_arms = self
            .assignment_register_names()
            .map(|r| (r.clone(), vec![]))
            .collect::<BTreeMap<_, _>>();

        let label_positions = self.compute_label_positions();
        for (i, line) in self.code_lines.iter().enumerate() {
            for (assign_reg, writes) in &line.write_regs {
                for reg in writes {
                    rom_constants
                        .get_mut(&format!("p_reg_write_{assign_reg}_{reg}"))
                        .unwrap()[i] = 1.into();
                }
            }
            for (assign_reg, value) in &line.value {
                for (coeff, item) in value {
                    match item {
                        AffineExpressionComponent::Register(reg) => {
                            rom_constants
                                .get_mut(&format!("p_read_{assign_reg}_{reg}"))
                                .unwrap()[i] += *coeff;
                        }
                        AffineExpressionComponent::Constant => {
                            rom_constants
                                .get_mut(&format!("p_{assign_reg}_const"))
                                .unwrap()[i] += *coeff
                        }
                        AffineExpressionComponent::FreeInput(expr) => {
                            // The rom just stores that we read a free input, the actual value
                            // is part of the execution trace that generates the witness.
                            rom_constants
                                .get_mut(&format!("p_{assign_reg}_read_free"))
                                .unwrap()[i] += *coeff;
                            free_value_query_arms
                                .get_mut(assign_reg)
                                .unwrap()
                                .push(MatchArm {
                                    pattern: Pattern::Number(SourceRef::unknown(), i.into()),
                                    value: expr.clone(),
                                });
                        }
                    }
                }
            }
            for (instr, literal_args) in &line.instructions {
                for (reg, writes) in &line.write_regs {
                    if !writes.is_empty() {
                        // If an instruction stores a value, assume that the assignment register is
                        // assigned in inline pil. We need to allow for "wiggle room" by setting
                        // the free input to 1.
                        // TODO This is horrible and needs to be fixed by a proper mechanism
                        // that enforces that the assignment register is actually properly constrained.
                        rom_constants
                            .get_mut(&format!("p_{reg}_read_free"))
                            .unwrap()[i] = 1.into();
                    }
                }
                rom_constants.get_mut(&format!("p_instr_{instr}")).unwrap()[i] = 1.into();
                for (arg, param) in literal_args
                    .iter()
                    .zip(self.instructions[instr].literal_arg_names())
                {
                    rom_constants
                        .get_mut(&format!("p_instr_{instr}_param_{}", param.clone()))
                        .unwrap()[i] = match arg {
                        InstructionLiteralArg::LabelRef(name) => (*label_positions
                            .get(name)
                            .unwrap_or_else(|| panic!("{name} not found in labels"))
                            as u64)
                            .into(),
                        InstructionLiteralArg::Number(n) => *n,
                    };
                }
            }
        }
        let pc_name = self.pc_name.clone();
        let free_value_pil = self
            .assignment_register_names()
            .flat_map(|reg| {
                let free_value = format!("{reg}_free_value");
                let prover_query_arms = free_value_query_arms.remove(reg).unwrap();
                let mut statements = vec![witness_column(
                    SourceRef::unknown(),
                    free_value.clone(),
                    None,
                )];
                if !prover_query_arms.is_empty() {
                    let mut prover_query_arms = prover_query_arms;
                    prover_query_arms.push(MatchArm {
                        pattern: Pattern::CatchAll(SourceRef::unknown()),
                        value: absolute_reference("::std::prelude::Query::None"),
                    });

                    let scrutinee = Box::new(
                        FunctionCall {
                            function: Box::new(absolute_reference("::std::prover::eval")),
                            arguments: vec![direct_reference(pc_name.as_ref().unwrap())],
                        }
                        .into(),
                    );

                    let call_to_handle_query = FunctionCall {
                        function: Box::new(absolute_reference("::std::prover::handle_query")),
                        arguments: vec![
                            direct_reference(&free_value),
                            direct_reference("__i"),
                            MatchExpression {
                                scrutinee,
                                arms: prover_query_arms,
                            }
                            .into(),
                        ],
                    };
                    let prover_function = LambdaExpression {
                        kind: FunctionKind::Query,
                        params: vec![Pattern::Variable(SourceRef::unknown(), "__i".to_string())],
                        body: Box::new(call_to_handle_query.into()),
                        param_types: vec![],
                    };

                    statements.push(PilStatement::Expression(
                        SourceRef::unknown(),
                        prover_function.into(),
                    ));
                }
                statements
            })
            .collect::<Vec<_>>();
        self.pil.extend(free_value_pil);
        for (name, values) in rom_constants {
            let array_expression = if values.iter().all(|v| v == &values[0]) {
                // Performance optimization: The block below converts every T to an Expression,
                // which has a 7x larger memory footprint. This is wasteful for constant columns,
                // of which there are a lot because this code has not been optimized yet.
                ArrayExpression::RepeatedValue(vec![values[0].to_arbitrary_integer().into()])
            } else {
                ArrayExpression::value(
                    values
                        .into_iter()
                        .map(|v| v.to_arbitrary_integer().into())
                        .collect(),
                )
                .pad_with_last()
                .unwrap_or_else(|| ArrayExpression::RepeatedValue(vec![0.into()]))
            };
            self.rom_pil
                .push(PilStatement::PolynomialConstantDefinition(
                    SourceRef::unknown(),
                    name.clone(),
                    FunctionDefinition::Array(array_expression),
                ));
        }
    }

    fn compute_label_positions(&self) -> HashMap<String, usize> {
        self.code_lines
            .iter()
            .enumerate()
            .flat_map(|(i, line)| line.labels.iter().map(|l| (l, i)).collect::<Vec<_>>())
            .fold(HashMap::new(), |mut r, (l, i)| {
                assert!(r.insert(l.clone(), i).is_none(), "Duplicate label: {l}");
                r
            })
    }

    /// Creates a pair of witness and fixed column and matches them in the lookup.
    fn create_witness_fixed_pair(&mut self, source: SourceRef, name: &str) {
        let fixed_name = format!("p_{name}");
        self.pil.push(witness_column(source, name, None));
        self.line_lookup
            .push((name.to_string(), fixed_name.clone()));
        self.rom_constant_names.push(fixed_name);
    }

    fn assignment_register_names(&self) -> impl Iterator<Item = &String> {
        self.assignment_register_names.iter()
    }

    fn write_register_names(&self) -> impl Iterator<Item = &String> {
        self.registers
            .iter()
            .filter_map(|(n, r)| r.ty.is_write().then_some(n))
    }

    fn pc_register_names(&self) -> impl Iterator<Item = &String> {
        self.registers
            .iter()
            .filter_map(|(n, r)| r.ty.is_pc().then_some(n))
    }

    fn read_only_register_names(&self) -> impl Iterator<Item = &String> {
        self.registers
            .iter()
            .filter_map(|(n, r)| r.ty.is_read_only().then_some(n))
    }

    fn return_instruction(&self) -> parsed::asm::Instruction {
        return_instruction(self.output_count, self.pc_name.as_ref().unwrap())
    }

    /// Return an expression of degree at most 1 whose value matches that of `expr`.
    /// Intermediate witness columns can be introduced, with names starting with `prefix` optionally followed by a suffix
    /// Suffixes are defined as follows: "", "_1", "_2", "_3" etc.
    /// In some situations, this function can fail and it will return an expression
    /// that might not be linear.
    fn linearize(&mut self, prefix: &str, expr: Expression) -> Expression {
        self.linearize_rec(prefix, 0, expr).1
    }

    fn linearize_rec(
        &mut self,
        prefix: &str,
        counter: usize,
        expr: Expression,
    ) -> (usize, Expression) {
        let Expression::BinaryOperation(source, BinaryOperation { left, op, right }) = expr else {
            return (counter, expr);
        };
        let (counter, left) = self.linearize_rec(prefix, counter, *left);
        let (counter, right) = self.linearize_rec(prefix, counter, *right);
        match op {
            BinaryOperator::Mul => {
                // if we have a quadratic term, we linearize each factor and introduce an intermediate variable for the product
                let intermediate_name = format!(
                    "{prefix}{}",
                    if counter == 0 {
                        "".to_string()
                    } else {
                        format!("_{counter}")
                    }
                );
                self.pil.push(PilStatement::PolynomialDefinition(
                    SourceRef::unknown(),
                    intermediate_name.clone().into(),
                    left * right,
                ));
                (counter + 1, direct_reference(intermediate_name))
            }
            _ => (
                counter,
                Expression::BinaryOperation(
                    source,
                    BinaryOperation {
                        left: Box::new(left),
                        op,
                        right: Box::new(right),
                    },
                ),
            ),
        }
    }
}

struct Register {
    /// Constraints to update this register, first item being the
    /// condition, second item the value.
    /// TODO check that condition is bool
    conditioned_updates: Vec<(Expression, Expression)>,
    default_update: Option<Expression>,
    ty: RegisterTy,
}

impl Register {
    /// Returns the expression assigned to this register in the next row.
    pub fn update_expression(&self) -> Option<Expression> {
        // TODO conditions need to be all boolean
        let updates = self
            .conditioned_updates
            .iter()
            .map(|(cond, value)| cond.clone() * value.clone())
            .sum();

        // TODO for computing the default condition, we need to ensure
        // that the conditions all exclude each other
        match (self.conditioned_updates.len(), &self.default_update) {
            (0, update) => update.clone(),
            (_, None) => Some(updates),
            (_, Some(def)) => {
                let default_condition = Expression::from(1)
                    - self
                        .conditioned_updates
                        .iter()
                        .map(|(cond, _value)| cond.clone())
                        .sum();
                Some(updates + (default_condition * def.clone()))
            }
        }
    }
}

struct Instruction {
    inputs: Vec<Input>,
    outputs: Vec<String>,
}

impl Instruction {
    fn literal_arg_names(&self) -> impl Iterator<Item = &String> {
        self.inputs.iter().filter_map(|input| match input {
            Input::Literal(name, _) => Some(name),
            _ => None,
        })
    }
}

// TODO turn this into an enum, split into
// label, assignment, instruction.
#[derive(Default)]
struct CodeLine<T> {
    /// Which regular registers to assign to, from which assignment register
    /// Maps assignment register to a vector of regular registers.
    write_regs: BTreeMap<String, Vec<String>>,
    /// The value on the right-hand-side, per assignment register
    value: BTreeMap<String, Vec<(T, AffineExpressionComponent)>>,
    labels: BTreeSet<String>,
    instructions: Vec<(String, Vec<InstructionLiteralArg<T>>)>,
    debug_directives: Vec<DebugDirective>,
}

enum AffineExpressionComponent {
    Register(String),
    Constant,
    FreeInput(Expression),
}

enum InstructionLiteralArg<T> {
    LabelRef(String),
    Number(T),
}

fn witness_column<S: Into<String>>(
    source: SourceRef,
    name: S,
    def: Option<FunctionDefinition>,
) -> PilStatement {
    PilStatement::PolynomialCommitDeclaration(
        source,
        None,
        vec![PolynomialName {
            name: name.into(),
            array_size: None,
        }],
        def,
    )
}

/// If the expression is of the form "x' = expr", returns x and expr.
fn try_extract_update(expr: &Expression) -> Option<(String, Expression)> {
    let Expression::BinaryOperation(
        _,
        BinaryOperation {
            left,
            op: BinaryOperator::Identity,
            right,
        },
    ) = expr
    else {
        return None;
    };
    // TODO check that there are no other "next" references in the expression
    match left.as_ref() {
        Expression::UnaryOperation(
            _,
            UnaryOperation {
                op: UnaryOperator::Next,
                expr: column,
            },
        ) => match column.as_ref() {
            Expression::Reference(_, column) => Some((
                column.try_to_identifier().unwrap().clone(),
                (**right).clone(),
            )),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod test {
    use powdr_ast::asm_analysis::AnalysisASMFile;
    use powdr_importer::load_dependencies_and_resolve_str;
    use powdr_number::{FieldElement, GoldilocksField};

    use crate::compile;

    fn parse_analyze_and_compile<T: FieldElement>(input: &str) -> AnalysisASMFile {
        let parsed = load_dependencies_and_resolve_str(input);
        let analyzed = powdr_analysis::analyze(parsed).unwrap();
        compile::<T>(analyzed)
    }

    #[test]
    #[should_panic(
        expected = "Assignment register 'Y' used in link definition must be present in instruction params"
    )]
    fn instr_external_rhs_register_not_on_lhs() {
        let asm = r"
machine Main {
  reg pc[@pc];
  reg X[<=];
  reg Y[<=];
  reg A;

  instr foo X link => Y = vm.foo(X);

  function main {
    foo;
  }
}
";
        parse_analyze_and_compile::<GoldilocksField>(asm);
    }
}

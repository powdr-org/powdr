// TODO: the unused is only here because the interpreter is not integrated in the final code yet
#![allow(unused)]
use super::effect::{Assertion, Effect};

use super::symbolic_expression::{BinaryOperator, BitOperator, SymbolicExpression, UnaryOperator};
use super::variable::{Cell, Variable};
use crate::witgen::data_structures::finalizable_data::CompactDataRef;
use crate::witgen::data_structures::mutable_state::MutableState;
use crate::witgen::machines::LookupCell;
use crate::witgen::{FixedData, QueryCallback};
use itertools::Itertools;
use powdr_ast::analyzed::{PolyID, PolynomialType};
use powdr_number::FieldElement;

use std::collections::{BTreeSet, HashMap};

/// Interpreter for instructions compiled from witgen effects.
pub struct EffectsInterpreter<T: FieldElement> {
    var_count: usize,
    actions: Vec<InterpreterAction<T>>,
}

/// Witgen effects compiled into instructions for a stack machine.
/// Variables have been removed and replaced by their index in the variable list.
enum InterpreterAction<T: FieldElement> {
    ReadCell(usize, Cell),
    ReadParam(usize, usize),
    ReadFixedColumn(usize, Cell),
    AssignExpression(usize, RPNExpression<T, usize>),
    WriteCell(usize, Cell),
    WriteParam(usize, usize),
    MachineCall(u64, Vec<MachineCallArgumentIdx>),
    Assertion(RPNExpression<T, usize>, RPNExpression<T, usize>, bool),
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum MachineCallArgumentIdx {
    /// var index of the evaluated known argument expression
    Known(usize),
    /// var index of the unknown
    Unknown(usize),
}

impl<T: FieldElement> EffectsInterpreter<T> {
    pub fn new(known_inputs: &[Variable], effects: &[Effect<T, Variable>]) -> Self {
        let mut actions = vec![];
        let mut var_mapper = VariableMapper::new();

        Self::load_fixed_column_values(&mut var_mapper, &mut actions, effects);
        Self::load_known_inputs(&mut var_mapper, &mut actions, known_inputs);
        Self::process_effects(&mut var_mapper, &mut actions, effects);
        Self::write_data(&mut var_mapper, &mut actions, effects);

        let ret = Self {
            var_count: var_mapper.var_count(),
            actions,
        };
        assert!(ret.is_valid());
        ret
    }

    fn load_fixed_column_values(
        var_mapper: &mut VariableMapper,
        actions: &mut Vec<InterpreterAction<T>>,
        effects: &[Effect<T, Variable>],
    ) {
        actions.extend(
            effects
                .iter()
                .flat_map(|e| e.referenced_variables())
                .filter_map(|v| match v {
                    Variable::FixedCell(c) => Some((v, c)),
                    _ => None,
                })
                .unique()
                .map(|(var, cell)| {
                    let idx = var_mapper.map_var(var);
                    InterpreterAction::ReadFixedColumn(idx, cell.clone())
                }),
        )
    }

    fn load_known_inputs(
        var_mapper: &mut VariableMapper,
        actions: &mut Vec<InterpreterAction<T>>,
        known_inputs: &[Variable],
    ) {
        actions.extend(known_inputs.iter().map(|var| match var {
            Variable::WitnessCell(c) => {
                let idx = var_mapper.map_var(var);
                InterpreterAction::ReadCell(idx, c.clone())
            }
            Variable::Param(i) => {
                let idx = var_mapper.map_var(var);
                InterpreterAction::ReadParam(idx, *i)
            }
            Variable::FixedCell(_) | Variable::MachineCallParam(_) => unreachable!(),
        }));
    }

    fn process_effects(
        var_mapper: &mut VariableMapper,
        actions: &mut Vec<InterpreterAction<T>>,
        effects: &[Effect<T, Variable>],
    ) {
        effects.iter().for_each(|effect| {
            let action = match effect {
                Effect::Assignment(var, e) => {
                    let idx = var_mapper.map_var(var);
                    InterpreterAction::AssignExpression(idx, var_mapper.map_expr_to_rpn(e))
                }
                Effect::RangeConstraint(..) => {
                    unreachable!("Final code should not contain pure range constraints.")
                }
                Effect::Assertion(Assertion {
                    lhs,
                    rhs,
                    expected_equal,
                }) => InterpreterAction::Assertion(
                    var_mapper.map_expr_to_rpn(lhs),
                    var_mapper.map_expr_to_rpn(rhs),
                    *expected_equal,
                ),
                Effect::MachineCall(id, known_inputs, arguments) => {
                    let arguments = known_inputs
                        .iter()
                        .zip(arguments)
                        .map(|(is_input, var)| {
                            if is_input {
                                MachineCallArgumentIdx::Known(var_mapper.map_var(var))
                            } else {
                                MachineCallArgumentIdx::Unknown(var_mapper.map_var(var))
                            }
                        })
                        .collect();
                    InterpreterAction::MachineCall(*id, arguments)
                }
                Effect::Branch(..) => {
                    unimplemented!("Branches are not supported in the interpreter yet")
                }
            };
            actions.push(action);
        })
    }

    fn write_data(
        var_mapper: &mut VariableMapper,
        actions: &mut Vec<InterpreterAction<T>>,
        effects: &[Effect<T, Variable>],
    ) {
        effects
            .iter()
            .flat_map(Effect::written_vars)
            .for_each(|(var, _mutable)| {
                match var {
                    Variable::WitnessCell(cell) => {
                        let idx = var_mapper.get_var(var).unwrap();
                        actions.push(InterpreterAction::WriteCell(idx, cell.clone()));
                    }
                    Variable::Param(i) => {
                        let idx = var_mapper.get_var(var).unwrap();
                        actions.push(InterpreterAction::WriteParam(idx, *i));
                    }
                    Variable::FixedCell(_) => panic!("Should not write to fixed column."),
                    Variable::MachineCallParam(_) => {
                        // This is just an internal variable.
                    }
                }
            });
    }

    /// Check that actions are valid (e.g., variables written to only once, and only read after being written to)
    fn is_valid(&self) -> bool {
        let mut prev_writes = BTreeSet::new();
        for action in &self.actions {
            let writes = action.writes();
            // writing to a variable already written?
            if !writes.is_disjoint(&prev_writes) {
                return false;
            }
            // reading a variable that was not written to?
            if !action.reads().is_subset(&prev_writes) {
                return false;
            }
            prev_writes.extend(writes);
        }
        true
    }

    /// Execute the machine effects for the given the parameters
    pub fn call<Q: QueryCallback<T>>(
        &self,
        fixed_data: &FixedData<'_, T>,
        mutable_state: &MutableState<'_, T, Q>,
        params: &mut [LookupCell<T>],
        data: CompactDataRef<'_, T>,
    ) {
        let mut vars = vec![T::zero(); self.var_count];

        let row_offset: i64 = data.row_offset.try_into().unwrap();
        let mut eval_stack = vec![];
        for action in &self.actions {
            match action {
                InterpreterAction::AssignExpression(idx, e) => {
                    let val = e.evaluate(&mut eval_stack, &vars[..]);
                    vars[*idx] = val;
                }
                InterpreterAction::ReadCell(idx, c) => {
                    vars[*idx] = data
                        .data
                        .get((row_offset + c.row_offset as i64).try_into().unwrap(), c.id)
                        .0;
                }
                InterpreterAction::ReadFixedColumn(idx, c) => {
                    let poly_id = PolyID {
                        id: c.id,
                        ptype: PolynomialType::Constant,
                    };
                    vars[*idx] = fixed_data.fixed_cols[&poly_id].values_max_size()
                        [usize::try_from(row_offset + c.row_offset as i64).unwrap()];
                }
                InterpreterAction::ReadParam(idx, i) => {
                    vars[*idx] = get_param(params, *i);
                }
                InterpreterAction::WriteCell(idx, c) => {
                    data.data.set(
                        (row_offset + c.row_offset as i64).try_into().unwrap(),
                        c.id,
                        vars[*idx],
                    );
                }
                InterpreterAction::WriteParam(idx, i) => {
                    set_param(params, *i, vars[*idx]);
                }
                InterpreterAction::MachineCall(id, arguments) => {
                    // we know it's safe to escape the references here, but the compiler doesn't, so we use unsafe
                    let mut args = arguments
                        .iter()
                        .map(|a| match a {
                            MachineCallArgumentIdx::Unknown(idx) => {
                                let var = &mut vars[*idx] as *mut T;
                                LookupCell::Output(unsafe { var.as_mut().unwrap() })
                            }
                            MachineCallArgumentIdx::Known(idx) => {
                                let var = &vars[*idx] as *const T;
                                LookupCell::Input(unsafe { var.as_ref().unwrap() })
                            }
                        })
                        .collect::<Vec<_>>();
                    mutable_state.call_direct(*id, &mut args[..]).unwrap();
                }
                InterpreterAction::Assertion(e1, e2, expected_equal) => {
                    let lhs_value = e1.evaluate(&mut eval_stack, &vars);
                    let rhs_value = e2.evaluate(&mut eval_stack, &vars);
                    if *expected_equal {
                        assert_eq!(lhs_value, rhs_value, "Assertion failed");
                    } else {
                        assert_ne!(lhs_value, rhs_value, "Assertion failed");
                    }
                }
            }
        }
        assert!(eval_stack.is_empty());
    }
}

impl<T: FieldElement> InterpreterAction<T> {
    /// variable indexes written by the action
    fn writes(&self) -> BTreeSet<usize> {
        let mut set = BTreeSet::new();
        match self {
            InterpreterAction::ReadCell(idx, _)
            | InterpreterAction::ReadParam(idx, _)
            | InterpreterAction::AssignExpression(idx, _) => {
                set.insert(*idx);
            }
            InterpreterAction::MachineCall(_, params) => params.iter().for_each(|p| {
                if let MachineCallArgumentIdx::Unknown(v) = p {
                    set.insert(*v);
                }
            }),
            _ => {}
        }
        set
    }

    /// variable indexes read by the action
    fn reads(&self) -> BTreeSet<usize> {
        let mut set = BTreeSet::new();
        match self {
            InterpreterAction::WriteCell(idx, _) | InterpreterAction::WriteParam(idx, _) => {
                set.insert(*idx);
            }
            InterpreterAction::AssignExpression(_, expr) => expr.elems.iter().for_each(|e| {
                if let RPNExpressionElem::Symbol(idx) = e {
                    set.insert(*idx);
                }
            }),
            InterpreterAction::MachineCall(_, params) => params.iter().for_each(|p| {
                if let MachineCallArgumentIdx::Known(v) = p {
                    set.insert(*v);
                }
            }),
            InterpreterAction::Assertion(lhs, rhs, _) => {
                lhs.elems.iter().for_each(|e| {
                    if let RPNExpressionElem::Symbol(idx) = e {
                        set.insert(*idx);
                    }
                });
                rhs.elems.iter().for_each(|e| {
                    if let RPNExpressionElem::Symbol(idx) = e {
                        set.insert(*idx);
                    }
                });
            }
            _ => {}
        }
        set
    }
}

/// Helper struct to map variables to contiguous indices, so they can be kept in
/// sequential memory and quickly refered to during execution.
pub struct VariableMapper {
    var_idx: HashMap<Variable, usize>,
    count: usize,
}

impl VariableMapper {
    pub fn new() -> Self {
        Self {
            var_idx: HashMap::new(),
            count: 0,
        }
    }

    pub fn var_count(&self) -> usize {
        self.count
    }

    /// Returns the index of the variable, allocates it if it does not exist.
    pub fn map_var(&mut self, var: &Variable) -> usize {
        let idx = *self.var_idx.entry(var.clone()).or_insert_with(|| {
            self.count += 1;
            self.count - 1
        });
        idx
    }

    /// reserve a new variable index
    pub fn reserve_idx(&mut self) -> usize {
        let idx = self.count;
        self.count += 1;
        idx
    }

    /// get the index of a variable if it was previously mapped
    pub fn get_var(&mut self, var: &Variable) -> Option<usize> {
        self.var_idx.get(var).copied()
    }

    pub fn map_expr_to_rpn<T: FieldElement>(
        &mut self,
        expr: &SymbolicExpression<T, Variable>,
    ) -> RPNExpression<T, usize> {
        RPNExpression::map_from(expr, self)
    }
}

/// An expression in Reverse Polish Notation.
pub struct RPNExpression<T: FieldElement, S> {
    pub elems: Vec<RPNExpressionElem<T, S>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RPNExpressionElem<T: FieldElement, S> {
    Concrete(T),
    Symbol(S),
    BinaryOperation(BinaryOperator),
    UnaryOperation(UnaryOperator),
    BitOperation(BitOperator, T::Integer),
}

impl<T: FieldElement> RPNExpression<T, usize> {
    /// Convert a symbolic expression to RPN, mapping variables to indices
    fn map_from(expr: &SymbolicExpression<T, Variable>, var_mapper: &mut VariableMapper) -> Self {
        fn inner<T: FieldElement>(
            expr: &SymbolicExpression<T, Variable>,
            elems: &mut Vec<RPNExpressionElem<T, usize>>,
            var_mapper: &mut VariableMapper,
        ) {
            match expr {
                SymbolicExpression::Concrete(n) => {
                    elems.push(RPNExpressionElem::Concrete(*n));
                }
                SymbolicExpression::Symbol(s, _) => {
                    elems.push(RPNExpressionElem::Symbol(var_mapper.map_var(s)));
                }
                SymbolicExpression::BinaryOperation(lhs, op, rhs, _) => {
                    inner(lhs, elems, var_mapper);
                    inner(rhs, elems, var_mapper);
                    elems.push(RPNExpressionElem::BinaryOperation(op.clone()));
                }
                SymbolicExpression::UnaryOperation(op, expr, _) => {
                    inner(expr, elems, var_mapper);
                    elems.push(RPNExpressionElem::UnaryOperation(op.clone()));
                }
                SymbolicExpression::BitOperation(expr, op, n, _) => {
                    inner(expr, elems, var_mapper);
                    elems.push(RPNExpressionElem::BitOperation(op.clone(), *n));
                }
            }
        }
        let mut elems = Vec::new();
        inner(expr, &mut elems, var_mapper);
        RPNExpression { elems }
    }

    /// Evaluate the expression using the provided variables.
    /// The stack is used to store intermediate results, it's taken as
    /// a parameter to avoid allocating on every call to evaluate.
    fn evaluate(&self, stack: &mut Vec<T>, vars: &[T]) -> T {
        self.elems.iter().for_each(|elem| match elem {
            RPNExpressionElem::Concrete(v) => stack.push(*v),
            RPNExpressionElem::Symbol(idx) => stack.push(vars[*idx]),
            RPNExpressionElem::BinaryOperation(op) => {
                let right = stack.pop().unwrap();
                let left = stack.pop().unwrap();
                let result = match op {
                    BinaryOperator::Add => left + right,
                    BinaryOperator::Sub => left - right,
                    BinaryOperator::Mul => left * right,
                    BinaryOperator::Div => left / right,
                    BinaryOperator::IntegerDiv => {
                        T::from(left.to_arbitrary_integer() / right.to_arbitrary_integer())
                    }
                };
                stack.push(result);
            }
            RPNExpressionElem::UnaryOperation(op) => {
                let inner = stack.pop().unwrap();
                let result = match op {
                    UnaryOperator::Neg => -inner,
                };
                stack.push(result);
            }
            RPNExpressionElem::BitOperation(op, right) => {
                let left = stack.pop().unwrap();
                let result = match op {
                    BitOperator::And => T::from(left.to_integer() & *right),
                };
                stack.push(result);
            }
        });
        stack.pop().unwrap()
    }
}

#[inline]
fn get_param<T: FieldElement>(params: &[LookupCell<T>], i: usize) -> T {
    match params[i] {
        LookupCell::Input(v) => *v,
        LookupCell::Output(_) => panic!("Output cell used as input"),
    }
}
#[inline]
fn set_param<T: FieldElement>(params: &mut [LookupCell<T>], i: usize, value: T) {
    match &mut params[i] {
        LookupCell::Input(_) => panic!("Input cell used as output"),
        LookupCell::Output(v) => **v = value,
    }
}

#[cfg(test)]
mod test {
    use std::fs::read_to_string;

    use super::EffectsInterpreter;
    use crate::witgen::data_structures::{
        finalizable_data::{CompactData, CompactDataRef},
        mutable_state::MutableState,
    };
    use crate::witgen::global_constraints;
    use crate::witgen::jit::block_machine_processor::BlockMachineProcessor;
    use crate::witgen::jit::test_util::read_pil;
    use crate::witgen::jit::variable::Variable;
    use crate::witgen::machines::{
        machine_extractor::MachineExtractor, KnownMachine, LookupCell, Machine,
    };
    use crate::witgen::FixedData;

    use bit_vec::BitVec;
    use itertools::Itertools;
    use powdr_number::GoldilocksField;

    #[test]
    fn call_poseidon() {
        let file = "../test_data/pil/poseidon_gl.pil";
        let machine_name = "main_poseidon";
        let (num_inputs, num_outputs) = (12, 4);
        let pil = read_to_string(file).unwrap();

        let (analyzed, fixed_col_vals) = read_pil::<GoldilocksField>(&pil);

        let fixed_data = FixedData::new(&analyzed, &fixed_col_vals, &[], Default::default(), 0);
        let (fixed_data, retained_identities) =
            global_constraints::set_global_constraints(fixed_data, &analyzed.identities);
        let machines = MachineExtractor::new(&fixed_data).split_out_machines(retained_identities);
        let [KnownMachine::BlockMachine(machine)] = machines
            .iter()
            .filter(|m| m.name().contains(machine_name))
            .collect_vec()
            .as_slice()
        else {
            panic!("Expected exactly one matching block machine")
        };
        let (machine_parts, block_size, latch_row) = machine.machine_info();
        assert_eq!(machine_parts.connections.len(), 1);
        let connection_id = *machine_parts.connections.keys().next().unwrap();
        let processor =
            BlockMachineProcessor::new(&fixed_data, machine_parts.clone(), block_size, latch_row);

        let mutable_state = MutableState::new(machines.into_iter(), &|_| {
            Err("Query not implemented".to_string())
        });

        let known_values = BitVec::from_iter(
            (0..num_inputs)
                .map(|_| true)
                .chain((0..num_outputs).map(|_| false)),
        );

        let effects = processor
            .generate_code(&mutable_state, connection_id, &known_values)
            .unwrap()
            .code;

        let known_inputs = (0..12).map(Variable::Param).collect::<Vec<_>>();

        // generate interpreter
        let interpreter = EffectsInterpreter::new(&known_inputs, &effects);
        // call it
        let mut params = [GoldilocksField::default(); 16];
        let mut param_lookups = params
            .iter_mut()
            .enumerate()
            .map(|(i, p)| {
                if i < 12 {
                    LookupCell::Input(p)
                } else {
                    LookupCell::Output(p)
                }
            })
            .collect::<Vec<_>>();
        let poly_ids = analyzed
            .committed_polys_in_source_order()
            .flat_map(|p| p.0.array_elements().map(|e| e.1))
            .collect_vec();

        let mut data = CompactData::new(poly_ids.iter());
        data.append_new_rows(31);
        let data_ref = CompactDataRef::new(&mut data, 0);
        interpreter.call(&fixed_data, &mutable_state, &mut param_lookups, data_ref);

        assert_eq!(
            &params,
            &[
                GoldilocksField::from(0),
                GoldilocksField::from(0),
                GoldilocksField::from(0),
                GoldilocksField::from(0),
                GoldilocksField::from(0),
                GoldilocksField::from(0),
                GoldilocksField::from(0),
                GoldilocksField::from(0),
                GoldilocksField::from(0),
                GoldilocksField::from(0),
                GoldilocksField::from(0),
                GoldilocksField::from(0),
                GoldilocksField::from(4330397376401421145u64),
                GoldilocksField::from(14124799381142128323u64),
                GoldilocksField::from(8742572140681234676u64),
                GoldilocksField::from(14345658006221440202u64),
            ]
        )
    }
}

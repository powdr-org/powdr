use super::compiler::written_vars_in_effect;
use super::effect::{Assertion, Effect};

use super::symbolic_expression::{BinaryOperator, BitOperator, SymbolicExpression, UnaryOperator};
use super::variable::{Cell, Variable};
use crate::witgen::data_structures::finalizable_data::CompactDataRef;
use crate::witgen::data_structures::mutable_state::MutableState;
use crate::witgen::jit::effect::MachineCallArgument;
use crate::witgen::machines::LookupCell;
use crate::witgen::QueryCallback;
use powdr_number::FieldElement;

use std::collections::HashMap;

// Witgen effects compiled into interpreter instructions.
pub struct EffectsInterpreter<T: FieldElement> {
    first_column_id: u64,
    column_count: usize,
    var_count: usize,
    actions: Vec<InterpreterAction<T>>,
}

// Witgen effects compiled into "instructions".
// Variables have been removed and replaced by their index in the variable list.
enum InterpreterAction<T: FieldElement> {
    ReadCell(usize, Cell),
    ReadParam(usize, usize),
    AssignExpression(usize, RPNExpression<T, usize>),
    WriteCell(usize, Cell),
    WriteParam(usize, usize),
    WriteKnown(Cell),
    MachineCall(Vec<usize>, u64, Vec<MachineCallArgument<T, usize>>),
    Assertion(RPNExpression<T, usize>, RPNExpression<T, usize>, bool),
}

impl<T: FieldElement> EffectsInterpreter<T> {
    pub fn new(
        first_column_id: u64,
        column_count: usize,
        known_inputs: &[Variable],
        effects: &[Effect<T, Variable>],
    ) -> Self {
        let mut actions = vec![];
        let mut var_mapper = VariableMapper::new();

        Self::load_known_inputs(&mut var_mapper, &mut actions, known_inputs);
        Self::process_effects(&mut var_mapper, &mut actions, effects);
        Self::write_data(&mut var_mapper, &mut actions, effects);

        Self {
            first_column_id,
            column_count,
            var_count: var_mapper.var_count(),
            actions,
        }
    }

    fn load_known_inputs(
        var_mapper: &mut VariableMapper,
        actions: &mut Vec<InterpreterAction<T>>,
        known_inputs: &[Variable],
    ) {
        actions.extend(known_inputs.iter().map(|var| match var {
            Variable::Cell(c) => {
                let idx = var_mapper.map_var(var);
                InterpreterAction::ReadCell(idx, c.clone())
            }
            Variable::Param(i) => {
                let idx = var_mapper.map_var(var);
                InterpreterAction::ReadParam(idx, *i)
            }
            Variable::MachineCallReturnValue(_) => unreachable!(),
        }));
    }

    fn process_effects(
        var_mapper: &mut VariableMapper,
        actions: &mut Vec<InterpreterAction<T>>,
        effects: &[Effect<T, Variable>],
    ) {
        actions.extend(effects.iter().map(|effect| match effect {
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
            Effect::MachineCall(id, arguments) => {
                let result_vars = arguments
                    .iter()
                    .filter_map(|a| match a {
                        MachineCallArgument::Unknown(v) => Some(var_mapper.map_var(v)),
                        MachineCallArgument::Known(_) => None,
                    })
                    .collect();

                InterpreterAction::MachineCall(
                    result_vars,
                    *id,
                    arguments
                        .iter()
                        .map(|a| match a {
                            MachineCallArgument::Unknown(_) => MachineCallArgument::Unknown(0),
                            MachineCallArgument::Known(v) => {
                                MachineCallArgument::Known(var_mapper.map_expr(v))
                            }
                        })
                        .collect(),
                )
            }
        }))
    }

    fn write_data(
        var_mapper: &mut VariableMapper,
        actions: &mut Vec<InterpreterAction<T>>,
        effects: &[Effect<T, Variable>],
    ) {
        effects
            .iter()
            .flat_map(written_vars_in_effect)
            .for_each(|var| {
                match var {
                    Variable::Cell(cell) => {
                        let idx = var_mapper.get_var(var).unwrap();
                        actions.push(InterpreterAction::WriteCell(idx, cell.clone()));
                        actions.push(InterpreterAction::WriteKnown(cell.clone()));
                    }
                    Variable::Param(i) => {
                        let idx = var_mapper.get_var(var).unwrap();
                        actions.push(InterpreterAction::WriteParam(idx, *i));
                    }
                    Variable::MachineCallReturnValue(_) => {
                        // This is just an internal variable.
                    }
                }
            });
    }

    // Execute the machine effects for the given the parameters
    pub fn call<Q: QueryCallback<T>>(
        &self,
        mutable_state: &MutableState<'_, T, Q>,
        params: &mut [LookupCell<T>],
        mut data: CompactDataRef<'_, T>,
    ) {
        let row_offset = data.row_offset().try_into().unwrap();
        let (data, known) = data.as_mut_slices();

        let mut vars = vec![None; self.var_count];

        let mut eval_stack = vec![];
        for action in &self.actions {
            match action {
                InterpreterAction::AssignExpression(idx, e) => {
                    let val = e.evaluate(&mut eval_stack, &vars);
                    assert!(vars[*idx].replace(val).is_none());
                }
                InterpreterAction::ReadCell(idx, c) => {
                    assert!(vars[*idx]
                        .replace(
                            data[index(
                                self.first_column_id,
                                self.column_count,
                                row_offset,
                                c.row_offset,
                                c.id,
                            )]
                        )
                        .is_none())
                }
                InterpreterAction::ReadParam(idx, i) => {
                    assert!(vars[*idx].replace(get_param(params, *i)).is_none());
                }
                InterpreterAction::WriteCell(idx, c) => {
                    set(
                        self.first_column_id,
                        self.column_count,
                        data,
                        row_offset,
                        c.row_offset,
                        c.id,
                        vars[*idx].unwrap(),
                    );
                }
                InterpreterAction::WriteParam(idx, i) => {
                    set_param(params, *i, vars[*idx].unwrap());
                }
                InterpreterAction::WriteKnown(c) => {
                    set_known(
                        self.first_column_id,
                        self.column_count,
                        known,
                        row_offset,
                        c.row_offset,
                        c.id,
                    );
                }
                InterpreterAction::MachineCall(result_vars, id, arguments) => {
                    let mut arg_values: Vec<_> = arguments
                        .iter()
                        .map(|a| match a {
                            MachineCallArgument::Unknown(v) => (Some(v), Default::default()),
                            MachineCallArgument::Known(v) => (
                                None,
                                RPNExpression::from(v).evaluate(&mut eval_stack, &vars),
                            ),
                        })
                        .collect();

                    // call machine
                    let mut args = arguments
                        .iter()
                        .zip(arg_values.iter_mut())
                        .map(|(a, v)| match a {
                            MachineCallArgument::Unknown(_) => LookupCell::Output(&mut v.1),
                            MachineCallArgument::Known(_) => LookupCell::Input(&v.1),
                        })
                        .collect::<Vec<_>>();

                    mutable_state.call_direct(*id, &mut args[..]).unwrap();

                    // write output to variables
                    let mut var_idx = 0;
                    args.into_iter().for_each(|arg| {
                        if let LookupCell::Output(v) = arg {
                            assert!(vars[result_vars[var_idx]].replace(*v).is_none());
                            var_idx += 1;
                        }
                    });
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
    }
}

/// Helper struct to map variables to unique indices, so they can be kept in
/// sequential memory and quickly refered to during execution.
pub struct VariableMapper {
    var_idx: HashMap<Variable, usize>,
}

impl VariableMapper {
    pub fn new() -> Self {
        Self {
            var_idx: HashMap::new(),
        }
    }

    pub fn var_count(&self) -> usize {
        self.var_idx.len()
    }

    pub fn map_var(&mut self, var: &Variable) -> usize {
        let var_count = self.var_idx.len();
        let idx = *self.var_idx.entry(var.clone()).or_insert(var_count);
        idx
    }

    pub fn get_var(&mut self, var: &Variable) -> Option<usize> {
        self.var_idx.get(var).copied()
    }

    pub fn map_expr<T: FieldElement>(
        &mut self,
        expr: &SymbolicExpression<T, Variable>,
    ) -> SymbolicExpression<T, usize> {
        expr.map_variables(&mut |var| self.map_var(var))
    }

    pub fn map_expr_to_rpn<T: FieldElement>(
        &mut self,
        expr: &SymbolicExpression<T, Variable>,
    ) -> RPNExpression<T, usize> {
        RPNExpression::from(&expr.map_variables(&mut |var| self.map_var(var)))
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

impl<T: FieldElement, S: Clone> From<&SymbolicExpression<T, S>> for RPNExpression<T, S> {
    fn from(expr: &SymbolicExpression<T, S>) -> Self {
        fn from_inner<T: FieldElement, S: Clone>(
            expr: &SymbolicExpression<T, S>,
            elems: &mut Vec<RPNExpressionElem<T, S>>,
        ) {
            match expr {
                SymbolicExpression::Concrete(n) => {
                    elems.push(RPNExpressionElem::Concrete(*n));
                }
                SymbolicExpression::Symbol(s, _) => {
                    elems.push(RPNExpressionElem::Symbol(s.clone()));
                }
                SymbolicExpression::BinaryOperation(lhs, op, rhs, _) => {
                    from_inner(lhs, elems);
                    from_inner(rhs, elems);
                    elems.push(RPNExpressionElem::BinaryOperation(op.clone()));
                }
                SymbolicExpression::UnaryOperation(op, expr, _) => {
                    from_inner(expr, elems);
                    elems.push(RPNExpressionElem::UnaryOperation(op.clone()));
                }
                SymbolicExpression::BitOperation(expr, op, n, _) => {
                    from_inner(expr, elems);
                    elems.push(RPNExpressionElem::BitOperation(op.clone(), *n));
                }
            }
        }
        let mut elems = Vec::new();
        from_inner(expr, &mut elems);
        RPNExpression { elems }
    }
}

impl<T: FieldElement> RPNExpression<T, usize> {
    /// Evaluate the expression using the provided variables
    fn evaluate(&self, stack: &mut Vec<T>, vars: &[Option<T>]) -> T {
        self.elems.iter().for_each(|elem| match elem {
            RPNExpressionElem::Concrete(v) => stack.push(*v),
            RPNExpressionElem::Symbol(idx) => stack.push(vars[*idx].unwrap()),
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

// the following functions come from the interface.rs file also included in the compiled jit code

#[inline]
fn index(
    first_column_id: u64,
    column_count: usize,
    global_offset: u64,
    local_offset: i32,
    column: u64,
) -> usize {
    let column = column - first_column_id;
    let row = (global_offset as i64 + local_offset as i64) as u64;
    (row * column_count as u64 + column) as usize
}

#[inline]
fn index_known(
    first_column_id: u64,
    column_count: usize,
    global_offset: u64,
    local_offset: i32,
    column: u64,
) -> (u64, u64) {
    let column = column - first_column_id;
    let row = (global_offset as i64 + local_offset as i64) as u64;
    let words_per_row = (column_count as u64 + 31) / 32;
    (row * words_per_row + column / 32, column % 32)
}

#[inline]
fn set<T: FieldElement>(
    first_column_id: u64,
    column_count: usize,
    data: &mut [T],
    global_offset: u64,
    local_offset: i32,
    column: u64,
    value: T,
) {
    let i = index(
        first_column_id,
        column_count,
        global_offset,
        local_offset,
        column,
    );
    data[i] = value;
}

#[inline]
fn set_known(
    first_column_id: u64,
    column_count: usize,
    known: &mut [u32],
    global_offset: u64,
    local_offset: i32,
    column: u64,
) {
    let (known_idx, known_bit) = index_known(
        first_column_id,
        column_count,
        global_offset,
        local_offset,
        column,
    );
    known[known_idx as usize] |= 1 << (known_bit);
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

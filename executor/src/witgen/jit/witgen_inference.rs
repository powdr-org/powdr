use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fmt::{Display, Formatter},
};

use bit_vec::BitVec;
use itertools::Itertools;
use powdr_ast::analyzed::{
    AlgebraicBinaryOperation, AlgebraicBinaryOperator, AlgebraicExpression as Expression,
    AlgebraicReference, AlgebraicUnaryOperation, AlgebraicUnaryOperator, PolynomialIdentity,
    PolynomialType,
};
use powdr_number::FieldElement;

use crate::witgen::{
    data_structures::{identity::Identity, mutable_state::MutableState},
    global_constraints::RangeConstraintSet,
    range_constraints::RangeConstraint,
    FixedData, QueryCallback,
};

use super::{
    affine_symbolic_expression::{AffineSymbolicExpression, Error, ProcessResult},
    effect::{BranchCondition, Effect},
    symbolic_expression::SymbolicExpression,
    variable::{Cell, MachineCallVariable, Variable},
};

/// This component can generate code that solves identities.
/// It needs a driver that tells it which identities to process on which rows.
#[derive(Clone)]
pub struct WitgenInference<'a, T: FieldElement, FixedEval> {
    fixed_data: &'a FixedData<'a, T>,
    fixed_evaluator: FixedEval,
    /// Sequences of branches taken in the past to get to the current state.
    branches_taken: Vec<(Variable, RangeConstraint<T>)>,
    derived_range_constraints: HashMap<Variable, RangeConstraint<T>>,
    known_variables: HashSet<Variable>,
    /// Identities that have already been completed.
    /// Completed identities are still processed to propagate range constraints
    /// and concrete values.
    /// This mainly avoids generating multiple submachine calls for the same
    /// connection on the same row.
    complete_identities: HashSet<(u64, i32)>,
    /// Internal equality constraints that are not identities from the constraint set.
    assignments: BTreeSet<Assignment<'a, T>>,
    code: Vec<Effect<T, Variable>>,
}

#[derive(Debug, Clone, Copy)]
pub enum Value<T> {
    Concrete(T),
    Known,
    Unknown,
}

impl<T: Display> Display for Value<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Concrete(v) => write!(f, "{v}"),
            Value::Known => write!(f, "<known>"),
            Value::Unknown => write!(f, "???"),
        }
    }
}

/// Return type of the `branch_on` method.
pub struct BranchResult<'a, T: FieldElement, FixedEval> {
    /// The code common to both branches.
    pub common_code: Vec<Effect<T, Variable>>,
    /// The condition of the branch.
    pub condition: BranchCondition<T, Variable>,
    /// The two branches.
    pub branches: [WitgenInference<'a, T, FixedEval>; 2],
}

impl<'a, T: FieldElement, FixedEval: FixedEvaluator<T>> WitgenInference<'a, T, FixedEval> {
    pub fn new(
        fixed_data: &'a FixedData<'a, T>,
        fixed_evaluator: FixedEval,
        known_variables: impl IntoIterator<Item = Variable>,
        complete_identities: impl IntoIterator<Item = (u64, i32)>,
    ) -> Self {
        Self {
            fixed_data,
            fixed_evaluator,
            branches_taken: Default::default(),
            derived_range_constraints: Default::default(),
            known_variables: known_variables.into_iter().collect(),
            complete_identities: complete_identities.into_iter().collect(),
            assignments: Default::default(),
            code: Default::default(),
        }
    }

    pub fn finish(self) -> Vec<Effect<T, Variable>> {
        self.code
    }

    pub fn code(&self) -> &Vec<Effect<T, Variable>> {
        &self.code
    }

    pub fn branches_taken(&self) -> &[(Variable, RangeConstraint<T>)] {
        &self.branches_taken
    }

    pub fn known_variables(&self) -> &HashSet<Variable> {
        &self.known_variables
    }

    pub fn is_known(&self, variable: &Variable) -> bool {
        if let Variable::FixedCell(_) = variable {
            true
        } else {
            self.known_variables.contains(variable)
        }
    }

    pub fn is_complete(&self, identity: &Identity<T>, row_offset: i32) -> bool {
        self.complete_identities
            .contains(&(identity.id(), row_offset))
    }

    pub fn value(&self, variable: &Variable) -> Value<T> {
        let rc = self.range_constraint(variable);
        if let Some(val) = rc.try_to_single_value() {
            Value::Concrete(val)
        } else if self.is_known(variable) {
            Value::Known
        } else {
            Value::Unknown
        }
    }

    /// Splits the current inference into two copies - one where the provided variable
    /// is in the "second half" of its range constraint and one where it is in the
    /// "first half" of its range constraint (determined by calling the `bisect` method).
    /// Returns the common code, the branch condition and the two branches.
    pub fn branch_on(mut self, variable: &Variable) -> BranchResult<'a, T, FixedEval> {
        // The variable needs to be known, we need to have a range constraint but
        // it cannot be a single value.
        assert!(self.is_known(variable));
        let rc = self.range_constraint(variable);
        assert!(rc.try_to_single_value().is_none());

        let (low_condition, high_condition) = rc.bisect();

        let common_code = std::mem::take(&mut self.code);
        let mut low_branch = self.clone();

        self.branch_to(variable, high_condition.clone());
        low_branch.branch_to(variable, low_condition.clone());

        BranchResult {
            common_code,
            condition: BranchCondition {
                variable: variable.clone(),
                condition: high_condition,
            },
            branches: [self, low_branch],
        }
    }

    fn branch_to(&mut self, var: &Variable, range_constraint: RangeConstraint<T>) {
        self.branches_taken
            .push((var.clone(), range_constraint.clone()));
        self.add_range_constraint(var.clone(), range_constraint);
    }

    /// Process an identity on a certain row.
    /// Returns Ok(true) if there was progress and Ok(false) if there was no progress.
    /// If this returns an error, it means we have conflicting constraints.
    pub fn process_identity(
        &mut self,
        can_process: impl CanProcessCall<T>,
        id: &'a Identity<T>,
        row_offset: i32,
    ) -> Result<Vec<Variable>, Error> {
        let result = match id {
            Identity::Polynomial(PolynomialIdentity { expression, .. }) => self
                .process_equality_on_row(
                    expression,
                    row_offset,
                    &VariableOrValue::Value(T::from(0)),
                )?,
            Identity::BusSend(bus_interaction) => self.process_call(
                can_process,
                bus_interaction.identity_id,
                &bus_interaction.selected_payload.selector,
                &bus_interaction.selected_payload.expressions,
                row_offset,
            ),
            Identity::BusReceive(_) => ProcessResult::empty(),
            Identity::Connect(_) => ProcessResult::empty(),
        };
        self.ingest_effects(result, Some((id.id(), row_offset)))
    }

    /// Process the constraint that the expression evaluated at the given offset equals the given value.
    /// This does not have to be solvable right away, but is always processed as soon as we have progress.
    /// Note that all variables in the expression can be unknown and their status can also change over time.
    pub fn assign_constant(&mut self, expression: &'a Expression<T>, row_offset: i32, value: T) {
        self.assignments.insert(Assignment {
            lhs: expression,
            row_offset,
            rhs: VariableOrValue::Value(value),
        });
        self.process_assignments().unwrap();
    }

    /// Process the constraint that the expression evaluated at the given offset equals the given formal variable.
    /// This does not have to be solvable right away, but is always processed as soon as we have progress.
    /// Note that all variables in the expression can be unknown and their status can also change over time.
    pub fn assign_variable(
        &mut self,
        expression: &'a Expression<T>,
        row_offset: i32,
        variable: Variable,
    ) {
        self.assignments.insert(Assignment {
            lhs: expression,
            row_offset,
            rhs: VariableOrValue::Variable(variable),
        });
        self.process_assignments().unwrap();
    }

    /// Set the provided variable to a constant value.
    pub fn set_variable(&mut self, variable: Variable, value: T) -> Result<Vec<Variable>, Error> {
        self.ingest_effects(
            ProcessResult {
                effects: vec![Effect::Assignment(variable.clone(), value.into())],
                complete: true,
            },
            None,
        )
    }

    /// Processes an equality constraint.
    /// If this returns an error, it means we have conflicting constraints.
    fn process_equality_on_row(
        &self,
        lhs: &Expression<T>,
        offset: i32,
        rhs: &VariableOrValue<T, Variable>,
    ) -> Result<ProcessResult<T, Variable>, Error> {
        // Try to find a new assignment to a variable in the equality.
        let mut result = self.process_equality_on_row_using_evaluator(lhs, offset, rhs, false)?;
        // Try to propagate range constraints.
        let result_concrete =
            self.process_equality_on_row_using_evaluator(lhs, offset, rhs, true)?;

        // We only use the effects of the second evaluation,
        // its `complete` flag is ignored.
        result.effects.extend(result_concrete.effects);
        Ok(result)
    }

    fn process_equality_on_row_using_evaluator(
        &self,
        lhs: &Expression<T>,
        offset: i32,
        rhs: &VariableOrValue<T, Variable>,
        only_concrete_known: bool,
    ) -> Result<ProcessResult<T, Variable>, Error> {
        let evaluator = if only_concrete_known {
            Evaluator::new(self).only_concrete_known()
        } else {
            Evaluator::new(self)
        };
        let Some(lhs_evaluated) = evaluator.evaluate(lhs, offset) else {
            return Ok(ProcessResult::empty());
        };
        let rhs_evaluated = match rhs {
            VariableOrValue::Variable(v) => evaluator.evaluate_variable(v.clone()),
            VariableOrValue::Value(v) => (*v).into(),
        };
        (lhs_evaluated - rhs_evaluated).solve()
    }

    fn process_call(
        &mut self,
        can_process_call: impl CanProcessCall<T>,
        lookup_id: u64,
        selector: &Expression<T>,
        arguments: &'a [Expression<T>],
        row_offset: i32,
    ) -> ProcessResult<T, Variable> {
        // We need to know the selector.
        let Some(selector) = self
            .evaluate(selector, row_offset)
            .and_then(|s| s.try_to_known().map(|k| k.try_to_number()))
            .flatten()
        else {
            return ProcessResult::empty();
        };
        if selector == 0.into() {
            return ProcessResult {
                effects: vec![],
                complete: true,
            };
        } else {
            assert_eq!(selector, 1.into(), "Selector is non-binary");
        }

        let evaluated = arguments
            .iter()
            .map(|a| self.evaluate(a, row_offset))
            .collect::<Vec<_>>();
        let range_constraints = evaluated
            .iter()
            .map(|e| e.as_ref().map(|e| e.range_constraint()).unwrap_or_default())
            .collect_vec();
        let known: BitVec = evaluated
            .iter()
            .map(|e| e.as_ref().and_then(|e| e.try_to_known()).is_some())
            .collect();

        let Some(new_range_constraints) =
            can_process_call.can_process_call_fully(lookup_id, &known, &range_constraints)
        else {
            return ProcessResult::empty();
        };
        let mut effects = vec![];
        let vars = arguments
            .iter()
            .zip_eq(new_range_constraints)
            .enumerate()
            .map(|(index, (arg, new_rc))| {
                let var = Variable::MachineCallParam(MachineCallVariable {
                    identity_id: lookup_id,
                    row_offset,
                    index,
                });
                self.assign_variable(arg, row_offset, var.clone());
                effects.push(Effect::RangeConstraint(var.clone(), new_rc.clone()));
                if known[index] {
                    assert!(self.is_known(&var));
                }
                var
            })
            .collect_vec();
        effects.push(Effect::MachineCall(lookup_id, known, vars.clone()));
        ProcessResult {
            effects,
            complete: true,
        }
    }

    fn process_assignments(&mut self) -> Result<Vec<Variable>, Error> {
        let mut updated_variables = vec![];
        loop {
            let mut progress = false;
            // We need to take them out because ingest_effects needs a &mut self.
            let assignments = std::mem::take(&mut self.assignments);
            for assignment in &assignments {
                let r = self.process_equality_on_row(
                    assignment.lhs,
                    assignment.row_offset,
                    &assignment.rhs,
                )?;
                let updated_vars = self.ingest_effects(r, None)?;
                progress |= !updated_vars.is_empty();
                updated_variables.extend(updated_vars);
            }
            assert!(self.assignments.is_empty());
            self.assignments = assignments;
            if !progress {
                break;
            }
        }
        Ok(updated_variables)
    }

    /// Analyze the effects and update the internal state.
    /// If the effect is the result of a machine call, `identity_id` must be given
    /// to avoid two calls to the same sub-machine on the same row.
    /// Returns the variables that have been updated.
    fn ingest_effects(
        &mut self,
        process_result: ProcessResult<T, Variable>,
        identity_id: Option<(u64, i32)>,
    ) -> Result<Vec<Variable>, Error> {
        let mut updated_variables = vec![];
        for e in process_result.effects {
            match &e {
                Effect::Assignment(variable, assignment) => {
                    // If the variable was determined to be a constant, we add this
                    // as a range constraint, so we can use it in future evaluations.
                    if self.add_range_constraint(variable.clone(), assignment.range_constraint()) {
                        updated_variables.push(variable.clone());
                    }
                    if self.record_known(variable.clone()) {
                        log::trace!("{variable} := {assignment}");
                        updated_variables.push(variable.clone());
                        self.code.push(e);
                    }
                }
                Effect::RangeConstraint(variable, rc) => {
                    if self.add_range_constraint(variable.clone(), rc.clone()) {
                        log::trace!("{variable}: {rc}");
                        updated_variables.push(variable.clone());
                    }
                }
                Effect::MachineCall(_, _, vars) => {
                    // If the machine call is already complete, it means that we should
                    // not create another submachine call. We might still process it
                    // multiple times to get better range constraints.
                    if self.complete_identities.insert(identity_id.unwrap()) {
                        log::trace!("Machine call: {:?}", identity_id.unwrap());
                        assert!(process_result.complete);
                        for v in vars {
                            // Inputs are already known, but it does not hurt to add all of them.
                            if self.record_known(v.clone()) {
                                updated_variables.push(v.clone());
                            }
                        }
                        self.code.push(e);
                    }
                }
                Effect::Assertion(_) => self.code.push(e),
                Effect::Branch(..) => unreachable!(),
            }
        }
        if process_result.complete {
            if let Some(identity_id) = identity_id {
                // We actually only need to store completeness for submachine calls,
                // but we do it for all identities.
                self.complete_identities.insert(identity_id);
            }
        }
        if !updated_variables.is_empty() {
            // TODO we could have an occurrence map for the assignments as well.
            updated_variables.extend(self.process_assignments()?);
        }
        Ok(updated_variables)
    }

    /// Adds a range constraint to the set of derived range constraints. Returns true if progress was made.
    fn add_range_constraint(&mut self, variable: Variable, rc: RangeConstraint<T>) -> bool {
        let old_rc = self.range_constraint(&variable);
        let rc = old_rc.conjunction(&rc);
        if rc == old_rc {
            return false;
        }
        if let Some(v) = rc.try_to_single_value() {
            // Special case: Variable is fixed to a constant by range constraints only.
            if self.record_known(variable.clone()) {
                self.code
                    .push(Effect::Assignment(variable.clone(), v.into()));
            }
        }
        self.derived_range_constraints.insert(variable.clone(), rc);
        true
    }

    /// Record a variable as known. Return true if it was not known before.
    fn record_known(&mut self, variable: Variable) -> bool {
        // We do not record fixed columns as known.
        if matches!(variable, Variable::FixedCell(_)) {
            false
        } else {
            self.known_variables.insert(variable)
        }
    }

    /// Returns the current best-known range constraint on the given variable
    /// combining global range constraints and newly derived local range constraints.
    /// For fixed columns, it also invokes the fixed evaluator.
    pub fn range_constraint(&self, variable: &Variable) -> RangeConstraint<T> {
        if let Variable::FixedCell(fixed_cell) = variable {
            if let Some(v) = self.fixed_evaluator.evaluate(fixed_cell) {
                return RangeConstraint::from_value(v);
            }
        }
        variable
            .try_to_poly_id()
            .and_then(|poly_id| {
                self.fixed_data
                    .global_range_constraints
                    .range_constraint(&AlgebraicReference {
                        name: Default::default(),
                        poly_id,
                        next: false,
                    })
            })
            .iter()
            .chain(self.derived_range_constraints.get(variable))
            .cloned()
            .reduce(|gc, rc| gc.conjunction(&rc))
            .unwrap_or_default()
    }

    pub fn evaluate(
        &self,
        expr: &Expression<T>,
        offset: i32,
    ) -> Option<AffineSymbolicExpression<T, Variable>> {
        Evaluator::new(self).evaluate(expr, offset)
    }
}

struct Evaluator<'a, T: FieldElement, FixedEval: FixedEvaluator<T>> {
    witgen_inference: &'a WitgenInference<'a, T, FixedEval>,
    only_concrete_known: bool,
}

impl<'a, T: FieldElement, FixedEval: FixedEvaluator<T>> Evaluator<'a, T, FixedEval> {
    pub fn new(witgen_inference: &'a WitgenInference<'a, T, FixedEval>) -> Self {
        Self {
            witgen_inference,
            only_concrete_known: false,
        }
    }

    /// Sets this evaluator into the mode where only concrete variables are
    /// considered "known". This means even if we know how to compute a variable,
    /// as long as we cannot determine it to have a fixed value at compile-time,
    /// it is considered "unknown" and we can solve for it.
    #[allow(unused)]
    pub fn only_concrete_known(self) -> Self {
        Self {
            witgen_inference: self.witgen_inference,
            only_concrete_known: true,
        }
    }

    pub fn evaluate(
        &self,
        expr: &Expression<T>,
        offset: i32,
    ) -> Option<AffineSymbolicExpression<T, Variable>> {
        Some(match expr {
            Expression::Reference(r) => match r.poly_id.ptype {
                PolynomialType::Constant | PolynomialType::Committed => {
                    self.evaluate_variable(Variable::from_reference(r, offset))
                }
                PolynomialType::Intermediate => {
                    let definition =
                        &self.witgen_inference.fixed_data.intermediate_definitions[&r.to_thin()];
                    self.evaluate(definition, offset)?
                }
            },
            Expression::PublicReference(_) | Expression::Challenge(_) => {
                // TODO we need to introduce a variable type for those.
                return None;
            }
            Expression::Number(n) => (*n).into(),
            Expression::BinaryOperation(op) => self.evaluate_binary_operation(op, offset)?,
            Expression::UnaryOperation(op) => self.evaluate_unary_operation(op, offset)?,
        })
    }

    /// Turns the given variable either to a known symbolic value or an unknown symbolic value
    /// depending on if it is known or not.
    /// If it is known to be range-constrained to a single value, that value is used.
    pub fn evaluate_variable(&self, variable: Variable) -> AffineSymbolicExpression<T, Variable> {
        // If a variable is known and has a compile-time constant value,
        // that value is stored in the range constraints.
        let rc = self.witgen_inference.range_constraint(&variable);
        match self.witgen_inference.value(&variable) {
            Value::Concrete(val) => val.into(),
            Value::Unknown => AffineSymbolicExpression::from_unknown_variable(variable, rc),
            Value::Known if self.only_concrete_known => {
                AffineSymbolicExpression::from_unknown_variable(variable, rc)
            }
            Value::Known => AffineSymbolicExpression::from_known_symbol(variable, rc),
        }
    }

    fn evaluate_binary_operation(
        &self,
        op: &AlgebraicBinaryOperation<T>,
        offset: i32,
    ) -> Option<AffineSymbolicExpression<T, Variable>> {
        let left = self.evaluate(&op.left, offset);
        let right = self.evaluate(&op.right, offset);
        match op.op {
            AlgebraicBinaryOperator::Add => Some(&left? + &right?),
            AlgebraicBinaryOperator::Sub => Some(&left? - &right?),
            AlgebraicBinaryOperator::Mul => {
                if is_known_zero(&left) || is_known_zero(&right) {
                    Some(SymbolicExpression::from(T::from(0)).into())
                } else {
                    left?.try_mul(&right?)
                }
            }
            AlgebraicBinaryOperator::Pow => {
                let result = left?
                    .try_to_known()?
                    .try_to_number()?
                    .pow(right?.try_to_known()?.try_to_number()?.to_integer());
                Some(AffineSymbolicExpression::from(result))
            }
        }
    }

    fn evaluate_unary_operation(
        &self,
        op: &AlgebraicUnaryOperation<T>,
        offset: i32,
    ) -> Option<AffineSymbolicExpression<T, Variable>> {
        let expr = self.evaluate(&op.expr, offset)?;
        match op.op {
            AlgebraicUnaryOperator::Minus => Some(-&expr),
        }
    }
}

fn is_known_zero<T: FieldElement>(x: &Option<AffineSymbolicExpression<T, Variable>>) -> bool {
    x.as_ref()
        .and_then(|x| x.try_to_known().map(|x| x.is_known_zero()))
        .unwrap_or(false)
}

/// An equality constraint between an algebraic expression evaluated
/// on a certain row offset and a variable or fixed constant value.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
struct Assignment<'a, T: FieldElement> {
    lhs: &'a Expression<T>,
    row_offset: i32,
    rhs: VariableOrValue<T, Variable>,
}

#[derive(Clone, derive_more::Display, Ord, PartialOrd, Eq, PartialEq, Debug)]
enum VariableOrValue<T, V> {
    Variable(V),
    Value(T),
}

pub trait FixedEvaluator<T: FieldElement>: Clone {
    /// Evaluate a fixed column cell and returns its value if it is
    /// compile-time constant, otherwise return None.
    /// If this function returns `None`, the value of the fixed column will
    /// be treated as symbolically known but not compile-time constant
    /// (i.e. it depends on the row).
    fn evaluate(&self, _fixed_cell: &Cell) -> Option<T> {
        None
    }
}

pub trait CanProcessCall<T: FieldElement>: Clone {
    /// Returns Some(..) if a call to the machine that handles the given identity
    /// can always be processed with the given known inputs and range constraints
    /// on the parameters.
    /// The value in the Option is a vector of new range constraints.
    /// @see Machine::can_process_call
    fn can_process_call_fully(
        &self,
        _identity_id: u64,
        _known_inputs: &BitVec,
        _range_constraints: &[RangeConstraint<T>],
    ) -> Option<Vec<RangeConstraint<T>>>;
}

impl<T: FieldElement, Q: QueryCallback<T>> CanProcessCall<T> for &MutableState<'_, T, Q> {
    fn can_process_call_fully(
        &self,
        identity_id: u64,
        known_inputs: &BitVec,
        range_constraints: &[RangeConstraint<T>],
    ) -> Option<Vec<RangeConstraint<T>>> {
        MutableState::can_process_call_fully(self, identity_id, known_inputs, range_constraints)
    }
}

#[cfg(test)]
mod test {
    use powdr_ast::analyzed::PolyID;
    use powdr_number::GoldilocksField;
    use pretty_assertions::assert_eq;
    use test_log::test;

    use crate::witgen::{
        global_constraints,
        jit::{effect::format_code, test_util::read_pil, variable::Cell},
        machines::{Connection, FixedLookup, KnownMachine},
        FixedData,
    };

    use super::*;

    #[derive(Clone)]
    pub struct FixedEvaluatorForFixedData<'a, T: FieldElement>(pub &'a FixedData<'a, T>);
    impl<T: FieldElement> FixedEvaluator<T> for FixedEvaluatorForFixedData<'_, T> {
        fn evaluate(&self, fixed_cell: &Cell) -> Option<T> {
            let poly_id = PolyID {
                id: fixed_cell.id,
                ptype: PolynomialType::Constant,
            };
            let values = self.0.fixed_cols[&poly_id].values_max_size();
            let row = (fixed_cell.row_offset + values.len() as i32) as usize % values.len();
            Some(values[row])
        }
    }

    fn solve_on_rows(input: &str, rows: &[i32], known_cells: Vec<(&str, i32)>) -> String {
        let (analyzed, fixed_col_vals) = read_pil::<GoldilocksField>(input);
        let fixed_data = FixedData::new(&analyzed, &fixed_col_vals, &[], Default::default(), 0);
        let fixed_data = global_constraints::set_global_constraints(fixed_data);

        let fixed_lookup_connections = fixed_data
            .identities
            .iter()
            .filter_map(|i| Connection::try_new(i, &fixed_data.bus_receives))
            .filter(|c| FixedLookup::is_responsible(c))
            .map(|c| (c.id, c))
            .collect();

        let global_constr = fixed_data.global_range_constraints.clone();
        let fixed_machine = FixedLookup::new(global_constr, &fixed_data, fixed_lookup_connections);
        let known_fixed = KnownMachine::FixedLookup(fixed_machine);
        let mutable_state = MutableState::new([known_fixed].into_iter(), &|_| {
            Err("Query not implemented".to_string())
        });

        let known_cells = known_cells.iter().map(|(name, row_offset)| {
            let id = fixed_data.try_column_by_name(name).unwrap().id;
            Variable::WitnessCell(Cell {
                column_name: name.to_string(),
                id,
                row_offset: *row_offset,
            })
        });

        let ref_eval = FixedEvaluatorForFixedData(&fixed_data);
        let mut witgen = WitgenInference::new(&fixed_data, ref_eval, known_cells, []);
        let mut counter = 0;
        loop {
            let mut progress = false;
            counter += 1;
            for row in rows {
                for id in fixed_data.identities.iter() {
                    progress |= !witgen
                        .process_identity(&mutable_state, id, *row)
                        .unwrap()
                        .is_empty();
                }
            }
            if !progress {
                break;
            }
            assert!(counter < 10000, "Solving took more than 10000 rounds.");
        }
        format_code(&witgen.finish())
    }

    #[test]
    fn simple_polynomial_solving() {
        let input = "let X; let Y; let Z; X = 1; Y = X + 1; Z * Y = X + 10;";
        let code = solve_on_rows(input, &[0], vec![]);
        assert_eq!(code, "X[0] = 1;\nY[0] = 2;\nZ[0] = -9223372034707292155;");
    }

    #[test]
    fn fib() {
        let input = "let X; let Y; X' = Y; Y' = X + Y;";
        let code = solve_on_rows(input, &[0, 1], vec![("X", 0), ("Y", 0)]);
        assert_eq!(
            code,
            "X[1] = Y[0];\nY[1] = (X[0] + Y[0]);\nX[2] = Y[1];\nY[2] = (X[1] + Y[1]);"
        );
    }

    #[test]
    fn fib_with_fixed() {
        let input = "
        namespace Fib(8);
            col fixed FIRST = [1] + [0]*;
            let x;
            let y;
            FIRST * (y - 1) = 0;
            FIRST * (x - 1) = 0;
            // This works in this test because we do not implement wrapping properly in this test.
            x' - y = 0;
            y' - (x + y) = 0;
        ";
        let code = solve_on_rows(input, &[0, 1, 2, 3], vec![]);
        assert_eq!(
            code,
            "Fib::y[0] = 1;
Fib::x[0] = 1;
Fib::x[1] = 1;
Fib::y[1] = 2;
Fib::x[2] = 2;
Fib::y[2] = 3;
Fib::x[3] = 3;
Fib::y[3] = 5;
Fib::x[4] = 5;
Fib::y[4] = 8;"
        );
    }

    #[test]
    fn xor() {
        let input = "
namespace Xor(256 * 256);
    let latch: col = |i| { if (i % 4) == 3 { 1 } else { 0 } };
    let FACTOR: col = |i| { 1 << (((i + 1) % 4) * 8) };

    let a: int -> int = |i| i % 256;
    let b: int -> int = |i| (i / 256) % 256;
    let P_A: col = a;
    let P_B: col = b;
    let P_C: col = |i| a(i) ^ b(i);

    let A_byte;
    let B_byte;
    let C_byte;

    [ A_byte, B_byte, C_byte ] in [ P_A, P_B, P_C ];

    let A;
    let B;
    let C;

    A' = A * (1 - latch) + A_byte * FACTOR;
    B' = B * (1 - latch) + B_byte * FACTOR;
    C' = C * (1 - latch) + C_byte * FACTOR;
";
        let code = solve_on_rows(
            input,
            // Use the second block to avoid wrap-around.
            &[3, 4, 5, 6, 7],
            vec![
                ("Xor::A", 7),
                ("Xor::C", 7), // We solve it in reverse, just for fun.
            ],
        );
        assert_eq!(
            code,
            "\
Xor::A_byte[6] = ((Xor::A[7] & 0xff000000) // 16777216);
Xor::A[6] = (Xor::A[7] & 0xffffff);
assert (Xor::A[7] & 0xffffffff00000000) == 0;
Xor::C_byte[6] = ((Xor::C[7] & 0xff000000) // 16777216);
Xor::C[6] = (Xor::C[7] & 0xffffff);
assert (Xor::C[7] & 0xffffffff00000000) == 0;
Xor::A_byte[5] = ((Xor::A[6] & 0xff0000) // 65536);
Xor::A[5] = (Xor::A[6] & 0xffff);
assert (Xor::A[6] & 0xffffffffff000000) == 0;
Xor::C_byte[5] = ((Xor::C[6] & 0xff0000) // 65536);
Xor::C[5] = (Xor::C[6] & 0xffff);
assert (Xor::C[6] & 0xffffffffff000000) == 0;
call_var(0, 6, 0) = Xor::A_byte[6];
call_var(0, 6, 2) = Xor::C_byte[6];
machine_call(0, [Known(call_var(0, 6, 0)), Unknown(call_var(0, 6, 1)), Known(call_var(0, 6, 2))]);
Xor::B_byte[6] = call_var(0, 6, 1);
Xor::A_byte[4] = ((Xor::A[5] & 0xff00) // 256);
Xor::A[4] = (Xor::A[5] & 0xff);
assert (Xor::A[5] & 0xffffffffffff0000) == 0;
Xor::C_byte[4] = ((Xor::C[5] & 0xff00) // 256);
Xor::C[4] = (Xor::C[5] & 0xff);
assert (Xor::C[5] & 0xffffffffffff0000) == 0;
call_var(0, 5, 0) = Xor::A_byte[5];
call_var(0, 5, 2) = Xor::C_byte[5];
machine_call(0, [Known(call_var(0, 5, 0)), Unknown(call_var(0, 5, 1)), Known(call_var(0, 5, 2))]);
Xor::B_byte[5] = call_var(0, 5, 1);
Xor::A_byte[3] = Xor::A[4];
Xor::C_byte[3] = Xor::C[4];
call_var(0, 4, 0) = Xor::A_byte[4];
call_var(0, 4, 2) = Xor::C_byte[4];
machine_call(0, [Known(call_var(0, 4, 0)), Unknown(call_var(0, 4, 1)), Known(call_var(0, 4, 2))]);
Xor::B_byte[4] = call_var(0, 4, 1);
call_var(0, 3, 0) = Xor::A_byte[3];
call_var(0, 3, 2) = Xor::C_byte[3];
machine_call(0, [Known(call_var(0, 3, 0)), Unknown(call_var(0, 3, 1)), Known(call_var(0, 3, 2))]);
Xor::B_byte[3] = call_var(0, 3, 1);
Xor::B[4] = Xor::B_byte[3];
Xor::B[5] = (Xor::B[4] + (Xor::B_byte[4] * 256));
Xor::B[6] = (Xor::B[5] + (Xor::B_byte[5] * 65536));
Xor::B[7] = (Xor::B[6] + (Xor::B_byte[6] * 16777216));"
        );
    }
}

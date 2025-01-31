#![allow(dead_code)]
use std::{
    collections::BTreeSet,
    fmt::{self, Display, Formatter, Write},
};

use itertools::Itertools;
use powdr_ast::analyzed::{PolyID, PolynomialType};
use powdr_number::FieldElement;

use crate::witgen::{
    data_structures::identity::Identity, jit::debug_formatter::format_identities,
    range_constraints::RangeConstraint, FixedData,
};

use super::{
    affine_symbolic_expression,
    effect::{format_code, Effect},
    identity_queue::IdentityQueue,
    prover_function_heuristics::ProverFunction,
    variable::{Cell, Variable},
    witgen_inference::{BranchResult, CanProcessCall, FixedEvaluator, Value, WitgenInference},
};

/// A generic processor for generating JIT code.
pub struct Processor<'a, T: FieldElement, FixedEval> {
    fixed_data: &'a FixedData<'a, T>,
    /// An evaluator for fixed columns
    fixed_evaluator: FixedEval,
    /// List of identities and row offsets to process them on.
    identities: Vec<(&'a Identity<T>, i32)>,
    /// The prover functions, i.e. helpers to compute certain values that
    /// we cannot easily determine.
    prover_functions: Vec<(ProverFunction<'a, T>, i32)>,
    /// The size of a block.
    block_size: usize,
    /// If the processor should check for correctly stackable block shapes.
    check_block_shape: bool,
    /// List of variables we want to be known at the end. One of them not being known
    /// is a failure.
    requested_known_vars: Vec<Variable>,
    /// List of variables we want to know the derived range constraints of at the very end
    /// (for every branch).
    requested_range_constraints: Vec<Variable>,
    /// Maximum branch depth allowed.
    max_branch_depth: usize,
}

pub struct ProcessorResult<T: FieldElement> {
    /// Generated code.
    pub code: Vec<Effect<T, Variable>>,
    /// Range constrainst of the variables they were requested on.
    pub range_constraints: Vec<RangeConstraint<T>>,
}

impl<'a, T: FieldElement, FixedEval: FixedEvaluator<T>> Processor<'a, T, FixedEval> {
    pub fn new(
        fixed_data: &'a FixedData<'a, T>,
        fixed_evaluator: FixedEval,
        identities: impl IntoIterator<Item = (&'a Identity<T>, i32)>,
        requested_known_vars: impl IntoIterator<Item = Variable>,
        max_branch_depth: usize,
    ) -> Self {
        let identities = identities.into_iter().collect_vec();
        Self {
            fixed_data,
            fixed_evaluator,
            identities,
            prover_functions: vec![],
            block_size: 1,
            check_block_shape: false,
            requested_known_vars: requested_known_vars.into_iter().collect(),
            requested_range_constraints: vec![],
            max_branch_depth,
        }
    }

    /// Provides a list of variables that we want to know the derived range constraints of at the end.
    pub fn with_requested_range_constraints(
        mut self,
        vars: impl IntoIterator<Item = Variable>,
    ) -> Self {
        self.requested_range_constraints.extend(vars);
        self
    }

    /// Sets the block size.
    pub fn with_block_size(mut self, block_size: usize) -> Self {
        self.block_size = block_size;
        self
    }

    /// Activates the check to see if the code for two subsequently generated
    /// blocks conflicts.
    pub fn with_block_shape_check(mut self) -> Self {
        self.check_block_shape = true;
        self
    }

    pub fn with_prover_functions(
        mut self,
        prover_functions: Vec<(ProverFunction<'a, T>, i32)>,
    ) -> Self {
        assert!(self.prover_functions.is_empty());
        self.prover_functions = prover_functions;
        self
    }

    pub fn generate_code(
        self,
        can_process: impl CanProcessCall<T>,
        witgen: WitgenInference<'a, T, FixedEval>,
    ) -> Result<ProcessorResult<T>, Error<'a, T, FixedEval>> {
        let branch_depth = 0;
        let identity_queue = IdentityQueue::new(self.fixed_data, &self.identities);
        self.generate_code_for_branch(can_process, witgen, identity_queue, branch_depth)
    }

    fn generate_code_for_branch(
        &self,
        can_process: impl CanProcessCall<T>,
        mut witgen: WitgenInference<'a, T, FixedEval>,
        mut identity_queue: IdentityQueue<'a, T>,
        branch_depth: usize,
    ) -> Result<ProcessorResult<T>, Error<'a, T, FixedEval>> {
        if self
            .process_until_no_progress(can_process.clone(), &mut witgen, &mut identity_queue)
            .is_err()
        {
            return Err(Error::conflicting_constraints(
                witgen,
                self.fixed_evaluator.clone(),
            ));
        }

        if self.check_block_shape {
            // Check that the "spill" into the previous block is compatible
            // with the "missing pieces" in the next block.
            // If this is not the case, this is a hard error
            // (i.e. cannot be fixed by runtime witgen) and thus we panic inside.
            // We could do this only at the end of each branch, but it's a bit
            // more convenient to do it here.
            self.check_block_shape(&witgen);
        }

        // Check that we could derive all requested variables.
        let missing_variables = self
            .requested_known_vars
            .iter()
            .filter(|var| !witgen.is_known(var))
            // Sort to get deterministic code.
            .sorted()
            .cloned()
            .collect_vec();

        let incomplete_machine_calls = self.incomplete_machine_calls(&witgen);
        if missing_variables.is_empty() && incomplete_machine_calls.is_empty() {
            let range_constraints = self
                .requested_range_constraints
                .iter()
                .map(|var| witgen.range_constraint(var))
                .collect();
            let code = witgen.finish();
            return Ok(ProcessorResult {
                code,
                range_constraints,
            });
        }

        // We need to do some work, try to branch.
        let most_constrained_var = witgen
            .known_variables()
            .iter()
            .map(|var| (var, witgen.range_constraint(var)))
            .filter(|(_, rc)| rc.try_to_single_value().is_none())
            .sorted()
            .min_by_key(|(_, rc)| rc.range_width())
            .map(|(var, rc)| (var.clone(), rc.clone()));
        // Either there is no variable left to branch on or the most constrained
        // still has more than (1 << max_branch_depth) possible values.
        let no_viable_branch_variable = most_constrained_var
            .as_ref()
            .map(|(_, rc)| (rc.range_width() >> self.max_branch_depth) > 0.into())
            .unwrap_or(true);
        if branch_depth >= self.max_branch_depth || no_viable_branch_variable {
            let reason = if no_viable_branch_variable {
                ErrorReason::NoBranchVariable
            } else {
                ErrorReason::MaxBranchDepthReached(self.max_branch_depth)
            };
            let incomplete_identities = self
                .identities
                .iter()
                .filter(|(id, row_offset)| !witgen.is_complete(id, *row_offset))
                .map(|(id, row_offset)| (*id, *row_offset))
                .collect_vec();
            return Err(Error {
                reason,
                witgen,
                fixed_evaluator: self.fixed_evaluator.clone(),
                missing_variables,
                incomplete_identities,
            });
        };
        let (most_constrained_var, range) = most_constrained_var.unwrap();

        log::debug!("Branching on variable {most_constrained_var} with range {range} at depth {branch_depth}");

        let BranchResult {
            common_code,
            condition,
            branches: [first_branch, second_branch],
        } = witgen.branch_on(&most_constrained_var.clone());

        identity_queue.variables_updated(vec![most_constrained_var.clone()], None);

        // TODO Tuning: If this fails (or also if it does not generate progress right away),
        // we could also choose a different variable to branch on.

        let first_branch_result = self.generate_code_for_branch(
            can_process.clone(),
            first_branch,
            identity_queue.clone(),
            branch_depth + 1,
        );
        let second_branch_result = self.generate_code_for_branch(
            can_process,
            second_branch,
            identity_queue,
            branch_depth + 1,
        );
        let mut result = match (first_branch_result, second_branch_result) {
            (Err(e), other) | (other, Err(e))
                if e.reason == ErrorReason::ConflictingConstraints =>
            {
                // Any branch with a conflicting constraint is not reachable and thus
                // can be pruned. We do not branch but still add the range constraint
                // of the branching variable.
                // Note that both branches might actually have a conflicting constraint,
                // but then it is correct to return one.
                log::trace!("Branching on {most_constrained_var} resulted in a conflict, we can reduce to a single branch.");
                other?
            }
            // Any other error should be propagated.
            (Err(e), _) | (_, Err(e)) => Err(e)?,
            (Ok(first_result), Ok(second_result)) if first_result.code == second_result.code => {
                log::trace!("Branching on {most_constrained_var} resulted in the same code, we can reduce to a single branch.");
                ProcessorResult {
                    code: first_result.code,
                    range_constraints: combine_range_constraints(
                        &first_result.range_constraints,
                        &second_result.range_constraints,
                    ),
                }
            }
            (Ok(first_result), Ok(second_result)) => {
                let code = vec![Effect::Branch(
                    condition,
                    first_result.code,
                    second_result.code,
                )];
                let range_constraints = combine_range_constraints(
                    &first_result.range_constraints,
                    &second_result.range_constraints,
                );
                ProcessorResult {
                    code,
                    range_constraints,
                }
            }
        };
        // Prepend the common code in the success case.
        result.code = common_code.into_iter().chain(result.code).collect();
        Ok(result)
    }

    fn process_until_no_progress(
        &self,
        can_process: impl CanProcessCall<T>,
        witgen: &mut WitgenInference<'a, T, FixedEval>,
        identity_queue: &mut IdentityQueue<'a, T>,
    ) -> Result<(), affine_symbolic_expression::Error> {
        loop {
            let identity = identity_queue.next();
            let updated_vars = match identity {
                Some((identity, row_offset)) => {
                    witgen.process_identity(can_process.clone(), identity, row_offset)
                }
                None => self.process_prover_functions(witgen),
            }?;
            if updated_vars.is_empty() && identity.is_none() {
                // No identities to process and prover functions did not make any progress,
                // we are done.
                return Ok(());
            }
            identity_queue.variables_updated(updated_vars, identity);
        }
    }

    /// Tries to process all prover functions until the first one is able to update a variable.
    /// Returns the updated variables.
    fn process_prover_functions(
        &self,
        witgen: &mut WitgenInference<'a, T, FixedEval>,
    ) -> Result<Vec<Variable>, affine_symbolic_expression::Error> {
        for (prover_function, row_offset) in &self.prover_functions {
            let updated_vars = witgen.process_prover_function(prover_function, *row_offset)?;
            if !updated_vars.is_empty() {
                return Ok(updated_vars);
            }
        }

        Ok(vec![])
    }

    /// If any machine call could not be completed, that's bad because machine calls typically have side effects.
    /// So, the underlying lookup / permutation / bus argument likely does not hold.
    /// This function checks that all machine calls are complete, at least for a window of <block_size> rows.
    /// It returns the list of incomplete calls, if any.
    fn incomplete_machine_calls(
        &self,
        witgen: &WitgenInference<'a, T, FixedEval>,
    ) -> Vec<(&Identity<T>, i32)> {
        self.identities
            .iter()
            .map(|(id, _)| id)
            .filter(|id| is_machine_call(id))
            .unique()
            .flat_map(|&call| {
                let rows = self.rows_for_identity(call);
                let complete_rows = rows
                    .iter()
                    .filter(|&&row| witgen.is_complete(call, row))
                    .collect::<Vec<_>>();
                // We might process more rows than `self.block_size`, so we check
                // that the complete calls are on consecutive rows.
                if complete_rows.len() >= self.block_size {
                    let (min, max) = complete_rows.iter().minmax().into_option().unwrap();
                    // TODO instead of checking for consecutive rows, we could also check
                    // that they "fit" the next block.
                    // TODO actually I think that we should not allow more than block size
                    // completed calls.
                    let is_consecutive = *max - *min == complete_rows.len() as i32 - 1;
                    if is_consecutive {
                        return vec![];
                    }
                }
                rows.iter()
                    .filter(|&row| !witgen.is_complete(call, *row))
                    .map(|row| (call, *row))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    }

    /// Returns the list of rows the given identity is processed on.
    fn rows_for_identity(&self, identity: &Identity<T>) -> Vec<i32> {
        self.identities
            .iter()
            .filter_map(move |(id, row_offset)| {
                if *id == identity {
                    Some(*row_offset)
                } else {
                    None
                }
            })
            .collect()
    }

    /// After solving, the known cells should be such that we can stack different blocks.
    /// If this is not the case, this function panics.
    /// TODO the same is actually true for machine calls.
    fn check_block_shape(&self, witgen: &WitgenInference<'a, T, FixedEval>) {
        let known_columns: BTreeSet<_> = witgen
            .known_variables()
            .iter()
            .filter_map(|var| match var {
                Variable::WitnessCell(cell) => Some(cell.id),
                _ => None,
            })
            .collect();
        for column_id in known_columns {
            let known_rows = witgen
                .known_variables()
                .iter()
                .filter_map(|var| match var {
                    Variable::WitnessCell(cell) if cell.id == column_id => Some(cell.row_offset),
                    _ => None,
                })
                .collect::<BTreeSet<_>>();

            // Two values that refer to the same row (modulo block size) are compatible if:
            // - One of them is unknown, or
            // - Both are concrete and equal
            let is_compatible = |v1: Value<T>, v2: Value<T>| match (v1, v2) {
                (Value::Unknown, _) | (_, Value::Unknown) => true,
                (Value::Concrete(a), Value::Concrete(b)) => a == b,
                _ => false,
            };
            let cell_var = |row_offset| {
                Variable::WitnessCell(Cell {
                    // Column name does not matter.
                    column_name: "".to_string(),
                    id: column_id,
                    row_offset,
                })
            };

            // A column is stackable if all rows equal to each other modulo
            // the block size are compatible.
            for row in &known_rows {
                let this_val = witgen.value(&cell_var(*row));
                let next_block_val = witgen.value(&cell_var(row + self.block_size as i32));
                if !is_compatible(this_val, next_block_val) {
                    let column_name = self.fixed_data.column_name(&PolyID {
                        id: column_id,
                        ptype: PolynomialType::Committed,
                    });
                    let row_vals = known_rows
                        .iter()
                        .map(|&r| format!("  row {r}: {}\n", witgen.value(&cell_var(r))))
                        .format("");
                    log::debug!(
                        "Code generated so far:\n{}\n\
                        Column {column_name} is not stackable in a {}-row block, \
                        conflict in rows {row} and {}.\n{row_vals}",
                        format_code(witgen.code()),
                        self.block_size,
                        row + self.block_size as i32
                    );
                    panic!(
                        "Column {column_name} is not stackable in a {}-row block, conflict in rows {row} and {}.\n{row_vals}",
                        self.block_size,
                        row + self.block_size as i32
                    );
                }
            }
        }
    }
}

fn is_machine_call<T>(identity: &Identity<T>) -> bool {
    matches!(identity, Identity::BusSend(_))
}

fn combine_range_constraints<T: FieldElement>(
    first: &[RangeConstraint<T>],
    second: &[RangeConstraint<T>],
) -> Vec<RangeConstraint<T>> {
    first
        .iter()
        .zip(second.iter())
        .map(|(rc1, rc2)| rc1.disjunction(rc2))
        .collect()
}

pub struct Error<'a, T: FieldElement, FixedEval: FixedEvaluator<T>> {
    pub reason: ErrorReason,
    pub witgen: WitgenInference<'a, T, FixedEval>,
    pub fixed_evaluator: FixedEval,
    /// Required variables that could not be determined
    pub missing_variables: Vec<Variable>,
    /// Identities that could not be processed completely.
    /// Note that we only force submachine calls to be complete.
    pub incomplete_identities: Vec<(&'a Identity<T>, i32)>,
}

#[derive(PartialEq, Eq)]
pub enum ErrorReason {
    /// This error means that the current branch (if it is a branch)
    /// is actually not reachable.
    ConflictingConstraints,
    /// We were not able to solve all required constraints and
    /// there is no variable left to branch on.
    NoBranchVariable,
    /// We were not able to solve all required constraints and
    /// the maximum branch depth was reached.
    MaxBranchDepthReached(usize),
}

impl<T: FieldElement, FE: FixedEvaluator<T>> Display for Error<'_, T, FE> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            self.to_string_with_variable_formatter(|var| var.to_string())
        )
    }
}

impl<'a, T: FieldElement, FE: FixedEvaluator<T>> Error<'a, T, FE> {
    pub fn conflicting_constraints(
        witgen: WitgenInference<'a, T, FE>,
        fixed_evaluator: FE,
    ) -> Self {
        Self {
            witgen,
            fixed_evaluator,
            reason: ErrorReason::ConflictingConstraints,
            missing_variables: vec![],
            incomplete_identities: vec![],
        }
    }

    pub fn to_string_with_variable_formatter(
        &self,
        var_formatter: impl Fn(&Variable) -> String,
    ) -> String {
        let mut s = String::new();
        let reason_str = match &self.reason {
            ErrorReason::ConflictingConstraints => "Conflicting constraints".to_string(),
            ErrorReason::NoBranchVariable => "No variable available to branch on".to_string(),
            ErrorReason::MaxBranchDepthReached(depth) => {
                format!("Maximum branch depth of {depth} reached")
            }
        };
        write!(
            s,
            "Unable to derive algorithm to compute required values: {reason_str}."
        )
        .unwrap();
        if !self.missing_variables.is_empty() {
            write!(
                s,
                "\nThe following variables or values are still missing: {}",
                self.missing_variables
                    .iter()
                    .map(var_formatter)
                    .format(", ")
            )
            .unwrap();
        };
        if !self.incomplete_identities.is_empty() {
            write!(
                s,
                "\nThe following identities have not been fully processed:\n{}",
                format_identities(&self.incomplete_identities, &self.witgen,)
            )
            .unwrap();
        };
        write!(
            s,
            "\nThe following branch decisions were taken:\n{}",
            self.witgen
                .branches_taken()
                .iter()
                .map(|(var, rc)| format!("    {var} = {rc}"))
                .join("\n")
        )
        .unwrap();
        let code = self.witgen.code();
        if code.is_empty() {
            write!(s, "\nNo code generated so far.").unwrap();
        } else {
            write!(s, "\nGenerated code so far:\n{}", format_code(code)).unwrap();
        };
        s
    }
}

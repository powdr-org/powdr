#![allow(dead_code)]
use std::collections::HashSet;

use itertools::Itertools;
use powdr_ast::analyzed::{AlgebraicReference, PolyID};
use powdr_number::FieldElement;

use crate::witgen::{machines::MachineParts, FixedData};

use super::{
    effect::Effect,
    variable::{Cell, Variable},
    witgen_inference::{BranchResult, CanProcessCall, FixedEvaluator, WitgenInference},
};

/// A processor for generating JIT code that computes the next row from the previous row.
pub struct SingleStepProcessor<'a, T: FieldElement> {
    fixed_data: &'a FixedData<'a, T>,
    machine_parts: MachineParts<'a, T>,
}

impl<'a, T: FieldElement> SingleStepProcessor<'a, T> {
    pub fn new(fixed_data: &'a FixedData<'a, T>, machine_parts: MachineParts<'a, T>) -> Self {
        SingleStepProcessor {
            fixed_data,
            machine_parts,
        }
    }

    pub fn generate_code<CanProcess: CanProcessCall<T> + Clone>(
        &self,
        can_process: CanProcess,
    ) -> Result<Vec<Effect<T, Variable>>, String> {
        self.generate_code_for_branch(can_process, self.initialize_witgen(), Default::default())
    }

    pub fn generate_code_for_branch<CanProcess: CanProcessCall<T> + Clone>(
        &self,
        can_process: CanProcess,
        mut witgen: WitgenInference<'a, T, NoEval>,
        mut complete: HashSet<u64>,
    ) -> Result<Vec<Effect<T, Variable>>, String> {
        self.process_until_no_progress(can_process.clone(), &mut witgen, &mut complete);

        // Check that we could derive all witness values in the next row.
        let unknown_witnesses = self
            .unknown_witness_cols_on_next_row(&witgen)
            // Sort to get deterministic code.
            .sorted()
            .collect_vec();

        let missing_identities = self.machine_parts.identities.len() - complete.len();
        let code = if unknown_witnesses.is_empty() && missing_identities == 0 {
            witgen.code()
        } else {
            let Some(most_constrained_var) = witgen
                .known_variables()
                .iter()
                .filter_map(|var| witgen.range_constraint(var).map(|rc| (var, rc)))
                .filter(|(_, rc)| rc.try_to_single_value().is_none())
                .sorted()
                .min_by_key(|(_, rc)| rc.range_width())
                .map(|(var, _)| var.clone())
            else {
                let incomplete_identities = self
                    .machine_parts
                    .identities
                    .iter()
                    .filter(|id| !complete.contains(&id.id()));
                let column_errors = if unknown_witnesses.is_empty() {
                    "".to_string()
                } else {
                    format!(
                        "\nThe following columns are still missing: {}",
                        unknown_witnesses
                            .iter()
                            .map(|wit| self.fixed_data.column_name(wit))
                            .format(", ")
                    )
                };
                let identity_errors = if missing_identities == 0 {
                    "".to_string()
                } else {
                    format!(
                        "\nThe following identities have not been fully processed:\n{}",
                        incomplete_identities
                            .map(|id| format!("    {id}"))
                            .join("\n")
                    )
                };
                return Err(format!(
                    "Unable to derive algorithm to compute values for witness columns in the next row and\n\
                    unable to branch on a variable.{column_errors}{identity_errors}",
                ));
            };

            let BranchResult {
                common_code,
                condition,
                branches: [first_branch, second_branch],
            } = witgen.branch_on(&most_constrained_var.clone());

            // TODO Tuning: If this fails (or also if it does not generate progress right away),
            // we could also choose a different variable to branch on.
            let left_branch_code =
                self.generate_code_for_branch(can_process.clone(), first_branch, complete.clone())?;
            let right_branch_code =
                self.generate_code_for_branch(can_process, second_branch, complete)?;
            if left_branch_code == right_branch_code {
                common_code.into_iter().chain(left_branch_code).collect()
            } else {
                common_code
                    .into_iter()
                    .chain(std::iter::once(Effect::Branch(
                        condition,
                        left_branch_code,
                        right_branch_code,
                    )))
                    .collect()
            }
        };
        Ok(code)
    }

    fn initialize_witgen(&self) -> WitgenInference<'a, T, NoEval> {
        // All witness columns in row 0 are known.
        let known_variables = self.machine_parts.witnesses.iter().map(|id| {
            Variable::Cell(Cell {
                column_name: self.fixed_data.column_name(id).to_string(),
                id: id.id,
                row_offset: 0,
            })
        });
        WitgenInference::new(self.fixed_data, NoEval, known_variables)
    }

    fn process_until_no_progress<CanProcess: CanProcessCall<T> + Clone>(
        &self,
        can_process: CanProcess,
        witgen: &mut WitgenInference<'a, T, NoEval>,
        complete: &mut HashSet<u64>,
    ) {
        let mut progress = true;
        while progress {
            progress = false;

            // TODO At this point, we should call a function on `witgen`
            // to propagate known concrete values across the identities
            // to other known (but not concrete) variables.

            for id in &self.machine_parts.identities {
                if complete.contains(&id.id()) {
                    continue;
                }
                // TODO this is wrong if intermediate columns are referenced.
                let row_offset = if id.contains_next_ref(&self.fixed_data.intermediate_definitions)
                {
                    0
                } else {
                    1
                };
                let result = witgen.process_identity(can_process.clone(), id, row_offset);
                progress |= result.progress;
                if result.complete {
                    complete.insert(id.id());
                }
            }
        }
    }

    fn unknown_witness_cols_on_next_row<'b>(
        &'b self,
        witgen: &'b WitgenInference<'_, T, NoEval>,
    ) -> impl Iterator<Item = &'b PolyID> + 'b {
        self.machine_parts.witnesses.iter().filter(move |wit| {
            !witgen.is_known(&Variable::Cell(Cell {
                column_name: self.fixed_data.column_name(wit).to_string(),
                id: wit.id,
                row_offset: 1,
            }))
        })
    }
}

#[derive(Clone)]
pub struct NoEval;

impl<T: FieldElement> FixedEvaluator<T> for NoEval {
    fn evaluate(&self, _var: &AlgebraicReference, _row_offset: i32) -> Option<T> {
        // We can only return something here if the fixed column is constant
        // in the region we are considering.
        // This might be the case if we know we are not evaluating the first or the last
        // row, but this is not yet implemented.
        None
    }
}

#[cfg(test)]
mod test {

    use pretty_assertions::assert_eq;
    use test_log::test;

    use powdr_number::GoldilocksField;

    use crate::witgen::{
        data_structures::mutable_state::MutableState,
        global_constraints,
        jit::effect::{format_code, Effect},
        machines::KnownMachine,
        FixedData,
    };
    use itertools::Itertools;

    use crate::witgen::{
        jit::test_util::read_pil,
        machines::{machine_extractor::MachineExtractor, Machine},
    };

    use super::{SingleStepProcessor, Variable};

    fn generate_single_step(
        input_pil: &str,
        machine_name: &str,
    ) -> Result<Vec<Effect<GoldilocksField, Variable>>, String> {
        let (analyzed, fixed_col_vals) = read_pil(input_pil);

        let fixed_data = FixedData::new(&analyzed, &fixed_col_vals, &[], Default::default(), 0);
        let (fixed_data, retained_identities) =
            global_constraints::set_global_constraints(fixed_data, &analyzed.identities);
        let machines = MachineExtractor::new(&fixed_data).split_out_machines(retained_identities);
        let [KnownMachine::DynamicMachine(machine)] = machines
            .iter()
            .filter(|m| m.name().contains(machine_name))
            .collect_vec()
            .as_slice()
        else {
            panic!("Expected exactly one matching dynamic machine")
        };
        let machine_parts = machine.machine_parts().clone();
        let mutable_state = MutableState::new(machines.into_iter(), &|_| {
            Err("Query not implemented".to_string())
        });
        SingleStepProcessor::new(&fixed_data, machine_parts).generate_code(&mutable_state)
    }

    #[test]
    fn fib() {
        let input = "namespace M(256); let X; let Y; X' = Y; Y' = X + Y;";
        let code = generate_single_step(input, "M").unwrap();
        assert_eq!(
            format_code(&code),
            "M::X[1] = M::Y[0];\nM::Y[1] = (M::X[0] + M::Y[0]);"
        );
    }

    #[test]
    fn no_progress() {
        let input = "namespace M(256); let X; let Y; X' = X;";
        let err = generate_single_step(input, "M").err().unwrap();
        assert_eq!(
            err.to_string(),
            "Unable to derive algorithm to compute values for witness columns in the next row and\n\
            unable to branch on a variable.\nThe following columns are still missing: M::Y"
        );
    }

    #[test]
    fn branching() {
        let input = "
    namespace VM(256);
        let A: col;
        let B: col;
        let instr_add: col;
        let instr_mul: col;
        let pc: col;

        col fixed LINE = [0, 1] + [2]*;
        col fixed INSTR_ADD = [0, 1] + [0]*;
        col fixed INSTR_MUL = [1, 0] + [1]*;

        pc' = pc + 1;
        [ pc, instr_add, instr_mul ] in [ LINE, INSTR_ADD, INSTR_MUL ];

        instr_add * (A' - (A + B)) + instr_mul * (A' - A * B) + (1 - instr_add - instr_mul) * (A' - A) = 0;
        B' = B;
        ";
        let code = generate_single_step(input, "Main").unwrap();
        assert_eq!(
            format_code(&code),
            "\
VM::pc[1] = (VM::pc[0] + 1);
machine_call(1, [Known(VM::pc[1]), Unknown(ret(1, 1, 1)), Unknown(ret(1, 1, 2))]);
VM::instr_add[1] = ret(1, 1, 1);
VM::instr_mul[1] = ret(1, 1, 2);
VM::B[1] = VM::B[0];
if (VM::instr_add[0] == 1) {
    if (VM::instr_mul[0] == 1) {
        VM::A[1] = -((-(VM::A[0] + VM::B[0]) + -(VM::A[0] * VM::B[0])) + VM::A[0]);
    } else {
        VM::A[1] = (VM::A[0] + VM::B[0]);
    }
} else {
    if (VM::instr_mul[0] == 1) {
        VM::A[1] = (VM::A[0] * VM::B[0]);
    } else {
        VM::A[1] = VM::A[0];
    }
}"
        );
    }
}

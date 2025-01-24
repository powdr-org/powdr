#![allow(dead_code)]

use itertools::Itertools;
use powdr_ast::analyzed::{
    AlgebraicExpression as Expression, AlgebraicReference, PolyID, PolynomialType,
};
use powdr_number::FieldElement;

use crate::witgen::{machines::MachineParts, FixedData};

use super::{
    effect::Effect,
    processor::Processor,
    prover_function_heuristics::decode_simple_prover_functions,
    variable::{Cell, Variable},
    witgen_inference::{CanProcessCall, FixedEvaluator, WitgenInference},
};

/// This is a tuning value. It is the maximum nesting depth of branches in the JIT code.
const SINGLE_STEP_MACHINE_MAX_BRANCH_DEPTH: usize = 6;

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

    pub fn generate_code(
        &self,
        can_process: impl CanProcessCall<T>,
    ) -> Result<Vec<Effect<T, Variable>>, String> {
        let all_witnesses = self
            .machine_parts
            .witnesses
            .iter()
            .cloned()
            .sorted()
            .collect_vec();
        // All witness columns in row 0 are known.
        let known_variables = all_witnesses.iter().map(|&id| self.cell(id, 0));
        // and we want to know the ones in the next row.
        let requested_known = all_witnesses.iter().map(|&id| self.cell(id, 1));
        // Identities that span two rows are only processed on row 0,
        // the others are processed on both rows.
        let mut complete_identities = vec![];
        let identities = self
            .machine_parts
            .identities
            .iter()
            .flat_map(|&id| {
                if id.contains_next_ref() {
                    vec![(id, 0)]
                } else {
                    // Process it on both rows, but mark it as complete on row 0,
                    // so that we do not produce two submachine calls.
                    complete_identities.push((id.id(), 0));
                    vec![(id, 0), (id, 1)]
                }
            })
            .collect_vec();

        let mut witgen =
            WitgenInference::new(self.fixed_data, self, known_variables, complete_identities);

        let prover_assignments = decode_simple_prover_functions(&self.machine_parts)
            .into_iter()
            .map(|(col_name, value)| (self.column(&col_name), value))
            .collect_vec();

        // TODO we should only do it if other methods fail, because it is "provide_if_unknown"
        for (col, value) in &prover_assignments {
            witgen.assign_constant(col, 1, *value);
        }

        Processor::new(
            self.fixed_data,
            self,
            identities,
            requested_known,
            SINGLE_STEP_MACHINE_MAX_BRANCH_DEPTH,
        )
        .generate_code(can_process, witgen)
        .map_err(|e| e.to_string())
        .map(|r| r.code)
    }

    fn cell(&self, id: PolyID, row_offset: i32) -> Variable {
        Variable::WitnessCell(Cell {
            column_name: self.fixed_data.column_name(&id).to_string(),
            id: id.id,
            row_offset,
        })
    }

    fn column(&self, name: &str) -> Expression<T> {
        Expression::Reference(AlgebraicReference {
            name: name.to_string(),
            poly_id: self.fixed_data.try_column_by_name(name).unwrap(),
            next: false,
        })
    }
}

/// Evaluator for fixed columns which are constant except for the first and last row.
impl<T: FieldElement> FixedEvaluator<T> for &SingleStepProcessor<'_, T> {
    fn evaluate(&self, fixed_cell: &Cell) -> Option<T> {
        let poly_id = PolyID {
            id: fixed_cell.id,
            ptype: PolynomialType::Constant,
        };
        self.fixed_data.fixed_cols[&poly_id].has_constant_inner_value()
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
        SingleStepProcessor::new(&fixed_data, machine_parts)
            .generate_code(&mutable_state)
            .map_err(|e| e.to_string())
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
    fn fib_with_boundary_conditions() {
        let input = "
namespace M(256);
    col fixed FIRST = [1] + [0]*;
    col fixed LAST = [0]* + [1];
    let X;
    let Y;
    FIRST * (X - 1) = 0;
    FIRST * (Y - 1) = 0;
    (X' - Y) * (1 - LAST) = 0;
    (Y' - (X + Y)) * (1 - LAST) = 0;";
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
            "Unable to derive algorithm to compute required values: \
            No variable available to branch on.\nThe following variables or values are still missing: M::Y[1]\n\
            The following branch decisions were taken:\n\
            \n\
            Generated code so far:\n\
            M::X[1] = M::X[0];"
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
call_var(1, 0, 0) = VM::pc[0];
call_var(1, 0, 1) = VM::instr_add[0];
call_var(1, 0, 2) = VM::instr_mul[0];
VM::B[1] = VM::B[0];
call_var(1, 1, 0) = VM::pc[1];
machine_call(1, [Known(call_var(1, 1, 0)), Unknown(call_var(1, 1, 1)), Unknown(call_var(1, 1, 2))]);
VM::instr_add[1] = call_var(1, 1, 1);
VM::instr_mul[1] = call_var(1, 1, 2);
if (VM::instr_add[0] == 1) {
    VM::A[1] = (VM::A[0] + VM::B[0]);
} else {
    VM::A[1] = (VM::A[0] * VM::B[0]);
}"
        );
    }

    #[test]
    fn range_constraints_from_lookup() {
        let input = "
    namespace VM(256);
        let instr_add: col;
        let instr_mul: col;
        let pc: col;

        col fixed LINE = [0, 1] + [2]*;
        col fixed INSTR_ADD = [0, 1] + [0]*;
        col fixed INSTR_MUL = [1, 0] + [1]*;

        pc' = pc;
        instr_add = 0;
        [ pc, instr_add, instr_mul ] in [ LINE, INSTR_ADD, INSTR_MUL ];

        ";
        let code = generate_single_step(input, "Main").unwrap();
        // After the machine call, we should have a direct assignment `VM::instr_mul[1] = 1`,
        // instead of just an assignment from the call variable.
        // This is because the fixed lookup machine can already provide a range constraint.
        // For reasons of processing order, the call variable will also be assigned
        // right before the call.
        assert_eq!(
            format_code(&code),
            "\
VM::pc[1] = VM::pc[0];
call_var(2, 0, 0) = VM::pc[0];
call_var(2, 0, 1) = 0;
call_var(2, 0, 2) = VM::instr_mul[0];
VM::instr_add[1] = 0;
call_var(2, 1, 0) = VM::pc[1];
call_var(2, 1, 1) = 0;
call_var(2, 1, 2) = 1;
machine_call(2, [Known(call_var(2, 1, 0)), Known(call_var(2, 1, 1)), Unknown(call_var(2, 1, 2))]);
VM::instr_mul[1] = 1;"
        );
    }

    #[test]
    fn nonconstant_fixed_columns() {
        let input = "
    namespace VM(256);
        let STEP: col = |i| i;
        let w;
        w = STEP;
        ";
        let code = generate_single_step(input, "Main").unwrap();
        assert_eq!(format_code(&code), "VM::w[1] = VM::STEP[1];");
    }

    #[test]
    fn no_progress_with_call() {
        // This mainly tests the error debug formatter.
        let input = "
        namespace Main(256);
            col witness a, b, c;
            col witness is_arith;
            a = 2;
            is_arith $ [a, b, c] is [Arith::X, Arith::Y, Arith::Z];
        namespace Arith(256);
            col witness X, Y, Z;
            Z = X + Y;
        ";
        match generate_single_step(input, "Main") {
            Ok(_) => panic!("Expected error"),
            Err(e) => {
                let expected = "\
Main::is_arith $ [ Main::a, Main::b, Main::c ]
     ???              2       ???      ???    
                                              
Main::is_arith        2     Main::b  Main::c  
     ???                      ???      ???    
                                          ";
                assert!(
                    e.contains(expected),
                    "Error did not contain expected substring. Error:\n{e}\nExpected substring:\n{expected}"
                );
            }
        }
    }
}

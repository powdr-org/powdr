use std::collections::HashSet;

use bit_vec::BitVec;
use itertools::Itertools;
use powdr_ast::analyzed::{PolyID, PolynomialType};
use powdr_number::FieldElement;

use crate::witgen::{jit::processor::Processor, machines::MachineParts, FixedData};

use super::{
    processor::ProcessorResult,
    variable::{Cell, Variable},
    witgen_inference::{CanProcessCall, FixedEvaluator, WitgenInference},
};

/// This is a tuning value. It is the maximum nesting depth of branches in the JIT code.
const BLOCK_MACHINE_MAX_BRANCH_DEPTH: usize = 6;

/// A processor for generating JIT code for a block machine.
pub struct BlockMachineProcessor<'a, T: FieldElement> {
    fixed_data: &'a FixedData<'a, T>,
    machine_parts: MachineParts<'a, T>,
    block_size: usize,
    latch_row: usize,
}

impl<'a, T: FieldElement> BlockMachineProcessor<'a, T> {
    pub fn new(
        fixed_data: &'a FixedData<'a, T>,
        machine_parts: MachineParts<'a, T>,
        block_size: usize,
        latch_row: usize,
    ) -> Self {
        BlockMachineProcessor {
            fixed_data,
            machine_parts,
            block_size,
            latch_row,
        }
    }

    /// Generates the JIT code for a given combination of connection and known arguments.
    /// Fails if it cannot solve for the outputs, or if any sub-machine calls cannot be completed.
    pub fn generate_code(
        &self,
        can_process: impl CanProcessCall<T>,
        identity_id: u64,
        known_args: &BitVec,
    ) -> Result<ProcessorResult<T>, String> {
        let connection = self.machine_parts.connections[&identity_id];
        assert_eq!(connection.right.expressions.len(), known_args.len());

        // Set up WitgenInference with known arguments.
        let known_variables = known_args
            .iter()
            .enumerate()
            .filter_map(|(i, is_input)| is_input.then_some(Variable::Param(i)))
            .collect::<HashSet<_>>();
        let mut witgen = WitgenInference::new(self.fixed_data, self, known_variables, []);

        // In the latch row, set the RHS selector to 1.
        let selector = &connection.right.selector;
        witgen.assign_constant(selector, self.latch_row as i32, T::one());

        // Set all other selectors to 0 in the latch row.
        for other_connection in self.machine_parts.connections.values() {
            let other_selector = &other_connection.right.selector;
            if other_selector != selector {
                witgen.assign_constant(other_selector, self.latch_row as i32, T::zero());
            }
        }

        // For each argument, connect the expression on the RHS with the formal parameter.
        for (index, expr) in connection.right.expressions.iter().enumerate() {
            witgen.assign_variable(expr, self.latch_row as i32, Variable::Param(index));
        }

        // Compute the identity-row-pairs we consider.
        let have_next_ref = self
            .machine_parts
            .identities
            .iter()
            .any(|id| id.contains_next_ref());
        let start_row = if !have_next_ref {
            // No identity contains a next reference - we do not need to consider row -1,
            // and the block has to be rectangular-shaped.
            0
        } else {
            // A machine that might have a non-rectangular shape.
            // We iterate over all rows of the block +/- one row.
            -1
        };
        let identities = (start_row..self.block_size as i32).flat_map(move |row| {
            self.machine_parts.identities.iter().filter_map(move |&id| {
                // Filter out identities with next references on the last row.
                if row as usize == self.block_size - 1 && id.contains_next_ref() {
                    None
                } else {
                    Some((id, row))
                }
            })
        });

        let requested_known = known_args
            .iter()
            .enumerate()
            .filter_map(|(i, is_input)| (!is_input).then_some(Variable::Param(i)));
        Processor::new(
            self.fixed_data,
            self,
            identities,
            requested_known,
            BLOCK_MACHINE_MAX_BRANCH_DEPTH,
        )
        .with_block_shape_check()
        .with_block_size(self.block_size)
        .with_requested_range_constraints((0..known_args.len()).map(Variable::Param))
        .generate_code(can_process, witgen)
        .map_err(|e| {
            let err_str = e.to_string_with_variable_formatter(|var| match var {
                Variable::Param(i) => format!("{} (connection param)", &connection.right.expressions[*i]),
                _ => var.to_string(),
            });
            log::trace!("\nCode generation failed for connection:\n  {connection}");
            let known_args_str = known_args
                .iter()
                .enumerate()
                .filter_map(|(i, b)| b.then_some(connection.right.expressions[i].to_string()))
                .join("\n  ");
            log::trace!("Known arguments:\n  {known_args_str}");
            log::trace!("Error:\n  {err_str}");
            let shortened_error = err_str
                .lines()
                .take(10)
                .format("\n  ");
            format!("Code generation failed: {shortened_error}\nRun with RUST_LOG=trace to see the code generated so far.")
        })
    }
}

impl<T: FieldElement> FixedEvaluator<T> for &BlockMachineProcessor<'_, T> {
    fn evaluate(&self, fixed_cell: &Cell) -> Option<T> {
        let poly_id = PolyID {
            id: fixed_cell.id,
            ptype: PolynomialType::Constant,
        };
        let values = self.fixed_data.fixed_cols[&poly_id].values_max_size();

        // By assumption of the block machine, all fixed columns are cyclic with a period of <block_size>.
        // An exception might be the first and last row.
        assert!(fixed_cell.row_offset >= -1);
        assert!(self.block_size >= 1);
        // The row is guaranteed to be at least 1.
        let row = (2 * self.block_size as i32 + fixed_cell.row_offset) as usize;

        assert!(values.len() >= self.block_size * 4);

        // Fixed columns are assumed to be cyclic, except in the first and last row.
        // The code above should ensure that we never access the first or last row.
        assert!(row > 0);
        assert!(row < values.len() - 1);

        Some(values[row])
    }
}

#[cfg(test)]
mod test {
    use std::fs::read_to_string;

    use pretty_assertions::assert_eq;
    use test_log::test;

    use powdr_number::GoldilocksField;

    use crate::witgen::{
        data_structures::mutable_state::MutableState,
        global_constraints,
        jit::{effect::format_code, test_util::read_pil},
        machines::{machine_extractor::MachineExtractor, KnownMachine, Machine},
        range_constraints::RangeConstraint,
        FixedData,
    };

    use super::*;

    fn generate_for_block_machine(
        input_pil: &str,
        machine_name: &str,
        num_inputs: usize,
        num_outputs: usize,
    ) -> Result<ProcessorResult<GoldilocksField>, String> {
        let (analyzed, fixed_col_vals) = read_pil(input_pil);

        let fixed_data = FixedData::new(&analyzed, &fixed_col_vals, &[], Default::default(), 0);
        let fixed_data = global_constraints::set_global_constraints(fixed_data);
        let machines = MachineExtractor::new(&fixed_data).split_out_machines();
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
        let processor = BlockMachineProcessor {
            fixed_data: &fixed_data,
            machine_parts: machine_parts.clone(),
            block_size,
            latch_row,
        };

        let mutable_state = MutableState::new(machines.into_iter(), &|_| {
            Err("Query not implemented".to_string())
        });

        let known_values = BitVec::from_iter(
            (0..num_inputs)
                .map(|_| true)
                .chain((0..num_outputs).map(|_| false)),
        );

        processor.generate_code(&mutable_state, connection_id, &known_values)
    }

    #[test]
    fn add() {
        let input = "
        namespace Main(256);
            col witness a, b, c;
            [a, b, c] is Add.sel $ [Add.a, Add.b, Add.c]; 
        namespace Add(256);
            col witness sel, a, b, c;
            c = a + b;
        ";
        let code = generate_for_block_machine(input, "Add", 2, 1).unwrap().code;
        assert_eq!(
            format_code(&code),
            "Add::sel[0] = 1;
Add::a[0] = params[0];
Add::b[0] = params[1];
Add::c[0] = (Add::a[0] + Add::b[0]);
params[2] = Add::c[0];"
        );
    }

    #[test]
    fn unconstrained_output() {
        let input = "
        namespace Main(256);
            col witness a, b, c;
            [a, b, c] is Unconstrained.sel $ [Unconstrained.a, Unconstrained.b, Unconstrained.c]; 
        namespace Unconstrained(256);
            col witness sel, a, b, c;
            a + b = 0;
        ";
        let code = generate_for_block_machine(input, "Unconstrained", 2, 1)
            .unwrap()
            .code;
        assert_eq!(
            format_code(&code),
            "Unconstrained::sel[0] = 1;
Unconstrained::a[0] = params[0];
Unconstrained::b[0] = params[1];
params[2] = 0;
Unconstrained::c[0] = 0;"
        );
    }

    #[test]
    #[should_panic = "Column NotStackable::a is not stackable in a 1-row block"]
    fn not_stackable() {
        let input = "
        namespace Main(256);
            col witness a, b, c;
            [a] is NotStackable.sel $ [NotStackable.a]; 
        namespace NotStackable(256);
            col witness sel, a;
            a = a';
        ";
        generate_for_block_machine(input, "NotStackable", 1, 0).unwrap();
    }

    #[test]
    fn binary() {
        let input = read_to_string("../test_data/pil/binary.pil").unwrap();
        let result = generate_for_block_machine(&input, "main_binary", 3, 1).unwrap();
        let [op_rc, a_rc, b_rc, c_rc] = &result.range_constraints.try_into().unwrap();
        assert_eq!(op_rc, &RangeConstraint::from_range(0.into(), 2.into()));
        assert_eq!(a_rc, &RangeConstraint::from_mask(0xffffffffu64));
        assert_eq!(b_rc, &RangeConstraint::from_mask(0xffffffffu64));
        assert_eq!(c_rc, &RangeConstraint::from_mask(0xffffffffu64));
        assert_eq!(
            format_code(&result.code),
            "main_binary::sel[0][3] = 1;
main_binary::operation_id[3] = params[0];
main_binary::A[3] = params[1];
main_binary::B[3] = params[2];
main_binary::operation_id[2] = main_binary::operation_id[3];
main_binary::operation_id[1] = main_binary::operation_id[2];
main_binary::operation_id[0] = main_binary::operation_id[1];
main_binary::operation_id_next[-1] = main_binary::operation_id[0];
main_binary::operation_id_next[0] = main_binary::operation_id[1];
main_binary::operation_id_next[1] = main_binary::operation_id[2];
main_binary::A_byte[2] = ((main_binary::A[3] & 0xff000000) // 16777216);
main_binary::A[2] = (main_binary::A[3] & 0xffffff);
assert (main_binary::A[3] & 0xffffffff00000000) == 0;
main_binary::A_byte[1] = ((main_binary::A[2] & 0xff0000) // 65536);
main_binary::A[1] = (main_binary::A[2] & 0xffff);
assert (main_binary::A[2] & 0xffffffffff000000) == 0;
main_binary::A_byte[0] = ((main_binary::A[1] & 0xff00) // 256);
main_binary::A[0] = (main_binary::A[1] & 0xff);
assert (main_binary::A[1] & 0xffffffffffff0000) == 0;
main_binary::A_byte[-1] = main_binary::A[0];
main_binary::B_byte[2] = ((main_binary::B[3] & 0xff000000) // 16777216);
main_binary::B[2] = (main_binary::B[3] & 0xffffff);
assert (main_binary::B[3] & 0xffffffff00000000) == 0;
main_binary::B_byte[1] = ((main_binary::B[2] & 0xff0000) // 65536);
main_binary::B[1] = (main_binary::B[2] & 0xffff);
assert (main_binary::B[2] & 0xffffffffff000000) == 0;
main_binary::B_byte[0] = ((main_binary::B[1] & 0xff00) // 256);
main_binary::B[0] = (main_binary::B[1] & 0xff);
assert (main_binary::B[1] & 0xffffffffffff0000) == 0;
main_binary::B_byte[-1] = main_binary::B[0];
call_var(9, -1, 0) = main_binary::operation_id_next[-1];
call_var(9, -1, 1) = main_binary::A_byte[-1];
call_var(9, -1, 2) = main_binary::B_byte[-1];
machine_call(9, [Known(call_var(9, -1, 0)), Known(call_var(9, -1, 1)), Known(call_var(9, -1, 2)), Unknown(call_var(9, -1, 3))]);
main_binary::C_byte[-1] = call_var(9, -1, 3);
main_binary::C[0] = main_binary::C_byte[-1];
call_var(9, 0, 0) = main_binary::operation_id_next[0];
call_var(9, 0, 1) = main_binary::A_byte[0];
call_var(9, 0, 2) = main_binary::B_byte[0];
machine_call(9, [Known(call_var(9, 0, 0)), Known(call_var(9, 0, 1)), Known(call_var(9, 0, 2)), Unknown(call_var(9, 0, 3))]);
main_binary::C_byte[0] = call_var(9, 0, 3);
main_binary::C[1] = (main_binary::C[0] + (main_binary::C_byte[0] * 256));
call_var(9, 1, 0) = main_binary::operation_id_next[1];
call_var(9, 1, 1) = main_binary::A_byte[1];
call_var(9, 1, 2) = main_binary::B_byte[1];
machine_call(9, [Known(call_var(9, 1, 0)), Known(call_var(9, 1, 1)), Known(call_var(9, 1, 2)), Unknown(call_var(9, 1, 3))]);
main_binary::C_byte[1] = call_var(9, 1, 3);
main_binary::C[2] = (main_binary::C[1] + (main_binary::C_byte[1] * 65536));
main_binary::operation_id_next[2] = main_binary::operation_id[3];
call_var(9, 2, 0) = main_binary::operation_id_next[2];
call_var(9, 2, 1) = main_binary::A_byte[2];
call_var(9, 2, 2) = main_binary::B_byte[2];
machine_call(9, [Known(call_var(9, 2, 0)), Known(call_var(9, 2, 1)), Known(call_var(9, 2, 2)), Unknown(call_var(9, 2, 3))]);
main_binary::C_byte[2] = call_var(9, 2, 3);
main_binary::C[3] = (main_binary::C[2] + (main_binary::C_byte[2] * 16777216));
params[3] = main_binary::C[3];"
        )
    }

    #[test]
    fn poseidon() {
        let input = read_to_string("../test_data/pil/poseidon_gl.pil").unwrap();
        generate_for_block_machine(&input, "main_poseidon", 12, 4).unwrap();
    }

    #[test]
    fn bitfield_opid() {
        // The issue with this machine is that if we pass 0 as the operation_id, the machine
        // is fully unconstrained.
        let input = "
        namespace Main(256);
            col witness x, a, b, c;
            [x, a, b, c] is [
                Arith::is_add + 2 * Arith::is_mul, Arith::X, Arith::Y, Arith::Z];
        namespace Arith(256);
            col witness is_add, is_mul, X, Y, Z;
            is_add * (1 - is_add) = 0;
            is_mul * (1 - is_mul) = 0;
            is_add * (X + Y - Z) = 0;
            is_mul * (X * Y - Z) = 0;
        ";
        let code = generate_for_block_machine(input, "Arith", 3, 1);
        assert_eq!(
            format_code(&code.unwrap().code),
            "Arith::is_add[0] = (params[0] & 0x1);
Arith::is_mul[0] = ((params[0] & 0x2) // 2);
assert (params[0] & 0xfffffffffffffffc) == 0;
Arith::X[0] = params[1];
Arith::Y[0] = params[2];
if (Arith::is_add[0] == 1) {
    Arith::Z[0] = (Arith::X[0] + Arith::Y[0]);
    params[3] = Arith::Z[0];
} else {
    if (Arith::is_mul[0] == 1) {
        Arith::Z[0] = (Arith::X[0] * Arith::Y[0]);
        params[3] = Arith::Z[0];
    } else {
        params[3] = 0;
        Arith::Z[0] = 0;
    }
}"
        );
    }
}

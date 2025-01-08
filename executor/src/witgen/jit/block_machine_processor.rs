use std::collections::HashSet;

use bit_vec::BitVec;
use itertools::Itertools;
use powdr_ast::analyzed::AlgebraicReference;
use powdr_number::FieldElement;

use crate::witgen::{jit::processor::Processor, machines::MachineParts, FixedData};

use super::{
    effect::Effect,
    variable::Variable,
    witgen_inference::{CanProcessCall, FixedEvaluator, WitgenInference},
};

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
    pub fn generate_code<CanProcess: CanProcessCall<T> + Clone>(
        &self,
        can_process: CanProcess,
        identity_id: u64,
        known_args: &BitVec,
    ) -> Result<Vec<Effect<T, Variable>>, String> {
        let connection = self.machine_parts.connections[&identity_id];
        assert_eq!(connection.right.expressions.len(), known_args.len());

        // Set up WitgenInference with known arguments.
        let known_variables = known_args
            .iter()
            .enumerate()
            .filter_map(|(i, is_input)| is_input.then_some(Variable::Param(i)))
            .collect::<HashSet<_>>();
        let mut witgen = WitgenInference::new(self.fixed_data, self, known_variables);

        // In the latch row, set the RHS selector to 1.
        witgen.assign_constant(&connection.right.selector, self.latch_row as i32, T::one());

        // For each argument, connect the expression on the RHS with the formal parameter.
        for (index, expr) in connection.right.expressions.iter().enumerate() {
            witgen.assign_variable(expr, self.latch_row as i32, Variable::Param(index));
        }

        let identities = self.row_range().flat_map(move |row| {
            self.machine_parts
                .identities
                .iter()
                .map(move |&id| (id, row))
        });
        let requested_known = known_args
            .iter()
            .enumerate()
            .filter_map(|(i, is_input)| (!is_input).then_some(Variable::Param(i)));
        Processor::new(
            self.fixed_data,
            self,
            identities,
            self.block_size,
            requested_known,
        )
        .generate_code(can_process, witgen)
        .map_err(|e| {
            log::debug!("\nCode generation failed for connection:\n  {connection}");
            let known_args_str = known_args
                .iter()
                .enumerate()
                .filter_map(|(i, b)| b.then_some(connection.right.expressions[i].to_string()))
                .join("\n  ");
            log::debug!("Known arguments:\n  {known_args_str}");
            log::debug!("Error:\n  {e}");
            format!("Code generation failed: {e}\nRun with RUST_LOG=debug to see the code generated so far.")
        })
    }

    fn row_range(&self) -> std::ops::Range<i32> {
        // We iterate over all rows of the block +/- one row, so that we can also solve for non-rectangular blocks.
        -1..(self.block_size + 1) as i32
    }
}

impl<T: FieldElement> FixedEvaluator<T> for &BlockMachineProcessor<'_, T> {
    fn evaluate(&self, var: &AlgebraicReference, row_offset: i32) -> Option<T> {
        assert!(var.is_fixed());
        let values = self.fixed_data.fixed_cols[&var.poly_id].values_max_size();

        // By assumption of the block machine, all fixed columns are cyclic with a period of <block_size>.
        // An exception might be the first and last row.
        assert!(row_offset >= -1);
        assert!(self.block_size >= 1);
        // The current row is guaranteed to be at least 1.
        let current_row = (2 * self.block_size as i32 + row_offset) as usize;
        let row = current_row + var.next as usize;

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

    use test_log::test;

    use powdr_number::GoldilocksField;

    use crate::witgen::{
        data_structures::mutable_state::MutableState,
        global_constraints,
        jit::{
            effect::{format_code, Effect},
            test_util::read_pil,
        },
        machines::{machine_extractor::MachineExtractor, KnownMachine, Machine},
        FixedData,
    };

    use super::*;

    fn generate_for_block_machine(
        input_pil: &str,
        machine_name: &str,
        num_inputs: usize,
        num_outputs: usize,
    ) -> Result<Vec<Effect<GoldilocksField, Variable>>, String> {
        let (analyzed, fixed_col_vals) = read_pil(input_pil);

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
        let code = generate_for_block_machine(input, "Add", 2, 1);
        assert_eq!(
            format_code(&code.unwrap()),
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
        let err_str = generate_for_block_machine(input, "Unconstrained", 2, 1)
            .err()
            .unwrap();
        assert!(err_str
            .contains("Unable to derive algorithm to compute output value \"Unconstrained::c\""));
    }

    #[test]
    #[should_panic = "Block machine shape does not allow stacking"]
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
        let code = generate_for_block_machine(&input, "main_binary", 3, 1).unwrap();
        assert_eq!(
            format_code(&code),
            "main_binary::sel[0][3] = 1;
main_binary::operation_id[3] = params[0];
main_binary::A[3] = params[1];
main_binary::B[3] = params[2];
main_binary::operation_id[2] = main_binary::operation_id[3];
main_binary::A_byte[2] = ((main_binary::A[3] & 4278190080) // 16777216);
main_binary::A[2] = (main_binary::A[3] & 16777215);
assert (main_binary::A[3] & 18446744069414584320) == 0;
main_binary::B_byte[2] = ((main_binary::B[3] & 4278190080) // 16777216);
main_binary::B[2] = (main_binary::B[3] & 16777215);
assert (main_binary::B[3] & 18446744069414584320) == 0;
main_binary::operation_id_next[2] = main_binary::operation_id[3];
machine_call(9, [Known(main_binary::operation_id_next[2]), Known(main_binary::A_byte[2]), Known(main_binary::B_byte[2]), Unknown(ret(9, 2, 3))]);
main_binary::C_byte[2] = ret(9, 2, 3);
main_binary::operation_id[1] = main_binary::operation_id[2];
main_binary::A_byte[1] = ((main_binary::A[2] & 16711680) // 65536);
main_binary::A[1] = (main_binary::A[2] & 65535);
assert (main_binary::A[2] & 18446744073692774400) == 0;
main_binary::B_byte[1] = ((main_binary::B[2] & 16711680) // 65536);
main_binary::B[1] = (main_binary::B[2] & 65535);
assert (main_binary::B[2] & 18446744073692774400) == 0;
main_binary::operation_id_next[1] = main_binary::operation_id[2];
machine_call(9, [Known(main_binary::operation_id_next[1]), Known(main_binary::A_byte[1]), Known(main_binary::B_byte[1]), Unknown(ret(9, 1, 3))]);
main_binary::C_byte[1] = ret(9, 1, 3);
main_binary::operation_id[0] = main_binary::operation_id[1];
main_binary::A_byte[0] = ((main_binary::A[1] & 65280) // 256);
main_binary::A[0] = (main_binary::A[1] & 255);
assert (main_binary::A[1] & 18446744073709486080) == 0;
main_binary::B_byte[0] = ((main_binary::B[1] & 65280) // 256);
main_binary::B[0] = (main_binary::B[1] & 255);
assert (main_binary::B[1] & 18446744073709486080) == 0;
main_binary::operation_id_next[0] = main_binary::operation_id[1];
machine_call(9, [Known(main_binary::operation_id_next[0]), Known(main_binary::A_byte[0]), Known(main_binary::B_byte[0]), Unknown(ret(9, 0, 3))]);
main_binary::C_byte[0] = ret(9, 0, 3);
main_binary::A_byte[-1] = main_binary::A[0];
main_binary::B_byte[-1] = main_binary::B[0];
main_binary::operation_id_next[-1] = main_binary::operation_id[0];
machine_call(9, [Known(main_binary::operation_id_next[-1]), Known(main_binary::A_byte[-1]), Known(main_binary::B_byte[-1]), Unknown(ret(9, -1, 3))]);
main_binary::C_byte[-1] = ret(9, -1, 3);
main_binary::C[0] = main_binary::C_byte[-1];
main_binary::C[1] = (main_binary::C[0] + (main_binary::C_byte[0] * 256));
main_binary::C[2] = (main_binary::C[1] + (main_binary::C_byte[1] * 65536));
main_binary::C[3] = (main_binary::C[2] + (main_binary::C_byte[2] * 16777216));
params[3] = main_binary::C[3];"
        )
    }

    #[test]
    fn poseidon() {
        let input = read_to_string("../test_data/pil/poseidon_gl.pil").unwrap();
        generate_for_block_machine(&input, "main_poseidon", 12, 4).unwrap();
    }
}

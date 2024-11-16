use bit_vec::BitVec;
use itertools::Itertools;
use powdr_number::FieldElement;

use crate::witgen::{
    data_structures::finalizable_data::CompactDataRef,
    jit::witgen_inference::WitgenInference,
    machines::{LookupCell, MachineParts},
    util::try_to_simple_poly,
    EvalError, FixedData, MutableState, QueryCallback,
};

pub struct JitProcessor<'a, T: FieldElement> {
    fixed_data: &'a FixedData<'a, T>,
    parts: MachineParts<'a, T>,
    block_size: usize,
    latch_row: usize,
}

impl<'a, T: FieldElement> JitProcessor<'a, T> {
    pub fn new(
        fixed_data: &'a FixedData<'a, T>,
        parts: MachineParts<'a, T>,
        block_size: usize,
        latch_row: usize,
    ) -> Self {
        JitProcessor {
            fixed_data,
            parts,
            block_size,
            latch_row,
        }
    }

    pub fn can_answer_lookup(&self, identity_id: u64, known_inputs: &BitVec) -> bool {
        // TODO cache the result

        // TODO what if the same column is mentioned multiple times on the RHS of the connection?

        let right = self.parts.connections[&identity_id].right;
        let Some(known_inputs) = known_inputs
            .iter()
            .zip(&right.expressions)
            .filter(|&(known, e)| known)
            .map(|(known, e)| try_to_simple_poly(e))
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        log::debug!(
            "Trying to auto-generate witgen code for known inputs: {}",
            known_inputs.iter().format(", ")
        );

        let known_inputs = known_inputs.into_iter().map(|p| p.poly_id);

        let mut inference = WitgenInference::new(
            self.fixed_data,
            &self.parts,
            self.block_size,
            self.latch_row,
            known_inputs,
            right,
        );
        if inference.run() {
            log::info!("Successfully generated witgen code for some machine.");
            log::trace!("Generated code:\n{}", inference.code());
            true
        } else {
            false
        }
    }

    pub fn process_lookup_direct<'b, 'c, 'd, Q: QueryCallback<T>>(
        &self,
        _mutable_state: &'b mut MutableState<'a, 'b, T, Q>,
        connection_id: u64,
        values: Vec<LookupCell<'c, T>>,
        mut data: CompactDataRef<'d, T>,
    ) -> Result<bool, EvalError<T>> {
        // Transfer inputs.
        let right = self.parts.connections[&connection_id].right;
        for (e, v) in right.expressions.iter().zip(&values) {
            match v {
                LookupCell::Input(&v) => {
                    let col = try_to_simple_poly(e).unwrap();
                    data.set(self.latch_row as i32, col.poly_id.id as u32, v);
                }
                LookupCell::Output(_) => {}
            }
        }

        // Just some code here to avoid "unused" warnings.
        // This code will not be called as long as `can_answer_lookup` returns false.
        data.get(self.latch_row as i32, 0);

        unimplemented!();
    }
}

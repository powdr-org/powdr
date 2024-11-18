use std::{
    collections::HashMap,
    ffi::c_void,
    sync::{Arc, RwLock},
};

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
    witgen_functions: RwLock<HashMap<(u64, BitVec), WitgenFunction>>,
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
            witgen_functions: RwLock::new(HashMap::new()),
        }
    }

    pub fn can_answer_lookup(&self, identity_id: u64, known_inputs: &BitVec) -> bool {
        if self
            .witgen_functions
            .read()
            .unwrap()
            .contains_key(&(identity_id, known_inputs.clone()))
        {
            return true;
        }

        // TODO what if the same column is mentioned multiple times on the RHS of the connection?

        let right = self.parts.connections[&identity_id].right;
        let Some(known_inputs_cols) = known_inputs
            .iter()
            .zip(&right.expressions)
            .filter(|(known, _)| *known)
            .map(|(_, e)| try_to_simple_poly(e))
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        log::debug!(
            "Trying to auto-generate witgen code for known inputs: {}",
            known_inputs_cols.iter().format(", ")
        );

        let known_inputs_cols = known_inputs_cols.into_iter().map(|p| p.poly_id);

        let mut inference = WitgenInference::new(
            self.fixed_data,
            &self.parts,
            self.block_size,
            self.latch_row,
            known_inputs_cols,
            right,
        );
        if !inference.run() {
            return false;
        }
        log::info!("Successfully generated witgen code for some machine.");
        let code = inference.code("witgen");
        log::trace!("Generated code:\n{code}");

        let lib_path = powdr_jit_compiler::compiler::call_cargo(&code)
            .map_err(|e| {
                log::error!("Failed to compile generated code: {}", e);
                false
            })
            .unwrap();

        let library = Arc::new(unsafe { libloading::Library::new(&lib_path.path).unwrap() });
        // TODO what happen if there is a conflict in function names? Should we
        // encode the ID and the known inputs?
        let witgen_fun =
            unsafe { library.get::<extern "C" fn(*mut c_void, u64, u64)>(b"witgen") }.unwrap();

        self.witgen_functions.write().unwrap().insert(
            (identity_id, known_inputs.clone()),
            WitgenFunction {
                library: library.clone(),
                witgen_function: *witgen_fun,
            },
        );
        true
    }

    pub fn process_lookup_direct<'b, 'c, 'd, Q: QueryCallback<T>>(
        &self,
        _mutable_state: &'b mut MutableState<'a, 'b, T, Q>,
        connection_id: u64,
        values: Vec<LookupCell<'c, T>>,
        // TODO maybe just a `*mut T` plus first_col would be best?
        mut data: CompactDataRef<'d, T>,
    ) -> Result<bool, EvalError<T>> {
        // Transfer inputs.
        let right = self.parts.connections[&connection_id].right;
        let mut known_inputs = BitVec::new();
        for (e, v) in right.expressions.iter().zip(&values) {
            match v {
                LookupCell::Input(&v) => {
                    let col = try_to_simple_poly(e).unwrap();
                    data.set(self.latch_row as i32, col.poly_id.id as u32, v);
                    known_inputs.push(true);
                }
                LookupCell::Output(_) => {
                    // TODO
                    known_inputs.push(false);
                }
            }
        }

        self.witgen_functions.read().unwrap()[&(connection_id, known_inputs)].call(&mut data);

        Ok(true)
    }
}

struct WitgenFunction {
    #[allow(dead_code)]
    library: Arc<libloading::Library>,
    witgen_function: extern "C" fn(*mut c_void, u64, u64),
}

impl WitgenFunction {
    fn call<T: FieldElement>(&self, data: &mut CompactDataRef<T>) {
        let (slice, row_offset) = data.direct_slice();
        let data_c_ptr = slice.as_mut_ptr() as *mut c_void;
        let len = slice.len() as u64;
        (self.witgen_function)(data_c_ptr, len, row_offset as u64);
    }
}

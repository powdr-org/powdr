use std::collections::BTreeMap;

use itertools::Itertools;
use powdr_ast::analyzed::{
    expression_evaluator::OwnedTerminalValues, AlgebraicExpression, AlgebraicReferenceThin,
    Analyzed,
};
use powdr_backend_utils::{machine_fixed_columns, machine_witness_columns};
use powdr_executor::constant_evaluator::VariablySizedColumn;
use powdr_executor_utils::WitgenCallback;
use powdr_number::{DegreeType, FieldElement};

/// A collection of columns with self-contained constraints.
pub struct Machine<'a, F> {
    pub machine_name: String,
    pub size: usize,
    pub values: OwnedTerminalValues<F>,
    pub pil: &'a Analyzed<F>,
    pub intermediate_definitions: BTreeMap<AlgebraicReferenceThin, AlgebraicExpression<F>>,
}

impl<'a, F: FieldElement> Machine<'a, F> {
    /// Creates a new machine from a witness, fixed columns, and a PIL - if it is not empty.
    pub fn try_new(
        machine_name: String,
        witness: &'a [(String, Vec<F>)],
        fixed: &'a [(String, VariablySizedColumn<F>)],
        pil: &'a Analyzed<F>,
        witgen_callback: &WitgenCallback<F>,
        challenges: &BTreeMap<u64, F>,
    ) -> Option<Self> {
        let mut witness = machine_witness_columns(witness, pil, &machine_name);
        let size = witness
            .iter()
            .map(|(_, v)| v.len())
            .unique()
            .exactly_one()
            .unwrap();

        if size == 0 {
            // Empty machines are removed always valid.
            return None;
        }

        for stage in 1..pil.stage_count() {
            log::debug!("Generating stage-{stage} witness for machine {machine_name}");
            witness =
                witgen_callback.next_stage_witness(pil, &witness, challenges.clone(), stage as u8);
        }

        let fixed = machine_fixed_columns(fixed, pil);
        let fixed = fixed.get(&(size as DegreeType)).unwrap();
        let fixed = fixed
            .iter()
            // TODO: Avoid clone?
            .map(|(name, col)| (name.clone(), col.to_vec()))
            .collect::<Vec<_>>();

        let intermediate_definitions = pil.intermediate_definitions();

        // TODO: Supports publics.
        let values =
            OwnedTerminalValues::new(pil, witness, fixed).with_challenges(challenges.clone());

        Some(Self {
            machine_name,
            size,
            values,
            pil,
            intermediate_definitions,
        })
    }
}

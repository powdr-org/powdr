use powdr_ast::analyzed::Analyzed;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

use std::sync::Arc;

use powdr_number::{DegreeType, FieldElement};

/// A callback that computes an updated witness, given:
/// - The PIL for the current machine.
/// - The current witness.
/// - The challenges sampled so far.
pub type WitgenCallbackFn<T> = Arc<
    dyn Fn(&Analyzed<T>, &[(String, Vec<T>)], BTreeMap<u64, T>, u8) -> Vec<(String, Vec<T>)>
        + Send
        + Sync,
>;

#[derive(Clone)]
pub struct WitgenCallback<T>(WitgenCallbackFn<T>);

impl<T: FieldElement> WitgenCallback<T> {
    pub fn new(f: WitgenCallbackFn<T>) -> Self {
        WitgenCallback(f)
    }

    /// Computes the next-stage witness, given the current witness and challenges.
    pub fn next_stage_witness(
        &self,
        pil: &Analyzed<T>,
        current_witness: &[(String, Vec<T>)],
        challenges: BTreeMap<u64, T>,
        stage: u8,
    ) -> Vec<(String, Vec<T>)> {
        (self.0)(pil, current_witness, challenges, stage)
    }
}

#[derive(Serialize, Deserialize)]
pub struct VariablySizedColumn<F> {
    column_by_size: BTreeMap<DegreeType, Vec<F>>,
}

#[derive(Debug)]
pub struct HasMultipleSizesError;

impl<F> VariablySizedColumn<F> {
    /// Create a view where each column has a single size. Fails if any column has multiple sizes.
    pub fn get_uniquely_sized(&self) -> Result<&Vec<F>, HasMultipleSizesError> {
        if self.column_by_size.len() != 1 {
            return Err(HasMultipleSizesError);
        }
        Ok(self.column_by_size.values().next().unwrap())
    }

    /// Returns the set of available sizes.
    pub fn available_sizes(&self) -> BTreeSet<DegreeType> {
        self.column_by_size.keys().cloned().collect()
    }

    /// Clones and returns the column with the given size.
    pub fn get_by_size(&self, size: DegreeType) -> Option<&[F]> {
        self.column_by_size
            .get(&size)
            .map(|column| column.as_slice())
    }
}

impl<F> From<Vec<F>> for VariablySizedColumn<F> {
    fn from(column: Vec<F>) -> Self {
        VariablySizedColumn {
            column_by_size: [(column.len() as DegreeType, column)].into_iter().collect(),
        }
    }
}

impl<F> From<Vec<Vec<F>>> for VariablySizedColumn<F> {
    fn from(columns: Vec<Vec<F>>) -> Self {
        VariablySizedColumn {
            column_by_size: columns
                .into_iter()
                .map(|column| (column.len() as DegreeType, column))
                .collect(),
        }
    }
}

use std::collections::{BTreeMap, BTreeSet};

use fp2::Fp2;
use itertools::Itertools;
use num_traits::{One, Zero};
use powdr_ast::analyzed::{
    expression_evaluator::{ExpressionEvaluator, OwnedTerminalValues},
    Analyzed, Identity, PhantomBusInteractionIdentity,
};
use powdr_executor_utils::VariablySizedColumn;
use powdr_number::{DegreeType, FieldElement};
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

mod fp2;

/// Witness generator for the second-stage bus accumulator.
pub struct BusAccumulatorGenerator<'a, T> {
    pil: &'a Analyzed<T>,
    bus_interactions: Vec<&'a PhantomBusInteractionIdentity<T>>,
    values: OwnedTerminalValues<T>,
    powers_of_alpha: Vec<Fp2<T>>,
    beta: Fp2<T>,
}

impl<'a, T: FieldElement> BusAccumulatorGenerator<'a, T> {
    pub fn new(
        pil: &'a Analyzed<T>,
        witness_columns: &'a [(String, Vec<T>)],
        fixed_columns: &'a [(String, VariablySizedColumn<T>)],
        challenges: BTreeMap<u64, T>,
    ) -> Self {
        let size = witness_columns.iter().next().unwrap().1.len() as DegreeType;

        // The provided PIL might only contain a subset of all fixed columns.
        let fixed_column_names = pil
            .constant_polys_in_source_order()
            .flat_map(|(symbol, _)| symbol.array_elements())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();

        // Select the columns in the current PIL and select the right size.
        let fixed_columns = fixed_columns
            .iter()
            .filter(|(n, _)| fixed_column_names.contains(n))
            .map(|(n, v)| (n.clone(), v.get_by_size(size).unwrap()));

        let bus_interactions = pil
            .identities
            .iter()
            .filter_map(|identity| match identity {
                Identity::PhantomBusInteraction(i) => Some(i),
                _ => None,
            })
            .collect::<Vec<_>>();

        let max_tuple_size = bus_interactions
            .iter()
            .map(|i| i.tuple.0.len())
            .max()
            .unwrap();

        let alpha = Fp2::new(challenges[&1], challenges[&2]);
        let beta = Fp2::new(challenges[&3], challenges[&4]);
        let powers_of_alpha = powers_of_alpha(alpha, max_tuple_size);

        let values = OwnedTerminalValues::new(
            pil,
            witness_columns.to_vec(),
            fixed_columns
                .map(|(name, values)| (name, values.to_vec()))
                .collect(),
        )
        .with_challenges(challenges);

        Self {
            pil,
            bus_interactions,
            values,
            powers_of_alpha,
            beta,
        }
    }

    pub fn generate(&self) -> Vec<(String, Vec<T>)> {
        let accumulators = self
            .bus_interactions
            .par_iter()
            .flat_map(|bus_interaction| self.interaction_columns(bus_interaction))
            .collect::<Vec<_>>();

        self.pil
            .committed_polys_in_source_order()
            .filter(|(symbol, _)| symbol.stage == Some(1))
            .flat_map(|(symbol, _)| symbol.array_elements().map(|(name, _)| name))
            .zip_eq(accumulators)
            .collect()
    }

    fn interaction_columns(
        &self,
        bus_interaction: &PhantomBusInteractionIdentity<T>,
    ) -> Vec<Vec<T>> {
        let intermediate_definitions = self.pil.intermediate_definitions();

        let size = self.values.height();
        let mut folded1 = vec![T::zero(); size];
        let mut folded2 = vec![T::zero(); size];
        let mut acc1 = vec![T::zero(); size];
        let mut acc2 = vec![T::zero(); size];

        for i in 0..size {
            let mut evaluator =
                ExpressionEvaluator::new(self.values.row(i), &intermediate_definitions);
            let current_acc = if i == 0 {
                Fp2::zero()
            } else {
                Fp2::new(acc1[i - 1], acc2[i - 1])
            };
            let multiplicity = evaluator.evaluate(&bus_interaction.multiplicity);

            let tuple = bus_interaction
                .tuple
                .0
                .iter()
                .map(|r| evaluator.evaluate(r))
                .collect::<Vec<_>>();
            let folded = self.beta - self.fingerprint(&tuple);

            let new_acc = match multiplicity.is_zero() {
                true => current_acc,
                false => current_acc + folded.inverse() * multiplicity,
            };

            folded1[i] = folded.0;
            folded2[i] = folded.1;
            acc1[i] = new_acc.0;
            acc2[i] = new_acc.1;
        }

        vec![folded1, folded2, acc1, acc2]
    }

    /// Fingerprints a tuples of field elements, using the pre-computed powers of alpha.
    fn fingerprint(&self, tuple: &[T]) -> Fp2<T> {
        tuple
            .iter()
            .zip_eq(self.powers_of_alpha.iter().take(tuple.len()).rev())
            .map(|(a, b)| (*b) * (*a))
            .sum()
    }
}

/// Given `alpha`, computes [1, alpha, alpha^2, ..., alpha^(n-1)].
fn powers_of_alpha<T: FieldElement>(alpha: Fp2<T>, n: usize) -> Vec<Fp2<T>> {
    (0..n)
        .scan(Fp2::one(), |state, _| {
            let result = *state;
            *state = *state * alpha;
            Some(result)
        })
        .collect::<Vec<_>>()
}

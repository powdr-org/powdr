use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    iter::once,
};

use extension_field::ExtensionField;
use fp2::Fp2;
use fp4::Fp4;
use itertools::Itertools;
use powdr_ast::{
    analyzed::{AlgebraicExpression, Analyzed, Identity, PhantomBusInteractionIdentity},
    parsed::visitor::AllChildren,
};
use powdr_executor_utils::{
    expression_evaluator::{ExpressionEvaluator, OwnedTerminalValues},
    VariablySizedColumn,
};
use powdr_number::{DegreeType, FieldElement, KnownField};
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use super::polynomial_references;

mod extension_field;
mod fp2;
mod fp4;

/// Generates the second-stage columns for the bus accumulator.
pub fn generate_bus_accumulator_columns<'a, T>(
    pil: &'a Analyzed<T>,
    witness_columns: &'a [(String, Vec<T>)],
    fixed_columns: &'a [(String, VariablySizedColumn<T>)],
    challenges: BTreeMap<u64, T>,
) -> Vec<(String, Vec<T>)>
where
    T: FieldElement,
{
    match T::known_field().unwrap() {
        KnownField::GoldilocksField => BusAccumulatorGenerator::<T, Fp2<T>>::new(
            pil,
            witness_columns,
            fixed_columns,
            challenges,
        )
        .generate(),
        KnownField::BabyBearField | KnownField::KoalaBearField | KnownField::Mersenne31Field => {
            BusAccumulatorGenerator::<T, Fp4<T>>::new(
                pil,
                witness_columns,
                fixed_columns,
                challenges,
            )
            .generate()
        }
        KnownField::Bn254Field => unimplemented!(),
    }
}

/// Witness generator for the second-stage bus accumulator.
struct BusAccumulatorGenerator<'a, T, Ext> {
    pil: &'a Analyzed<T>,
    bus_interactions: Vec<&'a PhantomBusInteractionIdentity<T>>,
    values: OwnedTerminalValues<T>,
    powers_of_alpha: Vec<Ext>,
    beta: Ext,
}

impl<'a, T: FieldElement, Ext: ExtensionField<T> + Sync> BusAccumulatorGenerator<'a, T, Ext> {
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
            // Maximum length of the payload + bus ID
            .map(|i| i.payload.0.len() + 1)
            .max()
            .unwrap();

        let alpha = Ext::get_challenge(&challenges, 0);
        let beta = Ext::get_challenge(&challenges, 1);
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
        let second_stage_cols = self
            .pil
            .committed_polys_in_source_order()
            .filter(|(symbol, _)| symbol.stage == Some(1))
            .flat_map(|(symbol, _)| {
                symbol
                    .array_elements()
                    .map(|(name, poly_id)| (poly_id, name))
            })
            .collect::<BTreeMap<_, _>>();
        let intermediate_definitions = self.pil.intermediate_definitions();
        let referenced_with_second_stage_cols = self
            .pil
            .identities
            .iter()
            .filter(|identity| {
                identity.all_children().any(|expr| match expr {
                    AlgebraicExpression::Reference(reference) => {
                        second_stage_cols.contains_key(&reference.poly_id)
                    }
                    _ => false,
                })
            })
            .map(|identity| polynomial_references(identity, &intermediate_definitions))
            .collect::<Vec<_>>();

        for bus_interaction in self.bus_interactions.iter() {
            // TODO: This is broken, this does not identify the bus interaction uniquely.
            let polys = polynomial_references(&bus_interaction.payload, &intermediate_definitions);
            let folded_or_acc = referenced_with_second_stage_cols
                .iter()
                .filter(|referenced_cols| polys.iter().all(|p| referenced_cols.contains(p)))
                .flatten()
                .filter(|col| second_stage_cols.contains_key(col))
                .collect::<BTreeSet<_>>();
            let acc = referenced_with_second_stage_cols
                .iter()
                .filter(|referenced_cols| folded_or_acc.iter().all(|p| referenced_cols.contains(p)))
                .flatten()
                .filter(|col| second_stage_cols.contains_key(col))
                .collect::<BTreeSet<_>>();
            println!(
                "\n\n{}\n  folded: {}\n  acc: {}",
                bus_interaction,
                folded_or_acc
                    .iter()
                    .map(|poly_id| &second_stage_cols[poly_id])
                    .join(", "),
                acc.iter()
                    .map(|poly_id| &second_stage_cols[poly_id])
                    .join(", ")
            );
        }

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
        let mut folded_list = vec![Ext::zero(); size];
        let mut acc_list = vec![Ext::zero(); size];

        for i in 0..size {
            let mut evaluator =
                ExpressionEvaluator::new(self.values.row(i), &intermediate_definitions);
            let current_acc = if i == 0 { Ext::zero() } else { acc_list[i - 1] };
            let multiplicity = evaluator.evaluate(&bus_interaction.multiplicity);

            let tuple = once(evaluator.evaluate(&bus_interaction.bus_id))
                .chain(
                    bus_interaction
                        .payload
                        .0
                        .iter()
                        .map(|r| evaluator.evaluate(r)),
                )
                .collect::<Vec<_>>();
            let folded = self.beta - self.fingerprint(&tuple);

            let new_acc = match multiplicity.is_zero() {
                true => current_acc,
                false => current_acc + folded.inverse() * multiplicity,
            };

            folded_list[i] = folded;
            acc_list[i] = new_acc;
        }

        // Transpose from row-major to column-major & flatten.
        let mut result = vec![Vec::with_capacity(size); Ext::size() * 2];
        for row_index in 0..size {
            for (col_index, x) in folded_list[row_index]
                .to_vec()
                .into_iter()
                .chain(acc_list[row_index].to_vec())
                .enumerate()
            {
                result[col_index].push(x);
            }
        }

        result
    }

    /// Fingerprints a tuples of field elements, using the pre-computed powers of alpha.
    fn fingerprint(&self, tuple: &[T]) -> Ext {
        tuple
            .iter()
            .zip_eq(self.powers_of_alpha.iter().take(tuple.len()))
            .map(|(a, b)| (*b) * (*a))
            .sum()
    }
}

/// Given `alpha`, computes [1, alpha, alpha^2, ..., alpha^(n-1)].
fn powers_of_alpha<T, Ext: ExtensionField<T>>(alpha: Ext, n: usize) -> Vec<Ext> {
    (0..n)
        .scan(Ext::one(), |state, _| {
            let result = *state;
            *state = *state * alpha;
            Some(result)
        })
        .collect::<Vec<_>>()
}

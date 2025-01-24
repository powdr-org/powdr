use std::{cmp::Ordering, collections::BTreeMap, fmt};

use itertools::Itertools;
use powdr_ast::{
    analyzed::{Analyzed, Identity, PhantomBusInteractionIdentity},
    parsed::visitor::Children,
};
use powdr_executor_utils::expression_evaluator::ExpressionEvaluator;
use powdr_number::FieldElement;
use rayon::iter::{IntoParallelIterator, ParallelIterator};

use super::{localize, machine::Machine, unique_referenced_namespaces};

pub struct BusChecker<'a, F> {
    interactions: &'a [BusInteraction<F>],
    machines: &'a BTreeMap<String, Machine<'a, F>>,
}

pub struct Error<F> {
    tuple: Vec<F>,
    sends: BTreeMap<BusInteraction<F>, usize>,
    receives: BTreeMap<BusInteraction<F>, usize>,
}

impl<F: fmt::Display> fmt::Display for Error<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(
            f,
            "Bus interaction {} failed for tuple {}:",
            self.tuple[0],
            self.tuple.iter().skip(1).map(|v| v.to_string()).join(", ")
        )?;
        for (BusInteraction { machine, identity }, count) in &self.sends {
            writeln!(f, "  - sent {count} times",)?;
            writeln!(f, "    by `{identity}`",)?;
            writeln!(f, "    in {machine}",)?;
        }
        for (BusInteraction { machine, identity }, count) in &self.receives {
            writeln!(f, "  - received {count} times",)?;
            writeln!(f, "    by `{identity}`",)?;
            writeln!(f, "    in {machine}",)?;
        }
        Ok(())
    }
}

#[derive(PartialEq, PartialOrd, Eq, Ord, Clone)]
pub struct BusInteraction<F> {
    pub machine: String,
    pub identity: PhantomBusInteractionIdentity<F>,
}

impl<F: FieldElement> BusInteraction<F> {
    /// Extracts all bus interactions from the global PIL.
    pub fn get_all(
        global_pil: &Analyzed<F>,
        machine_to_pil: &BTreeMap<String, Analyzed<F>>,
    ) -> Vec<Self> {
        global_pil
            .identities
            .iter()
            .filter_map(|identity| {
                // TODO: turn other relevant identities into bus interactions
                if let Identity::PhantomBusInteraction(identity) = identity {
                    Some(identity.clone())
                } else {
                    None
                }
            })
            .map(|interaction| {
                // Localize the interaction assuming a single namespace is accessed.
                let machine = unique_referenced_namespaces(&interaction).unwrap();
                let identity = localize(interaction, global_pil, &machine_to_pil[&machine]);
                BusInteraction { machine, identity }
            })
            .collect()
    }
}

impl<'a, F: FieldElement> BusChecker<'a, F> {
    pub fn new(
        interactions: &'a [BusInteraction<F>],
        machines: &'a BTreeMap<String, Machine<'a, F>>,
    ) -> Self {
        Self {
            interactions,
            machines,
        }
    }

    pub fn check(&self) -> Result<(), Vec<Error<F>>> {
        #[derive(Default)]
        struct TupleState<'a, F> {
            sends: BTreeMap<&'a BusInteraction<F>, usize>,
            receives: BTreeMap<&'a BusInteraction<F>, usize>,
        }

        impl<'a, F: Ord> TupleState<'a, F> {
            fn update(&mut self, interaction: &'a BusInteraction<F>, count: i64) {
                let entry = match count.cmp(&0) {
                    Ordering::Equal => {
                        panic!("Performance bug: This case should be handled before!")
                    }
                    Ordering::Greater => self.sends.entry(interaction),
                    Ordering::Less => self.receives.entry(interaction),
                };
                let count = count.unsigned_abs() as usize;
                entry.and_modify(|sends| *sends += count).or_insert(count);
            }
        }

        type BusState<'a, F> = BTreeMap<Vec<F>, TupleState<'a, F>>;

        let bus_state: BusState<F> = self
            .machines
            .into_par_iter()
            .flat_map(|(name, machine)| {
                (0..machine.size).into_par_iter().map(|row_id| {
                    // create an evaluator for this row
                    let mut evaluator = ExpressionEvaluator::new(
                        machine.values.row(row_id),
                        &machine.intermediate_definitions,
                    );

                    // for all interactions of this machine
                    self.interactions
                        .iter()
                        .filter(|bus_interaction| bus_interaction.machine == *name)
                        .filter_map(move |bus_interaction| {
                            let identity = &bus_interaction.identity;

                            let multiplicity = i64::try_from(
                                evaluator
                                    .evaluate(&identity.multiplicity)
                                    .to_signed_integer(),
                            )
                            .unwrap();

                            let tuple = identity
                                .payload
                                .children()
                                .map(|e| evaluator.evaluate(e))
                                .collect();

                            // if the multiplicity is not zero, return the bus interaction
                            (multiplicity != 0).then_some((bus_interaction, tuple, multiplicity))
                        })
                        // for each row, collect the bus interactions into a single state
                        .fold(
                            BusState::default(),
                            |mut state, (bus_interaction, tuple, multiplicity)| {
                                state
                                    .entry(tuple)
                                    .or_default()
                                    .update(bus_interaction, multiplicity);
                                state
                            },
                        )
                })
            })
            // combine all the states into one, in parallel
            .reduce(BusState::default, |mut a, b| {
                for (tuple, TupleState { sends, receives }) in b {
                    let state = a.entry(tuple).or_default();

                    for (bus_interaction, count) in sends {
                        state.update(bus_interaction, count as i64);
                    }

                    for (bus_interaction, count) in receives {
                        state.update(bus_interaction, -(count as i64));
                    }
                }

                a
            });

        let mut errors = vec![];

        for (tuple, TupleState { sends, receives }) in bus_state {
            let send_count = sends.values().sum::<usize>();
            let receive_count = receives.values().sum::<usize>();
            if send_count != receive_count {
                let error = Error {
                    tuple,
                    sends: sends.into_iter().map(|(k, v)| (k.clone(), v)).collect(),
                    receives: receives.into_iter().map(|(k, v)| (k.clone(), v)).collect(),
                };

                log::error!("{}", error);

                errors.push(error);
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }

        Ok(())
    }
}

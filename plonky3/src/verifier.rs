use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::iter::once;
use p3_air::Air;

use itertools::Itertools;
use p3_challenger::{CanObserve, CanSample, FieldChallenger};
use p3_commit::{Pcs as _, PolynomialSpace};
use p3_field::{AbstractExtensionField, AbstractField, Field};
use p3_matrix::dense::RowMajorMatrixView;
use p3_matrix::stack::VerticalPair;
use tracing::instrument;

use crate::circuit_builder::PowdrTable;
use crate::params::{Challenge, Challenger, Commitment, Pcs, ProverData};
use crate::symbolic_builder::{get_log_quotient_degree, SymbolicAirBuilder};
use crate::{
    ConstraintSystem, FieldElementMap, MultiStageAir, Proof, StageOpenedValues, StarkVerifyingKey,
    TableOpenedValues, TableVerifyingKeyCollection, VerifierConstraintFolder,
};
use p3_uni_stark::{Domain, PcsError, StarkGenericConfig, Val};

/// A sub-table to be proven, in the form of an air and values for the public inputs
struct Table<'a, T: FieldElementMap>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    air: PowdrTable<'a, T>,
    preprocessed: Option<&'a TableVerifyingKeyCollection<T::Config>>,
    opened_values: &'a TableOpenedValues<Challenge<T>>,
    public_values_by_stage: &'a [Vec<Val<T::Config>>],
}

impl<'a, T: FieldElementMap> Table<'a, T>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    fn get_log_quotient_degree(&self) -> usize {
        get_log_quotient_degree(
            &self.air,
            &self
                .public_values_by_stage
                .iter()
                .map(|values| values.len())
                .collect::<Vec<_>>(),
        )
    }

    fn natural_domain(&self, pcs: &Pcs<T>) -> Domain<T::Config> {
        let degree = 1 << self.opened_values.log_degree;
        pcs.natural_domain_for_degree(degree)
    }

    fn preprocessed_commit(&self) -> Option<&Commitment<T>> {
        self.preprocessed
            .as_ref()
            .map(|preprocessed| &preprocessed[&(1 << self.opened_values.log_degree)])
    }

    fn quotient_domains(&self, pcs: &Pcs<T>) -> Vec<Domain<T::Config>> {
        let log_quotient_degree = self.get_log_quotient_degree();
        self.natural_domain(pcs)
            .create_disjoint_domain(1 << (self.opened_values.log_degree + log_quotient_degree))
            .split_domains(1 << log_quotient_degree)
    }
}

#[instrument(skip_all)]
pub fn verify2<T: FieldElementMap>(
    verifying_key: Option<&StarkVerifyingKey<T::Config>>,
    split: &BTreeMap<String, ConstraintSystem<T>>,
    challenger: &mut Challenger<T>,
    proof: &Proof<T::Config>,
    public_inputs: &BTreeMap<String, Vec<Vec<T>>>,
) -> Result<(), VerificationError<PcsError<T::Config>>>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    // sanity check that the two maps have the same keys
    itertools::assert_equal(&mut split.keys(), public_inputs.keys());

    let public_inputs = public_inputs
        .iter()
        .map(|(name, values)| {
            (
                name,
                values
                    .iter()
                    .map(|values| values.iter().map(|v| v.into_p3_field()).collect_vec())
                    .collect_vec(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let Proof {
        commitments,
        opened_values,
        opening_proof,
    } = proof;

    // error out if the opened values do not have the same keys as the tables
    if !itertools::equal(&mut split.keys(), opened_values.keys()) {
        return Err(VerificationError::InvalidProofShape);
    }

    let tables: BTreeMap<String, Table<_>> = split
        .values()
        .zip_eq(public_inputs.iter())
        .zip_eq(opened_values.values())
        .map(
            |((constraints, (name, public_values_by_stage)), opened_values)| {
                (
                    (*name).clone(),
                    Table {
                        air: PowdrTable::new(constraints),
                        opened_values,
                        public_values_by_stage,
                        preprocessed: verifying_key
                            .as_ref()
                            .and_then(|vk| vk.preprocessed.get(*name)),
                    },
                )
            },
        )
        .collect();

    let config = T::get_config();

    let pcs = config.pcs();

    for table in tables.values() {
        if let Some(preprocessed_commit) = table.preprocessed_commit() {
            challenger.observe(preprocessed_commit.clone());
        }
    }

    // Observe the instances.
    for table in tables.values() {
        challenger.observe(Val::<T::Config>::from_canonical_usize(
            table.opened_values.log_degree,
        ));
    }
    // TODO: Might be best practice to include other instance data here in the transcript, like some
    // encoding of the AIR. This protects against transcript collisions between distinct instances.
    // Practically speaking though, the only related known attack is from failing to include public
    // values. It's not clear if failing to include other instance data could enable a transcript
    // collision, since most such changes would completely change the set of satisfying witnesses.

    let stage_count = tables
        .values()
        .map(|i| &i.air)
        .map(<_ as MultiStageAir<SymbolicAirBuilder<_>>>::stage_count)
        .max()
        .unwrap();

    let challenge_count_by_stage: Vec<usize> = (0..stage_count)
        .map(|stage_id| {
            tables
                .values()
                .map(|table| {
                    <_ as MultiStageAir<SymbolicAirBuilder<_>>>::stage_challenge_count(
                        &table.air, stage_id,
                    )
                })
                .max()
                .unwrap()
        })
        .collect();

    let challenges_by_stage = commitments
        .traces_by_stage
        .iter()
        .zip_eq((0..stage_count).map(|i| {
            tables
                .values()
                .map(|table| &table.public_values_by_stage[i as usize])
                .collect_vec()
        }))
        .zip_eq(challenge_count_by_stage)
        .map(|((commitment, public_values_by_stage), challenge_count)| {
            challenger.observe(commitment.clone());
            for public_values in &public_values_by_stage {
                challenger.observe_slice(public_values);
            }
            (0..challenge_count)
                .map(|_| challenger.sample())
                .collect_vec()
        })
        .collect_vec();

    let alpha: Challenge<T> = challenger.sample_ext_element();
    challenger.observe(commitments.quotient_chunks.clone());

    let zeta: Challenge<T> = challenger.sample();

    // for preprocessed commitments, we have one optional commitment per table, opened on the trace domain at `zeta` and `zeta_next`
    let preprocessed_domains_points_and_opens: Vec<(_, Vec<(_, _)>)> =
        tables
            .values()
            .flat_map(|table| {
                let trace_domain = table.natural_domain(pcs);

                let zeta_next = trace_domain.next_point(zeta).unwrap();

                table.opened_values.preprocessed.iter().map(
                    move |StageOpenedValues { local, next }| {
                        (
                            // choose the correct preprocessed commitment based on the degree in the proof
                            // this could be optimized by putting the preproccessed commitments in a merkle tree
                            // and have the prover prove that it used commitments matching the lengths of the traces
                            // this way the verifier does not need to have all the preprocessed commitments for all sizes
                            table.preprocessed_commit().expect("a preprocessed commitment was expected because a preprocessed opening was found").clone(),
                            vec![(
                                trace_domain,
                                vec![(zeta, local.clone()), (zeta_next, next.clone())],
                            )],
                        )
                    },
                )
            })
            .collect();

    // for trace commitments, we have one commitment per stage, opened on each trace domain at `zeta` and `zeta_next`
    let trace_domains_points_and_opens_by_stage: Vec<(_, Vec<(_, _)>)> = proof
        .commitments
        .traces_by_stage
        .iter()
        .zip_eq((0..stage_count as usize).map(|i| {
            tables
                .values()
                .map(|table| &table.opened_values.traces_by_stage[i])
                .collect_vec()
        }))
        .map(|(commit, openings)| {
            (
                commit.clone(),
                tables
                    .values()
                    .zip_eq(openings)
                    .map(|(table, StageOpenedValues { local, next })| {
                        let trace_domain = table.natural_domain(pcs);
                        let zeta_next = trace_domain.next_point(zeta).unwrap();
                        (
                            trace_domain,
                            vec![(zeta, local.clone()), (zeta_next, next.clone())],
                        )
                    })
                    .collect_vec(),
            )
        })
        .collect();

    // for quotient commitments, we have a single commitment, opened on each quotient domain at many points
    let quotient_chunks_domain_point_and_opens: (_, Vec<(_, _)>) = (
        proof.commitments.quotient_chunks.clone(),
        tables
            .values()
            .flat_map(|table| {
                let quotient_domains = table.quotient_domains(pcs);
                quotient_domains
                    .into_iter()
                    .zip_eq(table.opened_values.quotient_chunks.iter())
                    .map(|(domain, chunk)| (domain, vec![(zeta, chunk.clone())]))
            })
            .collect_vec(),
    );

    let verify_input = preprocessed_domains_points_and_opens
        .into_iter()
        .chain(trace_domains_points_and_opens_by_stage)
        .chain(once(quotient_chunks_domain_point_and_opens))
        .collect();

    pcs.verify(verify_input, opening_proof, challenger)
        .map_err(VerificationError::InvalidOpeningArgument)?;

    // Verify the constraint evaluations.
    for table in tables.values() {
        // Verify the shape of the opening arguments matches the expected values.
        verify_opening_shape(table)?;
        // Verify the constraint evaluation.
        let zps = table
            .quotient_domains(pcs)
            .iter()
            .enumerate()
            .map(|(i, domain)| {
                table
                    .quotient_domains(pcs)
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, other_domain)| {
                        other_domain.zp_at_point(zeta)
                            * other_domain.zp_at_point(domain.first_point()).inverse()
                    })
                    .product::<Challenge<T>>()
            })
            .collect_vec();

        let quotient = table
            .opened_values
            .quotient_chunks
            .iter()
            .enumerate()
            .map(|(ch_i, ch)| {
                ch.iter()
                    .enumerate()
                    .map(|(e_i, &c)| zps[ch_i] * Challenge::<T>::monomial(e_i) * c)
                    .sum()
            })
            .sum();

        let sels = table.natural_domain(pcs).selectors_at_point(zeta);

        let empty_vec = vec![];

        let preprocessed = if let Some(preprocessed) = table.opened_values.preprocessed.as_ref() {
            VerticalPair::new(
                RowMajorMatrixView::new_row(&preprocessed.local),
                RowMajorMatrixView::new_row(&preprocessed.next),
            )
        } else {
            VerticalPair::new(
                RowMajorMatrixView::new(&empty_vec, 0),
                RowMajorMatrixView::new(&empty_vec, 0),
            )
        };

        let traces_by_stage = table
            .opened_values
            .traces_by_stage
            .iter()
            .map(|trace| {
                VerticalPair::new(
                    RowMajorMatrixView::new_row(&trace.local),
                    RowMajorMatrixView::new_row(&trace.next),
                )
            })
            .collect::<Vec<VerticalPair<_, _>>>();

        let mut folder: VerifierConstraintFolder<'_, T::Config> = VerifierConstraintFolder {
            challenges: &challenges_by_stage,
            preprocessed,
            traces_by_stage,
            public_values_by_stage: table.public_values_by_stage,
            is_first_row: sels.is_first_row,
            is_last_row: sels.is_last_row,
            is_transition: sels.is_transition,
            alpha,
            accumulator: Challenge::<T>::zero(),
        };
        table.air.eval(&mut folder);
        let folded_constraints = folder.accumulator;

        // Finally, check that
        //     folded_constraints(zeta) / Z_H(zeta) = quotient(zeta)
        if folded_constraints * sels.inv_zeroifier != quotient {
            return Err(VerificationError::OodEvaluationMismatch);
        }
    }

    Ok(())
}

#[instrument(skip_all)]
pub fn verify<T: FieldElementMap>(
    verifying_key: Option<&StarkVerifyingKey<T::Config>>,
    split: &BTreeMap<&String, &ConstraintSystem<T>>,
    challenger: &mut Challenger<T>,
    proof: &Proof<T::Config>,
    public_inputs: BTreeMap<String, Vec<Vec<T>>>,
) -> Result<(), VerificationError<PcsError<T::Config>>>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    let public_inputs = public_inputs
        .into_iter()
        .map(|(name, values)| {
            (
                name,
                values
                    .into_iter()
                    .map(|values| values.into_iter().map(|v| v.into_p3_field()).collect_vec())
                    .collect_vec(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let Proof {
        commitments,
        opened_values,
        opening_proof,
    } = proof;

    // sanity check that the two maps have the same keys
    itertools::assert_equal(split.keys().cloned(), public_inputs.keys());

    // error out if the opened values do not have the same keys as the tables
    if !itertools::equal(split.keys().cloned(), opened_values.keys()) {
        return Err(VerificationError::InvalidProofShape);
    }

    let tables: BTreeMap<&String, Table<_>> = split
        .values()
        .zip_eq(public_inputs.iter())
        .zip_eq(opened_values.values())
        .map(
            |((constraints, (name, public_values_by_stage)), opened_values)| {
                (
                    name,
                    Table {
                        air: PowdrTable::new(constraints),
                        opened_values,
                        public_values_by_stage,
                        preprocessed: verifying_key
                            .as_ref()
                            .and_then(|vk| vk.preprocessed.get(name)),
                    },
                )
            },
        )
        .collect();

    let config = T::get_config();

    let pcs = config.pcs();

    // TODO: Instead of hashing each commit separately, we could hash a summary of all the commitments,
    // like a hash that is precomputed at setup phase.
    for table in tables.values() {
        if let Some(preprocessed_commit) = table.preprocessed_commit() {
            challenger.observe(preprocessed_commit.clone());
        }
    }

    // Observe the instances.
    for table in tables.values() {
        challenger.observe(Val::<T::Config>::from_canonical_usize(
            table.opened_values.log_degree,
        ));
    }
    // TODO: Might be best practice to include other instance data here in the transcript, like some
    // encoding of the AIR. This protects against transcript collisions between distinct instances.
    // Practically speaking though, the only related known attack is from failing to include public
    // values. It's not clear if failing to include other instance data could enable a transcript
    // collision, since most such changes would completely change the set of satisfying witnesses.

    let stage_count = tables
        .values()
        .map(|i| &i.air)
        .map(<_ as MultiStageAir<SymbolicAirBuilder<_>>>::stage_count)
        .max()
        .unwrap();

    let challenge_count_by_stage: Vec<usize> = (0..stage_count)
        .map(|stage_id| {
            tables
                .values()
                .map(|table| {
                    <_ as MultiStageAir<SymbolicAirBuilder<_>>>::stage_challenge_count(
                        &table.air, stage_id,
                    )
                })
                .max()
                .unwrap()
        })
        .collect();

    let challenges_by_stage = commitments
        .traces_by_stage
        .iter()
        .zip_eq((0..stage_count).map(|i| {
            tables
                .values()
                .map(|table| &table.public_values_by_stage[i as usize])
                .collect_vec()
        }))
        .zip_eq(challenge_count_by_stage)
        .map(|((commitment, public_values_by_stage), challenge_count)| {
            challenger.observe(commitment.clone());
            for public_values in &public_values_by_stage {
                challenger.observe_slice(public_values);
            }
            (0..challenge_count)
                .map(|_| challenger.sample())
                .collect_vec()
        })
        .collect_vec();

    let alpha: Challenge<T> = challenger.sample_ext_element();
    challenger.observe(commitments.quotient_chunks.clone());

    let zeta: Challenge<T> = challenger.sample();

    // for preprocessed commitments, we have one optional commitment per table, opened on the trace domain at `zeta` and `zeta_next`
    let preprocessed_domains_points_and_opens: Vec<(_, Vec<(_, _)>)> =
        tables
            .values()
            .flat_map(|table| {
                let trace_domain = table.natural_domain(pcs);

                let zeta_next = trace_domain.next_point(zeta).unwrap();

                table.opened_values.preprocessed.iter().map(
                    move |StageOpenedValues { local, next }| {
                        (
                            // choose the correct preprocessed commitment based on the degree in the proof
                            // this could be optimized by putting the preprocessed commitments in a merkle tree
                            // and have the prover prove that it used commitments matching the lengths of the traces
                            // this way the verifier does not need to have all the preprocessed commitments for all sizes
                            table.preprocessed_commit().expect("a preprocessed commitment was expected because a preprocessed opening was found").clone(),
                            vec![(
                                trace_domain,
                                vec![(zeta, local.clone()), (zeta_next, next.clone())],
                            )],
                        )
                    },
                )
            })
            .collect();

    // for trace commitments, we have one commitment per stage, opened on each trace domain at `zeta` and `zeta_next`
    let trace_domains_points_and_opens_by_stage: Vec<(_, Vec<(_, _)>)> = proof
        .commitments
        .traces_by_stage
        .iter()
        .zip_eq((0..stage_count as usize).map(|i| {
            tables
                .values()
                .map(|table| &table.opened_values.traces_by_stage[i])
                .collect_vec()
        }))
        .map(|(commit, openings)| {
            (
                commit.clone(),
                tables
                    .values()
                    .zip_eq(openings)
                    .map(|(table, StageOpenedValues { local, next })| {
                        let trace_domain = table.natural_domain(pcs);
                        let zeta_next = trace_domain.next_point(zeta).unwrap();
                        (
                            trace_domain,
                            vec![(zeta, local.clone()), (zeta_next, next.clone())],
                        )
                    })
                    .collect_vec(),
            )
        })
        .collect();

    // for quotient commitments, we have a single commitment, opened on each quotient domain at many points
    let quotient_chunks_domain_point_and_opens: (_, Vec<(_, _)>) = (
        proof.commitments.quotient_chunks.clone(),
        tables
            .values()
            .flat_map(|table| {
                let quotient_domains = table.quotient_domains(pcs);
                quotient_domains
                    .into_iter()
                    .zip_eq(table.opened_values.quotient_chunks.iter())
                    .map(|(domain, chunk)| (domain, vec![(zeta, chunk.clone())]))
            })
            .collect_vec(),
    );

    let verify_input = preprocessed_domains_points_and_opens
        .into_iter()
        .chain(trace_domains_points_and_opens_by_stage)
        .chain(once(quotient_chunks_domain_point_and_opens))
        .collect();

    pcs.verify(verify_input, opening_proof, challenger)
        .map_err(VerificationError::InvalidOpeningArgument)?;

    // Verify the constraint evaluations.
    for table in tables.values() {
        // Verify the shape of the opening arguments matches the expected values.
        verify_opening_shape(table)?;
        // Verify the constraint evaluation.
        let zps = table
            .quotient_domains(pcs)
            .iter()
            .enumerate()
            .map(|(i, domain)| {
                table
                    .quotient_domains(pcs)
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, other_domain)| {
                        other_domain.zp_at_point(zeta)
                            * other_domain.zp_at_point(domain.first_point()).inverse()
                    })
                    .product::<Challenge<T>>()
            })
            .collect_vec();

        let quotient = table
            .opened_values
            .quotient_chunks
            .iter()
            .enumerate()
            .map(|(ch_i, ch)| {
                ch.iter()
                    .enumerate()
                    .map(|(e_i, &c)| zps[ch_i] * Challenge::<T>::monomial(e_i) * c)
                    .sum()
            })
            .sum();

        let sels = table.natural_domain(pcs).selectors_at_point(zeta);

        let empty_vec = vec![];

        let preprocessed = if let Some(preprocessed) = table.opened_values.preprocessed.as_ref() {
            VerticalPair::new(
                RowMajorMatrixView::new_row(&preprocessed.local),
                RowMajorMatrixView::new_row(&preprocessed.next),
            )
        } else {
            VerticalPair::new(
                RowMajorMatrixView::new(&empty_vec, 0),
                RowMajorMatrixView::new(&empty_vec, 0),
            )
        };

        let traces_by_stage = table
            .opened_values
            .traces_by_stage
            .iter()
            .map(|trace| {
                VerticalPair::new(
                    RowMajorMatrixView::new_row(&trace.local),
                    RowMajorMatrixView::new_row(&trace.next),
                )
            })
            .collect::<Vec<VerticalPair<_, _>>>();

        let mut folder: VerifierConstraintFolder<'_, T::Config> = VerifierConstraintFolder {
            challenges: &challenges_by_stage,
            preprocessed,
            traces_by_stage,
            public_values_by_stage: table.public_values_by_stage,
            is_first_row: sels.is_first_row,
            is_last_row: sels.is_last_row,
            is_transition: sels.is_transition,
            alpha,
            accumulator: Challenge::<T>::zero(),
        };
        table.air.eval(&mut folder);
        let folded_constraints = folder.accumulator;

        // Finally, check that
        //     folded_constraints(zeta) / Z_H(zeta) = quotient(zeta)
        if folded_constraints * sels.inv_zeroifier != quotient {
            return Err(VerificationError::OodEvaluationMismatch);
        }
    }

    Ok(())
}

fn verify_opening_shape<T: FieldElementMap>(
    table: &Table<'_, T>,
) -> Result<(), VerificationError<PcsError<T::Config>>>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    let log_quotient_degree = get_log_quotient_degree::<Val<T::Config>, _>(
        &table.air,
        &table
            .public_values_by_stage
            .iter()
            .map(|values| values.len())
            .collect::<Vec<_>>(),
    );
    let quotient_degree = 1 << log_quotient_degree;
    let stage_count = <_ as MultiStageAir<SymbolicAirBuilder<_>>>::stage_count(&table.air);
    let challenge_counts: Vec<usize> = (0..stage_count)
        .map(|i| <_ as MultiStageAir<SymbolicAirBuilder<_>>>::stage_challenge_count(&table.air, i))
        .collect();

    let air_widths = (0..stage_count)
        .map(|stage| {
            <_ as MultiStageAir<SymbolicAirBuilder<Val<T::Config>>>>::stage_trace_width(
                &table.air, stage,
            )
        })
        .collect::<Vec<usize>>();
    let air_fixed_width =
        <_ as MultiStageAir<SymbolicAirBuilder<Val<T::Config>>>>::preprocessed_width(&table.air);
    let res = table
        .opened_values
        .preprocessed
        .as_ref()
        .map(|StageOpenedValues { local, next }| {
            local.len() == air_fixed_width && next.len() == air_fixed_width
        })
        .unwrap_or(true)
        && table
            .opened_values
            .traces_by_stage
            .iter()
            .zip_eq(&air_widths)
            .all(|(StageOpenedValues { local, next }, air_width)| {
                local.len() == *air_width && next.len() == *air_width
            })
        && table.opened_values.quotient_chunks.len() == quotient_degree
        && table
            .opened_values
            .quotient_chunks
            .iter()
            .all(|qc| qc.len() == <Challenge<T> as AbstractExtensionField<Val<T::Config>>>::D)
        && table.public_values_by_stage.len() as u8 == stage_count
        && challenge_counts.len() as u8 == stage_count;

    res.then_some(())
        .ok_or(VerificationError::InvalidProofShape)
}

#[derive(Debug)]
pub enum VerificationError<PcsErr> {
    InvalidProofShape,
    /// An error occurred while verifying the claimed openings.
    InvalidOpeningArgument(PcsErr),
    /// Out-of-domain evaluation mismatch, i.e. `constraints(zeta)` did not match
    /// `quotient(zeta) Z_H(zeta)`.
    OodEvaluationMismatch,
}

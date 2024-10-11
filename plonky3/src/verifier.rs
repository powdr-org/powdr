use alloc::vec;
use alloc::vec::Vec;
use p3_air::Air;
use std::collections::BTreeMap;
use std::iter::once;

use itertools::{izip, Itertools};
use p3_challenger::{CanObserve, CanSample, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{AbstractExtensionField, AbstractField, Field};
use p3_matrix::dense::RowMajorMatrixView;
use p3_matrix::stack::VerticalPair;
use tracing::instrument;

use crate::circuit_builder::{PowdrCircuit, PowdrTable};
use crate::params::{Challenge, Challenger, Commitment, Plonky3Field, ProverData};
use crate::symbolic_builder::{get_log_quotient_degree, SymbolicAirBuilder};
use crate::{
    FieldElementMap, MultiStageAir, Proof, StageOpenedValues, StarkVerifyingKey, TableOpenedValues,
    VerifierConstraintFolder,
};
use p3_uni_stark::{PcsError, StarkGenericConfig, Val};

/// A sub-table to be proven, in the form of an air and values for the public inputs
struct Table<'a, T: FieldElementMap>
where
    ProverData<T>: Send,
    Commitment<T>: Send,
{
    air: PowdrTable<'a, T>,
    public_values_by_stage: Vec<&'a Vec<Val<T::Config>>>,
}

#[instrument(skip_all)]
pub fn verify<T: FieldElementMap>(
    verifying_key: Option<&StarkVerifyingKey<T::Config>>,
    program: &PowdrCircuit<T>,
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

    let mut public_inputs: BTreeMap<&String, Vec<&Vec<Plonky3Field<T>>>> = public_inputs
        .iter()
        .map(|(name, values)| (name, values.iter().collect_vec()))
        .collect();

    let tables: BTreeMap<&String, Table<_>> = program
        .split
        .iter()
        .map(|(name, (_, constraints))| {
            (
                name,
                Table {
                    air: PowdrTable::new(constraints),
                    public_values_by_stage: public_inputs.remove(name).unwrap(),
                },
            )
        })
        .collect();

    assert!(public_inputs.is_empty());

    if proof.opened_values.len() != tables.len() {
        return Err(VerificationError::InvalidProofShape);
    }

    let config = T::get_config();

    let pcs = config.pcs();

    let Proof {
        commitments,
        opened_values,
        opening_proof,
    } = proof;

    if let Some(vk) = verifying_key {
        for commit in vk
            .preprocessed
            .iter()
            .map(|(name, map)| &map[&(1 << opened_values[name].log_degree)])
        {
            challenger.observe(commit.clone());
        }
    }

    // Observe the instances.
    for opened_values in opened_values.values() {
        challenger.observe(Val::<T::Config>::from_canonical_usize(
            opened_values.log_degree,
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
                .map(|table| table.public_values_by_stage[i as usize].clone())
                .collect_vec()
        }))
        .zip_eq(challenge_count_by_stage)
        .map(|((commitment, public_values), challenge_count)| {
            challenger.observe(commitment.clone());
            for public_values in &public_values {
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

    // maybe these need to be in the vk, right now the prover can mess with them
    let trace_domains = proof
        .opened_values
        .values()
        .map(|opened_values| {
            let degree = 1 << opened_values.log_degree;
            pcs.natural_domain_for_degree(degree)
        })
        .collect::<Vec<_>>();

    let quotient_domains: Vec<Vec<_>> = tables
        .values()
        .zip_eq(proof.opened_values.values())
        .map(|(input, opened_values)| {
            let degree = 1 << opened_values.log_degree;
            let trace_domain = pcs.natural_domain_for_degree(degree);
            trace_domain
                .create_disjoint_domain(
                    1 << (opened_values.log_degree
                        + get_log_quotient_degree::<Val<T::Config>, _>(
                            &input.air,
                            &input
                                .public_values_by_stage
                                .iter()
                                .map(|values| values.len())
                                .collect::<Vec<_>>(),
                        )),
                )
                .split_domains(
                    1 << get_log_quotient_degree::<Val<T::Config>, _>(
                        &input.air,
                        &input
                            .public_values_by_stage
                            .iter()
                            .map(|values| values.len())
                            .collect::<Vec<_>>(),
                    ),
                )
        })
        .collect::<Vec<_>>();

    // for preprocessed commitments, we have one commitment per table, opened on the trace domain at `zeta` and `zeta_next`
    let preprocessed_domains_points_and_opens: Vec<(_, Vec<(_, _)>)> = proof
        .opened_values
        .iter()
        .zip_eq(trace_domains.iter())
        .flat_map(|((table_name, opened_values), trace_domain)| {
            let zeta_next = trace_domain.next_point(zeta).unwrap();

            opened_values
                .preprocessed
                .iter()
                .map(move |StageOpenedValues { local, next }| {
                    (
                        // choose the correct preprocessed commitment based on the degree in the proof
                        // this could be optimized by putting the preproccessed commitments in a merkle tree
                        // and have the prover prove that it used commitments matching the lengths of the traces
                        // this way the verifier does not need to have all the preprocessed commitments for all sizes
                        verifying_key
                            .as_ref()
                            .unwrap()
                            .preprocessed
                            .get(table_name)
                            .unwrap()[&(1 << opened_values.log_degree)]
                            .clone(),
                        vec![(
                            *trace_domain,
                            vec![(zeta, local.clone()), (zeta_next, next.clone())],
                        )],
                    )
                })
        })
        .collect();

    // for trace commitments, we have one commitment per stage, opened on each trace domain at `zeta` and `zeta_next`
    let trace_domains_points_and_opens_by_stage: Vec<(_, Vec<(_, _)>)> = izip!(
        proof.commitments.traces_by_stage.iter(),
        (0..stage_count as usize).map(|i| opened_values
            .values()
            .map(|opened_values| &opened_values.traces_by_stage[i])
            .collect_vec()),
    )
    .map(|(commit, openings)| {
        (
            commit.clone(),
            trace_domains
                .iter()
                .zip_eq(openings)
                .map(|(trace_domain, StageOpenedValues { local, next })| {
                    let zeta_next = trace_domain.next_point(zeta).unwrap();
                    (
                        *trace_domain,
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
        quotient_domains
            .iter()
            .zip_eq(opened_values.values())
            .flat_map(|(domains, values)| {
                domains
                    .iter()
                    .zip_eq(values.quotient_chunks.iter())
                    .map(|(domain, chunk)| (*domain, vec![(zeta, chunk.clone())]))
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
    for (table, trace_domain, quotient_chunks_domains, opened_values) in izip!(
        tables.into_values(),
        trace_domains,
        quotient_domains,
        opened_values.values(),
    ) {
        // Verify the shape of the opening arguments matches the expected values.
        verify_opening_shape(&table, opened_values)?;
        // Verify the constraint evaluation.
        let zps = quotient_chunks_domains
            .iter()
            .enumerate()
            .map(|(i, domain)| {
                quotient_chunks_domains
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

        let quotient = opened_values
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

        let sels = trace_domain.selectors_at_point(zeta);

        let empty_vec = vec![];

        let preprocessed = if let Some(preprocessed) = opened_values.preprocessed.as_ref() {
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

        let traces_by_stage = opened_values
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
    opened_values: &TableOpenedValues<Challenge<T>>,
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
    let res = opened_values
        .preprocessed
        .as_ref()
        .map(|StageOpenedValues { local, next }| {
            local.len() == air_fixed_width && next.len() == air_fixed_width
        })
        .unwrap_or(true)
        && opened_values
            .traces_by_stage
            .iter()
            .zip_eq(&air_widths)
            .all(|(StageOpenedValues { local, next }, air_width)| {
                local.len() == *air_width && next.len() == *air_width
            })
        && opened_values.quotient_chunks.len() == quotient_degree
        && opened_values
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

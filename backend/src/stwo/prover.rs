use itertools::Itertools;
use num_traits::Zero;
use powdr_ast::analyzed::{Analyzed, DegreeRange};
use powdr_backend_utils::{machine_fixed_columns, machine_witness_columns};
use powdr_executor::constant_evaluator::VariablySizedColumn;
use powdr_number::FieldElement;
use serde::de::DeserializeOwned;
use serde::ser::Serialize;
use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::sync::Arc;
use std::{fmt, io};

use crate::stwo::circuit_builder::{
    gen_stwo_circle_column, get_constant_with_next_list, PowdrComponent, PowdrEval,
};
use crate::stwo::proof::{
    Proof, SerializableStarkProvingKey, StarkProvingKey, TableProvingKey, TableProvingKeyCollection,
};

use stwo_prover::constraint_framework::{
    TraceLocationAllocator, ORIGINAL_TRACE_IDX, PREPROCESSED_TRACE_IDX,
};

use stwo_prover::core::air::{Component, ComponentProver};
use stwo_prover::core::backend::{Backend, BackendForChannel, Column};
use stwo_prover::core::channel::{Channel, MerkleChannel};
use stwo_prover::core::fields::m31::{BaseField, M31};
use stwo_prover::core::fields::qm31::SecureField;
use stwo_prover::core::fri::FriConfig;
use stwo_prover::core::pcs::{CommitmentSchemeProver, CommitmentSchemeVerifier, PcsConfig};
use stwo_prover::core::poly::circle::{CanonicCoset, CircleDomain, CircleEvaluation};
use stwo_prover::core::poly::BitReversedOrder;
use stwo_prover::core::ColumnVec;

const FRI_LOG_BLOWUP: usize = 1;
const FRI_NUM_QUERIES: usize = 100;
const FRI_PROOF_OF_WORK_BITS: usize = 16;
const LOG_LAST_LAYER_DEGREE_BOUND: usize = 0;

pub enum KeyExportError {
    NoProvingKey,
    //NoVerificationKey,
}

impl fmt::Display for KeyExportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoProvingKey => write!(f, "No proving key set"),
            // Self::NoVerificationKey => write!(f, "No verification key set"),
        }
    }
}

pub struct StwoProver<T, B: BackendForChannel<MC> + Send, MC: MerkleChannel, C: Channel> {
    pub analyzed: Arc<Analyzed<T>>,
    /// The split analyzed PIL
    split: BTreeMap<String, Analyzed<T>>,
    /// The value of the fixed columns
    pub fixed: Arc<Vec<(String, VariablySizedColumn<T>)>>,

    /// Proving key
    proving_key: StarkProvingKey<B>,
    /// Verifying key placeholder
    _verifying_key: Option<()>,
    _channel_marker: PhantomData<C>,
    _merkle_channel_marker: PhantomData<MC>,
}

impl<'a, F: FieldElement, B, MC, C> StwoProver<F, B, MC, C>
where
    B: Backend + Send + BackendForChannel<MC>,
    MC: MerkleChannel + Send,
    C: Channel + Send,
    MC::H: DeserializeOwned + Serialize,
    PowdrComponent<'a, F>: ComponentProver<B>,
{
    pub fn new(
        analyzed: Arc<Analyzed<F>>,
        fixed: Arc<Vec<(String, VariablySizedColumn<F>)>>,
    ) -> Result<Self, io::Error> {
        let split: BTreeMap<String, Analyzed<F>> = powdr_backend_utils::split_pil(&analyzed)
            .into_iter()
            .collect();

        Ok(Self {
            analyzed,
            split,
            fixed,
            proving_key: StarkProvingKey { preprocessed: None },
            _verifying_key: None,
            _channel_marker: PhantomData,
            _merkle_channel_marker: PhantomData,
        })
    }

    pub fn set_proving_key(&mut self, rdr: &mut dyn std::io::Read) {
        let serializable_key: SerializableStarkProvingKey = bincode::deserialize_from(rdr).unwrap();
        self.proving_key = StarkProvingKey::from(serializable_key);
    }

    pub fn export_proving_key(
        &self,
        writer: &mut dyn std::io::Write,
    ) -> Result<(), KeyExportError> {
        let pk = SerializableStarkProvingKey::from(self.proving_key.clone());
        self.proving_key
            .preprocessed
            .as_ref()
            .ok_or(KeyExportError::NoProvingKey)?;
        bincode::serialize_into(writer, &pk).unwrap();
        Ok(())
    }

    pub fn setup(&mut self) {
        let domain_degree_range = DegreeRange {
            min: self
                .analyzed
                .degree_ranges()
                .iter()
                .map(|range| range.min)
                .min()
                .unwrap(),
            max: self
                .analyzed
                .degree_ranges()
                .iter()
                .map(|range| range.max)
                .max()
                .unwrap(),
        };

        let domain_map: BTreeMap<usize, CircleDomain> = domain_degree_range
            .iter()
            .map(|size| {
                (
                    size.ilog2() as usize,
                    CanonicCoset::new(size.ilog2()).circle_domain(),
                )
            })
            .collect();

        let preprocessed: BTreeMap<String, TableProvingKeyCollection<B>> = self
            .split
            .iter()
            .filter_map(|(namespace, pil)| {
                // if we have no fixed columns, we don't need to commit to anything.
                if pil.constant_count()+pil.publics_count() == 0 {
                    None
                } else {
                    let fixed_columns = machine_fixed_columns(&self.fixed, pil);

                    Some((
                        namespace.to_string(),
                        pil.committed_polys_in_source_order()
                            .find_map(|(s, _)| s.degree)
                            .unwrap()
                            .iter()
                            .map(|size| {
                                //Group the fixed columns by size
                                let fixed_columns = &fixed_columns[&size];
                                let mut constant_trace: ColumnVec<
                                    CircleEvaluation<B, BaseField, BitReversedOrder>,
                                > = fixed_columns
                                    .iter()
                                    .map(|(_, vec)| {
                                        gen_stwo_circle_column::<F, B, M31>(
                                            *domain_map.get(&(vec.len().ilog2() as usize)).unwrap(),
                                            vec,
                                        )
                                    })
                                    .collect();

                                let constant_with_next_list = get_constant_with_next_list(pil);

                                let constant_shifted_trace: ColumnVec<
                                    CircleEvaluation<B, BaseField, BitReversedOrder>,
                                > = fixed_columns
                                    .iter()
                                    .filter(|(name, _)| constant_with_next_list.contains(name))
                                    .map(|(_, values)| {
                                        let mut rotated_values = values.to_vec();
                                        rotated_values.rotate_left(1);
                                        gen_stwo_circle_column::<F, B, M31>(
                                            *domain_map
                                                .get(&(values.len().ilog2() as usize))
                                                .unwrap(),
                                            &rotated_values,
                                        )
                                    })
                                    .collect();

                                constant_trace.extend(constant_shifted_trace);

                                (
                                    size as usize,
                                    TableProvingKey {
                                        constant_trace_circle_domain: constant_trace,
                                    },
                                )
                            })
                            .collect(),
                    ))
                }
            })
            .collect();
        let proving_key = StarkProvingKey {
            preprocessed: Some(preprocessed),
        };
        self.proving_key = proving_key;
    }

    pub fn prove(&self, witness: &[(String, Vec<F>)]) -> Result<Vec<u8>, String> {
        let config = get_config();
        let domain_degree_range = DegreeRange {
            min: self
                .analyzed
                .degree_ranges()
                .iter()
                .map(|range| range.min)
                .min()
                .unwrap(),
            max: self
                .analyzed
                .degree_ranges()
                .iter()
                .map(|range| range.max)
                .max()
                .unwrap(),
        };

        let domain_map: BTreeMap<usize, CircleDomain> = domain_degree_range
            .iter()
            .map(|size| {
                (
                    size.ilog2() as usize,
                    CanonicCoset::new(size.ilog2()).circle_domain(),
                )
            })
            .collect();

        let tree_span_provider = &mut TraceLocationAllocator::default();
        //Each column size in machines needs its own component, the components from different machines are stored in this vector
        let mut components = Vec::new();

        //The preprocessed columns needs to be indexed in the whole execution instead of each machine, so we need to keep track of the offset
        let mut constant_cols_offset_acc = 0;
        let mut machine_log_sizes = Vec::new();

        let mut constant_cols = Vec::new();

        let witness_by_machine: ColumnVec<CircleEvaluation<B, BaseField, BitReversedOrder>> = self
            .split
            .iter()
            .filter_map(|(machine, pil)| {
                let witness_columns = machine_witness_columns(witness, pil, machine);
                if witness_columns[0].1.is_empty() {
                    //TODO: Empty machines can be removed entirely, but in verification it is not removed, need to be handled
                    None
                } else {
                    let witness_by_machine = machine_witness_columns(witness, pil, machine);
                    let machine_length = witness_by_machine[0].1.len();
                    assert!(
                        witness_by_machine
                            .iter()
                            .all(|(_, vec)| vec.len() == machine_length),
                        "All witness columns in a single machine must have the same length"
                    );

                    if let Some(constant_trace) = self
                        .proving_key
                        .preprocessed
                        .as_ref()
                        .and_then(|preprocessed| preprocessed.get(machine))
                        .and_then(|table_provingkey| table_provingkey.get(&machine_length))
                        .map(|table_provingkey_machine_size| {
                            table_provingkey_machine_size
                                .constant_trace_circle_domain
                                .clone()
                        })
                    {
                        constant_cols.extend(constant_trace)
                    }

                    let component = PowdrComponent::new(
                        tree_span_provider,
                        PowdrEval::new(
                            (*pil).clone(),
                            constant_cols_offset_acc,
                            machine_length.ilog2(),
                        ),
                        (SecureField::zero(), None),
                    );
                    components.push(component);

                    machine_log_sizes.push(machine_length.ilog2());

                    constant_cols_offset_acc +=
                        pil.constant_count() + get_constant_with_next_list(pil).len();

                    Some(
                        witness_by_machine
                            .into_iter()
                            .map(|(_name, vec)| {
                                gen_stwo_circle_column::<F, B, M31>(
                                    *domain_map
                                        .get(&(machine_length.ilog2() as usize))
                                        .expect("Domain not found for given size"),
                                    &vec,
                                )
                            })
                            .collect::<Vec<_>>(),
                    )
                }
            })
            .flatten()
            .collect();

        let constant_col_log_sizes = constant_cols
            .iter()
            .map(|eval| eval.len().ilog2())
            .collect::<Vec<_>>();

        let witness_col_log_sizes = witness_by_machine
            .iter()
            .map(|eval| eval.len().ilog2())
            .collect::<Vec<_>>();

        let twiddles_max_degree = B::precompute_twiddles(
            CanonicCoset::new(domain_degree_range.max.ilog2() + 1 + FRI_LOG_BLOWUP as u32)
                .circle_domain()
                .half_coset,
        );

        let prover_channel = &mut <MC as MerkleChannel>::C::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<'_, B, MC>::new(config, &twiddles_max_degree);

        let mut tree_builder = commitment_scheme.tree_builder();

        tree_builder.extend_evals(constant_cols);

        tree_builder.commit(prover_channel);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(witness_by_machine);
        tree_builder.commit(prover_channel);

        let mut components_slice: Vec<&dyn ComponentProver<B>> = components
            .iter_mut()
            .map(|component| component as &dyn ComponentProver<B>)
            .collect();

        let components_slice = components_slice.as_mut_slice();

        let proof_result = stwo_prover::core::prover::prove::<B, MC>(
            components_slice,
            prover_channel,
            commitment_scheme,
        );

        let stark_proof = match proof_result {
            Ok(value) => value,
            Err(e) => return Err(e.to_string()), // Propagate the error instead of panicking
        };

        let proof: Proof<MC> = Proof {
            stark_proof,
            constant_col_log_sizes,
            witness_col_log_sizes,
            machine_log_sizes,
        };
        Ok(bincode::serialize(&proof).unwrap())
    }

    pub fn verify(&self, proof: &[u8], _instances: &[F]) -> Result<(), String> {
        assert!(
            _instances.is_empty(),
            "Expected _instances slice to be empty, but it has {} elements.",
            _instances.len()
        );

        let config = get_config();

        let proof: Proof<MC> =
            bincode::deserialize(proof).map_err(|e| format!("Failed to deserialize proof: {e}"))?;

        let verifier_channel = &mut <MC as MerkleChannel>::C::default();
        let commitment_scheme = &mut CommitmentSchemeVerifier::<MC>::new(config);

        //Constraints that are to be proved

        let tree_span_provider = &mut TraceLocationAllocator::default();

        let mut constant_cols_offset_acc = 0;

        let mut components = self
            .split
            .iter()
            .zip_eq(proof.machine_log_sizes.iter())
            .map(|((_, pil), &machine_size)| {
                constant_cols_offset_acc += pil.constant_count();

                constant_cols_offset_acc += get_constant_with_next_list(pil).len();
                PowdrComponent::new(
                    tree_span_provider,
                    PowdrEval::new((*pil).clone(), constant_cols_offset_acc, machine_size),
                    (SecureField::zero(), None),
                )
            })
            .collect::<Vec<_>>();

        let mut components_slice: Vec<&dyn Component> = components
            .iter_mut()
            .map(|component| component as &dyn Component)
            .collect();

        let components_slice = components_slice.as_mut_slice();

        commitment_scheme.commit(
            proof.stark_proof.commitments[PREPROCESSED_TRACE_IDX],
            &proof.constant_col_log_sizes,
            verifier_channel,
        );
        print!("proof.stark_proof.commitments[PREPROCESSED]: {:?}", proof.stark_proof.commitments[PREPROCESSED_TRACE_IDX]);
        commitment_scheme.commit(
            proof.stark_proof.commitments[ORIGINAL_TRACE_IDX],
            &proof.witness_col_log_sizes,
            verifier_channel,
        );

        stwo_prover::core::prover::verify(
            components_slice,
            verifier_channel,
            commitment_scheme,
            proof.stark_proof,
        )
        .map_err(|e| e.to_string())
    }
}

fn get_config() -> PcsConfig {
    PcsConfig {
        pow_bits: FRI_PROOF_OF_WORK_BITS as u32,
        fri_config: FriConfig::new(
            LOG_LAST_LAYER_DEGREE_BOUND as u32,
            FRI_LOG_BLOWUP as u32,
            FRI_NUM_QUERIES,
        ),
    }
}

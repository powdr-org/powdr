use powdr_ast::analyzed::Analyzed;
use powdr_backend_utils::machine_fixed_columns;
use powdr_executor::constant_evaluator::VariablySizedColumn;
use powdr_number::{DegreeType, FieldElement};
use serde::de::DeserializeOwned;
use serde::ser::Serialize;
use std::collections::BTreeMap;
use std::io;
use std::marker::PhantomData;
use std::sync::Arc;

use crate::stwo::circuit_builder::{gen_stwo_circuit_trace, PowdrComponent, PowdrEval, ConstraintSystem};
use crate::stwo::proof::{TableProvingKeyCollection,TableProvingKey,StarkProvingKey};

use stwo_prover::constraint_framework::TraceLocationAllocator;
use stwo_prover::core::prover::StarkProof;

use stwo_prover::core::air::{Component, ComponentProver};
use stwo_prover::core::backend::{Backend, BackendForChannel};
use stwo_prover::core::channel::{Channel, MerkleChannel};
use stwo_prover::core::fields::m31::{BaseField, M31};
use stwo_prover::core::fri::FriConfig;
use stwo_prover::core::pcs::{CommitmentSchemeProver, CommitmentSchemeVerifier, PcsConfig};
use stwo_prover::core::poly::circle::{CanonicCoset, CircleEvaluation};
use stwo_prover::core::poly::BitReversedOrder;
use stwo_prover::core::utils::bit_reverse_coset_to_circle_domain_order;
use stwo_prover::core::ColumnVec;

const FRI_LOG_BLOWUP: usize = 1;
const FRI_NUM_QUERIES: usize = 100;
const FRI_PROOF_OF_WORK_BITS: usize = 16;
const LOG_LAST_LAYER_DEGREE_BOUND: usize = 0;

pub struct StwoProver<T, B: BackendForChannel<MC> + Send, MC: MerkleChannel, C: Channel> {
    pub analyzed: Arc<Analyzed<T>>,
    fixed: Arc<Vec<(String, VariablySizedColumn<T>)>>,

    /// The split analyzed PIL
    split: BTreeMap<String, (Analyzed<T>, ConstraintSystem<T>)>,

    /// Proving key placeholder
    proving_key: Option<StarkProvingKey<B,MC>>,
    /// Verifying key placeholder
    _verifying_key: Option<()>,
    _channel_marker: PhantomData<C>,
    _backend_marker: PhantomData<B>,
    _merkle_channel_marker: PhantomData<MC>,
}

impl<'a, F: FieldElement, B, MC, C> StwoProver<F, B, MC, C>
where
    B: Backend + Send + BackendForChannel<MC>, // Ensure B implements BackendForChannel<MC>
    MC: MerkleChannel + Send,
    C: Channel + Send,
    MC::H: DeserializeOwned + Serialize,
    PowdrComponent<'a, F>: ComponentProver<B>,
{   
    pub fn setup(&mut self) {
        let preprocessed: BTreeMap<String, TableProvingKeyCollection<B,MC>> = self
            .split
            .iter()
            .filter_map(|(namespace, (pil, _))| {
                // if we have neither fixed columns nor publics, we don't need to commit to anything
                if pil.constant_count() + pil.publics_count() == 0 {
                    None
                } else {
                    Some((
                        namespace.to_string(),
                        pil.committed_polys_in_source_order()
                            .find_map(|(s, _)| s.degree)
                            .unwrap()
                            .iter()
                            .map(|size| {
                                // get the config
                                let config = get_config();

                                // commit to the fixed columns
                                let twiddles = B::precompute_twiddles(
                                    CanonicCoset::new(self.analyzed.degree().ilog2() + 1 + FRI_LOG_BLOWUP as u32)
                                        .circle_domain()
                                        .half_coset,
                                );
                        
                                // Setup protocol.
                                let prover_channel = &mut <MC as MerkleChannel>::C::default();
                                let commitment_scheme = &mut CommitmentSchemeProver::<B, MC>::new(config, &twiddles);
                        
                                // get fix_columns evaluations
                                let fixed_columns = machine_fixed_columns(&self.fixed, &self.analyzed);
                        
                                let domain = CanonicCoset::new(
                                    fixed_columns
                                        .keys()
                                        .next()
                                        .map(|&first_key| first_key.ilog2())
                                        .unwrap_or(0),
                                )
                                .circle_domain();
                        
                                let updated_fixed_columns: BTreeMap<DegreeType, Vec<(String, Vec<F>)>> = fixed_columns
                                    .iter()
                                    .map(|(key, vec)| {
                                        let transformed_vec: Vec<(String, Vec<F>)> = vec
                                            .iter()
                                            .map(|(name, slice)| {
                                                let mut values: Vec<F> = slice.to_vec(); // Clone the slice into a Vec
                                                bit_reverse_coset_to_circle_domain_order(&mut values); // Apply bit reversal
                                                (name.clone(), values) // Return the updated tuple
                                            })
                                            .collect(); // Collect the updated vector
                                        (*key, transformed_vec) // Rebuild the BTreeMap with transformed vectors
                                    })
                                    .collect();
                        
                                let constant_trace: ColumnVec<CircleEvaluation<B, BaseField, BitReversedOrder>> =
                                    updated_fixed_columns
                                        .values()
                                        .flat_map(|vec| {
                                            vec.iter().map(|(_name, values)| {
                                                let values = values
                                                    .iter()
                                                    .map(|v| v.try_into_i32().unwrap().into())
                                                    .collect();
                                                CircleEvaluation::new(domain, values)
                                            })
                                        })
                                        .collect();
                        
                                // Preprocessed trace
                                let mut tree_builder = commitment_scheme.tree_builder();
                                tree_builder.extend_evals(constant_trace.clone());
                                tree_builder.commit(prover_channel);
                                let trees = std::mem::take(&mut commitment_scheme.trees);
                                   
                                   ( 
                                       self.analyzed.degree().ilog2() as usize,
                                       TableProvingKey {
                                       trees,
                                    }
                                )
                            })
                            .collect(),
                    ))
                }
            })
            .collect();
        let proving_key = StarkProvingKey { preprocessed };

        self.proving_key = Some(proving_key);
        }
    pub fn new(
        analyzed: Arc<Analyzed<F>>,
        fixed: Arc<Vec<(String, VariablySizedColumn<F>)>>,
    ) -> Result<Self, io::Error> {
        
        Ok(Self {
            split: powdr_backend_utils::split_pil(&analyzed)
                .into_iter()
                .map(|(name, pil)| {
                    let constraint_system = ConstraintSystem::from(&pil);
                    (name, (pil, constraint_system))
                })
                .collect(),
            analyzed,
            fixed,
            proving_key: None,
            _verifying_key: None,
            _channel_marker: PhantomData,
            _backend_marker: PhantomData,
            _merkle_channel_marker: PhantomData,
        })
    }
    pub fn prove(&self, witness: &[(String, Vec<F>)]) -> Result<Vec<u8>, String> {
        let config = get_config();
        // twiddles are used for FFT, they are computed in a bigger group than the eval domain.
        // the eval domain is the half coset G_{2n} + <G_{n/2}>
        // twiddles are computed in half coset G_{4n} + <G_{n}>, double the size of eval doamin.
        let twiddles = B::precompute_twiddles(
            CanonicCoset::new(self.analyzed.degree().ilog2() + 1 + FRI_LOG_BLOWUP as u32)
                .circle_domain()
                .half_coset,
        );

        // Setup protocol.
        let prover_channel = &mut <MC as MerkleChannel>::C::default();
        let commitment_scheme = &mut CommitmentSchemeProver::<B, MC>::new(config, &twiddles);

        // get fix_columns evaluations
        let fixed_columns = machine_fixed_columns(&self.fixed, &self.analyzed);

        let domain = CanonicCoset::new(
            fixed_columns
                .keys()
                .next()
                .map(|&first_key| first_key.ilog2())
                .unwrap_or(0),
        )
        .circle_domain();

        let updated_fixed_columns: BTreeMap<DegreeType, Vec<(String, Vec<F>)>> = fixed_columns
            .iter()
            .map(|(key, vec)| {
                let transformed_vec: Vec<(String, Vec<F>)> = vec
                    .iter()
                    .map(|(name, slice)| {
                        let mut values: Vec<F> = slice.to_vec(); // Clone the slice into a Vec
                        bit_reverse_coset_to_circle_domain_order(&mut values); // Apply bit reversal
                        (name.clone(), values) // Return the updated tuple
                    })
                    .collect(); // Collect the updated vector
                (*key, transformed_vec) // Rebuild the BTreeMap with transformed vectors
            })
            .collect();

        let constant_trace: ColumnVec<CircleEvaluation<B, BaseField, BitReversedOrder>> =
            updated_fixed_columns
                .values()
                .flat_map(|vec| {
                    vec.iter().map(|(_name, values)| {
                        let values = values
                            .iter()
                            .map(|v| v.try_into_i32().unwrap().into())
                            .collect();
                        CircleEvaluation::new(domain, values)
                    })
                })
                .collect();

        // Preprocessed trace
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(constant_trace.clone());
        tree_builder.commit(prover_channel);

        let transformed_witness: Vec<(String, Vec<F>)> = witness
            .iter()
            .map(|(name, vec)| {
                (
                    name.clone(),
                    vec.iter()
                        .map(|&elem| {
                            if elem == F::from(2147483647) {
                                F::zero()
                            } else {
                                elem
                            }
                        })
                        .collect(),
                )
            })
            .collect();

        let witness: &Vec<(String, Vec<F>)> = &transformed_witness
            .into_iter()
            .map(|(name, mut vec)| {
                bit_reverse_coset_to_circle_domain_order(&mut vec);
                (name, vec)
            })
            .collect();

        // committed/witness trace
        let trace = gen_stwo_circuit_trace::<F, B, M31>(witness);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(trace);
        tree_builder.commit(prover_channel);

        let component = PowdrComponent::new(
            &mut TraceLocationAllocator::default(),
            PowdrEval::new(self.analyzed.clone()),
        );

        let proof = stwo_prover::core::prover::prove::<B, MC>(
            &[&component],
            prover_channel,
            commitment_scheme,
        )
        .unwrap();

        Ok(bincode::serialize(&proof).unwrap())
    }

    pub fn verify(&self, proof: &[u8], _instances: &[F]) -> Result<(), String> {
        assert!(
            _instances.is_empty(),
            "Expected _instances slice to be empty, but it has {} elements.",
            _instances.len()
        );

        let config = get_config();
        let proof: StarkProof<MC::H> =
            bincode::deserialize(proof).map_err(|e| format!("Failed to deserialize proof: {e}"))?;

        let verifier_channel = &mut <MC as MerkleChannel>::C::default();
        let commitment_scheme = &mut CommitmentSchemeVerifier::<MC>::new(config);

        //Constraints that are to be proved
        let component = PowdrComponent::new(
            &mut TraceLocationAllocator::default(),
            PowdrEval::new(self.analyzed.clone()),
        );

        // Retrieve the expected column sizes in each commitment interaction, from the AIR.
        let sizes = component.trace_log_degree_bounds();

        commitment_scheme.commit(proof.commitments[0], &sizes[0], verifier_channel);
        commitment_scheme.commit(proof.commitments[1], &sizes[1], verifier_channel);

        stwo_prover::core::prover::verify(&[&component], verifier_channel, commitment_scheme, proof)
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

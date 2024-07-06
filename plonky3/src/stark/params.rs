//! The concrete parameters used in the prover
//! Inspired from [this example](https://github.com/Plonky3/Plonky3/blob/6a1b0710fdf85136d0fdd645b92933615867740a/keccak-air/examples/prove_goldilocks_keccak.rs#L57)

use lazy_static::lazy_static;

use p3_challenger::DuplexChallenger;
use p3_commit::{ExtensionMmcs, Pcs};
use p3_dft::Radix2DitParallel;
use p3_field::{extension::BinomialExtensionField, Field};
use p3_fri::{FriConfig, TwoAdicFriPcs};
use p3_goldilocks::MdsMatrixGoldilocks;
use p3_merkle_tree::FieldMerkleTreeMmcs;
use p3_poseidon::Poseidon;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{StarkConfig, StarkGenericConfig};
use p3_util::log2_ceil_usize;
use rand::{distributions::Standard, Rng, SeedableRng};
use serde::{Deserialize, Serialize};

use crate::circuit_builder::Val;

const D: usize = 2;
type Challenge = BinomialExtensionField<Val, D>;
const WIDTH: usize = 8;
const ALPHA: u64 = 7;
type Perm = Poseidon<Val, MdsMatrixGoldilocks, WIDTH, ALPHA>;

const RATE: usize = 4;
const OUT: usize = 4;
type Hash = PaddingFreeSponge<Perm, WIDTH, RATE, OUT>;

const N: usize = 2;
const CHUNK: usize = 4;
type Compress = TruncatedPermutation<Perm, N, CHUNK, WIDTH>;

const DIGEST_ELEMS: usize = 4;
type ValMmcs = FieldMerkleTreeMmcs<
    <Val as Field>::Packing,
    <Val as Field>::Packing,
    Hash,
    Compress,
    DIGEST_ELEMS,
>;
pub type Challenger = DuplexChallenger<Val, Perm, WIDTH>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Dft = Radix2DitParallel;
type MyPcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
pub type Config = StarkConfig<MyPcs, Challenge, Challenger>;

pub type PcsProverData<SC> = <<SC as StarkGenericConfig>::Pcs as p3_commit::Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::ProverData;

pub type Commitment<SC> = <<SC as StarkGenericConfig>::Pcs as p3_commit::Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Commitment;

pub struct StarkProvingKey<SC: StarkGenericConfig> {
    pub fixed_commit: Commitment<SC>,
    pub fixed_data: PcsProverData<SC>,
}

pub struct StarkVerifyingKey<SC: StarkGenericConfig> {
    pub fixed_commit: Commitment<SC>,
}

#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct Proof<SC: StarkGenericConfig> {
    pub(crate) commitments: Commitments<Com<SC>>,
    pub(crate) opened_values: OpenedValues<SC::Challenge>,
    pub(crate) opening_proof: PcsProof<SC>,
    pub(crate) degree_bits: usize,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Commitments<Com> {
    pub(crate) trace: Com,
    pub(crate) quotient_chunks: Com,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct OpenedValues<Challenge> {
    pub(crate) trace_local: Vec<Challenge>,
    pub(crate) trace_next: Vec<Challenge>,
    pub(crate) fixed_local: Option<Vec<Challenge>>,
    pub(crate) fixed_next: Option<Vec<Challenge>>,
    pub(crate) quotient_chunks: Vec<Vec<Challenge>>,
}

type Com<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Commitment;
type PcsProof<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Proof;

const HALF_NUM_FULL_ROUNDS: usize = 4;
const NUM_PARTIAL_ROUNDS: usize = 22;

const FRI_LOG_BLOWUP: usize = 1;
const FRI_NUM_QUERIES: usize = 100;
const FRI_PROOF_OF_WORK_BITS: usize = 16;

const NUM_ROUNDS: usize = 2 * HALF_NUM_FULL_ROUNDS + NUM_PARTIAL_ROUNDS;
const NUM_CONSTANTS: usize = WIDTH * NUM_ROUNDS;

const RNG_SEED: u64 = 42;

lazy_static! {
    static ref PERM: Perm = Perm::new(
        HALF_NUM_FULL_ROUNDS,
        NUM_PARTIAL_ROUNDS,
        rand_chacha::ChaCha8Rng::seed_from_u64(RNG_SEED)
            .sample_iter(Standard)
            .take(NUM_CONSTANTS)
            .collect(),
        MdsMatrixGoldilocks,
    );
}

pub fn get_challenger() -> Challenger {
    Challenger::new(PERM.clone())
}

pub fn get_config(degree: u64) -> StarkConfig<MyPcs, Challenge, Challenger> {
    let hash = Hash::new(PERM.clone());

    let compress = Compress::new(PERM.clone());

    let val_mmcs = ValMmcs::new(hash, compress);

    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());

    let dft = Dft {};

    let fri_config = FriConfig {
        log_blowup: FRI_LOG_BLOWUP,
        num_queries: FRI_NUM_QUERIES,
        proof_of_work_bits: FRI_PROOF_OF_WORK_BITS,
        mmcs: challenge_mmcs,
    };

    let pcs = MyPcs::new(log2_ceil_usize(degree as usize), dft, val_mmcs, fri_config);

    Config::new(pcs)
}

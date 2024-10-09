use std::collections::BTreeMap;

use alloc::vec::Vec;

use p3_commit::Pcs;
use serde::{Deserialize, Serialize};

use p3_uni_stark::{StarkGenericConfig, Val};

pub type Com<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Commitment;
pub type PcsProof<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Proof;
pub type PcsProverData<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::ProverData;

#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct Proof<SC: StarkGenericConfig> {
    pub(crate) commitments: Commitments<Com<SC>>,
    pub(crate) opened_values: BTreeMap<String, TableOpenedValues<SC::Challenge>>,
    pub(crate) opening_proof: PcsProof<SC>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Commitments<Com> {
    pub(crate) traces_by_stage: Vec<Com>,
    pub(crate) quotient_chunks: Com,
}

pub type OpenedValues<Challenge> = BTreeMap<String, TableOpenedValues<Challenge>>;

#[derive(Debug, Serialize, Deserialize)]
pub struct TableOpenedValues<Challenge> {
    pub(crate) preprocessed_local: Option<Vec<Challenge>>,
    pub(crate) preprocessed_next: Option<Vec<Challenge>>,
    pub(crate) traces_by_stage_local: Vec<Vec<Challenge>>,
    pub(crate) traces_by_stage_next: Vec<Vec<Challenge>>,
    pub(crate) quotient_chunks: Vec<Vec<Challenge>>,
    pub(crate) log_degree: usize,
}

pub struct StarkProvingKey<SC: StarkGenericConfig> {
    // for each table, the preprocessed data
    pub preprocessed: BTreeMap<String, TableProvingKeyCollection<SC>>,
}

/// For each possible size, the commitment and prover data
pub type TableProvingKeyCollection<SC> = BTreeMap<usize, TableProvingKey<SC>>;

/// For each possible size, the commitment
pub type TableVerifyingKeyCollection<SC> = BTreeMap<usize, Com<SC>>;

pub struct TableProvingKey<SC: StarkGenericConfig> {
    pub commitment: Com<SC>,
    pub prover_data: PcsProverData<SC>,
}

#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct StarkVerifyingKey<SC: StarkGenericConfig> {
    // for each table, for each possible size, the commitment
    pub preprocessed: BTreeMap<String, TableVerifyingKeyCollection<SC>>,
}

pub struct ProcessedStage<SC: StarkGenericConfig> {
    pub(crate) commitment: Com<SC>,
    pub(crate) prover_data: PcsProverData<SC>,
    pub(crate) challenge_values: Vec<Val<SC>>,
    pub(crate) public_values: Vec<Vec<Val<SC>>>,
}

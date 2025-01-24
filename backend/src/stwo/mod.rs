use serde::de::DeserializeOwned;
use serde::Serialize;
use std::io;
use std::path::PathBuf;
use std::sync::Arc;

use crate::{
    field_filter::generalize_factory, Backend, BackendFactory, BackendOptions, Error, Proof,
};
use powdr_ast::analyzed::Analyzed;
use powdr_executor::constant_evaluator::VariablySizedColumn;
use powdr_executor::witgen::WitgenCallback;
use powdr_number::Mersenne31Field;
use prover::StwoProver;
use stwo_prover::core::backend::{simd::SimdBackend, BackendForChannel};
use stwo_prover::core::channel::{Blake2sChannel, Channel, MerkleChannel};
use stwo_prover::core::vcs::blake2_merkle::Blake2sMerkleChannel;

mod circuit_builder;
mod params;
mod proof;
mod prover;

struct RestrictedFactory;

impl BackendFactory<Mersenne31Field> for RestrictedFactory {
    #[allow(unused_variables)]
    fn create(
        &self,
        pil: Arc<Analyzed<Mersenne31Field>>,
        fixed: Arc<Vec<(String, VariablySizedColumn<Mersenne31Field>)>>,
        _output_dir: Option<PathBuf>,
        setup: Option<&mut dyn io::Read>,
        proving_key: Option<&mut dyn io::Read>,
        verification_key: Option<&mut dyn io::Read>,
        verification_app_key: Option<&mut dyn io::Read>,
        options: BackendOptions,
    ) -> Result<Box<dyn crate::Backend<Mersenne31Field>>, Error> {
        if proving_key.is_some() {
            return Err(Error::BackendError("Proving key unused".to_string()));
        }

        assert!(pil.stage_count() <= 2, "stwo supports max 2 stages");

        let mut stwo: Box<StwoProver<SimdBackend, Blake2sMerkleChannel, Blake2sChannel>> =
            Box::new(StwoProver::new(pil, fixed)?);

        match (proving_key, verification_key) {
            (Some(pk), Some(vk)) => {
                stwo.set_proving_key(pk);
                //stwo.set_verifying_key(vk);
            }
            _ => {
                stwo.setup();
            }
        }

        Ok(stwo)
    }
}

generalize_factory!(Factory <- RestrictedFactory, [Mersenne31Field]);

impl<MC: MerkleChannel + Send, C: Channel + Send> Backend<Mersenne31Field>
    for StwoProver<SimdBackend, MC, C>
where
    SimdBackend: BackendForChannel<MC>,
    MC: MerkleChannel,
    C: Channel,
    MC::H: DeserializeOwned + Serialize,
{
    #[allow(unused_variables)]
    fn verify(&self, proof: &[u8], instances: &[Vec<Mersenne31Field>]) -> Result<(), Error> {
        assert_eq!(instances.len(), 1);
        let instances = &instances[0];

        Ok(self.verify(proof, instances)?)
    }

    #[allow(unused_variables)]
    fn prove(
        &self,
        witness: &[(String, Vec<Mersenne31Field>)],
        prev_proof: Option<Proof>,
        witgen_callback: WitgenCallback<Mersenne31Field>,
    ) -> Result<Proof, Error> {
        if prev_proof.is_some() {
            return Err(Error::NoAggregationAvailable);
        }
        Ok(StwoProver::prove(self, witness, witgen_callback)?)
    }
    fn export_proving_key(&self, output: &mut dyn io::Write) -> Result<(), Error> {
        self.export_proving_key(output)
            .map_err(|e| Error::BackendError(e.to_string()))
    }
}

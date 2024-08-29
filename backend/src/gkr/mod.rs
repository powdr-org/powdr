#![deny(clippy::print_stdout)]

use std::io;
use std::path::PathBuf;
use std::sync::Arc;

use crate::{Backend, BackendFactory, BackendOptions, Error, Proof};
use powdr_ast::analyzed::Analyzed;
use powdr_executor::constant_evaluator::{get_uniquely_sized_cloned, VariablySizedColumn};
use powdr_executor::witgen::WitgenCallback;
use powdr_number::{DegreeType, FieldElement};
use prover::{generate_setup, Halo2Prover};

use serde::de::{self, Deserializer};
use serde::ser::Serializer;
use serde::{Deserialize, Serialize};

mod aggregation;
mod circuit_builder;
mod mock_prover;
mod prover;

use halo2_proofs::poly::commitment::Params;
use halo2_proofs::SerdeFormat;

pub(crate) struct GkrFactory;

#[derive(Clone)]
enum ProofType {
    /// Create a single proof for a given PIL using Poseidon transcripts.
    Poseidon,
    /// Create a single proof for a given PIL using Keccak transcripts,
    /// which can be verified directly on Ethereum.
    SnarkSingle,
    /// Create a recursive proof that compresses a Poseidon proof,
    /// which can be verified directly on Ethereum.
    SnarkAggr,
}

impl From<BackendOptions> for ProofType {
    fn from(options: BackendOptions) -> Self {
        match options.as_str() {
            "" | "poseidon" => Self::Poseidon,
            "snark_single" => Self::SnarkSingle,
            "snark_aggr" => Self::SnarkAggr,
            _ => panic!("Unsupported proof type: {options}"),
        }
    }
}
#[derive(Serialize, Deserialize)]
struct Halo2Proof {
    #[serde(
        serialize_with = "serialize_as_hex",
        deserialize_with = "deserialize_from_hex"
    )]
    proof: Vec<u8>,
    publics: Vec<String>,
}

fn serialize_as_hex<S>(bytes: &Vec<u8>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let hex_string = hex::encode(bytes);
    serializer.serialize_str(&hex_string)
}

fn deserialize_from_hex<'de, D>(deserializer: D) -> Result<Vec<u8>, D::Error>
where
    D: Deserializer<'de>,
{
    let s = String::deserialize(deserializer)?;
    hex::decode(s).map_err(de::Error::custom)
}

impl<F: FieldElement> BackendFactory<F> for GkrFactory {
    fn create(
        &self,
        pil: Arc<Analyzed<F>>,
        fixed: Arc<Vec<(String, VariablySizedColumn<F>)>>,
        _output_dir: Option<PathBuf>,
        setup: Option<&mut dyn io::Read>,
        verification_key: Option<&mut dyn io::Read>,
        verification_app_key: Option<&mut dyn io::Read>,
        options: BackendOptions,
    ) -> Result<Box<dyn crate::Backend<F>>, Error> {
        if pil.degrees().len() > 1 {
            return Err(Error::NoVariableDegreeAvailable);
        }
        let proof_type = ProofType::from(options);
        let fixed = Arc::new(
            get_uniquely_sized_cloned(&fixed).map_err(|_| Error::NoVariableDegreeAvailable)?,
        );
        let mut gkr = Box::new(GkrProver::new(pil, fixed, setup, proof_type)?);

        Ok(gkr)
    }

    fn generate_setup(
        &self,
        size: DegreeType,
        mut output: &mut dyn io::Write,
    ) -> Result<(), Error> {
        let setup = generate_setup(size);
        Ok(setup.write(&mut output)?)
    }
}

fn fe_slice_to_string<F: FieldElement>(fe: &[F]) -> Vec<String> {
    fe.iter().map(|x| x.to_string()).collect()
}

impl<T: FieldElement> Backend<T> for GkrProver<T> {
    fn verify(&self, proof: &[u8], instances: &[Vec<T>]) -> Result<(), Error> {
        let proof: Halo2Proof = bincode::deserialize(proof).unwrap();
        // TODO should do a verification refactoring making it a 1d vec
        assert!(instances.len() == 1);
        if proof.publics != fe_slice_to_string(&instances[0]) {
            return Err(Error::BackendError(format!(
                "Invalid public inputs {:?} != {:?}",
                proof.publics, instances[0]
            )));
        }
        match self.proof_type() {
            ProofType::Poseidon => Ok(self.verify_poseidon(&proof.proof, instances)?),
            ProofType::SnarkSingle | ProofType::SnarkAggr => {
                Ok(self.verify_snark(&proof.proof, instances)?)
            }
        }
    }

    fn prove(
        &self,
        witness: &[(String, Vec<T>)],
        prev_proof: Option<Proof>,
        witgen_callback: WitgenCallback<T>,
    ) -> Result<Proof, Error> {
        let proof_and_publics = match self.proof_type() {
            ProofType::Poseidon => self.prove_poseidon(witness, witgen_callback),
            ProofType::SnarkSingle => self.prove_snark_single(witness, witgen_callback),
            ProofType::SnarkAggr => match prev_proof {
                Some(proof) => {
                    let proof: Halo2Proof = bincode::deserialize(&proof).unwrap();
                    self.prove_snark_aggr(witness, witgen_callback, proof.proof)
                }
                None => Err("Aggregated proof requires a previous proof".to_string()),
            },
        };
        let (proof, publics) = proof_and_publics?;
        let publics = fe_slice_to_string(&publics);
        let proof = Halo2Proof { proof, publics };
        let proof = bincode::serialize(&proof).unwrap();
        Ok(proof)
    }

    fn export_setup(&self, mut output: &mut dyn io::Write) -> Result<(), Error> {
        Ok(self.write_setup(&mut output)?)
    }

    fn verification_key_bytes(&self) -> Result<Vec<u8>, Error> {
        let vk = self.verification_key()?;
        Ok(vk.to_bytes(SerdeFormat::Processed))
    }

    fn export_ethereum_verifier(&self, output: &mut dyn io::Write) -> Result<(), Error> {
        match self.proof_type() {
            ProofType::Poseidon => Err(Error::NoEthereumVerifierAvailable),
            ProofType::SnarkSingle | ProofType::SnarkAggr => {
                match self.export_ethereum_verifier_snark(output) {
                    Ok(_) => Ok(()),
                    Err(e) => Err(Error::BackendError(e.to_string())),
                }
            }
        }
    }
}



use halo2_proofs::{
    halo2curves::bn256::{Bn256, Fr, G1Affine},
    halo2curves::ff::PrimeField,
    plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ProvingKey, VerifyingKey},
    poly::{
        commitment::{Params, ParamsProver},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverGWC, VerifierGWC},
            strategy::AccumulatorStrategy,
        },
        VerificationStrategy,
    },
    transcript::{EncodedChallenge, TranscriptReadBuffer, TranscriptWriterBuffer},
    SerdeFormat,
};

use powdr_ast::analyzed::Analyzed;
use powdr_executor::witgen::WitgenCallback;
use powdr_number::{DegreeType, FieldElement, KnownField};

use expander_rs::prover;

// We use two different EVM verifier libraries.
// 1. snark_verifier: supports single SNARK verification as well as aggregated proof verification.
// However the generated smart contract code size is often larger than the limit on Ethereum for complex VMs.
// This is mitigated in (2).
// 2. halo2_solidity_verifier: supports single SNARK verification only. The generated smart contract
// code size is reasonable.

use snark_verifier::{
    loader::{
        evm::{deploy_and_call, encode_calldata as encode_calldata_snark_verifier},
        native::NativeLoader,
    },
    system::halo2::{compile, transcript::evm::EvmTranscript, Config},
};

use halo2_solidity_verifier::{
    compile_solidity, encode_calldata, BatchOpenScheme, Evm, SolidityGenerator,
};

use crate::gkr::gkr_circuit_builder;

use super::{
    aggregation,
    circuit_builder::{convert_field, PowdrCircuit},
    ProofType,
};

use itertools::Itertools;
use rand::rngs::OsRng;
use std::{
    io::{self, Cursor},
    sync::Arc,
    time::Instant,
};

/// Generate a Gkr proof
pub struct GkrProver<F> {
    analyzed: Arc<Analyzed<F>>,
    fixed: Arc<Vec<(String, Vec<F>)>>,
    params: ParamsKZG<Bn256>,
    // Verification key of the proof type we're generating
    vkey: Option<VerifyingKey<G1Affine>>,
    // Verification key of the app we're proving recursively.
    // That is, if proof type is "snark_aggr", this will be
    // the vkey of the "poseidon" proof.
    vkey_app: Option<VerifyingKey<G1Affine>>,
    proof_type: ProofType,
}

fn degree_bits(degree: DegreeType) -> u32 {
    DegreeType::BITS - degree.leading_zeros() + 1
}

pub fn generate_setup(size: DegreeType) -> ParamsKZG<Bn256> {
    // Halo2 does not like degree < 2^4, so we enforce a minimum of 2^4 here.
    // Soundness is fine if we use a larger degree.
    // Performance is also fine if we have to raise it to 4 since it's still quite small.
    ParamsKZG::<Bn256>::new(std::cmp::max(4, degree_bits(size)))
}

impl<F: FieldElement> GkrProver<F> {
    pub fn new(
        analyzed: Arc<Analyzed<F>>,
        fixed: Arc<Vec<(String, Vec<F>)>>,
        setup: Option<&mut dyn io::Read>,
        proof_type: ProofType,
    ) -> Result<Self, io::Error> {
        Self::assert_field_is_bn254();

        let mut params = setup
            .map(|mut setup| ParamsKZG::<Bn256>::read(&mut setup))
            .transpose()?
            .unwrap_or_else(|| generate_setup(analyzed.degree()));

        if matches!(proof_type, ProofType::Poseidon | ProofType::SnarkSingle) {
            params.downsize(degree_bits(analyzed.degree()));
        }

        Ok(Self {
            analyzed,
            fixed,
            params,
            vkey: None,
            vkey_app: None,
            proof_type,
        })
    }

    pub fn proof_type(&self) -> ProofType {
        self.proof_type.clone()
    }

    pub fn write_setup(&self, output: &mut impl io::Write) -> Result<(), io::Error> {
        self.params.write(output)
    }

    fn prove<
    E: EncodedChallenge<G1Affine>,
    TW: TranscriptWriterBuffer<Vec<u8>, G1Affine, E>,
    TR: TranscriptReadBuffer<Cursor<Vec<u8>>, G1Affine, E>,
>(
    &self,
    witness: &[(String, Vec<F>)],
    witgen_callback: WitgenCallback<F>,
) -> Result<(Vec<u8>, Vec<Vec<Fr>>), String> {
    log::info!("Starting proof generation...");

    let circuit = PowdrCircuit::new(self.analyzed.clone(), &self.fixed)
        .with_witgen_callback(witgen_callback)
        .with_witness(witness);
    let publics = vec![circuit.instance_column()];

    log::info!("Generating PK for snark...");
    let vk = match self.vkey {
        Some(ref vk) => vk.clone(),
        None => keygen_vk(&self.params, &circuit).unwrap(),
    };
    let pk = keygen_pk(&self.params, vk.clone(), &circuit).unwrap();

    log::info!("Generating proof...");
    let start = Instant::now();

    let proof = gen_proof::<_, _, TW>(&self.params, &pk, circuit, &publics)?;

    let duration = start.elapsed();
    log::info!("Time taken: {:?}", duration);

    match self.verify_inner::<_, TR>(&vk, &self.params, &proof, &publics) {
        Ok(_) => {}
        Err(e) => {
            return Err(e.to_string());
        }
    }

    log::info!("Proof generation done.");

    Ok((proof, publics))
}

    /// Generate a single proof for a given PIL using Poseidon transcripts.
    /// One or more of these proofs can be aggregated by `prove_snark_aggr`.
    pub fn prove_poseidon(
        &self,
        witness: &[(String, Vec<F>)],
        witgen_callback: WitgenCallback<F>,
    ) -> Result<(Vec<u8>, Vec<F>), String> {
        assert!(matches!(self.proof_type, ProofType::Poseidon));

        let (proof, publics) = self.prove::<_, aggregation::PoseidonTranscript<NativeLoader, _>,  aggregation::PoseidonTranscript<NativeLoader, _>>(witness, witgen_callback)?;
        // Our Halo2 integration always has one instance column `publics[0]`
        // containing the public inputs.
        let publics: Vec<F> = publics[0]
            .clone()
            .into_iter()
            .map(|x| F::from_bytes_le(&x.to_repr()))
            .collect();

        Ok((proof, publics))
    }

    /// Generate a single proof for a given PIL using Keccak transcripts.
    /// These proofs can be verified directly on Ethereum.
    pub fn prove_snark_single(
        &self,
        witness: &[(String, Vec<F>)],
        witgen_callback: WitgenCallback<F>,
    ) -> Result<(Vec<u8>, Vec<F>), String> {
        assert!(matches!(self.proof_type, ProofType::SnarkSingle));

        let (proof, publics) = self
            .prove::<_, EvmTranscript<_, _, _, _>, EvmTranscript<G1Affine, _, _, _>>(
                witness,
                witgen_callback,
            )?;

        log::info!("Verifying SNARK in the EVM...");

        let verifier_solidity = self.ethereum_verifier_single_snark()?;

        let verifier_creation_code = compile_solidity(verifier_solidity);

        let mut evm = Evm::default();
        let verifier_address = evm.create(verifier_creation_code);

        let calldata = encode_calldata(None, &proof, &publics[0]);

        let (_gas_cost, output) = evm.call(verifier_address, calldata);
        assert_eq!(output, [vec![0; 31], vec![1]].concat());

        log::info!("EVM verification done.");

        // Our Halo2 integration always has one instance column `publics[0]`
        // containing the public inputs.
        let publics: Vec<F> = publics[0]
            .clone()
            .into_iter()
            .map(|x| F::from_bytes_le(&x.to_repr()))
            .collect();

        Ok((proof, publics))
    }

    /// Generate a recursive proof that compresses one or more Poseidon proofs.
    /// These proofs can be verified directly on Ethereum.
    pub fn gkr_prove(&self
        
    )  {
      gkr_circuit_builder::convert_pil_to_gkr(self.analyzed.clone());
      panic!("gkr prove not implemented")
    }

     
    

    pub fn add_verification_key(&mut self, mut vkey: &mut dyn io::Read) {
        let vkey = match self.proof_type {
            ProofType::Poseidon | ProofType::SnarkSingle => {
                VerifyingKey::<G1Affine>::read::<&mut dyn io::Read, PowdrCircuit<F>>(
                    &mut vkey,
                    SerdeFormat::Processed,
                    self.analyzed.clone().into(),
                )
                .unwrap()
            }
            ProofType::SnarkAggr => VerifyingKey::<G1Affine>::read::<
                &mut dyn io::Read,
                aggregation::AggregationCircuit,
            >(&mut vkey, SerdeFormat::Processed, ())
            .unwrap(),
        };
        self.vkey = Some(vkey);
    }

    pub fn add_verification_app_key(&mut self, mut vkey: &mut dyn io::Read) {
        assert!(matches!(self.proof_type, ProofType::SnarkAggr));
        let vkey_app = VerifyingKey::<G1Affine>::read::<&mut dyn io::Read, PowdrCircuit<F>>(
            &mut vkey,
            SerdeFormat::Processed,
            self.analyzed.clone().into(),
        )
        .unwrap();
        self.vkey_app = Some(vkey_app);
    }

    pub fn verification_key(&self) -> Result<VerifyingKey<G1Affine>, String> {
        if let Some(vkey) = self.vkey.as_ref() {
            return Ok(vkey.clone());
        }

        match self.proof_type {
            ProofType::Poseidon | ProofType::SnarkSingle => self.generate_verification_key_single(),
            ProofType::SnarkAggr => self.generate_verification_key_aggr(),
        }
    }

    fn generate_verification_key_single(&self) -> Result<VerifyingKey<G1Affine>, String> {
        let circuit = PowdrCircuit::new(self.analyzed.clone(), &self.fixed);
        keygen_vk(&self.params, &circuit).map_err(|e| e.to_string())
    }

    fn generate_verification_key_aggr(&self) -> Result<VerifyingKey<G1Affine>, String> {
        let vkey_app = match self.vkey_app.as_ref() {
            Some(vkey_app) => vkey_app,
            None => {
                return Err("Aggregation verification key needs app verification key".to_string())
            }
        };

        let mut params_app = self.params.clone();
        params_app.downsize(degree_bits(self.analyzed.degree()));

        let protocol_app = compile(
            &params_app,
            vkey_app,
            Config::kzg().with_num_instance(vec![0]),
        );
        let empty_snark = aggregation::Snark::new_without_witness(protocol_app.clone());
        let agg_circuit =
            aggregation::AggregationCircuit::new_without_witness(&self.params, [empty_snark]);

        log::info!("Generating VK for compression snark...");
        keygen_vk(&self.params, &agg_circuit).map_err(|e| e.to_string())
    }

    fn verify_inner<
        E: EncodedChallenge<G1Affine>,
        TR: TranscriptReadBuffer<Cursor<Vec<u8>>, G1Affine, E>,
    >(
        &self,
        vkey: &VerifyingKey<G1Affine>,
        params: &ParamsKZG<Bn256>,
        proof: &[u8],
        instances: &[Vec<Fr>],
    ) -> Result<(), String> {
        let instances = instances
            .iter()
            .map(|instances| instances.as_slice())
            .collect_vec();

        let mut transcript = TR::init(Cursor::new(proof.to_owned()));

        let res = verify_proof::<_, VerifierGWC<_>, _, TR, _>(
            params.verifier_params(),
            vkey,
            AccumulatorStrategy::new(self.params.verifier_params()),
            &[instances.as_slice()],
            &mut transcript,
        )
        .map(|strategy| {
            <AccumulatorStrategy<'_, _> as VerificationStrategy<'_, _, VerifierGWC<_>>>::finalize(
                strategy,
            )
        });

        match res {
            Err(e) => Err(e.to_string()),
            Ok(valid) => match valid {
                true => Ok(()),
                false => Err("Proof is invalid".to_string()),
            },
        }
    }

    fn verify_common<
        E: EncodedChallenge<G1Affine>,
        TR: TranscriptReadBuffer<Cursor<Vec<u8>>, G1Affine, E>,
    >(
        &self,
        proof: &[u8],
        instances: &[Vec<F>],
    ) -> Result<(), String> {
        let instances = instances
            .iter()
            .map(|instance| {
                instance
                    .iter()
                    .map(|x| convert_field(*x))
                    .collect::<Vec<_>>()
            })
            .collect_vec();

        self.verify_inner::<_, TR>(self.vkey.as_ref().unwrap(), &self.params, proof, &instances)
    }

    pub fn verify_poseidon(&self, proof: &[u8], instances: &[Vec<F>]) -> Result<(), String> {
        assert!(matches!(self.proof_type, ProofType::Poseidon));
        self.verify_common::<_, aggregation::PoseidonTranscript<NativeLoader, _>>(proof, instances)
    }

    pub fn verify_snark(&self, proof: &[u8], instances: &[Vec<F>]) -> Result<(), String> {
        assert!(matches!(
            self.proof_type,
            ProofType::SnarkSingle | ProofType::SnarkAggr
        ));
        self.verify_common::<_, EvmTranscript<G1Affine, _, _, _>>(proof, instances)
    }

    fn assert_field_is_bn254() {
        if !matches!(F::known_field(), Some(KnownField::Bn254Field)) {
            panic!("powdr modulus doesn't match halo2 modulus. Make sure you are using Bn254");
        }
    }

    pub fn export_ethereum_verifier_snark(&self, output: &mut dyn io::Write) -> Result<(), String> {
        let verifier = match self.proof_type {
            ProofType::SnarkSingle => self.ethereum_verifier_single_snark(),
            ProofType::SnarkAggr => self.ethereum_verifier_aggr_snark(),
            _ => Err("Invalid proof type".to_string()),
        }?;

        output
            .write_all(verifier.as_bytes())
            .map_err(|e| e.to_string())?;
        Ok(())
    }

    pub fn ethereum_verifier_single_snark(&self) -> Result<String, String> {
        assert!(matches!(self.proof_type, ProofType::SnarkSingle));

        let vk = self.verification_key()?;
        let generator = SolidityGenerator::new(&self.params, &vk, BatchOpenScheme::Gwc19, 0);
        let verifier_solidity = generator.render().map_err(|e| e.to_string())?;

        Ok(verifier_solidity)
    }

    pub fn ethereum_verifier_aggr_snark(&self) -> Result<String, String> {
        assert!(matches!(self.proof_type, ProofType::SnarkAggr));

        let vk = self.verification_key()?;

        let verifier = aggregation::gen_aggregation_solidity_verifier(
            &self.params,
            &vk,
            aggregation::AggregationCircuit::num_instance(),
            aggregation::AggregationCircuit::accumulator_indices(),
        );

        Ok(verifier)
    }
}

fn gen_proof<
    C: Circuit<Fr>,
    E: EncodedChallenge<G1Affine>,
    TW: TranscriptWriterBuffer<Vec<u8>, G1Affine, E>,
>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: &[Vec<Fr>],
) -> Result<Vec<u8>, String> {
    let instances = instances
        .iter()
        .map(|instances| instances.as_slice())
        .collect_vec();
    let proof = {
        let mut transcript = TW::init(Vec::new());
        create_proof::<KZGCommitmentScheme<Bn256>, ProverGWC<_>, _, _, TW, _>(
            params,
            pk,
            &[circuit],
            &[instances.as_slice()],
            OsRng,
            &mut transcript,
        )
        .map_err(|e| e.to_string())?;
        transcript.finalize()
    };

    Ok(proof)
}

use std::{
    collections::BTreeMap,
    io::{self, Cursor},
    marker::PhantomData,
    path::PathBuf,
    sync::Arc,
};

use powdr_ast::analyzed::Analyzed;
use powdr_executor::witgen::WitgenCallback;
use powdr_number::{DegreeType, FieldElement};
use serde::{Deserialize, Serialize};
use split::select_machine_columns;

use crate::{Backend, BackendFactory, BackendOptions, Error, Proof};

mod split;

/// A composite verification key that contains a verification key for each machine separately.
#[derive(Serialize, Deserialize)]
struct CompositeVerificationKey {
    /// Verification key for each machine
    verification_keys: Vec<Vec<u8>>,
}

/// A composite proof that contains a proof for each machine separately.
#[derive(Serialize, Deserialize)]
struct CompositeProof {
    /// Map from machine name to proof
    proofs: Vec<Vec<u8>>,
}

pub(crate) struct CompositeBackendFactory<F: FieldElement, B: BackendFactory<F>> {
    factory: B,
    _marker: PhantomData<F>,
}

impl<F: FieldElement, B: BackendFactory<F>> CompositeBackendFactory<F, B> {
    pub(crate) const fn new(factory: B) -> Self {
        Self {
            factory,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldElement, B: BackendFactory<F>> BackendFactory<F> for CompositeBackendFactory<F, B> {
    fn create<'a>(
        &self,
        pil: Arc<Analyzed<F>>,
        fixed: Arc<Vec<(String, Vec<F>)>>,
        output_dir: Option<PathBuf>,
        setup: Option<&mut dyn std::io::Read>,
        verification_key: Option<&mut dyn std::io::Read>,
        verification_app_key: Option<&mut dyn std::io::Read>,
        backend_options: BackendOptions,
    ) -> Result<Box<dyn Backend<'a, F> + 'a>, Error> {
        if verification_app_key.is_some() {
            unimplemented!();
        }

        let pils = split::split_pil((*pil).clone());

        // Read the setup once to pass to all backends.
        let has_setup = setup.is_some();
        let setup_bytes = setup
            .map(|setup| {
                let mut setup_data = Vec::new();
                setup.read_to_end(&mut setup_data).unwrap();
                setup_data
            })
            .unwrap_or_default();

        // Read all verification keys (or create empty ones if none are provided)
        let has_verification_key = verification_key.is_some();
        let verification_keys = verification_key
            .map(|verification_key| bincode::deserialize_from(verification_key).unwrap())
            .unwrap_or(CompositeVerificationKey {
                verification_keys: vec![Vec::new(); pils.len()],
            })
            .verification_keys;

        let per_machine_data = pils
            .into_iter()
            .zip(verification_keys.into_iter())
            .map(|((machine_name, pil), verification_key)| {
                // Set up readers for the setup and verification key
                let mut setup_cursor = Cursor::new(&setup_bytes);
                let setup: Option<&mut dyn std::io::Read> = has_setup.then_some(&mut setup_cursor);

                let mut verification_key_cursor = Cursor::new(&verification_key);
                let verification_key: Option<&mut dyn std::io::Read> =
                    has_verification_key.then_some(&mut verification_key_cursor);

                let pil = Arc::new(pil);
                let output_dir = output_dir
                    .clone()
                    .map(|output_dir| output_dir.join(&machine_name));
                if let Some(ref output_dir) = output_dir {
                    std::fs::create_dir_all(output_dir)?;
                }
                let fixed = Arc::new(select_machine_columns(
                    &fixed,
                    pil.constant_polys_in_source_order()
                        .into_iter()
                        .map(|(symbol, _)| symbol),
                ));
                let backend = self.factory.create(
                    pil.clone(),
                    fixed,
                    output_dir,
                    setup,
                    verification_key,
                    // TODO: Handle verification_app_key
                    None,
                    backend_options.clone(),
                );
                backend.map(|backend| (machine_name.to_string(), MachineData { pil, backend }))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let machine_names = per_machine_data
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        Ok(Box::new(CompositeBackend {
            machine_data: per_machine_data.into_iter().collect(),
            machine_names,
        }))
    }

    fn generate_setup(&self, size: DegreeType, output: &mut dyn io::Write) -> Result<(), Error> {
        self.factory.generate_setup(size, output)
    }
}

struct MachineData<'a, F> {
    pil: Arc<Analyzed<F>>,
    backend: Box<dyn Backend<'a, F> + 'a>,
}

pub(crate) struct CompositeBackend<'a, F> {
    machine_data: BTreeMap<String, MachineData<'a, F>>,
    machine_names: Vec<String>,
}

// TODO: This just forwards to the backend for now. In the future this should:
// - Compute a verification key for each machine separately
// - Compute a proof for each machine separately
// - Verify all the machine proofs
// - Run additional checks on public values of the machine proofs
impl<'a, F: FieldElement> Backend<'a, F> for CompositeBackend<'a, F> {
    fn prove(
        &self,
        witness: &[(String, Vec<F>)],
        prev_proof: Option<Proof>,
        witgen_callback: WitgenCallback<F>,
    ) -> Result<Proof, Error> {
        if prev_proof.is_some() {
            unimplemented!();
        }

        let proof = CompositeProof {
            proofs: self
                .machine_names
                .iter()
                .map(|machine| {
                    let MachineData { pil, backend } = self.machine_data.get(machine).unwrap();
                    let witgen_callback = witgen_callback.clone().with_pil(pil.clone());

                    log::info!("== Proving machine: {}", machine);
                    log::debug!("PIL:\n{}", pil);

                    let witness = select_machine_columns(
                        witness,
                        pil.committed_polys_in_source_order()
                            .into_iter()
                            .map(|(symbol, _)| symbol),
                    );

                    backend.prove(&witness, None, witgen_callback)
                })
                .collect::<Result<_, _>>()?,
        };
        Ok(bincode::serialize(&proof).unwrap())
    }

    fn verify(&self, proof: &[u8], instances: &[Vec<F>]) -> Result<(), Error> {
        let proof: CompositeProof = bincode::deserialize(proof).unwrap();
        for (machine, machine_proof) in self.machine_names.iter().zip(proof.proofs) {
            let machine_data = self
                .machine_data
                .get(machine)
                .ok_or_else(|| Error::BackendError(format!("Unknown machine: {machine}")))?;
            machine_data.backend.verify(&machine_proof, instances)?;
        }
        Ok(())
    }

    fn export_setup(&self, output: &mut dyn io::Write) -> Result<(), Error> {
        // All backend are the same, just pick the first
        self.machine_data
            .values()
            .next()
            .unwrap()
            .backend
            .export_setup(output)
    }

    fn get_verification_key_bytes(&self) -> Result<Vec<u8>, Error> {
        let verification_key = CompositeVerificationKey {
            verification_keys: self
                .machine_names
                .iter()
                .map(|machine| {
                    let backend = self.machine_data.get(machine).unwrap().backend.as_ref();
                    backend.get_verification_key_bytes()
                })
                .collect::<Result<_, _>>()?,
        };
        Ok(bincode::serialize(&verification_key).unwrap())
    }

    fn export_ethereum_verifier(&self, _output: &mut dyn io::Write) -> Result<(), Error> {
        unimplemented!();
    }
}

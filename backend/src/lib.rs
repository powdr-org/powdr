#![deny(clippy::print_stdout)]

mod estark;
#[cfg(feature = "halo2")]
mod halo2;
#[cfg(feature = "plonky3")]
mod plonky3;

mod composite;
mod gkr;

use powdr_ast::analyzed::Analyzed;
use powdr_executor::{constant_evaluator::VariablySizedColumn, witgen::WitgenCallback};
use powdr_number::{DegreeType, FieldElement};
use std::{io, path::PathBuf, sync::Arc};
use strum::{Display, EnumString, EnumVariantNames};

#[derive(Clone, EnumString, EnumVariantNames, Display, Copy)]
pub enum BackendType {
    #[cfg(feature = "halo2")]
    #[strum(serialize = "halo2")]
    Halo2,
    #[cfg(feature = "halo2")]
    #[strum(serialize = "halo2-composite")]
    Halo2Composite,
    #[cfg(feature = "halo2")]
    #[strum(serialize = "halo2-mock")]
    Halo2Mock,
    #[cfg(feature = "halo2")]
    #[strum(serialize = "halo2-mock-composite")]
    Halo2MockComposite,
    #[cfg(feature = "estark-polygon")]
    #[strum(serialize = "estark-polygon")]
    EStarkPolygon,
    #[cfg(feature = "estark-polygon")]
    #[strum(serialize = "estark-polygon-composite")]
    EStarkPolygonComposite,
    #[strum(serialize = "estark-starky")]
    EStarkStarky,
    #[strum(serialize = "estark-starky-composite")]
    EStarkStarkyComposite,
    #[strum(serialize = "estark-dump")]
    EStarkDump,
    #[strum(serialize = "estark-dump-composite")]
    EStarkDumpComposite,
    #[cfg(feature = "plonky3")]
    #[strum(serialize = "plonky3")]
    Plonky3,
    #[cfg(feature = "plonky3")]
    #[strum(serialize = "plonky3-composite")]
    Plonky3Composite,
    #[cfg(feature = "gkr")]
    #[strum(serialize = "gkr")]
    Gkr,
}

pub type BackendOptions = String;
pub const DEFAULT_HALO2_OPTIONS: &str = "poseidon";
pub const DEFAULT_HALO2_MOCK_OPTIONS: &str = "";
pub const DEFAULT_ESTARK_OPTIONS: &str = "stark_gl";

impl BackendType {
    pub fn factory<T: FieldElement>(&self) -> Box<dyn BackendFactory<T>> {
        match self {
            #[cfg(feature = "halo2")]
            BackendType::Halo2 => Box::new(halo2::Halo2ProverFactory),
            #[cfg(feature = "halo2")]
            BackendType::Halo2Composite => Box::new(composite::CompositeBackendFactory::new(
                halo2::Halo2ProverFactory,
            )),
            #[cfg(feature = "halo2")]
            BackendType::Halo2Mock => Box::new(halo2::Halo2MockFactory),
            #[cfg(feature = "halo2")]
            BackendType::Halo2MockComposite => Box::new(composite::CompositeBackendFactory::new(
                halo2::Halo2MockFactory,
            )),
            #[cfg(feature = "estark-polygon")]
            BackendType::EStarkPolygon => Box::new(estark::polygon_wrapper::Factory),
            #[cfg(feature = "estark-polygon")]
            BackendType::EStarkPolygonComposite => Box::new(
                composite::CompositeBackendFactory::new(estark::polygon_wrapper::Factory),
            ),
            BackendType::EStarkStarky => Box::new(estark::starky_wrapper::Factory),
            BackendType::EStarkStarkyComposite => Box::new(
                composite::CompositeBackendFactory::new(estark::starky_wrapper::Factory),
            ),
            BackendType::EStarkDump => Box::new(estark::DumpFactory),
            BackendType::EStarkDumpComposite => {
                Box::new(composite::CompositeBackendFactory::new(estark::DumpFactory))
            }
            #[cfg(feature = "plonky3")]
            BackendType::Plonky3 => Box::new(plonky3::Factory),
            #[cfg(feature = "plonky3")]
            BackendType::Plonky3Composite => {
                Box::new(composite::CompositeBackendFactory::new(plonky3::Factory))
            }
            #[cfg(feature="gkr")]
            BackendType::Gkr => Box::new(gkr::GkrFactory)
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("input/output error")]
    IO(#[from] std::io::Error),
    #[error("the witness is empty")]
    EmptyWitness,
    #[error("the backend has no setup operations")]
    NoSetupAvailable,
    #[error("the backend does not implement proof verification")]
    NoVerificationAvailable,
    #[error("the backend does not support Ethereum onchain verification")]
    NoEthereumVerifierAvailable,
    #[error("the backend does not support proof aggregation")]
    NoAggregationAvailable,
    #[error("the backend does not support variable degrees")]
    NoVariableDegreeAvailable,
    #[error("internal backend error")]
    BackendError(String),
}

impl From<String> for Error {
    fn from(s: String) -> Self {
        Error::BackendError(s)
    }
}

pub type Proof = Vec<u8>;

/*
    Bellow are the public interface traits. They are implemented in this
    module, wrapping the traits implemented by each backend.
*/

/// Dynamic interface for a backend factory.
pub trait BackendFactory<F: FieldElement> {
    /// Create a new backend object.
    #[allow(clippy::too_many_arguments)]
    fn create(
        &self,
        pil: Arc<Analyzed<F>>,
        fixed: Arc<Vec<(String, VariablySizedColumn<F>)>>,
        output_dir: Option<PathBuf>,
        setup: Option<&mut dyn io::Read>,
        verification_key: Option<&mut dyn io::Read>,
        verification_app_key: Option<&mut dyn io::Read>,
        backend_options: BackendOptions,
    ) -> Result<Box<dyn Backend<F>>, Error>;

    /// Generate a new setup.
    fn generate_setup(&self, _size: DegreeType, _output: &mut dyn io::Write) -> Result<(), Error> {
        Err(Error::NoSetupAvailable)
    }
}

/// Dynamic interface for a backend.
pub trait Backend<F: FieldElement>: Send {
    /// Perform the proving.
    ///
    /// The backend uses the BackendOptions provided at creation time
    /// to potentially perform aggregation/compression.
    ///
    /// Returns the generated proof.
    fn prove(
        &self,
        witness: &[(String, Vec<F>)],
        prev_proof: Option<Proof>,
        witgen_callback: WitgenCallback<F>,
    ) -> Result<Proof, Error>;

    /// Verifies a proof.
    fn verify(&self, _proof: &[u8], _instances: &[Vec<F>]) -> Result<(), Error> {
        Err(Error::NoVerificationAvailable)
    }

    /// Exports the setup in a backend specific format. Can be used to create a
    /// new backend object of the same kind.
    fn export_setup(&self, _output: &mut dyn io::Write) -> Result<(), Error> {
        Err(Error::NoSetupAvailable)
    }

    /// Exports the verification key in a backend specific format. Can be used
    /// to create a new backend object of the same kind.
    fn export_verification_key(&self, output: &mut dyn io::Write) -> Result<(), Error> {
        let v = self.verification_key_bytes()?;
        log::info!("Verification key size: {} bytes", v.len());
        output
            .write_all(&v)
            .map_err(|_| Error::BackendError("Could not write verification key".to_string()))?;
        Ok(())
    }

    fn verification_key_bytes(&self) -> Result<Vec<u8>, Error> {
        Err(Error::NoVerificationAvailable)
    }

    /// Exports an Ethereum verifier.
    fn export_ethereum_verifier(&self, _output: &mut dyn io::Write) -> Result<(), Error> {
        Err(Error::NoEthereumVerifierAvailable)
    }
}

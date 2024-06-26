#![deny(clippy::print_stdout)]

mod estark;
#[cfg(feature = "halo2")]
mod halo2;

mod composite;

use powdr_ast::analyzed::Analyzed;
use powdr_executor::witgen::WitgenCallback;
use powdr_number::{DegreeType, FieldElement};
use std::{io, path::Path};
use strum::{Display, EnumString, EnumVariantNames};

#[derive(Clone, EnumString, EnumVariantNames, Display, Copy)]
pub enum BackendType {
    #[cfg(feature = "halo2")]
    #[strum(serialize = "halo2")]
    Halo2,
    #[cfg(feature = "halo2")]
    #[strum(serialize = "halo2-mock")]
    Halo2Mock,
    #[cfg(feature = "halo2")]
    #[strum(serialize = "halo2-mock-composite")]
    Halo2MockComposite,
    #[cfg(feature = "estark-polygon")]
    #[strum(serialize = "estark-polygon")]
    EStarkPolygon,
    #[strum(serialize = "estark-starky")]
    EStarkStarky,
    #[strum(serialize = "estark-dump")]
    EStarkDump,
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
            BackendType::Halo2Mock => Box::new(halo2::Halo2MockFactory),
            #[cfg(feature = "halo2")]
            BackendType::Halo2MockComposite => Box::new(composite::CompositeBackendFactory::new(
                halo2::Halo2MockFactory,
            )),
            #[cfg(feature = "estark-polygon")]
            BackendType::EStarkPolygon => Box::new(estark::polygon_wrapper::Factory),
            BackendType::EStarkStarky => Box::new(estark::starky_wrapper::Factory),
            BackendType::EStarkDump => Box::new(estark::DumpFactory),
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
    fn create<'a>(
        &self,
        pil: &'a Analyzed<F>,
        fixed: &'a [(String, Vec<F>)],
        output_dir: Option<&'a Path>,
        setup: Option<&mut dyn io::Read>,
        verification_key: Option<&mut dyn io::Read>,
        verification_app_key: Option<&mut dyn io::Read>,
        backend_options: BackendOptions,
    ) -> Result<Box<dyn Backend<'a, F> + 'a>, Error>;

    /// Generate a new setup.
    fn generate_setup(&self, _size: DegreeType, _output: &mut dyn io::Write) -> Result<(), Error> {
        Err(Error::NoSetupAvailable)
    }
}

/// Dynamic interface for a backend.
pub trait Backend<'a, F: FieldElement> {
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
    fn export_verification_key(&self, _output: &mut dyn io::Write) -> Result<(), Error> {
        Err(Error::NoVerificationAvailable)
    }

    /// Exports an Ethereum verifier.
    fn export_ethereum_verifier(&self, _output: &mut dyn io::Write) -> Result<(), Error> {
        Err(Error::NoEthereumVerifierAvailable)
    }
}

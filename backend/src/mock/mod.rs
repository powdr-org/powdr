use std::{collections::BTreeMap, io, marker::PhantomData, path::PathBuf, sync::Arc};

use connection_constraint_checker::{Connection, ConnectionConstraintChecker};
use evaluator::Machine;
use itertools::Itertools;
use polynomial_constraint_checker::PolynomialConstraintChecker;
use powdr_ast::analyzed::Analyzed;
use powdr_backend_utils::{machine_fixed_columns, machine_witness_columns};
use powdr_executor::{constant_evaluator::VariablySizedColumn, witgen::WitgenCallback};
use powdr_number::{DegreeType, FieldElement};

use crate::{Backend, BackendFactory, BackendOptions, Error, Proof};

mod connection_constraint_checker;
mod evaluator;
mod polynomial_constraint_checker;

pub(crate) struct MockBackendFactory<F: FieldElement> {
    _marker: PhantomData<F>,
}

impl<F: FieldElement> MockBackendFactory<F> {
    pub(crate) const fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }
}

impl<F: FieldElement> BackendFactory<F> for MockBackendFactory<F> {
    fn create(
        &self,
        pil: Arc<Analyzed<F>>,
        fixed: Arc<Vec<(String, VariablySizedColumn<F>)>>,
        _output_dir: Option<PathBuf>,
        _setup: Option<&mut dyn std::io::Read>,
        proving_key: Option<&mut dyn std::io::Read>,
        _verification_key: Option<&mut dyn std::io::Read>,
        verification_app_key: Option<&mut dyn std::io::Read>,
        backend_options: BackendOptions,
    ) -> Result<Box<dyn Backend<F>>, Error> {
        if proving_key.is_some() {
            unimplemented!();
        }
        if verification_app_key.is_some() {
            unimplemented!();
        }
        let connections = pil
            .identities
            .iter()
            .filter_map(|identity| identity.try_into().ok())
            .collect();
        let machine_to_pil = powdr_backend_utils::split_pil(&pil);
        let allow_warnings = match backend_options.as_str() {
            "allow_warnings" => true,
            "" => false,
            _ => panic!("Invalid backend option: {backend_options}"),
        };

        Ok(Box::new(MockBackend {
            allow_warnings,
            machine_to_pil,
            fixed,
            connections,
        }))
    }

    fn generate_setup(&self, _size: DegreeType, _output: &mut dyn io::Write) -> Result<(), Error> {
        unreachable!()
    }
}

pub(crate) struct MockBackend<F> {
    allow_warnings: bool,
    machine_to_pil: BTreeMap<String, Analyzed<F>>,
    fixed: Arc<Vec<(String, VariablySizedColumn<F>)>>,
    connections: Vec<Connection<F>>,
}

impl<F: FieldElement> Backend<F> for MockBackend<F> {
    fn prove(
        &self,
        witness: &[(String, Vec<F>)],
        prev_proof: Option<Proof>,
        _witgen_callback: WitgenCallback<F>,
    ) -> Result<Proof, Error> {
        if prev_proof.is_some() {
            unimplemented!();
        }

        let machines = self
            .machine_to_pil
            .iter()
            .map(|(machine, pil)| {
                let witness = machine_witness_columns(witness, pil, machine);
                let size = witness
                    .iter()
                    .map(|(_, witness)| witness.len())
                    .unique()
                    .exactly_one()
                    .expect("All witness columns of a machine must have the same size")
                    as DegreeType;
                let all_fixed = machine_fixed_columns(&self.fixed, pil);
                let fixed = all_fixed.get(&size).unwrap();

                (
                    machine.as_str(),
                    Machine::new(machine.clone(), witness, fixed, pil),
                )
            })
            .collect::<BTreeMap<_, _>>();

        let mut is_ok = true;
        for (_, machine) in machines.iter() {
            let result = PolynomialConstraintChecker::new(machine).check();
            result.log();
            is_ok &= !result.has_errors();
            if !self.allow_warnings {
                is_ok &= !result.has_warnings();
            }
        }

        ConnectionConstraintChecker {
            connections: &self.connections,
            machines,
        }
        .check();

        // TODO:
        // - Check later-stage witness

        match is_ok {
            true => Ok(Vec::new()),
            false => Err(Error::BackendError("Constraint check failed".to_string())),
        }
    }

    fn verify(&self, _proof: &[u8], _instances: &[Vec<F>]) -> Result<(), Error> {
        unreachable!()
    }

    fn export_setup(&self, _output: &mut dyn io::Write) -> Result<(), Error> {
        unreachable!()
    }

    fn verification_key_bytes(&self) -> Result<Vec<u8>, Error> {
        unreachable!()
    }

    fn export_ethereum_verifier(&self, _output: &mut dyn io::Write) -> Result<(), Error> {
        unimplemented!();
    }
}

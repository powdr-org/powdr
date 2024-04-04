pub mod estark;
mod json_exporter;

use std::{
    fs::File,
    io::{self, BufWriter, Write},
    path::Path,
};

use crate::{Backend, BackendFactory, Error, Proof};
use powdr_ast::analyzed::Analyzed;
use powdr_executor::witgen::WitgenCallback;
use powdr_number::FieldElement;
use serde::Serialize;

pub struct PilStarkCliFactory;

impl<F: FieldElement> BackendFactory<F> for PilStarkCliFactory {
    fn create<'a>(
        &self,
        analyzed: &'a Analyzed<F>,
        fixed: &'a [(String, Vec<F>)],
        output_dir: Option<&'a Path>,
        setup: Option<&mut dyn std::io::Read>,
        verification_key: Option<&mut dyn std::io::Read>,
    ) -> Result<Box<dyn crate::Backend<'a, F> + 'a>, Error> {
        let estark = estark::EStark::create(analyzed, fixed, setup, verification_key)?;

        Ok(Box::new(PilStarkCli { estark, output_dir }))
    }
}

pub struct PilStarkCli<'a, F: FieldElement> {
    estark: estark::EStark<F>,
    output_dir: Option<&'a Path>,
}

fn buffered_write_file<R>(
    path: &Path,
    do_write: impl FnOnce(&mut BufWriter<File>) -> R,
) -> Result<R, io::Error> {
    let mut writer = BufWriter::new(File::create(path)?);
    let result = do_write(&mut writer);
    writer.flush()?;

    Ok(result)
}

fn write_json_file<T: ?Sized + Serialize>(path: &Path, data: &T) -> Result<(), Error> {
    buffered_write_file(path, |writer| {
        serde_json::to_writer(writer, data).map_err(|e| e.to_string())
    })??;

    Ok(())
}

impl<'a, F: FieldElement> Backend<'a, F> for PilStarkCli<'a, F> {
    fn prove(
        &self,
        _witness: &[(String, Vec<F>)],
        prev_proof: Option<Proof>,
        // TODO: Implement challenges
        _witgen_callback: WitgenCallback<F>,
    ) -> Result<Proof, Error> {
        if prev_proof.is_some() {
            return Err(Error::NoAggregationAvailable);
        }

        // Write the files in the format expected by Polygon's zkevm-prover.
        if let Some(output_dir) = self.output_dir {
            // Write the constraints in the json format expected by the zkvm-prover:
            let contraints_path = output_dir.join("constraints.json");
            log::info!("Writing {}.", contraints_path.to_string_lossy());
            write_json_file(&contraints_path, self.estark.pil())?;

            // Write the stark info JSON.
            // TODO: the generated json is too different from the expected format,
            // fix this.
            /*let stark_info_path = output_dir.join("starkinfo.json");
            log::info!("Writing {}.", stark_info_path.to_string_lossy());
            write_json_file(&stark_info_path, self.estark.stark_info())?;*/

            // Write the stark struct JSON.
            let stark_struct_path = output_dir.join("starkstruct.json");
            log::info!("Writing {}.", stark_struct_path.to_string_lossy());
            write_json_file(&stark_struct_path, self.estark.stark_struct())?;

            // Write the verification key JSON.
            let ver_key_path = output_dir.join("verification_key.json");
            log::info!("Writing {}.", ver_key_path.to_string_lossy());
            write_json_file(&ver_key_path, &self.estark.verification_key())?;

            // Write the constants tree binary.
            let const_tree_path = output_dir.join("consttree.bin");
            log::info!("Writing {}.", const_tree_path.to_string_lossy());
            buffered_write_file(&const_tree_path, |writer| {
                self.estark.write_bin_const_tree(writer)
            })??;
        } else {
            // If we were going to call the prover-cpp, we could write the
            // constraints.json to a temporary directory in case no output_dir
            // is provided.
        }

        // TODO: actually use prover-cpp to generate the proof
        Ok(Vec::new())
    }
}

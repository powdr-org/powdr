mod json_exporter;

use crate::{BackendImpl, Proof};
use ast::analyzed::Analyzed;
use json::JsonValue;
use number::{write_polys_file, DegreeType, FieldElement};
use std::{
    fs,
    io::{self, BufWriter},
    path::Path,
};

pub struct PilcomCli {
    degree: DegreeType,
}

impl<T: FieldElement> BackendImpl<T> for PilcomCli {
    fn new(degree: DegreeType) -> Self {
        Self { degree }
    }

    fn prove(
        &self,
        pil: &Analyzed<T>,
        fixed: &[(&str, Vec<T>)],
        witness: &[(&str, Vec<T>)],
        prev_proof: Option<Proof>,
        output_dir: Option<&Path>,
    ) -> io::Result<Option<Proof>> {
        if prev_proof.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Aggregration is not implemented for Pilcom CLI backend",
            ));
        }

        if let Some(output_dir) = output_dir {
            write_constants_to_fs(fixed, output_dir, self.degree);
            log::info!("Written constants.");

            write_commits_to_fs(witness, output_dir, self.degree);
            log::info!("Written witness.");

            let json_out = json_exporter::export(pil);
            write_compiled_json_to_fs(&json_out, output_dir);
            log::info!("Written compiled PIL in Pilcom json format.");
        }

        Ok(None)
    }
}

fn write_constants_to_fs<T: FieldElement>(
    commits: &[(&str, Vec<T>)],
    output_dir: &Path,
    degree: DegreeType,
) {
    write_polys_file(
        &mut BufWriter::new(&mut fs::File::create(output_dir.join("constants.bin")).unwrap()),
        degree,
        commits,
    );
    log::info!("Wrote constants.bin.");
}

fn write_commits_to_fs<T: FieldElement>(
    commits: &[(&str, Vec<T>)],
    output_dir: &Path,
    degree: DegreeType,
) {
    write_polys_file(
        &mut BufWriter::new(&mut fs::File::create(output_dir.join("commits.bin")).unwrap()),
        degree,
        commits,
    );
    log::info!("Wrote commits.bin.");
}

fn write_compiled_json_to_fs(json_out: &JsonValue, output_dir: &Path) {
    json_out
        .write(&mut fs::File::create(output_dir.join("constraints.json")).unwrap())
        .unwrap();
    log::info!("Wrote constraints.json.");
}

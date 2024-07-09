//! Numerical types used across powdr

#![deny(clippy::print_stdout)]

#[macro_use]
mod macros;
mod bn254;
mod goldilocks;
mod serialize;
mod traits;

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
pub use serialize::{
    buffered_write_file, read_polys_csv_file, write_polys_csv_file, CsvRenderMode, ReadWrite,
};

pub use bn254::Bn254Field;
pub use goldilocks::GoldilocksField;
pub use traits::KnownField;

pub use ibig::{IBig as BigInt, UBig as BigUint};
pub use traits::{FieldElement, LargeInt};
/// An arbitrary precision big integer, to be used as a last recourse

/// The type of polynomial degrees and indices into columns.
pub type DegreeType = u64;

/// Returns Some(i) if n == 2**i and None otherwise.
pub fn log2_exact(n: BigUint) -> Option<usize> {
    n.trailing_zeros()
        .filter(|zeros| n == (BigUint::from(1u32) << zeros))
}

#[derive(Serialize, Deserialize)]
/// Like Columns, but each column can exist in multiple sizes
pub struct VariablySizedColumns<F> {
    /// Maps each column name to a (size -> values) map
    columns: Vec<(String, BTreeMap<usize, Vec<F>>)>,
}

#[derive(Debug)]
pub struct HasMultipleSizesError;

impl<F: Clone> VariablySizedColumns<F> {
    /// Create a view where each column has a single size. Fails if any column has multiple sizes.
    pub fn get_only_size(&self) -> Result<Vec<(String, &Vec<F>)>, HasMultipleSizesError> {
        self.columns
            .iter()
            .map(|(name, column_by_size)| {
                if column_by_size.len() != 1 {
                    return Err(HasMultipleSizesError);
                }
                let values = column_by_size.values().next().unwrap();
                Ok((name.clone(), values))
            })
            .collect()
    }

    /// Like get_only_size, but clones the values.
    pub fn get_only_size_cloned(&self) -> Result<Vec<(String, Vec<F>)>, HasMultipleSizesError> {
        self.get_only_size()?
            .into_iter()
            .map(|(name, values)| Ok((name, values.clone())))
            .collect()
    }

    pub fn len(&self) -> usize {
        self.columns.len()
    }

    pub fn is_empty(&self) -> bool {
        self.columns.is_empty()
    }
}

impl<T: Iterator<Item = (String, BTreeMap<usize, Vec<F>>)>, F: Clone> From<T>
    for VariablySizedColumns<F>
{
    fn from(iter: T) -> Self {
        Self {
            columns: iter.collect(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use test_log::test;

    #[test]
    fn log2_exact_function() {
        assert_eq!(log2_exact(0u32.into()), None);
        assert_eq!(log2_exact(1u32.into()), Some(0));
        assert_eq!(log2_exact(2u32.into()), Some(1));
        assert_eq!(log2_exact(4u32.into()), Some(2));
        assert_eq!(log2_exact(BigUint::from(1u32) << 300), Some(300));
        assert_eq!(log2_exact(17u32.into()), None);
    }
}

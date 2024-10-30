//! Numerical types used across powdr

#![deny(clippy::print_stdout)]

#[macro_use]
mod macros;
mod baby_bear;
mod bn254;
mod goldilocks;
mod koala_bear;
mod mersenne31;
#[macro_use]
mod plonky3_macros;
mod data_structures;
mod serialize;
mod traits;

pub use data_structures::{
    get_uniquely_sized, get_uniquely_sized_cloned, VariablySizedColumn, WitgenCallback,
};

pub use serialize::{
    buffered_write_file, read_polys_csv_file, write_polys_csv_file, CsvRenderMode, ReadWrite,
};

pub use baby_bear::BabyBearField;
pub use bn254::Bn254Field;
pub use goldilocks::GoldilocksField;
pub use koala_bear::KoalaBearField;
pub use mersenne31::Mersenne31Field;
pub use traits::{FieldSize, KnownField};

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

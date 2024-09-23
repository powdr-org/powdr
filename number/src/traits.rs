use std::{fmt, hash::Hash, ops::*, str::FromStr};

use num_traits::{ConstOne, ConstZero, One, Zero};
use schemars::JsonSchema;
use serde::{de::DeserializeOwned, Deserialize, Serialize};

use crate::{BigUint, DegreeType};

/// A fixed-width integer type
pub trait LargeInt:
    Copy
    + Send
    + Sync
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
    + From<u64>
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
    + BitOrAssign
    + BitAndAssign
    + AddAssign
    + Add<Output = Self>
    + fmt::Display
    + fmt::Debug
    + Copy
    + Not<Output = Self>
    + Shl<usize, Output = Self>
    + Shr<usize, Output = Self>
    + BitXor<Output = Self>
    + BitAnd<Output = Self>
    + Zero
    + ConstZero
    + fmt::LowerHex
{
    /// Number of bits of this base type. Not to be confused with the number of bits
    /// of the field elements!
    const NUM_BITS: usize;
    fn to_arbitrary_integer(self) -> BigUint;
    /// Number of bits required to encode this particular number.
    fn num_bits(&self) -> usize;

    /// Returns the constant one.
    /// We are not implementing num_traits::One because it also requires multiplication.
    fn one() -> Self;

    /// Checks if the number is one.
    fn is_one(&self) -> bool;

    /// Tries to convert to u64.
    ///
    /// Returns None if value is out of u64 range.
    fn try_into_u64(&self) -> Option<u64>;

    /// Tries to convert to u32.
    ///
    /// Returns None if value is out of u32 range.
    fn try_into_u32(&self) -> Option<u32>;

    /// Creates a LargeInt from a hex string.
    /// Panics on failure - intended for testing.
    fn from_hex(s: &str) -> Self;
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub enum KnownField {
    BabyBearField,
    Mersenne31Field,
    GoldilocksField,
    Bn254Field,
}

/// A field element
pub trait FieldElement:
    'static
    + Sync
    + Send
    + Default
    + Copy
    + PartialEq
    + Eq
    + Send
    + Sync
    + PartialOrd
    + Ord
    + Hash
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Mul<Output = Self>
    + Div<Output = Self>
    + Neg<Output = Self>
    + Zero
    + ConstZero
    + ConstOne
    + One
    + fmt::Display
    + fmt::Debug
    + From<Self::Integer>
    + From<crate::BigUint>
    + FromStr<Err = String>
    + From<u32>
    + From<u64>
    + From<i32>
    + From<i64>
    + From<bool>
    + fmt::LowerHex
    + Serialize
    + DeserializeOwned
    + JsonSchema
{
    /// The underlying fixed-width integer type
    type Integer: LargeInt;
    /// Number of bits required to represent elements of this field.
    const BITS: u32;

    fn to_degree(&self) -> DegreeType;

    fn to_integer(&self) -> Self::Integer;

    fn to_arbitrary_integer(&self) -> BigUint {
        self.to_integer().to_arbitrary_integer()
    }

    fn modulus() -> Self::Integer;

    fn pow(self, exponent: Self::Integer) -> Self;

    fn to_bytes_le(&self) -> Vec<u8>;

    fn from_bytes_le(bytes: &[u8]) -> Self;

    fn from_str_radix(s: &str, radix: u32) -> Result<Self, String>;

    /// Only converts the value to a field element if it is less than the modulus.
    fn checked_from(value: BigUint) -> Option<Self>;

    /// Returns true if the value is in the "lower half" of the field,
    /// i.e. the value <= (modulus() - 1) / 2
    fn is_in_lower_half(&self) -> bool;

    /// If the field is a known field (as listed in the `KnownField` enum), returns the field variant.
    fn known_field() -> Option<KnownField>;

    /// Tries to convert to i32.
    ///
    /// As conventional, negative values are in relation to 0 in the field.
    /// Returns None if out of the range [0 - 2^31, 2^31).
    fn try_into_i32(&self) -> Option<i32>;
}

#[cfg(test)]
pub fn int_from_hex_str<T: FieldElement>(s: &str) -> T::Integer {
    T::Integer::from_hex(s)
}

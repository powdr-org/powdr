use powdr_number::{FieldElement, LargeInt, Mersenne31Field};
use stwo_prover::core::fields::m31::M31;

pub trait BaseFieldElementMap: FieldElement {
    type StwoField;

    fn into_stwo_field(self) -> Self::StwoField;

    fn from_stwo_m31(stwo_m31: M31) -> Self;
}

impl BaseFieldElementMap for Mersenne31Field {
    fn into_stwo_m31(self) -> M31 {
        M31::from(self.to_integer().try_into_u32().unwrap())
    }

    fn from_stwo_m31(stwo_m31: M31) -> Self {
        Self::from(stwo_m31.0)
    }
}

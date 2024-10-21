/// Create a clap parser for an enum which implements `strum::{EnumString, EnumVariantNames}`
#[macro_export]
macro_rules! clap_enum_variants {
    ($e: ty) => {{
        use clap::builder::TypedValueParser;
        use strum::VariantNames;
        clap::builder::PossibleValuesParser::new(<$e>::VARIANTS).map(|s| s.parse::<$e>().unwrap())
    }};
}

/// Call a function using a given field generic
#[macro_export]
macro_rules! call_with_field {
    ($function:ident::<$field:ident>($($args:expr),*) ) => {
        match $field {
            FieldArgument::Bb => $function::<BabyBearField>($($args),*),
            FieldArgument::Kb => $function::<KoalaBearField>($($args),*),
            FieldArgument::Gl => $function::<GoldilocksField>($($args),*),
            // FieldArgument::Bn254 => $function::<Bn254Field>($($args),*),
        }
    };
}

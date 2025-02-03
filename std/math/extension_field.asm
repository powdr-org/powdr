use std::field::known_field;
use std::field::KnownField;

use std::array::len;
use std::check::panic;

/// Whether we need to operate on an extension field (because the base field is too small).
let needs_extension: -> bool = || required_extension_size() > 1;

/// How many field elements / field extensions are recommended for the current base field.
let required_extension_size: -> int = || match known_field() {
    Option::Some(KnownField::Goldilocks) => 2,
    Option::Some(KnownField::BN254) => 1,
    Option::Some(KnownField::BabyBear) => 4,
    Option::Some(KnownField::KoalaBear) => 4,
    Option::Some(KnownField::M31) => 4,
    None => panic("The permutation/lookup argument is not implemented for the current field!")
};

/// Wrapper around T, Fp2<T> and Fp4<T> to abstract which extension field is used (if any).
/// Once PIL supports traits, we can remove this type and the functions below.
enum Ext<T> {
    Fp(T),
    Fp2(std::math::fp2::Fp2<T>),
    Fp4(std::math::fp4::Fp4<T>)
}

let<T: Add> add_ext: Ext<T>, Ext<T> -> Ext<T> = |a, b| match (a, b) {
    (Ext::Fp(aa), Ext::Fp(bb)) => Ext::Fp(aa + bb),
    (Ext::Fp2(aa), Ext::Fp2(bb)) => Ext::Fp2(std::math::fp2::add_ext(aa, bb)),
    (Ext::Fp4(aa), Ext::Fp4(bb)) => Ext::Fp4(std::math::fp4::add_ext(aa, bb)),
    _ => panic("Operands have different types")
};

let<T: Sub> sub_ext: Ext<T>, Ext<T> -> Ext<T> = |a, b| match (a, b) {
    (Ext::Fp(aa), Ext::Fp(bb)) => Ext::Fp(aa - bb),
    (Ext::Fp2(aa), Ext::Fp2(bb)) => Ext::Fp2(std::math::fp2::sub_ext(aa, bb)),
    (Ext::Fp4(aa), Ext::Fp4(bb)) => Ext::Fp4(std::math::fp4::sub_ext(aa, bb)),
    _ => panic("Operands have different types")
};

let<T: Add + FromLiteral + Mul> mul_ext: Ext<T>, Ext<T> -> Ext<T> = |a, b| match (a, b) {
    (Ext::Fp(aa), Ext::Fp(bb)) => Ext::Fp(aa * bb),
    (Ext::Fp2(aa), Ext::Fp2(bb)) => Ext::Fp2(std::math::fp2::mul_ext(aa, bb)),
    (Ext::Fp4(aa), Ext::Fp4(bb)) => Ext::Fp4(std::math::fp4::mul_ext(aa, bb)),
    _ => panic("Operands have different types")
};

let eval_ext: Ext<expr> -> Ext<fe> = query |a| match a {
    Ext::Fp(aa) => Ext::Fp(std::prover::eval(aa)),
    Ext::Fp2(aa) => Ext::Fp2(std::math::fp2::eval_ext(aa)),
    Ext::Fp4(aa) => Ext::Fp4(std::math::fp4::eval_ext(aa)),
};

let inv_ext: Ext<fe> -> Ext<fe> = query |a| match a {
    Ext::Fp(aa) => Ext::Fp(std::math::ff::inv_field(aa)),
    Ext::Fp2(aa) => Ext::Fp2(std::math::fp2::inv_ext(aa)),
    Ext::Fp4(aa) => Ext::Fp4(std::math::fp4::inv_ext(aa)),
};

let<T> unpack_ext_array: Ext<T> -> T[] = |a| match a {
    Ext::Fp(aa) => [aa],
    Ext::Fp2(aa) => std::math::fp2::unpack_ext_array(aa),
    Ext::Fp4(aa) => std::math::fp4::unpack_ext_array(aa),
};

let next_ext: Ext<expr> -> Ext<expr> = |a| match a {
    Ext::Fp(aa) => Ext::Fp(aa'),
    Ext::Fp2(aa) => Ext::Fp2(std::math::fp2::next_ext(aa)),
    Ext::Fp4(aa) => Ext::Fp4(std::math::fp4::next_ext(aa)),
};

let<T: FromLiteral> from_base: T -> Ext<T> = |x| match required_extension_size() {
    1 => Ext::Fp(x),
    2 => Ext::Fp2(std::math::fp2::from_base(x)),
    4 => Ext::Fp4(std::math::fp4::from_base(x)),
    _ => panic("Expected 1, 2, or 4")
};

let<T> from_array: T[] -> Ext<T> = |arr| match len(arr) {
    1 => Ext::Fp(arr[0]),
    2 => Ext::Fp2(std::math::fp2::from_array(arr)),
    4 => Ext::Fp4(std::math::fp4::Fp4::Fp4(arr[0], arr[1], arr[2], arr[3])),
    _ => panic("Expected 1, 2, or 4")
};

let constrain_eq_ext: Ext<expr>, Ext<expr> -> Constr[] = |a, b| match (a, b) {
    (Ext::Fp(aa), Ext::Fp(bb)) => [aa = bb],
    (Ext::Fp2(aa), Ext::Fp2(bb)) => std::math::fp2::constrain_eq_ext(aa, bb),
    (Ext::Fp4(aa), Ext::Fp4(bb)) => std::math::fp4::constrain_eq_ext(aa, bb),
    _ => panic("Operands have different types")
};
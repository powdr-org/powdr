use std::array::len;
use std::array::fold;
use std::check::assert;
use std::check::panic;
use std::convert::fe;
use std::convert::int;
use std::convert::expr;
use std::field::known_field;
use std::field::KnownField;
use std::math::ff::inv_field;
use std::math::extension_field::needs_extension;
use std::prover::eval;

/// Corresponding Sage code to test irreducibility
/// BabyBear = 0x78000001
/// M31 = 0x7fffffff
/// BN254 = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
/// GL = 0xffffffff00000001
/// 
/// fields = [BabyBear, M31, BN254, GL]
/// 
/// def check_irreducibility(field):
///     F = GF(field)
///     R.<x> = PolynomialRing(F)
///     f = x^2 - 11
///     return f"Field: {field}\nIs irreducible: {f.is_irreducible()}"
/// 
/// print("\n".join(map(check_irreducibility, fields)))

/// An element of the extension field over the implied base field (which has to be one
/// of the field elements: Goldilocks, BN254, BabyBear, M31) relative to the irreducible polynomial X^2 - 11,
/// where Fp2(a0, a1) is interpreted as a0 + a1 * X.
/// T is assumed to either be fe, expr or any other object whose algebraic operations
/// are compatible with fe.
enum Fp2<T> {
    Fp2(T, T)
}

/// Converts a base field element to an extension field element
let<T: FromLiteral> from_base: T -> Fp2<T> = |x| Fp2::Fp2(x, 0);

/// Extension field addition
let<T: Add> add_ext: Fp2<T>, Fp2<T> -> Fp2<T> = |a, b| match (a, b) {
    (Fp2::Fp2(a0, a1), Fp2::Fp2(b0, b1)) => Fp2::Fp2(
        a0 + b0,
        a1 + b1
    )
};

/// Extension field subtraction
let<T: Sub> sub_ext: Fp2<T>, Fp2<T> -> Fp2<T> = |a, b| match (a, b) {
    (Fp2::Fp2(a0, a1), Fp2::Fp2(b0, b1)) => Fp2::Fp2(
        a0 - b0,
        a1 - b1
    )
};

/// Extension field multiplication
let<T: Add + FromLiteral + Mul> mul_ext: Fp2<T>, Fp2<T> -> Fp2<T> = |a, b| match (a, b) {
    (Fp2::Fp2(a0, a1), Fp2::Fp2(b0, b1)) => Fp2::Fp2(
        // Multiplication modulo the polynomial x^2 - 11. We'll use the fact
        // that x^2 == 11 (mod x^2 - 11), so:
        // (a0 + a1 * x) * (b0 + b1 * x) = a0 * b0 + 11 * a1 * b1 + (a1 * b0 + a0 * b1) * x (mod x^2 - 11)
        a0 * b0 + 11 * a1 * b1,
        a1 * b0 + a0 * b1
    )
};

/// Extension field squaring
/// This implementation yields a shorter expression than `mul_ext(a, a)` and should be preferred
/// when squaring expressions many times.
let<T: Add + FromLiteral + Mul> square_ext: Fp2<T> -> Fp2<T> = |a| match (a) {
    Fp2::Fp2(a0, a1) => Fp2::Fp2(
        a0 * a0 + 11 * a1 * a1,
        2 * a1 * a0
    )
};

/// Computes the power operation on an extension field element.
let<T: Add + Mul + FromLiteral> pow_ext: Fp2<T>, int -> Fp2<T> = |x, i| match i {
    0 => from_base(1),
    1 => x,
    _ => {
        let z = square_ext(pow_ext(x, i / 2));
        if i % 2 == 0 {
            z
        } else {
            mul_ext(z, x)
        }
    }
};


/// Converts an Fp2<expr> into an Fp2<fe>
let eval_ext: Fp2<expr> -> Fp2<fe> = query |a| match a {
    Fp2::Fp2(a0, a1) => Fp2::Fp2(eval(a0), eval(a1))
};

/// Converts an Fp2<fe> into an Fp2<expr>
let expr_ext: Fp2<fe> -> Fp2<expr> = |a| match a {
    Fp2::Fp2(a0, a1) => Fp2::Fp2(expr(a0), expr(a1))
};

/// Extension field equality
let eq_ext: Fp2<fe>, Fp2<fe> -> bool = |a, b| match (a, b) {
    (Fp2::Fp2(a0, a1), Fp2::Fp2(b0, b1)) => (a0 == b0) && (a1 == b1)
};

/// Returns constraints that two extension field elements are equal
let constrain_eq_ext: Fp2<expr>, Fp2<expr> -> Constr[] = |a, b| match (a, b) {
    (Fp2::Fp2(a0, a1), Fp2::Fp2(b0, b1)) => [a0 = b0, a1 = b1]
};

/// Extension field inversion
let inv_ext: Fp2<fe> -> Fp2<fe> = |a| match a {
    // The inverse of (a0, a1) is a point (b0, b1) such that:
    // (a0 + a1 * x) (b0 + b1 * x) = 1 (mod x^2 - 11)
    // Multiplying out and plugging in x^2 = 11 yields the following system of linear equations:
    // a0 * b0 + 11 * a1 * b1 = 1
    // a1 * b0 + a0 * b1 = 0
    // Solving for (b0, b1) yields:
    Fp2::Fp2(a0, a1) => {
        let factor = inv_field(11 * a1 * a1 - a0 * a0);
        Fp2::Fp2(-a0 * factor, a1 * factor)
    }
};

/// Applies the next operator to both components of the extension field element
let next_ext: Fp2<expr> -> Fp2<expr> = |a| match a {
    Fp2::Fp2(a0, a1) => Fp2::Fp2(a0', a1')
};

/// Returns the two components of the extension field element as a tuple
let<T> unpack_ext: Fp2<T> -> (T, T) = |a| match a {
    Fp2::Fp2(a0, a1) => (a0, a1)
};

/// Returns the two components of the extension field element as an array
let<T> unpack_ext_array: Fp2<T> -> T[] = |a| match a {
    Fp2::Fp2(a0, a1) => [a0, a1]
};

/// Constructs an extension field element `a0 + a1 * X` from either `[a0, a1]` or `[a0]` (setting `a1`to zero in that case)
let<T> from_array: T[] -> Fp2<T> = |arr| match len(arr) {
    2 => Fp2::Fp2(arr[0], arr[1]),
    _ => panic("Expected array of length 2")
};

mod test {
    use super::Fp2;
    use super::from_base;
    use super::add_ext;
    use super::sub_ext;
    use super::mul_ext;
    use super::square_ext;
    use super::pow_ext;
    use super::inv_ext;
    use super::eq_ext;
    use std::check::assert;
    use std::array::map;

    let test_add = || {
        let test_add = |a, b, c| assert(eq_ext(add_ext(a, b), c), || "Wrong addition result");

        // Test adding 0
        let _ = test_add(from_base(0), from_base(0), from_base(0));
        let _ = test_add(Fp2::Fp2(123, 1234), from_base(0), Fp2::Fp2(123, 1234));
        let _ = test_add(from_base(0), Fp2::Fp2(123, 1234), Fp2::Fp2(123, 1234));

        // Add arbitrary elements
        let _ = test_add(Fp2::Fp2(123, 1234), Fp2::Fp2(567, 5678), Fp2::Fp2(690, 6912));
        test_add(Fp2::Fp2(-1, -1), Fp2::Fp2(3, 4), Fp2::Fp2(2, 3))
    };

    let test_sub = || {
        let test_sub = |a, b, c| assert(eq_ext(sub_ext(a, b), c), || "Wrong subtraction result");

        // Test subtracting 0
        let _ = test_sub(from_base(0), from_base(0), from_base(0));
        let _ = test_sub(Fp2::Fp2(123, 1234), from_base(0), Fp2::Fp2(123, 1234));

        // Subtract arbitrary elements
        let _ = test_sub(Fp2::Fp2(123, 1234), Fp2::Fp2(567, 5678), Fp2::Fp2(123 - 567, 1234 - 5678));
        test_sub(Fp2::Fp2(-1, -1), Fp2::Fp2(0x78000000, 1), Fp2::Fp2(-0x78000000 - 1, -2))
    };

    let test_mul = || {
        let test_mul = |a, b, c| assert(eq_ext(mul_ext(a, b), c), || "Wrong multiplication result");

        // Test multiplication by 1
        let _ = test_mul(from_base(1), from_base(1), from_base(1));
        let _ = test_mul(Fp2::Fp2(123, 1234), from_base(1), Fp2::Fp2(123, 1234));
        let _ = test_mul(from_base(1), Fp2::Fp2(123, 1234), Fp2::Fp2(123, 1234));

        // Test multiplication by 0
        let _ = test_mul(Fp2::Fp2(123, 1234), from_base(0), from_base(0));
        let _ = test_mul(from_base(0), Fp2::Fp2(123, 1234), from_base(0));

        // Multiply arbitrary elements
        let _ = test_mul(Fp2::Fp2(123, 1234), Fp2::Fp2(567, 5678), Fp2::Fp2(77142913, 1398072));

        // Multiplication with field overflow
        test_mul(Fp2::Fp2(-1, -2), Fp2::Fp2(-3, 4), Fp2::Fp2(3 - 11 * 8, 6 - 4))
    };

    let test_square = || {
        // Tests consistency with mul_ext
        let test_square = |a| assert(eq_ext(mul_ext(a, a), square_ext(a)), || "Wrong squaring result");

        test_square(from_base(0));
        test_square(from_base(1));
        test_square(from_base(2));
        test_square(Fp2::Fp2(1, 1));
        test_square(Fp2::Fp2(123, 1234));
        test_square(Fp2::Fp2(-1, -2));
    };

    let test_inverse = || {
        let test_elements = [
            from_base(1),
            Fp2::Fp2(123, 1234),
            Fp2::Fp2(-1, 500)
        ];

        map(test_elements, |x| {
            let mul_with_inverse = mul_ext(x, inv_ext(x));

            assert(eq_ext(mul_with_inverse, from_base(1)), || "Should be 1")
        })
    };

    let test_pow = || {
        let test_pow = |a, i, b| assert(eq_ext(pow_ext(a, i), b), || "Wrong power result");

        test_pow(from_base(0), 0, from_base(1));
        test_pow(from_base(1), 0, from_base(1));
        test_pow(Fp2::Fp2(123, 1234), 0, from_base(1));

        test_pow(from_base(9), 1, from_base(9));
        test_pow(Fp2::Fp2(123, 1234), 1, Fp2::Fp2(123, 1234));

        test_pow(from_base(9), 2, from_base(9 * 9));
        test_pow(Fp2::Fp2(123, 1234), 2, Fp2::Fp2(16765445, 303564));

        test_pow(from_base(9), 20, from_base(std::convert::fe(12157665459056928801 % std::field::modulus())));
    };
}

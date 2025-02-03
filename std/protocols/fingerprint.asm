use std::array;
use std::array::len;
use std::math::extension_field::Ext;
use std::math::extension_field::add_ext;
use std::math::extension_field::mul_ext;
use std::math::extension_field::from_base;
use std::math::extension_field::eval_ext;
use std::check::assert;

/// Maps [x_1, x_2, ..., x_n] to its Read-Solomon fingerprint, using a challenge alpha: $\sum_{i=1}^n alpha**{(i - 1)} * x_i$
/// To generate an expression that computes the fingerprint, use `fingerprint_inter` instead.
/// Note that alpha is passed as an expressions, so that it is only evaluated if needed (i.e., if len(expr_array) > 1).
let fingerprint: fe[], Ext<expr> -> Ext<fe> = query |expr_array, alpha| if array::len(expr_array) == 1 {
    // No need to evaluate `alpha` (which would be removed by the optimizer).
    from_base(expr_array[0])
} else {
    fingerprint_impl(expr_array, eval_ext(alpha), 0)
};

let fingerprint_impl: fe[], Ext<fe>, int -> Ext<fe> = query |expr_array, alpha, i| if i == len(expr_array) - 1 {
    // Base case: Return the last element
    from_base(expr_array[i])
} else {

    // Recursively compute the fingerprint as expr_array[i] + alpha * fingerprint(expr_array[i + 1:], alpha)
    let intermediate_fingerprint = fingerprint_impl(expr_array, alpha, i + 1);
    add_ext(from_base(expr_array[i]), mul_ext(alpha, intermediate_fingerprint))
};

/// Like `fingerprint`, but "materializes" the intermediate results as intermediate columns.
/// Inlining them would lead to an exponentially-sized expression.
let fingerprint_inter: expr[], Ext<expr> -> Ext<expr> = |expr_array, alpha| if len(expr_array) == 1 {
    // Base case
    from_base(expr_array[0])
} else {
    assert(len(expr_array) > 1, || "fingerprint requires at least one element");

    // Recursively compute the fingerprint as expr_array[0] + alpha * fingerprint(expr_array[1:], alpha)
    let intermediate_fingerprint = match fingerprint_inter(array::sub_array(expr_array, 1, len(expr_array) - 1), alpha) {
        Ext::Fp(a) => {
            let intermediate_fingerprint: inter = a;
            Ext::Fp(intermediate_fingerprint)
        },
        Ext::Fp2(std::math::fp2::Fp2::Fp2(a0, a1)) => {
            let intermediate_fingerprint_0: inter = a0;
            let intermediate_fingerprint_1: inter = a1;
            Ext::Fp2(std::math::fp2::Fp2::Fp2(intermediate_fingerprint_0, intermediate_fingerprint_1))
        },
        Ext::Fp4(std::math::fp4::Fp4::Fp4(a0, a1, a2, a3)) => {
            let intermediate_fingerprint_0: inter = a0;
            let intermediate_fingerprint_1: inter = a1;
            let intermediate_fingerprint_2: inter = a2;
            let intermediate_fingerprint_3: inter = a3;
            Ext::Fp4(std::math::fp4::Fp4::Fp4(intermediate_fingerprint_0, intermediate_fingerprint_1, intermediate_fingerprint_2, intermediate_fingerprint_3))
        }
    };
    add_ext(from_base(expr_array[0]), mul_ext(alpha, intermediate_fingerprint))
};

/// Maps [id, x_1, x_2, ..., x_n] to its Read-Solomon fingerprint, using a challenge alpha: $\sum_{i=1}^n alpha**{(n - i)} * x_i$
let fingerprint_with_id: fe, fe[], Ext<expr> -> Ext<fe> = query |id, expr_array, alpha| fingerprint([id] + expr_array, alpha);

/// Maps [id, x_1, x_2, ..., x_n] to its Read-Solomon fingerprint, using a challenge alpha: $\sum_{i=1}^n alpha**{(n - i)} * x_i$
let fingerprint_with_id_inter: expr, expr[], Ext<expr> -> Ext<expr> = |id, expr_array, alpha| fingerprint_inter([id] + expr_array, alpha);

mod test {
    use super::fingerprint;
    use std::check::assert;
    use std::math::extension_field::Ext;
    use std::math::extension_field::from_base;
    use std::check::panic;

    /// Helper function to assert that the fingerprint of a tuple is equal to the expected value.
    let assert_fingerprint_equal: fe[], expr, fe -> () = query |tuple, challenge, expected| {
        let result = fingerprint(tuple, from_base(challenge));
        match result {
            Ext::Fp(actual) => assert(expected == actual, || "expected != actual"),
            Ext::Fp2(std::math::fp2::Fp2::Fp2(actual, zero)) => {
                assert(zero == 0, || "Returned an extension field element");
                assert(expected == actual, || "expected != actual");
            },
            Ext::Fp4(std::math::fp4::Fp4::Fp4(actual, zero1, zero2, zero3)) => {
                assert(zero1 == 0, || "Returned an extension field element");
                assert(zero2 == 0, || "Returned an extension field element");
                assert(zero3 == 0, || "Returned an extension field element");
                assert(expected == actual, || "expected != actual");
            },
        }
    };

    let test_fingerprint = query || {
        // A tuple t of size n with challenge x should be mapped to:
        // t[0] * x**(n-1) + t[1] * x**(n-2) + ... + t[n-2] * x + t[n-1]

        // For lists of length one, the fingerprint is the element itself
        assert_fingerprint_equal([123], 0, 123);
        assert_fingerprint_equal([123], 1234, 123);
        assert_fingerprint_equal([123], -4, 123);

        // For a list [a, b] of length two, the fingerprint is a + b * x
        assert_fingerprint_equal([123, 456], 0, 123);
        assert_fingerprint_equal([123, 456], 1, 123 + 456);
        assert_fingerprint_equal([123, 456], 2, 123 + 456 * 2);
        assert_fingerprint_equal([123, 456], -1, 123 - 456);

        // For a list [a, b, c] of length three, the fingerprint is a + b * x + c * x**2
        assert_fingerprint_equal([123, 456, 789], 0, 123);
        assert_fingerprint_equal([123, 456, 789], 1, 123 + 456 + 789);
        assert_fingerprint_equal([123, 456, 789], 2, 123 + 456 * 2 + 789 * 4);
    };
}
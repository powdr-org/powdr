use std::prover::challenge;
use std::array::fold;
use std::utils::unwrap_or_else;
use std::array::len;
use std::array::map;
use std::check::assert;
use std::check::panic;
use std::field::known_field;
use std::field::KnownField;
use std::math::fp2::Fp2;
use std::math::fp2::add_ext;
use std::math::fp2::sub_ext;
use std::math::fp2::mul_ext;
use std::math::fp2::unpack_ext;
use std::math::fp2::next_ext;
use std::math::fp2::inv_ext;
use std::math::fp2::eval_ext;
use std::math::fp2::from_base;


let is_first: col = |i| if i == 0 { 1 } else { 0 };

// challenges to be used in polynomial evaluation and folding different columns
let alpha1: expr = challenge(0, 1);
let alpha2: expr = challenge(0, 2);

let beta1: expr = challenge(0, 3);
let beta2: expr = challenge(0, 4);

let unpack_lookup_constraint: Constr -> (expr, expr[], expr, expr[]) = |lookup_constraint| match lookup_constraint {
    Constr::Lookup((lhs_selector, rhs_selector), values) => (
        unwrap_or_else(lhs_selector, || 1),
        map(values, |(lhs, _)| lhs),
        unwrap_or_else(rhs_selector, || 1),
        map(values, |(_, rhs)| rhs)
    ),
    _ => panic("Expected lookup constraint")
};

/// Whether we need to operate on the F_{p^2} extension field (because the current field is too small).
let needs_extension: -> bool = || match known_field() {
    Option::Some(KnownField::Goldilocks) => true,
    Option::Some(KnownField::BN254) => false,
    None => panic("The lookup argument is not implemented for the current field!")
};

//* Generic for both permutation and lookup arguments
/// Maps [x_1, x_2, ..., x_n] to alpha**(n - 1) * x_1 + alpha ** (n - 2) * x_2 + ... + x_n
let<T: Add + Mul + FromLiteral> compress_expression_array: T[], Fp2<T> -> Fp2<T> = |expr_array, alpha| fold(
    expr_array,
    from_base(0),
    |sum_acc, el| add_ext(mul_ext(alpha, sum_acc), from_base(el))
);


// Compute z' = z + 1/(beta-a_i) * lhs_selector - m_i/(beta-b_i) * rhs_selector, using extension field arithmetic
    let compute_next_z: Fp2<expr>, Constr, expr -> fe[] = query |acc, lookup_constraint, multiplicities| {

        let (lhs_selector, lhs, rhs_selector, rhs) = unpack_lookup_constraint(lookup_constraint);

        let alpha = if len(lhs) > 1 {
            Fp2::Fp2(alpha1, alpha2)
        } else {
            // The optimizer will have removed alpha, but the compression function
            // still accesses it (to multiply by 0 in this case)
            from_base(0)
        };

        let beta = Fp2::Fp2(beta1, beta2);
        
        let lhs_folded = sub_ext(beta, compress_expression_array(lhs, alpha));
        let rhs_folded = sub_ext(beta, compress_expression_array(rhs, alpha));
        let m_ext = from_base(multiplicities);
        
        // acc' = acc + 1/(beta-ai) * lhs_selector - mi/(beta-bi) * rhs_selector
        let res = add_ext(
            eval_ext(acc),
            sub_ext(
                mul_ext(
                    inv_ext(eval_ext(lhs_folded)), 
                    eval_ext(from_base(lhs_selector))),
                mul_ext(
                    mul_ext(eval_ext(m_ext), inv_ext(eval_ext(rhs_folded))),
                    eval_ext(from_base(rhs_selector))
            )
        ));

        match res {
            Fp2::Fp2(a0_fe, a1_fe) => [a0_fe, a1_fe]
        }
    };
    
// Adds constraints that enforce that rhs is the lookup for lhs
// Arguments:
// - acc: A phase-2 witness column to be used as the accumulator. If 2 are provided, computations
//        are done on the F_{p^2} extension field.
// - lookup_constraint: The lookup constraint
let lookup: expr[], Constr, expr -> Constr[] = |acc, lookup_constraint, multiplicities| {

    let (lhs_selector, lhs, rhs_selector, rhs) = unpack_lookup_constraint(lookup_constraint);

    let _ = assert(len(lhs) == len(rhs), || "LHS and RHS should have equal length");

    let with_extension = match len(acc) {
        1 => false,
        2 => true,
        _ => panic("Expected 1 or 2 accumulator columns!")
    };

    let _ = if !with_extension {
        assert(!needs_extension(), || "The Goldilocks field is too small and needs to move to the extension field. Pass two accumulators instead!")
    } else { () };

    // On the extension field, we'll need two field elements to represent the challenge.
    // If we don't need an extension field, we can simply set the second component to 0,
    // in which case the operations below effectively only operate on the first component.
    let fp2_from_array = |arr| if with_extension { Fp2::Fp2(arr[0], arr[1]) } else { from_base(arr[0]) };
    let acc_ext = fp2_from_array(acc);
    let alpha = fp2_from_array([alpha1, alpha2]);
    let beta = fp2_from_array([beta1, beta2]);

    // If the selector is 1, contribute a sum of with the value to accumulator.
    // If the selector is 0, contribute a sum of 0 to the accumulator.
    // Implemented as: folded = sub_ext(beta, compress_expression_array(value, alpha))
    let lhs_folded = sub_ext(beta, compress_expression_array(lhs, alpha));
    let rhs_folded = sub_ext(beta, compress_expression_array(rhs, alpha));
    let m_ext = from_base(multiplicities);

    let next_acc = if with_extension {
        next_ext(acc_ext)
    } else {
        // The second component is 0, but the next operator is not defined on it...
        from_base(acc[0]')
    };

    // Update rule new:
    // h' * (alpha - A) * (alpha - B)  + m * rhs_selector * (alpha - A) = h * (alpha - A) * (alpha - B) + lhs_selector * (alpha - B)
    // => (lhs_folded) * (rhs_folded) * (acc' - acc) + (m_folded) * rhs_selector * (lhs_folded) - lhs_selector * rhs_folded

    let (update_expr_1, update_expr_2) = unpack_ext(
        sub_ext(
            add_ext(
                mul_ext(
                    mul_ext(lhs_folded, rhs_folded),
                    sub_ext(next_acc, acc_ext)
                ),
                mul_ext(
                    mul_ext(m_ext, from_base(rhs_selector)),
                    lhs_folded
                )
            ),
            mul_ext(
                from_base(lhs_selector),
                rhs_folded
            )
        )
    );

    let (acc_1, acc_2) = unpack_ext(acc_ext);

    [
        is_first * acc_1 = 0,
        is_first * acc_2 = 0,

        // Assert that the update rule has been obeyed
        update_expr_1 = 0,

        // Again, update_expr_2 will be equal to 0 in the non-extension case.
        update_expr_2 = 0
    ]
};
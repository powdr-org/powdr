use std::prelude::Query;
use std::convert::fe;
use std::protocols::permutation_via_bus::permutation;
use std::math::fp2::from_base;
use std::prover::challenge;

machine Main with degree: 8 {
    let alpha = from_base(challenge(0, 1));
    let beta = from_base(challenge(0, 2));

    col fixed first_four = [1, 1, 1, 1, 0, 0, 0, 0];

    // Two pairs of witness columns, claimed to be permutations of one another
    // (when selected by first_four and (1 - first_four), respectively)
    col witness a1, a2, b1, b2;
    query |i| {
        std::prover::provide_value(a1, i, fe(i));
        std::prover::provide_value(a2, i, fe(i + 42));
        std::prover::provide_value(b1, i, fe(7 - i));
        std::prover::provide_value(b2, i, fe(7 - i + 42));
    };

    let permutation_constraint = Constr::Permutation(
        (Option::Some(first_four), Option::Some(1 - first_four)),
        [(a1, b1), (a2, b2)]
    );

    // TODO: Functions currently cannot add witness columns at later stages,
    // so we have to manually create it here and pass it to permutation(). 
    col witness stage(1) z;
    col witness stage(1) u;

    let is_first: col = std::well_known::is_first;
    permutation(is_first, 1, [z], [u], alpha, beta, permutation_constraint);

    is_first' * (z + u) = 0;
}

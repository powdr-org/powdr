use std::prelude::Query;
use std::convert::fe;
use std::protocols::lookup::lookup;
use std::math::fp2::from_base;
use std::prover::challenge;

machine Main with degree: 8 {

    let alpha =  from_base(challenge(0, 1));
    let beta = from_base(challenge(0, 2));

    col fixed random_six = [1, 1, 1, 0, 1, 1, 1, 0];
    col fixed first_seven = [1, 1, 1, 1, 1, 1, 1, 0];

    col fixed a1 = [1, 2, 4, 3, 1, 1, 4, 1];
    col fixed a2 = [1, 2, 4, 1, 1, 1, 4, 1];
    col fixed a3 = [1, 2, 4, 1, 1, 1, 4, 3];
    col witness b1, b2, b3;
    query |i| {
        std::prover::provide_value(b1, i, fe(i + 1));
        std::prover::provide_value(b2, i, fe(i + 1));
        std::prover::provide_value(b3, i, fe(i + 1));
    };
    col fixed m = [3, 1, 0, 2, 0, 0, 0, 0];

    let lookup_constraint = Constr::Lookup(
        (Option::Some(random_six), Option::Some(first_seven)),
        [(a1, b1), (a2, b2), (a3, b3)]
    );

    // TODO: Functions currently cannot add witness columns at later stages,
    // so we have to manually create it here and pass it to permutation(). 
    col witness stage(1) z;
    let is_first: col = std::well_known::is_first;
    lookup(is_first, [z], alpha, beta, lookup_constraint, m);
    
}
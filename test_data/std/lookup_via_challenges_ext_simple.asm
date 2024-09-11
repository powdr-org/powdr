use std::prelude::Query;
use std::convert::fe;
use std::protocols::lookup::lookup;
use std::protocols::lookup::compute_next_z;
use std::math::fp2::Fp2;
use std::prover::challenge;

machine Main with degree: 8 {

    // We don't need an alpha here, because we only "fold" one element.
    // Therefore, the optimizer will remove it, but the hint still accesses it...
    let alpha = Fp2::Fp2(0, 0);

    let beta1: expr = challenge(0, 3);
    let beta2: expr = challenge(0, 4);
    let beta = Fp2::Fp2(beta1, beta2);

    col fixed a = [1, 1, 4, 1, 1, 2, 1, 1];
    let b;
    query |i| {
        std::prover::provide_value(b, i, fe(i + 1));
    };
    col fixed m = [6, 1, 0, 1, 0, 0, 0, 0];

    let lookup_constraint = Constr::Lookup(
        (Option::None, Option::None),
        [(a, b)]
    );

    // TODO: Functions currently cannot add witness columns at later stages,
    // so we have to manually create it here and pass it to lookup(). 
    col witness stage(1) z1;
    col witness stage(1) z2;
    let z = Fp2::Fp2(z1, z2);

    let is_first: col = std::well_known::is_first;
    lookup(is_first, [z1, z2], alpha, beta, lookup_constraint, m);

    // TODO: Helper columns, because we can't access the previous row in hints
    col witness stage(1) z1_next;
    col witness stage(1) z2_next;
    query |i| {
        let hint = compute_next_z(z, alpha, beta, lookup_constraint, m);
        std::prover::provide_value(z1_next, i, hint[0]);
        std::prover::provide_value(z2_next, i, hint[1]);
    };

    z1' = z1_next;
    z2' = z2_next;
}
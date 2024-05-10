use std::prover::Query;
use std::convert::fe;
use std::protocols::permutation::permutation;
use std::protocols::permutation::compute_next_z;
use std::math::fp2::Fp2;

machine Main with degree: 8 {
    col fixed first_four = [1, 1, 1, 1, 0, 0, 0, 0];

    // Two pairs of witness columns, claimed to be permutations of one another
    // (when selected by first_four and (1 - first_four), respectively)
    col witness a1(i) query Query::Hint(fe(i));
    col witness a2(i) query Query::Hint(fe(i + 42));
    col witness b1(i) query Query::Hint(fe(7 - i));
    col witness b2(i) query Query::Hint(fe(7 - i + 42));

    let permutation_constraint = Constr::Permutation(
        Option::Some(first_four),
        [a1, a2],
        Option::Some(1 - first_four),
        [b1, b2]
    );

    // TODO: Functions currently cannot add witness columns at later stages,
    // so we have to manually create it here and pass it to permutation(). 
    col witness stage(1) z1;
    col witness stage(1) z2;
    permutation([z1, z2], permutation_constraint);

    // TODO: Helper columns, because we can't access the previous row in hints
    let hint = query |i| Query::Hint(compute_next_z(Fp2::Fp2(z1, z2), permutation_constraint)[i]); 
    col witness stage(1) z1_next(i) query hint(0);
    col witness stage(1) z2_next(i) query hint(1);

    z1' = z1_next;
    z2' = z2_next;

}

use std::prelude::Query;
use std::prover::eval;
use std::prover::challenge;

machine Main with degree: 8 {
    let is_first: col = std::well_known::is_first;

    let count;

    is_first * count = 0;
    (1 - is_first') * (count' - 1 - count) = 0;

    let alpha: expr = challenge(0, 3);
    col witness stage(1) z;
    query |i| std::prover::provide_value(z, i, eval(count) + eval(alpha));

    // Allow *both*: z = count + alpha and z = count + alpha + 1
    // Having a constraint ensures that the optimizer does not remove z.
    // Allowing for two values of z makes sure that the solution is not unique
    // and the hint above is actually needed.
    (z - (count + alpha)) * (z - (count + alpha + 1)) = 0;
}

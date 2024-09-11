use std::protocols::bus::bus_receive;
use std::protocols::bus::bus_send;
use std::protocols::bus::compute_next_z_send;
use std::protocols::bus::compute_next_z_receive;
use std::math::fp2::Fp2;
use std::math::fp2::from_base;
use std::prelude::Query;
use std::prover::challenge;

// Like block_to_block.asm, but also adds a bus to both machines.
// This is still flawed currently, because:
// - The Arith machine does not receive the tuple from the bus yet
// - Final accumulator values are not exposed as public yet
// In the future, this can be used to test that challenges can be shared between machines.

let ARITH_INTERACTION_ID = 1234;

// calls a constrained machine from a constrained machine
machine Arith with
    degree: 8,
    latch: latch,
    operation_id: operation_id,
    call_selectors: sel,
{
    operation add<0> x, y -> z;

    let used = std::array::sum(sel);

    // ==== Begin bus: Receive tuple (0, x, y, z) with ARITH_INTERACTION_ID ====

    // Non-extension case, can be useful for debugging
    /*
    let alpha = from_base(challenge(0, 1));
    let beta = from_base(challenge(0, 2));

    let is_first: col = std::well_known::is_first;
    col witness stage(1) acc;

    bus_receive(is_first, ARITH_INTERACTION_ID, [0, x, y, z], latch * used, [acc], alpha, beta);
    */

    let alpha1: expr = challenge(0, 1);
    let alpha2: expr = challenge(0, 2);
    let beta1: expr = challenge(0, 3);
    let beta2: expr = challenge(0, 4);
    let alpha = Fp2::Fp2(alpha1, alpha2);
    let beta = Fp2::Fp2(beta1, beta2);

    let is_first: col = std::well_known::is_first;
    col witness stage(1) acc1;
    col witness stage(1) acc2;
    let acc = Fp2::Fp2(acc1, acc2);

    bus_receive(is_first, ARITH_INTERACTION_ID, [0, x, y, z], latch * used, [acc1, acc2], alpha, beta);

    col witness stage(1) acc1_next;
    col witness stage(1) acc2_next;
    query |i| {
        let hint = compute_next_z_receive(is_first, ARITH_INTERACTION_ID, [0, x, y, z], latch * used, acc, alpha, beta);
        std::prover::provide_value(acc1_next, i, hint[0]);
        std::prover::provide_value(acc2_next, i, hint[1]);
    };

    acc1' = acc1_next;
    acc2' = acc2_next;

    // TODO: Expose final value of acc as public.

    // ==== End bus ====

    col fixed operation_id = [0]*;
    col fixed latch = [1]*;
    col witness x;
    col witness y;
    col witness z;
    z = x + y;
}

machine Main with
    degree: 8,
    latch: latch,
    operation_id: operation_id
{
    Arith arith;

    // return `3*x + 3*y`, adding twice locally and twice externally
    operation main<0>;

    link if instr_add ~> z = arith.add(x, y);

    // Can't have a challenge without a witness column, so add one here
    col witness dummy;
    // Need a constraint so that it's not optimized away
    dummy = dummy';

    // ==== Begin bus: Send tuple (0, x, y, z) with ARITH_INTERACTION_ID ====

    // Non-extension case, can be useful for debugging
    /*
    let alpha = from_base(challenge(0, 1));
    let beta = from_base(challenge(0, 2));

    let is_first: col = std::well_known::is_first;
    col witness stage(1) acc;

    bus_send(is_first, ARITH_INTERACTION_ID, [0, x, y, z], instr_add, [acc], alpha, beta);
    */

    let alpha1: expr = challenge(0, 1);
    let alpha2: expr = challenge(0, 2);
    let beta1: expr = challenge(0, 3);
    let beta2: expr = challenge(0, 4);
    let alpha = Fp2::Fp2(alpha1, alpha2);
    let beta = Fp2::Fp2(beta1, beta2);

    let is_first: col = std::well_known::is_first;
    col witness stage(1) acc1;
    col witness stage(1) acc2;
    let acc = Fp2::Fp2(acc1, acc2);

    bus_send(is_first, ARITH_INTERACTION_ID, [0, x, y, z], instr_add, [acc1, acc2], alpha, beta);

    col witness stage(1) acc1_next;
    col witness stage(1) acc2_next;
    query |i| {
        let hint = compute_next_z_send(is_first, ARITH_INTERACTION_ID, [0, x, y, z], instr_add, acc, alpha, beta);
        std::prover::provide_value(acc1_next, i, hint[0]);
        std::prover::provide_value(acc2_next, i, hint[1]);
    };

    acc1' = acc1_next;
    acc2' = acc2_next;

    // TODO: Expose final value of acc as public.

    // ==== End bus ====

    col fixed operation_id = [0]*;
    col fixed x(i) { i / 4 };
    col fixed y(i) { i / 4 + 1 };
    col witness z;
    col witness res;
    col fixed latch = [0, 0, 0, 1]*; // return every 4th row

    // accumulate the intermediate results into `res`
    // we waste a row here as we initialize res at 0
    // this is due to a limitation in witgen
    res' = (1 - latch) * (res + z);

    // add locally when `instr_add` is off
    (1 - instr_add) * (x + y - z) = 0;
    // add using `arith` every other row
    col fixed instr_add = [0, 1]*;
}

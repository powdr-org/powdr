use std::protocols::bus::bus_receive;
use std::protocols::bus::bus_send;
use std::prelude::Query;
use std::prover::challenge;

// Like block_to_block_with_bus.asm, but with differently-sized machines.

let ARITH_INTERACTION_ID = 1234;

// calls a constrained machine from a constrained machine
machine Arith with
    degree: 4,
    latch: latch,
    operation_id: operation_id,
    call_selectors: sel,
{
    operation add<0> x, y -> z;

    let used = std::array::sum(sel);

    col witness bus_selector;
    std::utils::force_bool(bus_selector);
    bus_receive(ARITH_INTERACTION_ID, [0, x, y, z], latch * bus_selector, latch * bus_selector);

    // TODO: Expose final value of acc as public.

    col fixed operation_id = [0]*;
    col fixed latch = [1]*;
    col witness x;
    col witness y;
    col witness z;
    z = x + y;
}

machine Main with
    // HACK: We need to provide a range here, because otherwise the linker will set all machines to the same degree.
    // Witgen will choose the degree 4.
    min_degree: 2,
    max_degree: 4,
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

    bus_send(ARITH_INTERACTION_ID, [0, x, y, z], instr_add);

    // TODO: Expose final value of acc as public.

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

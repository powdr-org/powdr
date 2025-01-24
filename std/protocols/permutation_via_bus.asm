use std::protocols::bus::bus_send;
use std::protocols::bus::bus_receive;
use std::protocols::permutation::unpack_permutation_constraint;
use std::constraints::to_phantom_permutation;


/// Given an ID and permutation constraints, sends the (ID, permutation_constraint.lhs...) tuple to the bus
/// if permutation_constraint.lhs_selector is 1.
let permutation_send: expr, Constr -> () = constr |id, permutation_constraint| {
    let (lhs_selector, lhs, rhs_selector, rhs) = unpack_permutation_constraint(permutation_constraint);

    bus_send(id, lhs, lhs_selector);
};

/// Given an ID and permutation constraints, receives the (ID, permutation_constraint.rhs...) tuple from the bus
/// with a prover-provided multiplicity if permutation_constraint.rhs_selector is 1.
let permutation_receive: expr, Constr -> () = constr |id, permutation_constraint| {
    let (lhs_selector, lhs, rhs_selector, rhs) = unpack_permutation_constraint(permutation_constraint);
    
    bus_receive(id, rhs, rhs_selector, rhs_selector);
};
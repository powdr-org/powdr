use std::protocols::bus::bus_receive;

/// Given an ID, selector, and tuple, receives (ID, ...tuple) tuple from the bus
/// with multiplicity 1 if the selector is 1.
let permutation_receive: expr, expr, expr[] -> () = constr |id, selector, tuple| {
    bus_receive(id, tuple, selector, selector);
};
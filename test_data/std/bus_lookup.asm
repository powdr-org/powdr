use std::protocols::bus::bus_send;
use std::protocols::lookup_via_bus::lookup_receive;

machine Main with degree: 8 {

    col fixed x = [1, 5, 2, 6, 4, 2, 6, 3];
    col witness y;

    // Pre-compute f(x) = x + 1 for all x in [1, 8]
    col fixed INC_X = [1, 2, 3, 4, 5, 6, 7, 8];
    col fixed INC_Y = [2, 3, 4, 5, 6, 7, 8, 9];

    let LOOKUP_ID = 42;
    bus_send(LOOKUP_ID, [x, y], 1);
    lookup_receive(LOOKUP_ID, 1, [INC_X, INC_Y]);
}
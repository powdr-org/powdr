use std::array;
use std::utils;

mod circuit;

use circuit::State;
use circuit::Gate;


let input_count = 50;
/// Represent the numbers 0 to 31, used for rotl.
/// TODO actually not all of them are used.
/// TODO and we can also re-use them in the permutation, so we don't have to add them for every circuit.
let rotl_constants = array::new(32, |i| Gate::Reference(input_count + i));
/// Represent the array RC.
let rc_constants = array::new(24, |i| Gate64::Reference(
    input_count + array::len(rotl_constants) + 2 * i,
    input_count + array::len(rotl_constants) + 2 * i + 1
));
/// The all-ones constant, used for bitwise negation.
let all_ones = Gate::Reference(input_count + array::len(rotl_constants) + array::len(rc_constants) * 2);

/// -------------- the elementary 64-bit gates -----------------
enum Gate64 {
    /// A 64-bit reference references two 32-bit gates.
    Reference(int, int),
    Xor(Gate64, Gate64),
    Rotl(Gate64, int),
    AndNot(Gate64, Gate64),
}
let xor: Gate64, Gate64 -> Gate64 = |a, b| Gate64::Xor(a, b);
let rotl64: Gate64, int -> Gate64 = |x, n| Gate64::Rotl(x, n);
/// Evaluates as and(not(a), b)
let and_not: Gate64, Gate64 -> Gate64 = |a, b| Gate64::AndNot(a, b);

/// -------------- conversion from 64 bit gates to 32 bit gates ----------

let xor32: Gate, Gate -> Gate = |a, b| Gate::Op(1, a, b);
let and_not32: Gate, Gate -> Gate = |a, b| Gate::Op(2, xor32(a, all_ones), b);
let shl32: Gate, int -> Gate = |a, n| Gate::Op(3, a, rotl_constants[n]);
let shr32: Gate, int -> Gate = |a, n| Gate::Op(4, a, rotl_constants[n]);

let rotl32: Gate, Gate, int -> (Gate, Gate) = |a, b, n| match n {
    0 => (a, b),
    _ =>
        if n >= 32 {
            rotl32(b, a, n - 32)
        } else {
            (
                xor32(shl32(a, n), shr32(b, 32 - n)),
                xor32(shl32(b, n), shr32(a, 32 - n))
            )
        }
    };

let to_gate32: Gate64 -> (Gate, Gate) = |gate| match gate {
    Gate64::Reference(i, j) => (Gate::Reference(i), Gate::Reference(j)),
    Gate64::Xor(a, b) => {
        let (a0, a1) = to_gate32(a);
        let (b0, b1) = to_gate32(b);
        (xor32(a0, b0), xor32(a1, b1))
    },
    Gate64::Rotl(x, n) => {
        let (a, b) = to_gate32(x);
        rotl32(a, b, n)
    },
    Gate64::AndNot(a, b) => {
        let (a0, a1) = to_gate32(a);
        let (b0, b1) = to_gate32(b);
        (and_not32(a0, b0), and_not32(a1, b1))
    }
};

let to_gate32_array: Gate64[] -> Gate[] = |gates| array::flatten(array::map(gates, |g| { let (a, b) = to_gate32(g); [a, b] }));

let to_gate64: Gate, Gate -> Gate64 = |g1, g2| match (g1, g2) {
    (Gate::Reference(i), Gate::Reference(j)) => Gate64::Reference(i, j),
    _ => std::check::panic("Invalid gate"),
};
let to_gate64_array: Gate[] -> Gate64[] = |gates| array::new(25, |i| to_gate64(gates[2 * i], gates[2 * i + 1]));

// ---------------- constants --------------------
let RHO: int[] = [
    1,  3,  6,  10, 15, 21, 28, 36, 45, 55, 2,  14,
    27, 41, 56, 8,  25, 43, 62, 18, 39, 61, 20, 44
];
let PI: int[] = [
    10, 7,  11, 17, 18, 3, 5,  16, 8,  21, 24, 4,
    15, 23, 19, 13, 12, 2, 20, 14, 22, 9,  6,  1
];
// PI[PI_INVERSE[i] - 1] = i for all i = 1 to 24
// PI_INVERSE has one more element than PI,
// with an extra 0 inserted at the start,
// because st[0] isn't updated in rho pi step
let PI_INVERSE: int[] = [
    0, 
    24, 18, 6, 12, 7, 23, 2, 9, 22, 1, 3, 17, 
    16, 20, 13, 8, 4, 5, 15, 19, 10, 21, 14, 11
];
let RC: int[] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
    0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008
];

/// ------------------------- circuit construction routines -------------------

let theta_bc = |st, i| xor(xor(xor(xor(st[i], st[i + 5]), st[i + 10]), st[i + 15]), st[i + 20]);

let theta_st = |inputs| {
    let bc = array::new(5, |i| theta_bc(inputs, i));
    // TODO we could turn the bc into a reference here already.
    array::map_enumerated(inputs, |idx, elem| {
        let i = idx % 5;
        let t = xor(bc[(i + 4) % 5], rotl64(bc[(i + 1) % 5], 1));
        xor(elem, t)
    })
};

let rho_pi: Gate64[], int -> Gate64 = |inputs, i| {
    let p = if i == 0 { 23 } else { i - 1 };
    rotl64(inputs[PI[p]], RHO[i])
};
// collect st_j
let rho_pi_loop = |inputs| array::new(25, |i| if i == 0 { inputs[0] } else { rho_pi(inputs, i - 1) } );

// rearrange st_j
let rho_pi_rearrange: Gate64[] -> Gate64[] = |inputs| array::new(25, |i| inputs[PI_INVERSE[i]]);

// chi
let chi: Gate64[] -> Gate64[] = |inputs| array::map_enumerated(inputs, |idx, elem| {
    let i = idx / 5;
    let j = idx % 5;
    xor(inputs[idx], and_not(inputs[i * 5 + (j + 1) % 5], inputs[i * 5 + (j + 2) % 5]))
});

// iota
let iota: Gate64[], int -> Gate64[] = |inputs, r| array::map_enumerated(inputs, |idx, elem| if idx == 0 { xor(elem, rc_constants[r]) } else { elem } );

let add_inputs: State, int -> (State, Gate[]) = |state, n|
    utils::fold(n, |i| i, (state, []), |(s, inp), _| {
        let (s2, g) = circuit::add_input(s);
        (s2, inp + [g])
    });

/// Wraps 64-bit gate constructor function to a 32-bit gate constructor function.
let wrap_64_in_32: (Gate64[] -> Gate64[]) -> (Gate[] -> Gate[]) = |f| |inputs| to_gate32_array(f(to_gate64_array(inputs)));
let theta_st_32 = wrap_64_in_32(theta_st);
let round_32 = |round| wrap_64_in_32(|inputs| iota(chi(rho_pi_rearrange(rho_pi_loop(inputs))), round));

let keccakf_circuit: -> (circuit::State, Gate[]) = || {
    let (s1, inputs) = add_inputs(circuit::new(), 50);
    // TODO maybe add_constants?
    let (s2, rotl_const) = add_inputs(s1, 32);
    let (s3, rc_const) = add_inputs(s2, 48);
    let (s4, all_ones_gate) = add_inputs(s3, 1);
    // TODO assert that rotl_const equal rotl_constants
    // TODO assert that rc_const equal rc_constants


    // TODO We start with 50 32-bit inputs here and we need to group them to
    // 25 Gate64 references, which we then pass to theta_st.
    // Then we turn them into 32-bit gates and add them as routines.
    // As a result we get 50 32-bit gates, which we can re-group again.
    // So essentially we need a function add_step, which takes 25 64-bit gates and returns 25 64-bit gates.
    utils::fold(24, |i| i, (s4, inputs), |(s, st), r| {
        let (s_1, th_r) = circuit::add_routines(s, theta_st_32(st));
        circuit::add_routines(s_1, round_32(r)(th_r))
    })
};


let eval_gate: int, int, int -> int = |gate, in1, in2| match gate {
    1 => in1 ^ in2,
    2 => in1 & in2,
    3 => (in1 << in2) & 0xffffffff,
    4 => in1 >> in2,
    _ => std::check::panic("Invalid gate"),
};

let values64_to_32: int[] -> int[] = |values| array::new(array::len(values) * 2, |i| match i % 2 {
    0 => values[i / 2] >> 32,
    1 => values[i / 2] & 0xffffffff,
});
let values32_to_64: int[] -> int[] = |values| array::new(array::len(values) / 2, |i| (values[2 * i] << 32) | values[2 * i + 1]);

let eval_circuit: circuit::State, Gate[], int[] -> int[] = |state, outputs, inputs| match state {
    State::S(gates, _) => {
        let initial = values64_to_32(inputs) + array::new(32, |i| i) + values64_to_32(RC) + [0xffffffff];
        let _ = std::check::assert(std::array::len(initial) == input_count + array::len(rotl_constants) + array::len(rc_constants) * 2 + 1, || "invalid initial length");
        let values = std::utils::fold(std::array::len(gates), |i| i, [], |acc, i| {
            let value = if i < array::len(initial) { initial[i] } else {
                let (id, in1, in2) = gates[i];
                eval_gate(id, acc[in1], acc[in2])
            };
            acc + [value]
        });
        values32_to_64(array::map(outputs, |g| match g {
            Gate::Reference(i) => values[i],
            _ => std::check::panic("Invalid output gate"),
        }))
    },
};


let test: -> Constr[] = || {
    let input = [8315180248889782138, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9223372036854775808, 0, 0, 0, 0, 0, 0, 0, 0];
    let expectation = [
        0xb6dc406d97d185ca,
        0x836e59c6c8ec3bca,
        0x6a01cf85414f77c0,
        0x397fa356584f8305,
        0xc8ad140a950d0cba,
        0x3dacc584b36c843f,
        0x428a466fad758146,
        0xa68af9b0cfafaf4c,
        0xffbba567083af2a9,
        0xb880d631598051a4,
        0x683f441da93e7295,
        0xbb5b42d2641b17c6,
        0xf4ec07dc2064443c,
        0x21959efb97953f8b,
        0x31c5e9b638335876,
        0xaa95e01d2bf963ed,
        0x82117b4b8decd828,
        0xe2a255871d47f57f,
        0x659b271c81bf6d3b,
        0x680b15e3d98b97ee,
        0x58118ac68850970d,
        0xada41f9e251307e6,
        0xf9a0529a1f229355,
        0x17cf3d9d8026e97f,
        0xdf84d5da988117d2
    ];

    let (circuit_state, circuit_outputs) = keccakf_circuit();
    let l = match circuit_state {
        State::S(gates, _) => std::array::len(gates),
    };
    let _ = std::debug::print("Gate count: ");
    let _ = std::debug::println(l);
    let result = eval_circuit(circuit_state, circuit_outputs, input);
    let _ = std::array::zip(result, expectation, |a, b| std::check::assert(a == b, || "Keccakf failed"));
    let _ = circuit::permutation(circuit_state);
    []
};

machine Main with degree: 196608 {
    // TODO uncomment to run the evaluation test.
    // test();


    std::machines::binary::Binary binary;
    std::machines::shift::Shift shift;

    col witness in1, in2, out;

    // TODO we need this because we do not have destructuring assignments
    let circuit = keccakf_circuit();
    let circuit_gates = (|(state, _)| match state { State::S(gates, _) => gates })(circuit);
    let output_gates = (|(_, output)| output)(circuit);
    let circuit_permutation = (|(state, _)| circuit::permutation(state))(circuit);
    let circuit_len = std::array::len(circuit_gates);

    let GATE_ID: col = |i| i % circuit_len;
    let GATE_OP: col = |i| { let (op, _, _) = circuit_gates[i % circuit_len]; op };

    // ----- fix the test inputs ------------
    IS_INPUT { GATE_ID, out } in { GATE_ID, INPUTS };

    let test_inputs = values64_to_32([8315180248889782138, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9223372036854775808, 0, 0, 0, 0, 0, 0, 0, 0]);
    let INPUTS: col = |i| if i % circuit_len < std::array::len(test_inputs) { test_inputs[i % circuit_len] } else { 0 };

    // ----- fix the constants ---------------

    // TODO

    // ------ gate operations ----------
    // TODO Can we do without fixed cols?
    // TODO "op" really needs to be an enum, this is horrible.
    let IS_INPUT: col = |i| { let (op, _, _) = circuit_gates[i % circuit_len]; if op == 0 { 1 } else { 0 } };
    let IS_XOR: col = |i| { let (op, _, _) = circuit_gates[i % circuit_len]; if op == 1 { 1 } else { 0 } };
    let IS_AND: col = |i| { let (op, _, _) = circuit_gates[i % circuit_len]; if op == 2 { 1 } else { 0 } };
    let IS_SHL: col = |i| { let (op, _, _) = circuit_gates[i % circuit_len]; if op == 3 { 1 } else { 0 } };
    let IS_SHR: col = |i| { let (op, _, _) = circuit_gates[i % circuit_len]; if op == 4 { 1 } else { 0 } };

    link IS_XOR => binary.xor in1, in2 -> out;
    link IS_AND => binary.and in1, in2 -> out;
    link IS_SHL => shift.shl in1, in2 -> out;
    link IS_SHR => shift.shr in1, in2 -> out;

    let IN1_PERM = |r| circuit_permutation(0, r);
    let IN2_PERM = |r| circuit_permutation(1, r);
    let OUT_PERM = |r| circuit_permutation(2, r);

    // Commented out because the types are not as expected.
    //{in1, in2, out} connect { IN1_PERM, IN2_PERM, OUT_PERM };

}

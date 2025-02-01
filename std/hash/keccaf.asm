use std::array;
use std::utils;

// ln 9 - 12
// TODO: check that these are good for word size 32
let RHO: int[] = [
    1,  3,  6,  10, 15, 21, 28, 36, 45, 55, 2,  14,
    27, 41, 56, 8,  25, 43, 62, 18, 39, 61, 20, 44
];

// ln 14 - 16
// TODO: check that these are good for word size 32
let PI: int[] = [
    10, 7,  11, 17, 18, 3, 5,  16, 8,  21, 24, 4,
    15, 23, 19, 13, 12, 2, 20, 14, 22, 9,  6,  1
];
// inverse of PI using 1 index plus zero at the beginning
// because rho pi step doesn't update st[0]
let PI_INVERSE: int[] = [
    0, 
    24, 18, 6, 12, 7, 23, 2, 9, 22, 1, 3, 17, 
    16, 20, 13, 8, 4, 5, 15, 19, 10, 21, 14, 11
];

// ln 19 - 28
// TODO: check that these are good for word size 32
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

// ln 30 - 33
// left rotation
let rotl64: int, int, (int, int -> int) -> int = |x, n, or| or((x << n), (x >> (64 - n))); // 32 if u32

// ln 35 - 40
// change endianness for a 32 bit number byte by byte
// e.g. 0xaabbccdd -> 0xddccbbaa
// let swap_u32: int, (int, int -> int), (int, int -> int) -> int = |x, or, and| 
//     or((or(and((x << 8), 0xff00ff00), and((x >> 8), 0x00ff00ff)) >> 16),
//     (or(and((x << 8), 0xff00ff00), and((x >> 8), 0x00ff00ff)) << 16)); 

let swap_u64: int, (int, int -> int), (int, int -> int) -> int = |x, or, and| {
    let val = or(and((x << 8), 0xFF00FF00FF00FF00), and((x >> 8), 0x00FF00FF00FF00FF));
    let val_2 = or(and((val << 16), 0xFFFF0000FFFF0000), and((val >> 16), 0x0000FFFF0000FFFF));
    or((val_2 << 32), (val_2 >> 32))
};

// ln 47 - 49
let swap_u64_loop: int[], (int, int -> int), (int, int -> int) -> int[] = |st, or, and| array::new(25, |i| swap_u64(st[i], or, and)); // int[25] -> int[25]

// Note that neither t nor bc is needed as they are both helper variables
// ln 52 - 55
let xor_mult: int[], (int, int -> int) -> int = |input, xor| array::fold(input, 0, |x, y| xor(x, y));
let theta_bc: int[], int, (int, int -> int) -> int = |st, i, xor| xor_mult([st[i], st[i + 5], st[i + 10], st[i + 15], st[i + 20]], xor); // int[25] -> int

// ln 57 - 62
let theta_st: int[], (int, int -> int), (int, int -> int) -> int[] = |st, xor, or| array::map_enumerated(st, |idx, elem| { // int[25] -> int[25]
    let i = idx % 5;
    let j = idx / 5;
    let t = xor(theta_bc(st, (i + 4) % 5, xor), rotl64(theta_bc(st, (i + 1) % 5, xor), 1, or));
    xor(elem, t)
});

// ln 66 - 72
// rho pi
let rho_pi: int[], int, (int, int -> int) -> int = |st, i, or| { // int[25], int -> int
    let p = if i == 0 { 23 } else { i - 1 };
    rotl64(st[PI[p]], RHO[i], or)
};
// collect st_j
let rho_pi_loop: int[], (int, int -> int) -> int[] = |st, or| array::new(25, |i| if i == 0 { st[0] } else { rho_pi(st, i - 1, or) } ); // int[25] -> int[25]
// rearrange st_j
let rho_pi_rearrange: int[] -> int[] = |st| array::new(25, |i| st[PI_INVERSE[i]]); // int[25] -> int[25]

// ln 74 - 83
// chi
// TODO: make sure that modulus has the same precedence as multiplication
let chi: int[], (int, int -> int), (int, int -> int), (int -> int) -> int[] = |st, xor, and, not| array::map_enumerated(st, |idx, elem| { // int[25] -> int[25]
    let i = idx / 5;
    let j = idx % 5;
    xor(elem, and(not(st[i * 5 + (j + 1) % 5]), st[i * 5 + (j + 2) % 5]))
});

// ln 85 - 86
// iota
let iota: int[], int, (int, int -> int) -> int[] = |st, r, xor| array::map_enumerated(st, |idx, elem| if idx == 0 { xor(elem, RC[r]) } else { elem } ); // int[25], int -> int[25]

// ln 51 - 87
let r_loop: int[], (int, int -> int), (int, int -> int), (int, int -> int), (int -> int) -> int[] = |st, xor, and, or, not| utils::fold(24, |i| i, st, |acc, r| iota(chi(rho_pi_rearrange(rho_pi_loop(theta_st(acc, xor, or), or)), xor, and, not), r, xor) ); // int[25] -> int[25]

// ln 42 - 94
// compression function
let keccakf: int[], (int, int -> int), (int, int -> int), (int, int -> int), (int -> int) -> int[] = |st, xor, and, or, not| swap_u64_loop(r_loop(swap_u64_loop(st, or, and), xor, and, or, not), or, and); // int[25] -> int[25]

// ln 96 - 141
// TODO: to_bytes and from_bytes are implemented below but I'm not sure if we have existing helper functions to use
let to_bytes: int[] -> int[] = |input| // int[25] -> int[200] 
    array::fold(input, [], |acc, elem| {
        let new_bytes = array::new(8, |i| 
            // elem % (1 << 8)
            // elem % (1 << 16) / (1 << 8)
            // elem % (1 << 24) / (1 << 16)
            // ...
            elem % (1 << (8 * i + 8)) / (1 << (8 * i))
        );
        acc + new_bytes
    });

let from_bytes: int[] -> int[] = |input| // int[200] -> int[25]
    array::new(25, |i| 
        utils::fold(8, |j| j, 0, |acc, idx| 
            acc + input[i * 8 + idx] * (1 << (8 * idx))
        )
    );
    

// ln 148 - 158
let update_finalize_b: int[], int[], int, int, (int, int -> int), (int, int -> int), (int, int -> int), (int -> int) -> int[] = |input, b, rate, delim, xor, and, or, not| {
    let num_loop = array::len(input) / rate;
    let num_remaining = array::len(input) % rate;
    let b_delim_idx = (num_remaining + 1) % rate;
    let b_keccak = utils::fold(num_loop, |i| i, b, |acc, idx| {
        let new_b = array::zip(array::new(rate, |i| acc[i]), array::new(rate, |i| input[idx * rate + i]), xor);
        to_bytes(keccakf(from_bytes(new_b), xor, and, or, not))
    });
    let b_update = array::new(rate, |i| 
        // num_remaining is 0 the minimum and rate - 1 the maximum
        if i < num_remaining {
            // ln 150, one of the remaining to be xor'ed
            xor(b_keccak[i], input[num_loop * rate + i])
        } else {
            if i == num_remaining {
                if i == rate - 1 { 
                    // num_remaining == rate - 1, so ln 156 and 157 update the same index of b
                    xor_mult([b_keccak[i], delim, 0x80], xor)
                } else {
                    // ln 156
                    xor(b_keccak[i], delim)
                }
            } else {
                if i == rate - 1 {
                // ln 157
                xor(b_keccak[i], 0x80)
                } else {
                    // not one of the remaining, just return as is
                    b_keccak[i]
                }
            }
        }
    );
    // ln 158
    to_bytes(keccakf(from_bytes(b_update), xor, and, or, not))    
};

// ln 143 - 161
let routine: int, int[], int, (int, int -> int), (int, int -> int), (int, int -> int), (int -> int) -> int[] = 
    |(W, input, delim, or, and, xor, not)| { // W: int (number of bytes to return); input: int[] (arbitrary length array of bytes); delim: int (u8)
        // ln 144 - 145
        let b = array::new(200, |i| 0); // int[200], 100 if u32
        let rate = 200 - (2 * W); // int, 100 if u32

        let b_finalized = update_finalize_b(input, b, rate, delim, xor, and, or, not);

        // TODO: as per ln 143, should return array of length W, but what if array length, i.e. rate, is less than W?
        // here we return the entire array rather than padding it to length W
        // ln 160
        if 3 * W <= 200 { array::new(W, |i| b_finalized[i]) } else { b_finalized } // 100 if u32
    };

let concrete: int, int[], int -> (int, int[], int, (int, int -> int), (int, int -> int), (int, int -> int), (int -> int)) = |W, input, delim| (
    W, input, delim,
    |x, y| x | y,
    |x, y| x & y,
    |x, y| x ^ y,
    // TODO: how to do bitwise not
    |x| x
);

let concrete_routine: int, int[], int -> int[] = |W, input, delim| routine(concrete(W, input, delim));

// main machine
machine Main {
    let x;
}

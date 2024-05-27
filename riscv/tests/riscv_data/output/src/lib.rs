#![no_std]

use powdr_riscv_runtime::io::{read_u32, write_u8, write_slice, write};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct Point {
    x: i32,
    y: i32,
}

#[no_mangle]
pub fn main() {
    let input = read_u32(0);

    write_u8(42, input);
    write_slice(43, &[input, input * 2, input * 3]);

    let point = Point { x: 1, y: 2 };
    write(44, &point);
}

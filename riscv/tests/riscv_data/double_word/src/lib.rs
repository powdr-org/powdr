#![no_std]

use powdr_riscv_runtime::io::read_word;

#[no_mangle]
pub fn main() {
    let a0 = read_word(0) as u64;
    let a1 = (read_word(1) as u64) << 32;
    let b0 = read_word(2) as u64;
    let b1 = (read_word(3) as u64) << 32;
    let c = (a0 + a1).wrapping_mul(b0 + b1);
    let c0 = (c & 0xffffffffu64) as u32;
    let c1 = ((c >> 32) & 0xffffffffu64) as u32;
    assert!(c0 == read_word(4));
    assert!(c1 == read_word(5));
}

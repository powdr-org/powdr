#![no_main]
#![no_std]

extern crate powdr_riscv_runtime;
use tiny_keccak::{Hasher, Keccak};

#[no_mangle]
pub fn main() {
    let inputs = [b"Solidity", b"Powdrrrr"];
    let mut output = [0u8; 32];
    let mut hasher = Keccak::v256();
    for input in inputs.into_iter().cycle().take(100) {
        hasher.update(input);
    }
    hasher.finalize(&mut output);

    /*
        assert_eq!(
            output,
            [
                0xb2, 0x60, 0x1c, 0x72, 0x12, 0xd8, 0x26, 0x0d, 0xa4, 0x6d, 0xde, 0x19, 0x8d, 0x50,
                0xa7, 0xe4, 0x67, 0x1f, 0xc1, 0xbb, 0x8f, 0xf2, 0xd1, 0x72, 0x5a, 0x8d, 0xa1, 0x08,
                0x11, 0xb5, 0x81, 0x69
            ],
        );
    */
}

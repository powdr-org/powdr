use core::arch::asm;

use powdr_riscv_syscalls::Syscall;

const GOLDILOCKS: u64 = 0xffffffff00000001;

/// Calls the low level Poseidon PIL machine, where
/// the last 4 elements are the "cap"
/// and the return value is placed in data[0:4].
/// This is unsafe because it does not check if the u64 elements fit the Goldilocks field.
pub fn poseidon_gl_unsafe(mut data: [u64; 12]) -> [u64; 4] {
    unsafe {
        asm!("ecall", in("a0") &mut data as *mut [u64; 12], in("t0") u32::from(Syscall::PoseidonGL));
    }

    [data[0], data[1], data[2], data[3]]
}

/// Calls the low level Poseidon PIL machine, where
/// the last 4 elements are the "cap"
/// and the return value is placed in data[0:4].
/// This function will panic if any of the u64 elements doesn't fit the Goldilocks field.
pub fn poseidon_gl(data: [u64; 12]) -> [u64; 4] {
    for &n in data.iter() {
        assert!(n < GOLDILOCKS);
    }

    poseidon_gl_unsafe(data)
}

/// Calls the keccakf machine.
/// Return value is placed in the output array.
pub fn keccakf(input: &[u64; 25], output: &mut [u64; 25]) {
    unsafe {
        // Syscall inputs: memory pointer to input array and memory pointer to output array.
        asm!("ecall", in("a0") input, in("a1") output, in("t0") u32::from(Syscall::KeccakF));
    }
}

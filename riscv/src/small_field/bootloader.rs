use std::marker::PhantomData;

use powdr_number::KnownField;
use powdr_number::{FieldElement, LargeInt};

use crate::continuations::bootloader::BootloaderImpl;

use crate::continuations::bootloader::WORDS_PER_PAGE;

pub fn split_word<F: FieldElement>(v: u32) -> (F, F) {
    ((v & 0xffff).into(), (v >> 16).into())
}

pub fn split_fe<F: FieldElement>(v: &F) -> [F; 2] {
    let v = v.to_integer().try_into_u32().unwrap();
    [(v >> 16).into(), (v & 0xffff).into()]
}

pub struct SmallFieldBootloader<F: FieldElement>(PhantomData<F>);

impl<F: FieldElement> BootloaderImpl<F> for SmallFieldBootloader<F> {
    const FE_PER_WORD: usize = 2;
    type Page = [F; 2 * WORDS_PER_PAGE];
    type Hash = [F; 8];

    fn update_page(page: &mut Self::Page, idx: usize, word: u32) {
        let (hi, lo) = split_word(word);
        // TODO: check proper endianess here!
        page[idx] = hi;
        page[idx + 1] = lo;
    }

    fn hash_page(page: &Self::Page) -> Self::Hash {
        let mut hash = [0.into(); 8];
        for chunk in page.chunks_exact(8) {
            hash = Self::hash_two(&hash, chunk.try_into().unwrap());
        }
        hash
    }

    fn hash_two(a: &Self::Hash, b: &Self::Hash) -> Self::Hash {
        let mut buffer = [0.into(); 16];
        buffer[..8].copy_from_slice(a);
        buffer[8..16].copy_from_slice(b);
        match F::known_field() {
            Some(KnownField::BabyBearField) => {
                todo!("call rust implememtation of poseidon bb")
                // poseidon_bb(&buffer)
            }
            _ => todo!("field has no poseidon hash implementation"),
        }
    }

    fn zero_page() -> Self::Page {
        [0.into(); 2 * WORDS_PER_PAGE]
    }

    fn iter_hash_as_fe(h: &Self::Hash) -> impl Iterator<Item = F> {
        h.iter().flat_map(|f| split_fe(f).into_iter())
    }

    fn iter_page_as_fe(p: &Self::Page) -> impl Iterator<Item = F> {
        p.iter().copied()
    }

    fn iter_word_as_fe(v: u32) -> impl Iterator<Item = F> {
        let (hi, lo) = split_word(v);
        // TODO: check proper endianess here!
        [hi, lo].into_iter()
    }
}

pub const BOOTLOADER_SPECIFIC_INSTRUCTION_NAMES: [&str; 2] =
    ["load_bootloader_input", "jump_to_bootloader_input"];

pub fn bootloader_preamble() -> String {
    todo!()
}

/// The bootloader: An assembly program that can be executed at the beginning of RISC-V execution.
///
/// It lets the prover provide arbitrary memory pages and writes them to memory, as well as values for
/// the registers (including the PC, which is set last).
/// This can be used to implement continuations. Note that this is completely non-sound. Progress to
/// make it sound is tracked in https://github.com/powdr-labs/powdr/issues/814.
/// Bootloader inputs are in the format:
/// - First 37 values: Values of x1-x31, tmp1-tmp4, lr_sc_reservation, and the PC
/// - Second 37 values: The same values, but after this chunk's execution
/// - The root hash of the memory Merkle tree (8 words)
/// - The root hash of the memory Merkle tree *after this chunk's execution* (8 words)
/// - Number of pages
/// - For each page:
///   - The page number
///   - The words of the page
///   - The hash (8 words) of the page *after* this chunk's execution
///   - For each level of the Merkle tree, except the root (1..=22):
///     - The hash (8 words) of the sibling page
pub fn bootloader_and_shutdown_routine(_submachine_initialization: &[String]) -> String {
    todo!()
}

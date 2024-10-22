use std::collections::{BTreeMap, HashMap};

use powdr_number::FieldElement;

use super::bootloader::{BootloaderImpl, BYTES_PER_WORD, N_LEAVES_LOG, WORDS_PER_PAGE};

const N_LEVELS_DEFAULT: usize = N_LEAVES_LOG + 1;

/// A Merkle tree of memory pages.
pub struct MerkleTree<
    F: FieldElement,
    B: BootloaderImpl<F>,
    const N_LEVELS: usize = N_LEVELS_DEFAULT,
> {
    /// Hashes of non-default nodes of the Merkle tree.
    ///
    /// The key is the tuple (level, index), where level is the tree level, and
    /// index is the index of the node in that level.
    ///
    /// Level 0 is the tree root, and only contains node index 0, the root_hash.
    ///
    /// Level N_LEVELS - 1 is the last level, and contains up to 2**(N_LEVELS-1)
    /// nodes with the hash of the non-zero leaves. These hashes should be
    /// updated whenever the data is updated.
    ///
    /// If a node is not present in the map, it is assumed to be the default.
    hashes: HashMap<(usize, usize), B::Hash>,
    /// Memory pages, numbered sequentially.
    data: HashMap<usize, B::Page>,

    /// The default hash for each level of the tree, when all leaves below are
    /// zeroed.
    default_hashes: [B::Hash; N_LEVELS],

    /// A zeroed page, used as a default value for missing pages.
    zero_page: B::Page,
}

/// Takes the ordered list of node indices in one level, and updates the list
/// in-place with the indices of the parent nodes in the level above.
fn level_up(ordered_indices: &mut Vec<usize>) {
    // I tried implementing this as a single dedup_by_key() call, but it doesn't
    // invoke the closure in case of a single element, so it is not updated.
    for i in ordered_indices.iter_mut() {
        *i >>= 1;
    }
    ordered_indices.dedup();
}

impl<F: FieldElement, B: BootloaderImpl<F>, const N_LEVELS: usize> MerkleTree<F, B, N_LEVELS> {
    /// Build a new Merkle tree starting from an all-zero memory.
    pub fn new() -> Self {
        Self {
            hashes: HashMap::new(),
            data: HashMap::new(),
            default_hashes: Self::default_hashes_per_level(),
            zero_page: B::zero_page(),
        }
    }

    /// Function update() relies on the result being sorted by page_index, so we
    /// use a BTreeMap here.
    pub fn organize_updates_by_page(
        &self,
        updates: impl Iterator<Item = (u32, u32)>,
    ) -> BTreeMap<usize, Vec<(usize, u32)>> {
        let mut updates_by_page: BTreeMap<usize, Vec<(usize, u32)>> = BTreeMap::new();
        for (addr, value) in updates {
            assert!(addr % BYTES_PER_WORD as u32 == 0);
            let word_index = addr as usize / BYTES_PER_WORD;
            let page_index = word_index / WORDS_PER_PAGE;
            let index_within_page = word_index - page_index * WORDS_PER_PAGE;
            updates_by_page
                .entry(page_index)
                .or_default()
                .push((index_within_page, value));
        }
        updates_by_page
    }

    /// Applies updates, given an iterator of (memory address, value) pairs.
    /// Memory addresses are assumed to be word-aligned.
    pub fn update(&mut self, updates: impl Iterator<Item = (u32, u32)>) {
        let mut updated_indices = Vec::new();

        // Update all leaves first:
        for (page_index, updates) in self.organize_updates_by_page(updates) {
            self.update_page_impl(page_index, &updates);
            self.update_leaf_hash(page_index);
            // Insert page index in ascending order.
            updated_indices.push(page_index);
        }

        // Then update all inner hashes, per level:
        for level in (0..(N_LEVELS - 1)).rev() {
            level_up(&mut updated_indices);
            for &index in &updated_indices {
                self.update_inner_hash(level, index);
            }
        }
    }

    /// Applies updates to a single page, given an iterator of (word index, value) pairs.
    /// Word indices addresses are assumed to be word-aligned.
    pub fn update_page(&mut self, page_index: usize, updates: &[(usize, u32)]) {
        self.update_page_impl(page_index, updates);
        self.update_hashes(page_index)
    }

    fn update_page_impl(&mut self, page_index: usize, updates: &[(usize, u32)]) {
        let page = &mut self
            .data
            .entry(page_index)
            .or_insert_with(|| B::zero_page());
        for (index, value) in updates {
            B::update_page(page, *index, *value);
        }
    }

    fn get_hash(&self, level: usize, index: usize) -> &B::Hash {
        assert!(level < N_LEVELS);
        assert!(index < (1 << level));
        self.hashes
            .get(&(level, index))
            .unwrap_or(&self.default_hashes[level])
    }

    /// Updates the hashes of a page and all its ancestors.
    fn update_hashes(&mut self, page_index: usize) {
        self.update_leaf_hash(page_index);
        for (level, index) in self.iter_path(page_index).skip(1) {
            self.update_inner_hash(level, index);
        }
    }

    fn update_leaf_hash(&mut self, page_index: usize) {
        self.hashes.insert(
            (N_LEVELS - 1, page_index),
            B::hash_page(&self.data[&page_index]),
        );
    }

    fn update_inner_hash(&mut self, level: usize, index: usize) {
        let new_hash = B::hash_two(
            self.get_hash(level + 1, index * 2),
            self.get_hash(level + 1, index * 2 + 1),
        );
        self.hashes.insert((level, index), new_hash);
    }

    /// Returns the root hash of the Merkle tree.
    pub fn root_hash(&self) -> &B::Hash {
        self.get_hash(0, 0)
    }

    /// Returns the data and Merkle proof for a given page.
    pub fn get(&self, page_index: usize) -> (&B::Page, &B::Hash, Vec<&B::Hash>) {
        let mut proof = vec![];
        for (level, index) in self.iter_path(page_index).take(N_LEVELS - 1) {
            let sibling_index = index ^ 1;
            proof.push(self.get_hash(level, sibling_index));
        }
        assert_eq!(proof.len(), N_LEVELS - 1);

        let page_hash = self.get_hash(N_LEVELS - 1, page_index);

        let page_data = self.data.get(&page_index).unwrap_or(&self.zero_page);

        (page_data, page_hash, proof)
    }

    /// Yields (level, index) pairs for the path from the given page to the root.
    fn iter_path(&self, page_index: usize) -> impl Iterator<Item = (usize, usize)> {
        (0..N_LEVELS).rev().map(move |level| {
            let index = page_index >> (N_LEVELS - level - 1);
            (level, index)
        })
    }

    fn default_hashes_per_level() -> [B::Hash; N_LEVELS] {
        assert!(usize::BITS >= N_LEVELS as u32);
        let zero_page = B::zero_page();

        let mut generator = std::iter::successors(Some(B::hash_page(&zero_page)), |hash| {
            Some(B::hash_two(hash, hash))
        });
        let mut result = std::array::from_fn(|_| generator.next().unwrap());
        result.reverse();

        result
    }
}

impl<F: FieldElement, B: BootloaderImpl<F>> Default for MerkleTree<F, B> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    use powdr_number::GoldilocksField;

    use crate::large_field::bootloader::LargeFieldBootloader;

    use super::*;
    const P: u32 = WORDS_PER_PAGE as u32;
    const W: u32 = BYTES_PER_WORD as u32;
    const N_LEVELS: usize = 3;
    type TestMerkleTree =
        MerkleTree<GoldilocksField, LargeFieldBootloader<GoldilocksField>, N_LEVELS>;

    fn root_hash(
        pages: &[[GoldilocksField; WORDS_PER_PAGE]; 4],
    ) -> <LargeFieldBootloader<GoldilocksField> as BootloaderImpl<GoldilocksField>>::Hash {
        let page_hashes = pages
            .iter()
            .map(LargeFieldBootloader::hash_page)
            .collect::<Vec<_>>();

        let hash_1_0 = LargeFieldBootloader::hash_two(&page_hashes[0], &page_hashes[1]);
        let hash_1_1 = LargeFieldBootloader::hash_two(&page_hashes[2], &page_hashes[3]);
        LargeFieldBootloader::hash_two(&hash_1_0, &hash_1_1)
    }

    fn zero_page() -> [GoldilocksField; WORDS_PER_PAGE] {
        <LargeFieldBootloader<GoldilocksField> as BootloaderImpl<_>>::zero_page()
    }

    #[test]
    fn update() {
        let mut tree = TestMerkleTree::new();
        let mut data: [[GoldilocksField; WORDS_PER_PAGE]; 4] = [zero_page(); 4];

        // Update page 0
        data[0][4] = 1.into();
        tree.update([(4 * W, 1)].into_iter());
        let expected_root_hash = root_hash(&data);
        assert_eq!(tree.root_hash(), &expected_root_hash);

        // Update page 1
        data[1][3] = 2.into();
        tree.update([((P + 3) * W, 2)].into_iter());
        let expected_root_hash = root_hash(&data);
        assert_eq!(tree.root_hash(), &expected_root_hash);

        // Update page 2
        data[2][7] = 3.into();
        tree.update([((2 * P + 7) * W, 3)].into_iter());
        let expected_root_hash = root_hash(&data);
        assert_eq!(tree.root_hash(), &expected_root_hash);

        // Update page 3
        data[3][6] = 4.into();
        tree.update([((3 * P + 6) * W, 4)].into_iter());
        let expected_root_hash = root_hash(&data);
        assert_eq!(tree.root_hash(), &expected_root_hash);

        // Update page 0, again
        data[0][3] = 5.into();
        tree.update([(3 * W, 5)].into_iter());
        let expected_root_hash = root_hash(&data);
        assert_eq!(tree.root_hash(), &expected_root_hash);

        // Update all at once
        let mut tree = TestMerkleTree::new();
        tree.update(
            [
                (4 * W, 1),
                ((P + 3) * W, 2),
                ((2 * P + 7) * W, 3),
                ((3 * P + 6) * W, 4),
                (3 * W, 5),
            ]
            .into_iter(),
        );
        assert_eq!(tree.root_hash(), &expected_root_hash);
    }

    #[test]
    fn get() {
        let g = GoldilocksField::from;
        let mut tree = TestMerkleTree::new();
        tree.update(
            [
                (4 * W, 1),
                ((P + 3) * W, 2),
                ((2 * P + 7) * W, 3),
                ((3 * P + 6) * W, 4),
                (3 * W, 5),
            ]
            .into_iter(),
        );
        let root_hash = tree.root_hash();

        // Get page 0
        let (page, page_hash, proof) = tree.get(0);
        for e in &page[8..] {
            assert!(e == &g(0));
        }
        let mut expected_page = zero_page();
        expected_page[3] = g(5);
        expected_page[4] = g(1);
        assert_eq!(page, &expected_page);
        assert_eq!(
            page_hash,
            &LargeFieldBootloader::<GoldilocksField>::hash_page(&expected_page)
        );

        // Verify Merkle proof
        assert_eq!(proof.len(), 2);
        let computed_hash = &LargeFieldBootloader::<GoldilocksField>::hash_two(page_hash, proof[0]);
        let computed_hash =
            &LargeFieldBootloader::<GoldilocksField>::hash_two(computed_hash, proof[1]);
        assert_eq!(computed_hash, root_hash);

        // Get page 1
        let (page, page_hash, proof) = tree.get(1);
        let mut expected_page = zero_page();
        expected_page[3] = g(2);
        assert_eq!(page, &expected_page);
        assert_eq!(
            page_hash,
            &LargeFieldBootloader::<GoldilocksField>::hash_page(&expected_page)
        );

        // Verify Merkle proof
        assert_eq!(proof.len(), 2);
        let computed_hash = &LargeFieldBootloader::<GoldilocksField>::hash_two(proof[0], page_hash);
        let computed_hash =
            &LargeFieldBootloader::<GoldilocksField>::hash_two(computed_hash, proof[1]);
        assert_eq!(computed_hash, root_hash);

        // Get page 2
        let (page, page_hash, proof) = tree.get(2);
        let mut expected_page = zero_page();
        expected_page[7] = g(3);
        assert_eq!(page, &expected_page);
        assert_eq!(
            page_hash,
            &LargeFieldBootloader::<GoldilocksField>::hash_page(&expected_page)
        );

        // Verify Merkle proof
        assert_eq!(proof.len(), 2);
        let computed_hash = &LargeFieldBootloader::<GoldilocksField>::hash_two(page_hash, proof[0]);
        let computed_hash =
            &LargeFieldBootloader::<GoldilocksField>::hash_two(proof[1], computed_hash);
        assert_eq!(computed_hash, root_hash);

        // Get page 3
        let (page, page_hash, proof) = tree.get(3);
        let mut expected_page = zero_page();
        expected_page[6] = g(4);
        assert_eq!(page, &expected_page);
        assert_eq!(
            page_hash,
            &LargeFieldBootloader::<GoldilocksField>::hash_page(&expected_page)
        );

        // Verify Merkle proof
        assert_eq!(proof.len(), 2);
        let computed_hash = &LargeFieldBootloader::<GoldilocksField>::hash_two(proof[0], page_hash);
        let computed_hash =
            &LargeFieldBootloader::<GoldilocksField>::hash_two(proof[1], computed_hash);
        assert_eq!(computed_hash, root_hash);
    }
}

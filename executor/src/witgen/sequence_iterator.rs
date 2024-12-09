use std::collections::BTreeMap;

use powdr_number::FieldElement;

use super::affine_expression::AffineExpression;

#[derive(Clone, Debug)]
pub struct SequenceStep {
    pub row_delta: i64,
    pub action: Action,
}

/// Goes through all rows of the block machine (plus the ones before and after)
/// forward, backward, and forward again.
/// In each row, iterates over all identities until no further progress is made.
pub struct DefaultSequenceIterator {
    identities_count: usize,
    row_deltas: Vec<i64>,
    outer_query_row: Option<i64>,

    /// Whether any progress was made in the current round.
    progress_in_current_round: bool,
    /// The current row delta index.
    cur_row_delta_index: usize,
    /// Index of the current action. Actions are:
    /// [process identity 1, ..., process identity <identities_count>, process queries, process outer query (if on outer_query_row)]
    /// Can be -1 to indicate that the round has just started.
    cur_action_index: i32,
    /// The number of rounds for the current row delta.
    /// If this number gets too large, we will assume that we're in an infinite loop and exit.
    current_round_count: usize,

    /// The steps on which we made progress.
    progress_steps: Vec<SequenceStep>,
}

const MAX_ROUNDS_PER_ROW_DELTA: usize = 102;

impl DefaultSequenceIterator {
    pub fn new(block_size: usize, identities_count: usize, outer_query_row: Option<i64>) -> Self {
        let max_row = block_size as i64 - 1;
        DefaultSequenceIterator {
            identities_count,
            row_deltas: (-1..=max_row)
                .chain((-1..max_row).rev())
                .chain(0..=max_row)
                .chain((-1..max_row).rev())
                .collect(),
            outer_query_row,
            progress_in_current_round: false,
            cur_row_delta_index: 0,
            cur_action_index: -1,
            current_round_count: 0,
            progress_steps: vec![],
        }
    }

    /// Update the state of the iterator.
    /// If we're not at the last identity in the current row, just moves to the next.
    /// Otherwise, starts with identity 0 and moves to the next row if no progress was made.
    fn update_state(&mut self) {
        while !self.is_done() && !self.has_more_actions() {
            self.start_next_round();
        }

        self.cur_action_index += 1;
    }

    fn is_done(&self) -> bool {
        self.cur_row_delta_index == self.row_deltas.len()
    }

    fn has_more_actions(&self) -> bool {
        let row_delta = self.row_deltas[self.cur_row_delta_index];
        let is_on_row_with_outer_query = self.outer_query_row == Some(row_delta);

        let last_action_index = if is_on_row_with_outer_query {
            // In the last row, we want to do one more action, processing the outer query.
            self.identities_count as i32 + 1
        } else {
            // Otherwise, we want to process all identities + 1 action processing the prover queries
            self.identities_count as i32
        };

        self.cur_action_index < last_action_index
    }

    fn start_next_round(&mut self) {
        if self.current_round_count > MAX_ROUNDS_PER_ROW_DELTA {
            panic!("In witness generation for block machine, we have been stuck in the same row for {MAX_ROUNDS_PER_ROW_DELTA} rounds. \
                    This is a bug in the witness generation algorithm.");
        }

        if !self.progress_in_current_round {
            // Move to next row delta
            self.cur_row_delta_index += 1;
            self.current_round_count = 0;
        } else {
            // Stay and current row delta
            self.current_round_count += 1;
        }
        // Reset action index and progress flag
        self.cur_action_index = -1;
        self.progress_in_current_round = false;
    }

    pub fn report_progress(&mut self, progress_in_last_step: bool) {
        assert!(
            self.cur_action_index != -1,
            "Called report_progress() before next()"
        );

        if progress_in_last_step {
            self.progress_steps.push(self.current_step());
        }
        self.progress_in_current_round |= progress_in_last_step;
    }

    pub fn next(&mut self) -> Option<SequenceStep> {
        self.update_state();

        if self.is_done() {
            return None;
        }

        Some(self.current_step())
    }

    fn current_step(&self) -> SequenceStep {
        assert!(self.cur_action_index != -1);
        SequenceStep {
            row_delta: self.row_deltas[self.cur_row_delta_index],
            action: match self.cur_action_index.cmp(&(self.identities_count as i32)) {
                std::cmp::Ordering::Less => {
                    Action::InternalIdentity(self.cur_action_index as usize)
                }
                std::cmp::Ordering::Equal => Action::ProverQueries,
                std::cmp::Ordering::Greater => Action::OuterQuery,
            },
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Action {
    InternalIdentity(usize),
    OuterQuery,
    ProverQueries,
}

#[derive(PartialOrd, Ord, PartialEq, Eq, Debug)]
pub struct SequenceCacheKey {
    /// For each expression on the left-hand side of the lookup, whether it is a constant.
    known_columns: Vec<bool>,
}

impl<K, T> From<&[AffineExpression<K, T>]> for SequenceCacheKey
where
    K: Copy + Ord,
    T: FieldElement,
{
    fn from(value: &[AffineExpression<K, T>]) -> Self {
        SequenceCacheKey {
            known_columns: value.iter().map(|v| v.is_constant()).collect(),
        }
    }
}

/// The iterator to be used when the a cached sequence is available.
/// In theory, it should only yield the steps from `cached_iterator`.
/// However, we also run the default iterator afterwards, because the cached sequence
/// is not guaranteed to be sufficient.
pub struct CachedSequenceIterator {
    cached_iterator: <Vec<SequenceStep> as IntoIterator>::IntoIter,
    cached_iterator_exhausted: bool,
    default_iterator: DefaultSequenceIterator,
}

pub enum ProcessingSequenceIterator {
    /// The default strategy
    Default(DefaultSequenceIterator),
    /// The machine has been run successfully before and the sequence is cached.
    Cached(CachedSequenceIterator),
    /// The machine has been run before, but did not succeed. There is no point in trying again.
    Incomplete,
}

impl ProcessingSequenceIterator {
    pub fn report_progress(&mut self, progress_in_last_step: bool) {
        match self {
            Self::Default(it) => it.report_progress(progress_in_last_step),
            Self::Cached(it) => {
                if it.cached_iterator_exhausted {
                    // The default iterator changes its behavior depending on whether
                    // we made any progress, so we need to report it even though we won't
                    // ever access the progress steps.
                    it.default_iterator.report_progress(progress_in_last_step)
                }
            }
            Self::Incomplete => unreachable!(),
        }
    }

    pub fn has_steps(&self) -> bool {
        match self {
            Self::Default(_) | Self::Cached(_) => true,
            Self::Incomplete => false,
        }
    }
}

impl Iterator for ProcessingSequenceIterator {
    type Item = SequenceStep;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Default(it) => it.next(),
            // After the cached iterator is exhausted, run the default iterator again.
            // This is because the order in which the identities should be processed *might*
            // depend on the concrete input values.
            // In the typical scenario, most identities will be completed at this point and
            // the block processor will skip them. But if an identity was not completed before,
            // it will try again.
            Self::Cached(it) => {
                let cached_step = it.cached_iterator.next();
                it.cached_iterator_exhausted = cached_step.is_none();
                cached_step.or_else(|| it.default_iterator.next())
            }
            Self::Incomplete => unreachable!(),
        }
    }
}

enum CacheEntry {
    /// The machine has been run successfully before and the sequence is cached.
    Complete(Vec<SequenceStep>),
    /// The machine has been run before, but did not succeed. There is no point in trying again.
    Incomplete,
}

pub struct ProcessingSequenceCache {
    block_size: usize,
    outer_query_row: usize,
    identities_count: usize,
    cache: BTreeMap<SequenceCacheKey, CacheEntry>,
}

impl ProcessingSequenceCache {
    pub fn new(block_size: usize, outer_query_row: usize, identities_count: usize) -> Self {
        ProcessingSequenceCache {
            block_size,
            outer_query_row,
            identities_count,
            cache: Default::default(),
        }
    }

    pub fn get_processing_sequence<K, T>(
        &self,
        left: &[AffineExpression<K, T>],
    ) -> ProcessingSequenceIterator
    where
        K: Copy + Ord,
        T: FieldElement,
    {
        match self.cache.get(&left.into()) {
            Some(CacheEntry::Complete(cached_sequence)) => {
                log::trace!("Using cached sequence");
                ProcessingSequenceIterator::Cached(CachedSequenceIterator {
                    cached_iterator: cached_sequence.clone().into_iter(),
                    cached_iterator_exhausted: false,
                    default_iterator: self.get_default_sequence_iterator_inner(),
                })
            }
            Some(CacheEntry::Incomplete) => ProcessingSequenceIterator::Incomplete,
            None => {
                log::trace!("Using default sequence");
                self.get_default_sequence_iterator()
            }
        }
    }

    pub fn get_default_sequence_iterator(&self) -> ProcessingSequenceIterator {
        ProcessingSequenceIterator::Default(self.get_default_sequence_iterator_inner())
    }

    fn get_default_sequence_iterator_inner(&self) -> DefaultSequenceIterator {
        DefaultSequenceIterator::new(
            self.block_size,
            self.identities_count,
            Some(self.outer_query_row as i64),
        )
    }

    pub fn report_incomplete<K, T>(&mut self, left: &[AffineExpression<K, T>])
    where
        K: Copy + Ord,
        T: FieldElement,
    {
        assert!(self
            .cache
            .insert(left.into(), CacheEntry::Incomplete)
            .is_none());
    }

    pub fn report_processing_sequence<K, T>(
        &mut self,
        left: &[AffineExpression<K, T>],
        sequence_iterator: ProcessingSequenceIterator,
    ) where
        K: Copy + Ord,
        T: FieldElement,
    {
        match sequence_iterator {
            ProcessingSequenceIterator::Default(it) => {
                assert!(self
                    .cache
                    .insert(left.into(), CacheEntry::Complete(it.progress_steps))
                    .is_none());
            }
            ProcessingSequenceIterator::Incomplete => unreachable!(),
            ProcessingSequenceIterator::Cached(_) => {} // Already cached, do nothing
        }
    }
}

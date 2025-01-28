use std::{
    collections::HashSet,
    ops::{Index, IndexMut},
};

use auto_enums::auto_enum;
use bit_vec::BitVec;
use itertools::Itertools;
use powdr_ast::analyzed::{PolyID, PolynomialType};
use powdr_number::FieldElement;

use crate::witgen::{rows::Row, FixedData};

use super::padded_bitvec::PaddedBitVec;

#[derive(Debug, Clone)]
pub struct ColumnLayout {
    /// The ID of the first column used in the table.
    pub first_column_id: u64,
    /// The length of a row in the table.
    pub column_count: usize,
}

impl ColumnLayout {
    pub fn from_id_list<'a>(column_ids: impl Iterator<Item = &'a PolyID>) -> Self {
        let col_id_range = column_ids.map(|id| id.id).minmax();
        let (first_column_id, last_column_id) = col_id_range.into_option().unwrap();
        let column_count = (last_column_id - first_column_id + 1) as usize;
        Self {
            first_column_id,
            column_count,
        }
    }

    pub fn to_relative_col(&self, absolute_col: u64) -> u64 {
        absolute_col - self.first_column_id
    }

    pub fn to_absolute_col(&self, relative_col: u64) -> u64 {
        relative_col + self.first_column_id
    }

    #[inline]
    pub fn index(&self, row: usize, col: u64) -> usize {
        let col = col - self.first_column_id;
        row * self.column_count + col as usize
    }

    fn column_ids(&self) -> impl Iterator<Item = u64> {
        self.first_column_id..(self.first_column_id + self.column_count as u64)
    }
}

/// Sequence of rows of field elements, stored in a compact form.
/// Optimized for contiguous column IDs, but works with any combination.
#[derive(Clone)]
pub struct CompactData<T> {
    /// The column layout.
    layout: ColumnLayout,
    /// The cell values, stored in row-major order.
    data: Vec<T>,
    /// Bit vector of known cells, stored in row-major order.
    /// We use PaddedBitVec so that the row access is uniform and we can
    /// combine setting the same bits in each row to setting a full word.
    known_cells: PaddedBitVec,
}

impl<T: FieldElement> CompactData<T> {
    /// Creates a new empty compact data storage.
    pub fn new<'a>(column_ids: impl Iterator<Item = &'a PolyID>) -> Self {
        let layout = ColumnLayout::from_id_list(column_ids);
        let known_cells = PaddedBitVec::new(layout.column_count);
        Self {
            layout,
            data: Vec::new(),
            known_cells,
        }
    }

    pub fn layout(&self) -> ColumnLayout {
        self.layout.clone()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Returns the number of stored rows.
    pub fn len(&self) -> usize {
        self.data.len() / self.layout.column_count
    }

    /// Truncates the data to `len` rows.
    pub fn truncate(&mut self, len: usize) {
        self.data.truncate(len * self.layout.column_count);
        self.known_cells.truncate_to_rows(len);
    }

    pub fn clear(&mut self) {
        self.data.clear();
        self.known_cells.clear();
    }

    /// Appends a non-finalized row to the data, turning it into a finalized row.
    pub fn push(&mut self, row: Row<T>) {
        self.data.reserve(self.layout.column_count);
        self.known_cells.reserve_rows(1);
        for col_id in self.column_ids() {
            if let Some(v) = row.value(&col_id) {
                self.data.push(v);
                self.known_cells.push(true);
            } else {
                self.data.push(T::zero());
                self.known_cells.push(false);
            }
        }
    }

    /// Sets an entire row at the given index
    pub fn set_row(&mut self, row: usize, new_row: Row<T>) {
        let idx = row * self.layout.column_count;
        for (i, col_id) in self.column_ids().enumerate() {
            if let Some(v) = new_row.value(&col_id) {
                self.data[idx + i] = v;
                self.known_cells.set(row, i as u64, true);
            } else {
                self.known_cells.set(row, i as u64, false);
            }
        }
    }

    pub fn append_new_rows(&mut self, count: usize) {
        self.data.resize(
            self.data.len() + count * self.layout.column_count,
            T::zero(),
        );
        self.known_cells.append_empty_rows(count);
    }

    #[inline]
    fn index(&self, row: usize, col: u64) -> usize {
        self.layout.index(row, col)
    }

    fn column_ids(&self) -> impl Iterator<Item = PolyID> {
        self.layout.column_ids().map(|id| PolyID {
            id,
            ptype: PolynomialType::Committed,
        })
    }

    /// Sets a single cell
    pub fn set(&mut self, row: usize, col: u64, value: T) {
        let idx = self.index(row, col);
        self.data[idx] = value;
        let relative_col = self.layout.to_relative_col(col);
        self.known_cells.set(row, relative_col, true);
    }

    pub fn get(&self, row: usize, col: u64) -> (T, bool) {
        let idx = self.index(row, col);
        let relative_col = self.layout.to_relative_col(col);
        (self.data[idx], self.known_cells.get(row, relative_col))
    }

    pub fn known_values_in_row(&self, row: usize) -> impl Iterator<Item = (u64, &T)> {
        (0..self.layout.column_count)
            .filter(move |i| self.known_cells.get(row, *i as u64))
            .map(move |i| {
                let col = self.layout.to_absolute_col(i as u64);
                let idx = self.index(row, col);
                (col, &self.data[idx])
            })
    }

    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [u32]) {
        (&mut self.data, self.known_cells.as_mut_slice())
    }
}

/// A mutable reference into CompactData that is meant to be used
/// only for a certain block of rows, starting from row index zero.
/// It allows negative row indices as well.
pub struct CompactDataRef<'a, T> {
    pub data: &'a mut CompactData<T>,
    pub row_offset: usize,
}

impl<'a, T: FieldElement> CompactDataRef<'a, T> {
    /// Creates a new reference to the data, supplying the offset of the row
    /// that is supposed to be "row zero".
    pub fn new(data: &'a mut CompactData<T>, row_offset: usize) -> Self {
        Self { data, row_offset }
    }

    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [u32]) {
        self.data.as_mut_slices()
    }
}

/// A data structure that stores witness data.
/// It allows to finalize rows, which means that those rows are then stored in a more
/// compact form. Information about range constraints on those rows is lost, but the
/// information which cells are known is preserved.
/// There is always a single contiguous area of finalized rows from the first row to some
/// row index.
/// Once a row has been finalized, some operations trying to access it again will fail at runtime.
/// [FinalizableData::take_transposed] and [FinalizableData::get_in_progress_row] can be used to access the cells.
/// This data structure is more efficient if the used column IDs are contiguous.
#[derive(Clone)]
pub struct FinalizableData<'a, T: FieldElement> {
    /// Finalized data stored in a compact form.
    finalized_data: CompactData<T>,
    /// The non-finalized rows after the finalized data.
    post_finalized_data: Vec<Row<T>>,
    /// The list of column IDs (in sorted order), used to index finalized rows.
    column_ids: Vec<PolyID>,
    fixed_data: &'a FixedData<'a, T>,
}

impl<'a, T: FieldElement> FinalizableData<'a, T> {
    pub fn new(column_ids: &HashSet<PolyID>, fixed_data: &'a FixedData<'a, T>) -> Self {
        Self::with_initial_rows_in_progress(column_ids, [].into_iter(), fixed_data)
    }

    pub fn layout(&self) -> ColumnLayout {
        self.finalized_data.layout()
    }

    pub fn with_initial_rows_in_progress(
        column_ids: &HashSet<PolyID>,
        rows: impl Iterator<Item = Row<T>>,
        fixed_data: &'a FixedData<'a, T>,
    ) -> Self {
        let column_ids = column_ids.iter().cloned().sorted().collect::<Vec<_>>();
        Self {
            finalized_data: CompactData::new(column_ids.iter()),
            post_finalized_data: rows.collect_vec(),
            column_ids,
            fixed_data,
        }
    }

    /// Returns the total number of rows, including non-finalized rows.
    pub fn len(&self) -> usize {
        self.finalized_data.len() + self.post_finalized_data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.finalized_data.is_empty() && self.post_finalized_data.is_empty()
    }

    fn location_of_row(&self, row: usize) -> Location {
        if row < self.finalized_data.len() {
            Location::Finalized(row)
        } else {
            Location::PostFinalized(row - self.finalized_data.len())
        }
    }

    fn location_of_last_row(&self) -> Option<Location> {
        (!self.is_empty()).then(|| self.location_of_row(self.len() - 1))
    }

    pub fn push(&mut self, row: Row<T>) {
        self.post_finalized_data.push(row);
    }

    pub fn pop(&mut self) -> Option<Row<T>> {
        match self.location_of_last_row()? {
            Location::Finalized(_) => panic!("Row already finalized"),
            Location::PostFinalized(_) => self.post_finalized_data.pop(),
        }
    }

    /// Returns this data as a vector of rows in progress.
    /// Panics if any data has been finalized already.
    pub fn into_rows_in_progress(self) -> Vec<Row<T>> {
        assert!(self.finalized_data.is_empty());
        self.post_finalized_data
    }

    pub fn extend(&mut self, other: Self) {
        assert!(other.finalized_data.is_empty());
        self.post_finalized_data.extend(other.post_finalized_data);
    }

    pub fn truncate(&mut self, len: usize) {
        if len == 0 {
            self.clear();
        } else {
            match self.location_of_row(len - 1) {
                Location::Finalized(local) => {
                    self.finalized_data.truncate(local + 1);
                    self.post_finalized_data.clear();
                }
                Location::PostFinalized(local) => {
                    self.post_finalized_data.truncate(local + 1);
                }
            }
        }
    }

    pub fn clear(&mut self) {
        self.finalized_data.clear();
        self.post_finalized_data.clear();
    }

    pub fn get_mut(&mut self, i: usize) -> Option<&mut Row<T>> {
        match self.location_of_row(i) {
            Location::Finalized(_) => panic!("Row {i} already finalized."),
            Location::PostFinalized(local) => self.post_finalized_data.get_mut(local),
        }
    }

    /// Returns an iterator over the values known in that row together with the PolyIDs.
    #[auto_enum(Iterator)]
    pub fn known_values_in_row(&self, row: usize) -> impl Iterator<Item = (PolyID, T)> + '_ {
        match self.location_of_row(row) {
            Location::Finalized(local) => {
                self.finalized_data
                    .known_values_in_row(local)
                    .map(|(id, v)| {
                        (
                            PolyID {
                                id,
                                ptype: PolynomialType::Committed,
                            },
                            *v,
                        )
                    })
            }
            Location::PostFinalized(local) => {
                let row = &self.post_finalized_data[local];
                self.column_ids
                    .iter()
                    .filter_map(move |id| row.value(id).map(|v| (*id, v)))
            }
        }
    }

    pub fn last(&self) -> Option<&Row<T>> {
        match self.location_of_last_row()? {
            Location::Finalized(_) => panic!("Row already finalized"),
            Location::PostFinalized(local) => self.post_finalized_data.get(local),
        }
    }

    pub fn mutable_row_pair(&mut self, i: usize) -> (&mut Row<T>, &mut Row<T>) {
        let (before, after) = match self.location_of_row(i) {
            Location::Finalized(_) => panic!("Row {i} already finalized."),
            Location::PostFinalized(local) => self.post_finalized_data.split_at_mut(local + 1),
        };

        let current = before.last_mut().unwrap();
        let next = after.first_mut().unwrap();
        (current, next)
    }

    pub fn finalize_until(&mut self, end: usize) -> usize {
        if end < self.finalized_data.len() {
            return 0;
        }
        assert!(end <= self.finalized_data.len() + self.post_finalized_data.len());
        let rows_to_finalize = end - self.finalized_data.len();
        self.post_finalized_data
            .drain(0..rows_to_finalize)
            .for_each(|row| self.finalized_data.push(row));
        rows_to_finalize
    }

    pub fn finalize_all(&mut self) -> usize {
        self.finalize_until(self.len())
    }

    /// Appends a given amount of new finalized rows set to zero and "unknown".
    /// Returns a `CompactDataRef` that is built so that its "row zero" is the
    /// first newly appended row.
    ///
    /// Panics if there are any non-finalized rows at the end.
    pub fn append_new_finalized_rows(&mut self, count: usize) -> CompactDataRef<'_, T> {
        assert!(self.post_finalized_data.is_empty());
        let row_zero = self.finalized_data.len();
        self.finalized_data.append_new_rows(count);
        CompactDataRef::new(&mut self.finalized_data, row_zero)
    }

    /// Takes all data out of the [FinalizableData] and returns it as a list of columns.
    /// Columns are represented as a tuple of:
    /// - A list of values
    /// - A bit vector indicating which cells are known. Values of unknown cells should be ignored.
    pub fn take_transposed(&mut self) -> impl Iterator<Item = (PolyID, (Vec<T>, BitVec))> {
        log::trace!(
            "Transposing {} rows with {} columns...",
            self.len(),
            self.column_ids.len()
        );
        log::trace!("Finalizing remaining rows...");
        let counter = self.finalize_all();
        log::trace!("Needed to finalize {} / {} rows.", counter, self.len());
        assert!(self.post_finalized_data.is_empty());

        // Store transposed columns in vectors for performance reasons
        let mut columns = vec![Vec::with_capacity(self.len()); self.column_ids.len()];
        let mut known_cells_col = vec![BitVec::with_capacity(self.len()); self.column_ids.len()];

        for row in 0..self.finalized_data.len() {
            for (i, col_id) in self.column_ids.iter().enumerate() {
                let (v, known) = self.finalized_data.get(row, col_id.id);
                columns[i].push(v);
                known_cells_col[i].push(known);
            }
        }

        log::trace!("Done transposing.");

        // Pair columns with their IDs
        let column_ids = std::mem::take(&mut self.column_ids);
        columns.into_iter().zip(known_cells_col).enumerate().map(
            move |(col_index, (column, known_cells))| {
                (column_ids[col_index], (column, known_cells))
            },
        )
    }

    /// Returns a row with the given index. If the row is already finalized,
    /// it will be "unfinalized" and returned as a fresh row. Note that any
    /// range constraints will be lost in that case. If the row is not finalized,
    /// a copy of it will be returned.
    pub fn get_in_progress_row(&self, i: usize) -> Row<T> {
        match self.location_of_row(i) {
            Location::Finalized(local) => {
                let layout = self.layout();
                let mut row = Row::fresh(self.fixed_data, i);
                for column in row.columns() {
                    if column.id >= layout.first_column_id
                        && column.id < layout.first_column_id + layout.column_count as u64
                    {
                        let (value, known) = self.finalized_data.get(local, column.id);
                        if known {
                            row.set_cell_known(&column, value);
                        }
                    }
                }
                row
            }
            Location::PostFinalized(local) => self.post_finalized_data[local].clone(),
        }
    }

    /// Sets a row at the given index.
    pub fn set(&mut self, i: usize, row: Row<T>) {
        match self.location_of_row(i) {
            Location::Finalized(local) => {
                self.finalized_data.set_row(local, row);
            }
            Location::PostFinalized(local) => self.post_finalized_data[local] = row,
        }
    }
}

impl<T: FieldElement> Index<usize> for FinalizableData<'_, T> {
    type Output = Row<T>;

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.finalized_data.len() {
            panic!("Row {index} already finalized.");
        } else {
            &self.post_finalized_data[index - self.finalized_data.len()]
        }
    }
}

impl<T: FieldElement> IndexMut<usize> for FinalizableData<'_, T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.finalized_data.len() {
            panic!("Row {index} already finalized.");
        } else {
            &mut self.post_finalized_data[index - self.finalized_data.len()]
        }
    }
}

/// The area a row falls into and the offset inside that area.
enum Location {
    Finalized(usize),
    PostFinalized(usize),
}

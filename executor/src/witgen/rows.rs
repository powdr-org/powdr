use std::{
    collections::BTreeMap,
    fmt::Display,
    ops::{Add, Sub},
};

use itertools::Itertools;
use powdr_ast::analyzed::{AlgebraicExpression as Expression, AlgebraicReference, PolyID};
use powdr_number::{DegreeType, FieldElement};

use crate::witgen::Constraint;

use super::{
    affine_expression::{AffineExpression, AffineResult, AlgebraicVariable},
    data_structures::column_map::WitnessColumnMap,
    evaluators::symbolic_witness_evaluator::{SymbolicWitnessEvaluator, WitnessColumnEvaluator},
    global_constraints::RangeConstraintSet,
    machines::MachineParts,
    range_constraints::RangeConstraint,
    FixedData, PartialExpressionEvaluator,
};

/// A small wrapper around a row index, which knows the total number of rows.
/// When converted to DegreeType or usize, it will be reduced modulo the number of rows
/// (handling negative indices as well).
#[derive(Clone, Copy, PartialOrd, PartialEq, Eq, Ord)]
pub struct RowIndex {
    index: i64,
    num_rows: DegreeType,
}

impl From<RowIndex> for DegreeType {
    fn from(row_index: RowIndex) -> Self {
        // Ensure that 0 <= index < num_rows
        if row_index.index >= 0 {
            (row_index.index as DegreeType) % row_index.num_rows
        } else {
            assert!(row_index.index > -(row_index.num_rows as i64));
            row_index.num_rows - (-row_index.index as DegreeType)
        }
    }
}

impl From<RowIndex> for usize {
    fn from(row_index: RowIndex) -> Self {
        DegreeType::from(row_index).try_into().unwrap()
    }
}

impl RowIndex {
    pub fn from_i64(index: i64, num_rows: DegreeType) -> Self {
        Self { index, num_rows }
    }

    pub fn from_degree(index: DegreeType, num_rows: DegreeType) -> Self {
        Self {
            index: index.try_into().unwrap(),
            num_rows,
        }
    }

    /// Compute the current row index as usize, assuming index 0 is the given row offset.
    pub fn to_local(self, row_offset: &RowIndex) -> usize {
        let row_index = DegreeType::from(self);
        let row_offset = DegreeType::from(*row_offset);
        if row_index >= row_offset {
            (row_index - row_offset).try_into().unwrap()
        } else {
            (row_index + self.num_rows - row_offset).try_into().unwrap()
        }
    }
}

impl<T> Add<T> for RowIndex
where
    i64: TryFrom<T>,
    <i64 as TryFrom<T>>::Error: std::fmt::Debug,
{
    type Output = RowIndex;

    fn add(self, rhs: T) -> RowIndex {
        RowIndex {
            index: self.index + i64::try_from(rhs).unwrap(),
            num_rows: self.num_rows,
        }
    }
}

impl Sub<RowIndex> for RowIndex {
    type Output = i64;

    fn sub(self, rhs: RowIndex) -> i64 {
        assert_eq!(self.num_rows, rhs.num_rows);
        let num_rows = i64::try_from(self.num_rows).unwrap();
        let lhs = i64::try_from(DegreeType::from(self)).unwrap();
        let rhs = i64::try_from(DegreeType::from(rhs)).unwrap();
        let diff = lhs - rhs;
        if diff <= -num_rows / 2 {
            diff + num_rows
        } else if diff >= num_rows / 2 {
            diff - num_rows
        } else {
            diff
        }
    }
}

impl Display for RowIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.index)
    }
}

#[derive(Debug, Default, Clone, PartialEq)]
enum CellValue<T: FieldElement> {
    Known(T),
    RangeConstraint(RangeConstraint<T>),
    #[default]
    Unknown,
}

impl<T: FieldElement> CellValue<T> {
    pub fn is_known(&self) -> bool {
        matches!(self, CellValue::Known(_))
    }

    /// Returns the value if known, otherwise zero.
    pub fn unwrap_or_zero(&self) -> T {
        match self {
            CellValue::Known(v) => *v,
            _ => Default::default(),
        }
    }

    /// Returns Some(value) if known, otherwise None.
    pub fn value(&self) -> Option<T> {
        match self {
            CellValue::Known(v) => Some(*v),
            _ => None,
        }
    }

    /// Updates the cell with the new combined range constraint or new value for this cell.
    ///
    /// # Panics
    /// Panics if the update is not an improvement.
    pub fn apply_update(&mut self, c: &Constraint<T>) {
        match (&self, c) {
            (CellValue::Known(_), _) => {
                // Note that this is a problem even if the value that was set is the same,
                // because we would return that progress was made when it wasn't.
                panic!("Value was already set.");
            }
            (_, Constraint::Assignment(v)) => {
                *self = CellValue::Known(*v);
            }
            (CellValue::RangeConstraint(current), Constraint::RangeConstraint(c)) => {
                let new = c.conjunction(current);
                assert!(new != *current, "Range constraint was already set");
                log::trace!("         (the conjunction is {})", new);
                *self = CellValue::RangeConstraint(new)
            }
            (CellValue::Unknown, Constraint::RangeConstraint(c)) => {
                *self = CellValue::RangeConstraint(c.clone())
            }
        }
    }
}

impl<T: FieldElement> Display for CellValue<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CellValue::Known(v) => write!(f, "{v}"),
            CellValue::RangeConstraint(rc) => write!(f, "?  (range constraint: {rc})"),
            CellValue::Unknown => write!(f, "?"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Row<T: FieldElement> {
    values: WitnessColumnMap<CellValue<T>>,
}

impl<T: FieldElement> Row<T> {
    pub fn columns(&self) -> impl Iterator<Item = PolyID> {
        self.values.keys()
    }

    pub fn value_or_zero(&self, poly_id: &PolyID) -> T {
        self.values[poly_id].unwrap_or_zero()
    }

    pub fn value(&self, poly_id: &PolyID) -> Option<T> {
        self.values[poly_id].value()
    }

    pub fn range_constraint(&self, poly_id: &PolyID) -> Option<RangeConstraint<T>> {
        match &self.values[poly_id] {
            CellValue::RangeConstraint(c) => Some(c.clone()),
            _ => None,
        }
    }

    /// Merges two rows, updating the first.
    /// Range constraints from the second row are ignored.
    pub fn merge_with(&mut self, other: &Row<T>) -> Result<(), ()> {
        // First check for conflicts, otherwise we would have to roll back changes.
        if self
            .values
            .values()
            .zip(other.values.values())
            .any(|(cell1, cell2)| match (&cell1, &cell2) {
                (CellValue::Known(v1), CellValue::Known(v2)) => v1 != v2,
                _ => false,
            })
        {
            return Err(());
        };

        self.values
            .values_iter_mut()
            .zip(other.values.values())
            .for_each(|(cell1, cell2)| match (&cell1, &cell2) {
                (CellValue::Known(_), _) => {}
                _ => *cell1 = cell2.clone(),
            });
        Ok(())
    }

    /// Merges a list of known values into the current row.
    /// Returns an error if there is a conflict.
    pub fn merge_with_values(
        &mut self,
        values: impl Iterator<Item = (PolyID, T)>,
    ) -> Result<(), ()> {
        let stored = self.values.clone();

        for (poly_id, value) in values {
            let v = &mut self.values[&poly_id];
            if let CellValue::Known(stored_value) = v {
                if *stored_value != value {
                    self.values = stored;
                    return Err(());
                }
            }
            *v = CellValue::Known(value);
        }
        Ok(())
    }

    pub fn value_is_known(&self, poly_id: &PolyID) -> bool {
        self.values[poly_id].is_known()
    }

    pub fn set_cell_known(&mut self, poly_id: &PolyID, value: T) {
        self.values[poly_id] = CellValue::Known(value);
    }

    pub fn set_cell_unknown(&mut self, poly_id: &PolyID) {
        self.values[poly_id] = CellValue::Unknown;
    }

    pub fn apply_update(&mut self, poly_id: &PolyID, constr: &Constraint<T>) {
        self.values[poly_id].apply_update(constr);
    }
}

impl<T: FieldElement> Row<T> {
    /// Creates a "fresh" row, i.e., one that is empty but initialized with the global range constraints.
    pub fn fresh<E>(
        fixed_data: &FixedData<'_, T>,
        row: impl TryInto<DegreeType, Error = E>,
    ) -> Row<T>
    where
        E: std::fmt::Debug,
    {
        // TODO this instance could be computed exactly once (per column set) and then cloned.
        // TODO and we could copy in the external witnesses later on
        // TODO we should really only have a subset of the columns.
        let row = row.try_into().unwrap();
        let values = WitnessColumnMap::from(
            fixed_data
                .global_range_constraints()
                .witness_constraints
                .iter()
                .map(|(poly_id, rc)| {
                    if let Some(external_witness) = fixed_data.external_witness(row, &poly_id) {
                        CellValue::Known(external_witness)
                    } else if let Some(rc) = rc {
                        CellValue::RangeConstraint(rc.clone())
                    } else {
                        CellValue::Unknown
                    }
                }),
        );
        Self { values }
    }

    /// Builds a string representing the current row
    pub fn render(
        &self,
        title: &str,
        include_unknown: bool,
        parts: &MachineParts<'_, T>,
    ) -> String {
        format!(
            "{}:\n{}\n---------------------",
            title,
            self.render_values(include_unknown, parts)
        )
    }

    /// Builds a string listing all values, one by row. Nonzero entries are
    /// first, then zero, then unknown (if `include_unknown == true`).
    pub fn render_values(&self, include_unknown: bool, parts: &MachineParts<'_, T>) -> String {
        self.values
            .iter()
            .filter(|(_, cell)| cell.is_known() || include_unknown)
            .filter(|(col, _)| parts.witnesses.contains(col))
            // Nonzero first, then zero, then unknown
            .sorted_by_key(|(i, cell)| {
                (
                    match cell {
                        CellValue::Known(v) if v.is_zero() => 1,
                        CellValue::Known(_) => 0,
                        _ => 2,
                    },
                    *i,
                )
            })
            .map(|(poly_id, cell)| format!("    {} = {cell}", parts.column_name(&poly_id)))
            .join("\n")
    }
}

impl<T: FieldElement> From<Row<T>> for WitnessColumnMap<T> {
    /// Builds a map from polynomial ID to value. Unknown values are set to zero.
    fn from(row: Row<T>) -> Self {
        WitnessColumnMap::from(row.values.values_into_iter().map(|c| c.unwrap_or_zero()))
    }
}

/// A pair of mutable row references which knows how to apply updates.
pub struct RowUpdater<'row, T: FieldElement> {
    current: &'row mut Row<T>,
    next: &'row mut Row<T>,
    current_row_index: RowIndex,
}

impl<'row, T: FieldElement> RowUpdater<'row, T> {
    pub fn new(
        current: &'row mut Row<T>,
        next: &'row mut Row<T>,
        current_row_index: RowIndex,
    ) -> Self {
        Self {
            current,
            next,
            current_row_index,
        }
    }

    pub fn apply_update(&mut self, poly: &AlgebraicReference, c: &Constraint<T>) {
        match c {
            Constraint::Assignment(value) => {
                log::trace!(
                    "      => {} (Row {}) = {}",
                    poly.name,
                    self.row_number(poly),
                    value
                );
            }
            Constraint::RangeConstraint(constraint) => {
                log::trace!(
                    "      => Adding range constraint for {} (Row {}): {}",
                    poly.name,
                    self.row_number(poly),
                    constraint
                );
            }
        }
        self.get_row_mut(poly.next).apply_update(&poly.poly_id, c);
    }

    fn get_row_mut(&mut self, next: bool) -> &mut Row<T> {
        match next {
            false => self.current,
            true => self.next,
        }
    }

    fn row_number(&self, poly: &AlgebraicReference) -> RowIndex {
        match poly.next {
            false => self.current_row_index,
            true => self.current_row_index + 1,
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
pub enum UnknownStrategy {
    /// If a value is unknown, evaluate it to zero.
    Zero,
    /// If a value is unknown, leave it unknown.
    Unknown,
}

/// A pair of row references which knows which value / range constraint
/// to return for a given [AlgebraicReference].
pub struct RowPair<'row, 'a, T: FieldElement> {
    pub current: &'row Row<T>,
    pub next: Option<&'row Row<T>>,
    pub current_row_index: RowIndex,
    publics: &'row BTreeMap<&'a str, T>,
    fixed_data: &'a FixedData<'a, T>,
    unknown_strategy: UnknownStrategy,
    size: DegreeType,
}
impl<'row, 'a, T: FieldElement> RowPair<'row, 'a, T> {
    /// Creates a new row pair.
    pub fn new(
        current: &'row Row<T>,
        next: &'row Row<T>,
        current_row_index: RowIndex,
        publics: &'row BTreeMap<&'a str, T>,
        fixed_data: &'a FixedData<'a, T>,
        unknown_strategy: UnknownStrategy,
        size: DegreeType,
    ) -> Self {
        Self {
            current,
            next: Some(next),
            current_row_index,
            publics,
            fixed_data,
            unknown_strategy,
            size,
        }
    }

    /// Creates a new row pair from a single row, setting the next row to None.
    pub fn from_single_row(
        current: &'row Row<T>,
        current_row_index: RowIndex,
        publics: &'row BTreeMap<&'a str, T>,
        fixed_data: &'a FixedData<'a, T>,
        unknown_strategy: UnknownStrategy,
        size: DegreeType,
    ) -> Self {
        Self {
            current,
            next: None,
            current_row_index,
            publics,
            fixed_data,
            unknown_strategy,
            size,
        }
    }

    pub fn value_is_known(&self, poly: &AlgebraicReference) -> bool {
        self.get_row_mut(poly.next).value_is_known(&poly.poly_id)
    }

    fn get_row_mut(&self, next: bool) -> &Row<T> {
        match next {
            false => self.current,
            true => self
                .next
                .unwrap_or_else(|| panic!("Tried to access next row, but it is not available.")),
        }
    }

    fn get_row(&self, next: bool) -> &Row<T> {
        match next {
            false => self.current,
            true => self
                .next
                .unwrap_or_else(|| panic!("Tried to access next row, but it is not available.")),
        }
    }

    pub fn get_value(&self, poly: AlgebraicVariable) -> Option<T> {
        let value = match poly {
            AlgebraicVariable::Column(poly) => self.get_row(poly.next).value(&poly.poly_id),
            AlgebraicVariable::Public(public_name) => self.publics.get(public_name).copied(),
        };
        match self.unknown_strategy {
            UnknownStrategy::Zero => value.or(Some(T::ZERO)),
            UnknownStrategy::Unknown => value,
        }
    }

    /// Tries to evaluate the expression to an expression affine in the witness polynomials,
    /// taking current values of polynomials into account.
    /// @returns an expression affine in the witness polynomials
    pub fn evaluate(&self, expr: &'a Expression<T>) -> AffineResult<AlgebraicVariable<'a>, T> {
        let variables = SymbolicWitnessEvaluator::new(
            self.fixed_data,
            self.current_row_index.into(),
            self,
            self.size,
        );
        // Note that because we instantiate a fresh evaluator here, we don't benefit from caching
        // of intermediate values across calls of `RowPair::evaluate`. In practice, we only call
        // it many times for the same RowPair though.
        PartialExpressionEvaluator::new(variables, &self.fixed_data.intermediate_definitions)
            .evaluate(expr)
    }
}

impl<T: FieldElement> WitnessColumnEvaluator<T> for RowPair<'_, '_, T> {
    fn value<'b>(&self, poly: AlgebraicVariable<'b>) -> AffineResult<AlgebraicVariable<'b>, T> {
        Ok(match self.get_value(poly) {
            Some(v) => v.into(),
            None => AffineExpression::from_variable_id(poly),
        })
    }
}

impl<'a, T: FieldElement> RangeConstraintSet<AlgebraicVariable<'a>, T> for RowPair<'_, '_, T> {
    fn range_constraint(&self, poly: AlgebraicVariable<'a>) -> Option<RangeConstraint<T>> {
        match poly {
            AlgebraicVariable::Column(poly) => {
                self.get_row(poly.next).range_constraint(&poly.poly_id)
            }
            // No range constraints stored for publics.
            AlgebraicVariable::Public(_) => None,
        }
    }
}

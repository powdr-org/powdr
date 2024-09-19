use super::affine_expression::AffineResult;
use super::expression_evaluator::SymbolicVariables;
use super::FixedData;
use powdr_ast::analyzed::AlgebraicReference;
use powdr_number::{DegreeType, FieldElement};

/// Evaluates only fixed columns on a specific row.
pub struct FixedEvaluator<'a, T: FieldElement> {
    fixed_data: &'a FixedData<'a, T>,
    row: usize,
    size: DegreeType,
}

impl<'a, T: FieldElement> FixedEvaluator<'a, T> {
    pub fn new(fixed_data: &'a FixedData<'a, T>, row: usize, size: DegreeType) -> Self {
        FixedEvaluator {
            fixed_data,
            row,
            size,
        }
    }
}

impl<'a, T: FieldElement> SymbolicVariables<T> for FixedEvaluator<'a, T> {
    fn value<'b>(&self, poly: &'b AlgebraicReference) -> AffineResult<&'b AlgebraicReference, T> {
        // TODO arrays
        assert!(
            poly.is_fixed(),
            "Can only access fixed columns in the fixed evaluator."
        );
        let col_data = self.fixed_data.fixed_cols[&poly.poly_id].values(self.size);
        let degree = col_data.len();
        let row = if poly.next {
            (self.row + 1) % degree
        } else {
            self.row
        };
        Ok(col_data[row].into())
    }
}

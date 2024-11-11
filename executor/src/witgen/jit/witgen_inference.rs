use std::{
    collections::{BTreeSet, HashMap, HashSet},
    iter::once,
};

use itertools::Itertools;
use powdr_ast::{
    analyzed::{
        AlgebraicBinaryOperation, AlgebraicBinaryOperator, AlgebraicExpression as Expression,
        AlgebraicReference, AlgebraicUnaryOperation, AlgebraicUnaryOperator, Identity,
        LookupIdentity, PhantomLookupIdentity, PolyID, PolynomialIdentity, PolynomialType,
        SelectedExpressions,
    },
    parsed::visitor::AllChildren,
};
use powdr_number::FieldElement;

use crate::witgen::global_constraints::RangeConstraintSet;

use super::{
    super::{machines::MachineParts, range_constraints::RangeConstraint, FixedData},
    cell::Cell,
    eval_result::{EvalResult, KnownValue},
};

pub struct WitgenInference<'a, T: FieldElement> {
    fixed_data: &'a FixedData<'a, T>,
    parts: &'a MachineParts<'a, T>,
    block_size: usize,
    latch_row: usize,
    lookup_rhs: &'a SelectedExpressions<T>,
    range_constraints: HashMap<Cell, RangeConstraint<T>>,
    known_cells: HashSet<Cell>,
    code: Vec<String>, // TODO make this a proper expression
}
pub enum Effect<T: FieldElement> {
    Assignment(Cell, String),
    RangeConstraint(Cell, RangeConstraint<T>),
    Code(String),
}

impl<'a, T: FieldElement> WitgenInference<'a, T> {
    pub fn new(
        fixed_data: &'a FixedData<'a, T>,
        parts: &'a MachineParts<'a, T>,
        block_size: usize,
        latch_row: usize,
        initially_known_on_latch: impl IntoIterator<Item = PolyID>,
        lookup_rhs: &'a SelectedExpressions<T>,
    ) -> Self {
        Self {
            fixed_data,
            parts,
            block_size,
            latch_row,
            lookup_rhs,
            range_constraints: Default::default(),
            known_cells: initially_known_on_latch
                .into_iter()
                .map(|id| Cell {
                    column_name: fixed_data.column_name(&id).to_string(),
                    id: id.id,
                    row_offset: 0,
                })
                .collect(),
            code: Default::default(),
        }
    }

    pub fn run(&mut self) -> bool {
        self.process_effects(self.set_unreferenced_cells_to_zero());
        loop {
            let code_len = self.code.len();

            self.considered_row_range().for_each(|offset| {
                // TODO structure that better
                if self.minimum_range_around_latch().contains(&offset) {
                    // Set selector to one on latch row and zero on others.
                    let value = KnownValue::from(T::from(u32::from(offset == 0))).into();
                    if let Some(r) = self.evaluate(&self.lookup_rhs.selector, offset) {
                        self.process_effects((&r - &value).solve(self))
                    }
                }
                for id in &self.parts.identities {
                    self.infer_from_identity_at_offset(id, offset);
                }
            });
            self.force_selector_array_element_zero_if_last_remaining();

            // TODO does not consider newly learnt range constraints
            if self.code.len() == code_len {
                break;
            }
        }
        if self.all_cells_known() {
            true
        } else {
            let unknown_columns = self
                .unknown_columns()
                .map(|id| PolyID {
                    id,
                    ptype: PolynomialType::Committed,
                })
                .collect::<BTreeSet<_>>();
            log::debug!(
                "Not all cells known. The following columns still have missing entries: {}",
                unknown_columns
                    .iter()
                    .map(|poly_id| self.fixed_data.column_name(poly_id))
                    .join(", ")
            );
            log::trace!(
                "The identities concerned with these columns are:\n{}",
                self.parts
                    .identities
                    .iter()
                    .filter(|id| id.all_children().any(|e| match e {
                        Expression::Reference(r) => unknown_columns.contains(&r.poly_id),
                        _ => false,
                    }))
                    .format("\n")
            );
            false
        }
    }

    pub fn code(&self) -> String {
        self.code.join("\n")
    }

    fn cell_at_row(&self, id: u64, row_offset: i32) -> Cell {
        let poly_id = PolyID {
            id,
            ptype: PolynomialType::Committed,
        };
        Cell {
            column_name: self.parts.column_name(&poly_id).to_string(),
            id,
            row_offset,
        }
    }

    fn considered_row_range(&self) -> std::ops::RangeInclusive<i32> {
        (-(self.block_size as i32) - 4)..=(self.block_size as i32 + 4)
    }

    fn minimum_range_around_latch(&self) -> std::ops::RangeInclusive<i32> {
        assert!(self.block_size >= 1);
        let reach = (self.block_size - 1) as i32;
        -reach..=reach
    }

    /// Returns an iterator over all columns whose values are not known
    /// in a range of size `self.block_size`.
    fn unknown_columns(&self) -> impl Iterator<Item = u64> + '_ {
        let known_per_column: HashMap<u64, usize> =
            self.known_cells
                .iter()
                .fold(HashMap::new(), |mut acc, cell| {
                    *acc.entry(cell.id).or_default() += 1;
                    acc
                });
        // TODO we should also check that the known cells per column are consecutive.
        known_per_column
            .iter()
            .filter_map(|(id, count)| (*count < self.block_size).then_some(*id))
            .sorted()
    }

    fn all_cells_known(&self) -> bool {
        // TODO we should also check that the known cells per column are consecutive.
        let known_per_column: HashMap<u64, usize> =
            self.known_cells
                .iter()
                .fold(HashMap::new(), |mut acc, cell| {
                    *acc.entry(cell.id).or_default() += 1;
                    acc
                });
        known_per_column
            .values()
            .all(|count| *count >= self.block_size)
    }

    /// Sets all unreferenced cells to zero. Columns can be unreferenced
    /// if they are used in a different connection than the one we are currently
    /// considering.
    fn set_unreferenced_cells_to_zero(&self) -> Vec<Effect<T>> {
        let referenced_columns = self
            .parts
            .identities
            .iter()
            .flat_map(|id| id.all_children())
            .chain(self.lookup_rhs.all_children())
            .filter_map(|e| match e {
                Expression::Reference(r) => Some(r.poly_id),
                _ => None,
            })
            .collect::<HashSet<_>>();
        let unreferenced_columns = self
            .parts
            .witnesses
            .difference(&referenced_columns)
            .sorted();
        unreferenced_columns
            .flat_map(|poly_id| {
                self.minimum_range_around_latch().flat_map(move |row| {
                    EvalResult::from_unknown_cell(&self.cell_at_row(poly_id.id, row)).solve(self)
                })
            })
            .collect()
    }

    fn force_selector_array_element_zero_if_last_remaining(&mut self) {
        let missing = self.unknown_columns().collect::<Vec<_>>();
        if missing.len() != 1 {
            return;
        }
        let id = missing[0];
        let name = self.parts.column_name(&PolyID {
            id,
            ptype: PolynomialType::Committed,
        });
        if !name.contains("::sel[") {
            return;
        }

        for row_offset in self.minimum_range_around_latch() {
            let cell = self.cell_at_row(id, row_offset);
            self.process_effects(EvalResult::from_unknown_cell(&cell).solve(self));
        }
    }

    fn infer_from_identity_at_offset(&mut self, id: &'a Identity<T>, offset: i32) {
        let effects = match id {
            Identity::Polynomial(PolynomialIdentity { expression, .. }) => {
                self.infer_from_polynomial_identity_at_offset(expression, offset)
            }
            Identity::Lookup(LookupIdentity {
                id,
                source: _,
                left,
                right,
            })
            | Identity::PhantomLookup(PhantomLookupIdentity {
                id,
                source: _,
                left,
                right,
                multiplicity: _,
            }) => {
                // TODO multiplicity?
                self.infer_from_lookup_at_offset(*id, left, right, offset)
            }
            _ => {
                // TODO
                vec![]
            }
        };
        self.process_effects(effects);
    }

    fn infer_from_polynomial_identity_at_offset(
        &self,
        expression: &'a Expression<T>,
        offset: i32,
    ) -> Vec<Effect<T>> {
        if let Some(r) = self.evaluate(expression, offset) {
            r.solve(self)
        } else {
            vec![]
        }
    }

    fn infer_from_lookup_at_offset(
        &self,
        lookup_id: u64,
        left: &SelectedExpressions<T>,
        right: &SelectedExpressions<T>,
        offset: i32,
    ) -> Vec<Effect<T>> {
        // TODO: In the future, call the 'mutable state' to check if the
        // lookup can always be answered.

        // If the RHS is fully fixed columns...
        if right.expressions.iter().all(|e| match e {
            Expression::Reference(r) => r.is_fixed(),
            Expression::Number(_) => true,
            _ => false,
        }) {
            // and the selector is known to be 1 and all except one expression is known on the LHS.
            if self
                .evaluate(&left.selector, offset)
                .map(|s| s.is_known_one())
                == Some(true)
            {
                if let Some(inputs) = left
                    .expressions
                    .iter()
                    .map(|e| self.evaluate(e, offset))
                    .collect::<Option<Vec<_>>>()
                {
                    if inputs.iter().filter(|i| i.is_known()).count() == inputs.len() - 1 {
                        let mut var_decl = String::new();
                        let mut output_var = String::new();
                        let query = inputs
                            .iter()
                            .enumerate()
                            .map(|(i, e)| {
                                if e.is_known() {
                                    format!("LookupCell::Input(&({e}))")
                                } else {
                                    let var_name = format!("lookup_{lookup_id}_{i}");
                                    output_var = var_name.clone();
                                    var_decl
                                        .push_str(&format!("let mut {var_name}: T = 0.into();"));
                                    format!("LookupCell::Output(&mut {var_name})")
                                }
                            })
                            .format(", ");
                        let machine_call = format!(
                            "fixed_lookup_machine.process_lookup_direct(({lookup_id}, vec![{query}]))",
                        );
                        // TODO range constraints?
                        let output_expr = inputs.iter().find(|i| !i.is_known()).unwrap();
                        return once(Effect::Code(var_decl))
                            .chain(once(Effect::Code(machine_call)))
                            .chain(
                                (output_expr
                                    - &KnownValue::from_known_local_var(&output_var).into())
                                    .solve(self),
                            )
                            .collect();
                    }
                }
            }
        }
        vec![]
    }

    fn process_effects(&mut self, effects: Vec<Effect<T>>) {
        for e in effects {
            match e {
                Effect::Assignment(cell, assignment) => {
                    self.known_cells.insert(cell.clone());
                    self.code.push(assignment);
                }
                Effect::RangeConstraint(cell, rc) => {
                    self.add_range_constraint(cell, rc);
                }
                Effect::Code(code) => {
                    self.code.push(code);
                }
            }
        }
    }

    fn add_range_constraint(&mut self, cell: Cell, rc: RangeConstraint<T>) {
        let rc = self
            .range_constraint(cell.clone())
            .map_or(rc.clone(), |existing_rc| existing_rc.conjunction(&rc));
        self.range_constraints.insert(cell, rc);
    }

    fn evaluate(&self, expr: &Expression<T>, offset: i32) -> Option<EvalResult<T>> {
        Some(match expr {
            Expression::Reference(r) => {
                if r.is_fixed() {
                    let mut row = self.latch_row as i64 + offset as i64;
                    while row < 0 {
                        row += self.block_size as i64;
                    }
                    // TODO at some point we should check that all of the fixed columns are periodic.
                    let v = self.fixed_data.fixed_cols[&r.poly_id].values_max_size()[row as usize];
                    EvalResult::from_number(v)
                } else {
                    let cell = Cell::from_reference(r, offset);
                    if let Some(v) = self
                        .range_constraint(cell.clone())
                        .and_then(|rc| rc.try_to_single_value())
                    {
                        KnownValue::from(v).into()
                    } else if self.known_cells.contains(&cell) {
                        EvalResult::from_known_cell(&cell)
                    } else {
                        EvalResult::from_unknown_cell(&cell)
                    }
                }
            }
            Expression::PublicReference(_) => return None, // TODO
            Expression::Challenge(_) => return None,       // TODO
            Expression::Number(n) => EvalResult::from_number(*n),
            Expression::BinaryOperation(op) => self.evaulate_binary_operation(op, offset)?,
            Expression::UnaryOperation(op) => self.evaluate_unary_operation(op, offset)?,
        })
    }

    fn evaulate_binary_operation(
        &self,
        op: &AlgebraicBinaryOperation<T>,
        offset: i32,
    ) -> Option<EvalResult<T>> {
        let left = self.evaluate(&op.left, offset)?;
        let right = self.evaluate(&op.right, offset)?;
        match op.op {
            AlgebraicBinaryOperator::Add => Some(&left + &right),
            AlgebraicBinaryOperator::Sub => Some(&left - &right),
            AlgebraicBinaryOperator::Mul => left.try_mul(&right),
            _ => todo!(),
        }
    }

    fn evaluate_unary_operation(
        &self,
        op: &AlgebraicUnaryOperation<T>,
        offset: i32,
    ) -> Option<EvalResult<T>> {
        let expr = self.evaluate(&op.expr, offset)?;
        match op.op {
            AlgebraicUnaryOperator::Minus => Some(-&expr),
        }
    }
}

impl<T: FieldElement> RangeConstraintSet<Cell, T> for WitgenInference<'_, T> {
    // TODO would be nice to use &Cell, but this leads to lifetime trouble
    // in the solve() function.
    fn range_constraint(&self, cell: Cell) -> Option<RangeConstraint<T>> {
        self.fixed_data
            .global_range_constraints
            .range_constraint(&AlgebraicReference {
                name: Default::default(),
                poly_id: PolyID {
                    id: cell.id,
                    ptype: PolynomialType::Committed,
                },
                next: false,
            })
            .iter()
            .chain(self.range_constraints.get(&cell))
            .cloned()
            .reduce(|gc, rc| gc.conjunction(&rc))
    }
}

use std::collections::{BTreeMap, HashMap};

use itertools::{Either, Itertools};

use num_traits::One;
use powdr_ast::analyzed::{PolyID, PolynomialType};
use powdr_number::{DegreeType, FieldElement};

use crate::witgen::data_structures::identity::Identity;
use crate::witgen::data_structures::mutable_state::MutableState;
use crate::witgen::{
    rows::RowPair, util::try_to_simple_poly, EvalError, EvalResult, EvalValue, FixedData,
    IncompleteCause, QueryCallback,
};

use super::{Connection, LookupCell, Machine, MachineParts};

/// A memory machine with a fixed address space, and each address can only have one
/// value during the lifetime of the program.
/// In the simplest case, it looks like this:
/// ```pil
/// let ADDR = |i| i;
/// let v;
/// // Stores a value, fails if the cell already has a value that's different
/// instr mstore X, Y -> { [X, Y] in [ADDR, v] }
/// // Loads a value. If the cell is empty, the prover can choose a value.
/// // Note that this is the same lookup, only Y is considered an output instead
/// // of an input.
/// instr mload X -> Y { [X, Y] in [ADDR, v] }
/// ```
pub struct WriteOnceMemory<'a, T: FieldElement> {
    degree: DegreeType,
    connections: BTreeMap<u64, Connection<'a, T>>,
    /// The fixed data
    fixed_data: &'a FixedData<'a, T>,
    /// The polynomials that are used as values (witness polynomials on the RHS)
    value_polys: Vec<PolyID>,
    /// A map from keys to row indices
    key_to_index: BTreeMap<Vec<T>, DegreeType>,
    /// The memory content
    data: BTreeMap<DegreeType, Vec<Option<T>>>,
    name: String,
}

impl<'a, T: FieldElement> WriteOnceMemory<'a, T> {
    pub fn try_new(
        name: String,
        fixed_data: &'a FixedData<'a, T>,
        parts: &MachineParts<'a, T>,
    ) -> Option<Self> {
        if parts
            .identities
            .iter()
            // The only identity we'd expect is a bus receive.
            .any(|id| !matches!(id, Identity::BusReceive(_)))
        {
            return None;
        }

        if parts.connections.is_empty() {
            return None;
        }

        if !parts.connections.values().all(|i| i.is_lookup()) {
            return None;
        }

        // All connecting identities should have a selector of 1
        if parts
            .connections
            .values()
            .any(|i| !i.right.selector.is_one())
        {
            return None;
        }

        // All RHS expressions should be the same
        let rhs_exprs = parts
            .connections
            .values()
            .map(|i| &i.right.expressions)
            .collect_vec();
        if !rhs_exprs.iter().all_equal() {
            return None;
        }

        let rhs_polys = rhs_exprs
            .first()
            .unwrap()
            .iter()
            .map(|e| try_to_simple_poly(e))
            .collect::<Option<Vec<_>>>();

        // Returns None if any RHS polynomial is a complex expression
        let rhs_polys = rhs_polys?;

        // Build a Vec<PolyID> for the key and value polynomials
        let (key_polys, value_polys): (Vec<_>, Vec<_>) = rhs_polys.into_iter().partition_map(|p| {
            assert!(!p.next);
            if p.poly_id.ptype == PolynomialType::Constant {
                Either::Left(p.poly_id)
            } else {
                Either::Right(p.poly_id)
            }
        });

        let degree = parts.common_degree_range().max;

        let mut key_to_index = BTreeMap::new();
        for row in 0..degree {
            let key = key_polys
                .iter()
                .map(|k| fixed_data.fixed_cols[k].values(degree)[row as usize])
                .collect::<Vec<_>>();
            if key_to_index.insert(key, row).is_some() {
                // Duplicate keys, can't be a write-once memory
                return None;
            }
        }

        if !parts.prover_functions.is_empty() {
            log::warn!(
                "WriteOnceMemory machine does not support prover functions.\
                The following prover functions are ignored:\n{}",
                parts.prover_functions.iter().format("\n")
            );
        }

        Some(Self {
            degree,
            connections: parts.connections.clone(),
            name,
            fixed_data,
            value_polys,
            key_to_index,
            data: BTreeMap::new(),
        })
    }

    fn process_plookup_internal(
        &mut self,
        identity_id: u64,
        caller_rows: &RowPair<'_, 'a, T>,
    ) -> EvalResult<'a, T> {
        let identity = self.connections[&identity_id];
        let args = identity
            .left
            .expressions
            .iter()
            .map(|e| caller_rows.evaluate(e).unwrap())
            .collect::<Vec<_>>();
        let (key_expressions, value_expressions): (Vec<_>, Vec<_>) = args
            .iter()
            .zip(identity.right.expressions.iter())
            .partition(|(_, r)| {
                try_to_simple_poly(r).unwrap().poly_id.ptype == PolynomialType::Constant
            });
        let key = key_expressions
            .into_iter()
            .map(|(k, _)| k.constant_value())
            .collect::<Option<Vec<_>>>();
        let value_expressions = value_expressions
            .into_iter()
            .map(|(v, _)| v)
            .collect::<Vec<_>>();
        let value = value_expressions
            .iter()
            .map(|v| v.constant_value())
            .collect::<Vec<_>>();

        log::trace!("Key: {:?}", key);
        log::trace!("Value: {:?}", value);

        let Some(key) = key else {
            return Ok(EvalValue::incomplete(
                IncompleteCause::NonConstantRequiredArgument("key"),
            ));
        };

        let index = self.key_to_index.get(&key).cloned().ok_or_else(|| {
            EvalError::from(format!("Key {key:?} not found in write-once memory"))
        })?;

        // If there is an externally provided memory value, use it
        let external_witness_value = self
            .value_polys
            .iter()
            .map(|p| self.fixed_data.external_witness(index, p))
            .collect::<Vec<_>>();
        let stored_value = match self.data.get(&index) {
            Some(values) => values
                .iter()
                .zip(external_witness_value.iter())
                .map(|(&stored, &external)| external.or(stored))
                .collect(),
            None => external_witness_value,
        };

        let mut updates = vec![];
        let values = value_expressions
            .into_iter()
            .zip(stored_value.iter())
            .map(|(l, r)| {
                match (l.constant_value(), r) {
                    // No value provided and none stored -> keep value as None
                    (None, None) => Ok::<Option<T>, EvalError<T>>(None),
                    // Value provided but none stored -> write, no updates
                    (Some(l), None) => Ok(Some(l)),
                    // Value stored -> keep stored value & either update LHS or assert equality
                    (_, Some(r)) => {
                        updates.extend((l.clone() - (*r).into()).solve()?.constraints);
                        Ok(Some(*r))
                    }
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Write values
        let is_complete = !values.contains(&None);
        let side_effect = self.data.insert(index, values).is_none();

        match is_complete {
            true => Ok({
                let res = EvalValue::complete(updates);
                if side_effect {
                    res.report_side_effect()
                } else {
                    res
                }
            }),
            false => Ok(EvalValue::incomplete_with_constraints(
                updates,
                IncompleteCause::NonConstantRequiredArgument("value"),
            )),
        }
    }
}

impl<'a, T: FieldElement> Machine<'a, T> for WriteOnceMemory<'a, T> {
    fn process_lookup_direct<'b, 'c, Q: QueryCallback<T>>(
        &mut self,
        _mutable_state: &'b MutableState<'a, T, Q>,
        _identity_id: u64,
        _values: &mut [LookupCell<'c, T>],
    ) -> Result<bool, EvalError<T>> {
        unimplemented!("Direct lookup not supported by machine {}.", self.name())
    }

    fn identity_ids(&self) -> Vec<u64> {
        self.connections.keys().copied().collect()
    }

    fn name(&self) -> &str {
        &self.name
    }

    fn process_plookup<'b, Q: QueryCallback<T>>(
        &mut self,
        _mutable_state: &'b MutableState<'a, T, Q>,
        identity_id: u64,
        caller_rows: &RowPair<'_, 'a, T>,
    ) -> EvalResult<'a, T> {
        self.process_plookup_internal(identity_id, caller_rows)
    }

    fn take_witness_col_values<'b, Q: QueryCallback<T>>(
        &mut self,
        _mutable_state: &'b MutableState<'a, T, Q>,
    ) -> HashMap<String, Vec<T>> {
        self.value_polys
            .iter()
            .enumerate()
            .map(|(value_index, poly)| {
                let column = self.fixed_data.witness_cols[poly]
                    .external_values
                    .cloned()
                    .map(|mut external_values| {
                        // External witness values might only be provided partially.
                        external_values.resize(self.degree as usize, T::zero());
                        external_values
                    })
                    .unwrap_or_else(|| {
                        let mut column = vec![T::zero(); self.degree as usize];
                        for (row, values) in self.data.iter() {
                            column[*row as usize] = values[value_index].unwrap_or_default();
                        }
                        column
                    });
                (*poly, column)
            })
            .map(|(poly_id, column)| (self.fixed_data.column_name(&poly_id).to_string(), column))
            .collect()
    }
}

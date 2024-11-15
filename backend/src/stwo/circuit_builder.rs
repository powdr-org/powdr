use num_traits::One;
extern crate alloc;
use alloc::{collections::btree_map::BTreeMap, string::String, vec::Vec};
use powdr_ast::analyzed::Identity;
use powdr_ast::analyzed::{
    AlgebraicBinaryOperation, AlgebraicBinaryOperator, AlgebraicExpression, Analyzed,
};
use powdr_number::FieldElement;
use powdr_number::LargeInt;
use std::sync::Arc;

use powdr_ast::analyzed::{
    AlgebraicUnaryOperation, AlgebraicUnaryOperator, PolyID, PolynomialType,
};
use stwo_prover::constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval};
use stwo_prover::core::backend::Col;
use stwo_prover::core::backend::ColumnOps;
use stwo_prover::core::fields::m31::BaseField;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::{ExtensionOf, FieldOps};
use stwo_prover::core::poly::circle::{CanonicCoset, CircleEvaluation};
use stwo_prover::core::poly::BitReversedOrder;
use stwo_prover::core::ColumnVec;

pub type PowdrComponent<'a, F> = FrameworkComponent<PowdrEval<F>>;

pub(crate) fn gen_stwo_circuit_trace<T, B, F>(
    witness: Option<&[(String, Vec<T>)]>,
    analyzed: Arc<Analyzed<T>>,
) -> ColumnVec<CircleEvaluation<B, BaseField, BitReversedOrder>>
where
    T: FieldElement, //only Merenne31Field is supported, checked in runtime
    B: FieldOps<M31> + ColumnOps<F>, // Ensure B implements FieldOps for M31
    F: ExtensionOf<BaseField>,
{
    let element: Option<Vec<(String, Col<B, M31>)>> = Some(
        witness
            .as_ref()
            .expect("Witness needs to be set")
            .iter()
            .map(|(name, values)| {
                let values = values
                    .iter()
                    .map(|v| v.try_into_i32().unwrap().into())
                    .collect();
                (name.clone(), values)
            })
            .collect(),
    );

    let domain = CanonicCoset::new(analyzed.degree().ilog2()).circle_domain();
    element
        .map(|elements| {
            elements
                .iter()
                .map(|(_, base_column)| CircleEvaluation::new(domain, base_column.clone()))
                .collect()
        })
        .unwrap()
}

pub struct PowdrEval<T> {
    analyzed: Arc<Analyzed<T>>,
    witness_columns: BTreeMap<PolyID, usize>,
}

impl<T: FieldElement> PowdrEval<T> {
    pub fn new(analyzed: Arc<Analyzed<T>>) -> Self {
        let witness_columns: BTreeMap<PolyID, usize> = analyzed
            .definitions_in_source_order(PolynomialType::Committed)
            .flat_map(|(symbol, _)| symbol.array_elements())
            .enumerate()
            .map(|(index, (_, id))| (id, index))
            .collect();

        Self {
            analyzed,
            witness_columns,
        }
    }
}

impl<T: FieldElement> FrameworkEval for PowdrEval<T> {
    fn log_size(&self) -> u32 {
        self.analyzed.degree().ilog2()
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.analyzed.degree().ilog2() + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        assert!(
            self.analyzed.constant_count() == 0 && self.analyzed.publics_count() == 0,
            "Error: Expected no fixed columns nor public inputs, as they are not supported yet.",
        );

        let witness_eval: BTreeMap<PolyID, [<E as EvalAtRow>::F; 2]> = self
            .witness_columns
            .keys()
            .map(|poly_id| (*poly_id, eval.next_interaction_mask(0, [0, 1])))
            .collect();

        for id in self
            .analyzed
            .identities_with_inlined_intermediate_polynomials()
        {
            match id {
                Identity::Polynomial(identity) => {
                    let expr = to_stwo_expression::<T, E>(&identity.expression, &witness_eval);
                    eval.add_constraint(expr);
                }
                Identity::Connect(..) => {
                    unimplemented!("Connect is not implemented in stwo yet")
                }
                Identity::Lookup(..) => {
                    unimplemented!("Lookup is not implemented in stwo yet")
                }
                Identity::Permutation(..) => {
                    unimplemented!("Permutation is not implemented in stwo yet")
                }
                Identity::PhantomPermutation(..) => {
                    unimplemented!("PhantomPermutation is not implemented in stwo yet")
                }
                Identity::PhantomLookup(..) => {
                    unimplemented!("PhantomLookup is not implemented in stwo yet")
                }
            }
        }
        eval
    }
}

fn to_stwo_expression<T: FieldElement, E: EvalAtRow>(
    expr: &AlgebraicExpression<T>,
    witness_eval: &BTreeMap<PolyID, [<E as EvalAtRow>::F; 2]>,
) -> E::F {
    use AlgebraicBinaryOperator::*;
    match expr {
        AlgebraicExpression::Reference(r) => {
            let poly_id = r.poly_id;

            match poly_id.ptype {
                PolynomialType::Committed => match r.next {
                    false => witness_eval[&poly_id][0].clone(),
                    true => witness_eval[&poly_id][1].clone(),
                },
                PolynomialType::Constant => {
                    unimplemented!("Constant polynomials are not supported in stwo yet")
                }
                PolynomialType::Intermediate => {
                    unimplemented!("Intermediate polynomials are not supported in stwo yet")
                }
            }
        }
        AlgebraicExpression::PublicReference(..) => {
            unimplemented!("Public references are not supported in stwo yet")
        }
        AlgebraicExpression::Number(n) => E::F::from(M31::from(n.try_into_i32().unwrap())),
        AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation {
            left,
            op: Pow,
            right,
        }) => match **right {
            AlgebraicExpression::Number(n) => {
                let left = to_stwo_expression::<T, E>(left, witness_eval);
                (0u32..n.to_integer().try_into_u32().unwrap())
                    .fold(E::F::one(), |acc, _| acc * left.clone())
            }
            _ => unimplemented!("pow with non-constant exponent"),
        },
        AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation { left, op, right }) => {
            let left = to_stwo_expression::<T, E>(left, witness_eval);
            let right = to_stwo_expression::<T, E>(right, witness_eval);

            match op {
                Add => left + right,
                Sub => left - right,
                Mul => left * right,
                Pow => unreachable!("This case was handled above"),
            }
        }
        AlgebraicExpression::UnaryOperation(AlgebraicUnaryOperation { op, expr }) => {
            let expr: <E as EvalAtRow>::F = to_stwo_expression::<T, E>(expr, witness_eval);

            match op {
                AlgebraicUnaryOperator::Minus => -expr,
            }
        }
        AlgebraicExpression::Challenge(_challenge) => {
            unimplemented!("challenges are not supported in this stwo yet")
        }
    }
}

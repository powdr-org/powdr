use core::unreachable;
use powdr_ast::parsed::visitor::AllChildren;
use powdr_executor_utils::expression_evaluator::{ExpressionEvaluator, TerminalAccess};
use std::collections::HashSet;

extern crate alloc;
use crate::stwo::prover::into_stwo_field;
use alloc::collections::btree_map::BTreeMap;
use powdr_ast::analyzed::{AlgebraicExpression, AlgebraicReference, Analyzed, Challenge, Identity};
use powdr_ast::analyzed::{PolyID, PolynomialType};
use powdr_number::Mersenne31Field as M31;
use stwo_prover::constraint_framework::preprocessed_columns::PreprocessedColumn;
use stwo_prover::constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, ORIGINAL_TRACE_IDX,
};
use stwo_prover::core::backend::{Column, ColumnOps};
use stwo_prover::core::fields::m31::BaseField;
use stwo_prover::core::fields::{ExtensionOf, FieldOps};
use stwo_prover::core::poly::circle::{CircleDomain, CircleEvaluation};
use stwo_prover::core::poly::BitReversedOrder;
use stwo_prover::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};

pub type PowdrComponent = FrameworkComponent<PowdrEval>;

pub fn gen_stwo_circle_column<B, F>(
    domain: CircleDomain,
    slice: &[M31],
) -> CircleEvaluation<B, BaseField, BitReversedOrder>
where
    B: FieldOps<BaseField> + ColumnOps<F>,

    F: ExtensionOf<BaseField>,
{
    assert!(
        slice.len().ilog2() == domain.size().ilog2(),
        "column size must be equal to domain size"
    );
    let mut column: <B as ColumnOps<BaseField>>::Column =
        <B as ColumnOps<BaseField>>::Column::zeros(slice.len());
    slice.iter().enumerate().for_each(|(i, v)| {
        column.set(
            bit_reverse_index(
                coset_index_to_circle_domain_index(i, slice.len().ilog2()),
                slice.len().ilog2(),
            ),
            into_stwo_field(v),
        );
    });

    CircleEvaluation::new(domain, column)
}

pub struct PowdrEval {
    log_degree: u32,
    analyzed: Analyzed<M31>,
    // the pre-processed are indexed in the whole proof, instead of in each component.
    // this offset represents the index of the first pre-processed column in this component
    preprocess_col_offset: usize,
    witness_columns_stage0: BTreeMap<PolyID, usize>,
    witness_columns_stage1: BTreeMap<PolyID, usize>,
    constant_shifted: BTreeMap<PolyID, usize>,
    constant_columns: BTreeMap<PolyID, usize>,
    // stwo supports maximum 2 stages, challenges are only created after stage 0
    pub challenges: BTreeMap<u64, M31>,
}

impl PowdrEval {
    pub fn new(
        analyzed: Analyzed<M31>,
        preprocess_col_offset: usize,
        log_degree: u32,
        challenges: BTreeMap<u64, M31>,
    ) -> Self {
        let witness_columns_stage0: BTreeMap<PolyID, usize> = analyzed
            .definitions_in_source_order(PolynomialType::Committed)
            .filter(|(symbol, _)| symbol.stage.is_none() || symbol.stage == Some(0))
            .flat_map(|(symbol, _)| symbol.array_elements())
            .enumerate()
            .map(|(index, (_, id))| (id, index))
            .collect();

        let witness_columns_stage1: BTreeMap<PolyID, usize> = analyzed
            .definitions_in_source_order(PolynomialType::Committed)
            .filter(|(symbol, _)| symbol.stage == Some(1))
            .flat_map(|(symbol, _)| symbol.array_elements())
            .enumerate()
            .map(|(index, (_, id))| (id, index + witness_columns_stage0.len()))
            .collect();

        let constant_with_next_list = get_constant_with_next_list(&analyzed);

        let constant_shifted: BTreeMap<PolyID, usize> = analyzed
            .definitions_in_source_order(PolynomialType::Constant)
            .flat_map(|(symbol, _)| symbol.array_elements())
            .enumerate()
            .filter(|(_, (name, _))| constant_with_next_list.contains(name))
            .map(|(index, (_, id))| (id, index))
            .collect();

        let constant_columns: BTreeMap<PolyID, usize> = analyzed
            .definitions_in_source_order(PolynomialType::Constant)
            .flat_map(|(symbol, _)| symbol.array_elements())
            .enumerate()
            .map(|(index, (_, id))| (id, index))
            .collect();

        Self {
            log_degree,
            analyzed,
            preprocess_col_offset,
            witness_columns_stage0,
            witness_columns_stage1,
            constant_shifted,
            constant_columns,
            challenges,
        }
    }
}

struct Data<'a, F> {
    witness_eval: &'a BTreeMap<PolyID, [F; 2]>,
    constant_shifted_eval: &'a BTreeMap<PolyID, F>,
    constant_eval: &'a BTreeMap<PolyID, F>,
    // challenges for stage 1
    challenges: &'a BTreeMap<u64, F>,
}

impl<F: Clone> TerminalAccess<F> for &Data<'_, F> {
    fn get(&self, poly_ref: &AlgebraicReference) -> F {
        match poly_ref.poly_id.ptype {
            PolynomialType::Committed => match poly_ref.next {
                false => self.witness_eval[&poly_ref.poly_id][0].clone(),
                true => self.witness_eval[&poly_ref.poly_id][1].clone(),
            },
            PolynomialType::Constant => match poly_ref.next {
                false => self.constant_eval[&poly_ref.poly_id].clone(),
                true => self.constant_shifted_eval[&poly_ref.poly_id].clone(),
            },
            PolynomialType::Intermediate => unreachable!(),
        }
    }

    fn get_public(&self, _public: &str) -> F {
        unimplemented!("Public references are not supported in stwo yet")
    }

    fn get_challenge(&self, challenge: &Challenge) -> F {
        self.challenges[&challenge.id].clone()
    }
}

impl FrameworkEval for PowdrEval {
    fn log_size(&self) -> u32 {
        self.log_degree
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_degree + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        assert!(
            self.analyzed.publics_count() == 0,
            "Error: Expected no public inputs, as they are not supported yet.",
        );

        let mut witness_eval_stage0: BTreeMap<PolyID, [<E as EvalAtRow>::F; 2]> = self
            .witness_columns_stage0
            .keys()
            .map(|poly_id| {
                (
                    *poly_id,
                    eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]),
                )
            })
            .collect();

        let witness_eval_stage1: BTreeMap<PolyID, [<E as EvalAtRow>::F; 2]> = self
            .witness_columns_stage1
            .keys()
            .map(|poly_id| (*poly_id, eval.next_interaction_mask(2, [0, 1])))
            .collect();

        let constant_eval: BTreeMap<_, _> = self
            .constant_columns
            .keys()
            .enumerate()
            .map(|(i, poly_id)| {
                (
                    *poly_id,
                    eval.get_preprocessed_column(PreprocessedColumn::Plonk(
                        i + self.preprocess_col_offset,
                    )),
                )
            })
            .collect();

        let constant_shifted_eval: BTreeMap<_, _> = self
            .constant_shifted
            .keys()
            .enumerate()
            .map(|(i, poly_id)| {
                (
                    *poly_id,
                    eval.get_preprocessed_column(PreprocessedColumn::Plonk(
                        i + constant_eval.len() + self.preprocess_col_offset,
                    )),
                )
            })
            .collect();
        let challenges = self
            .challenges
            .iter()
            .map(|(k, v)| (*k, E::F::from(into_stwo_field(v))))
            .collect();
        witness_eval_stage0.extend(witness_eval_stage1);
        let intermediate_definitions = self.analyzed.intermediate_definitions();
        let data = Data {
            witness_eval: &witness_eval_stage0,
            constant_shifted_eval: &constant_shifted_eval,
            constant_eval: &constant_eval,
            challenges: &challenges,
        };
        let mut evaluator =
            ExpressionEvaluator::new_with_custom_expr(&data, &intermediate_definitions, |v| {
                E::F::from(into_stwo_field(v))
            });

        for id in &self.analyzed.identities {
            match id {
                Identity::Polynomial(identity) => {
                    let expr = evaluator.evaluate(&identity.expression);
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
                Identity::PhantomPermutation(..)
                | Identity::PhantomLookup(..)
                | Identity::PhantomBusInteraction(..) => {}
            }
        }
        eval
    }
}

// This function creates a list of the names of the constant polynomials that have next references constraint
pub fn get_constant_with_next_list(analyzed: &Analyzed<M31>) -> HashSet<&String> {
    let mut constant_with_next_list: HashSet<&String> = HashSet::new();
    analyzed.all_children().for_each(|e| {
        if let AlgebraicExpression::Reference(AlgebraicReference {
            name,
            poly_id,
            next,
        }) = e
        {
            if matches!(poly_id.ptype, PolynomialType::Constant) && *next {
                // add the name of the constant polynomial to the list
                constant_with_next_list.insert(name);
            }
        };
    });
    constant_with_next_list
}

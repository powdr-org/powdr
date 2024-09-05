use expander_rs::{Circuit,GKRConfig};
use powdr_number::FieldElement;
use std::{cmp::max, collections::BTreeMap, iter, sync::Arc};

use powdr_ast::analyzed::{
    AlgebraicBinaryOperation, AlgebraicBinaryOperator, AlgebraicExpression, SelectedExpressions,
};
use powdr_ast::{
    analyzed::{Analyzed, IdentityKind},
    parsed::visitor::ExpressionVisitable,
};

use super::circuit_builder;

pub fn convert_pil_to_gkr<T: FieldElement,C:GKRConfig>(pil: Arc<Analyzed<T>>)->Circuit<C>{
    let mut circuit=Circuit::<C>::default();
    pil.degree();
    pil.commitment_count()+pil.constant_count();
    circuit
}

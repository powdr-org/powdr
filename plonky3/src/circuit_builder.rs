//! A plonky3 adapter for powdr

use std::{any::TypeId, collections::BTreeMap};

use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_field::AbstractField;
use p3_goldilocks::Goldilocks;
use p3_matrix::{dense::RowMajorMatrix, MatrixRowSlices};
use powdr_ast::analyzed::{
    AlgebraicBinaryOperation, AlgebraicBinaryOperator, AlgebraicExpression,
    AlgebraicUnaryOperation, AlgebraicUnaryOperator, Analyzed, IdentityKind, PolynomialType,
};
use powdr_executor::witgen::WitgenCallback;
use powdr_number::{FieldElement, GoldilocksField, LargeInt};

pub type Val = p3_goldilocks::Goldilocks;

pub(crate) struct PowdrCircuit<'a, T> {
    /// The analyzed PIL
    analyzed: &'a Analyzed<T>,
    /// The value of the witness columns, if set
    witness: Option<&'a [(String, Vec<T>)]>,
    /// Column name and index of public cells
    publics: Vec<(String, usize)>,
    /// Callback to augment the witness in the later stages
    _witgen_callback: Option<WitgenCallback<T>>,
}

impl<'a, T: FieldElement> PowdrCircuit<'a, T> {
    pub fn generate_trace_rows(&self) -> RowMajorMatrix<Goldilocks> {
        // an iterator over all columns, committed then fixed
        let witness = self.witness().iter();
        let publics = self.publics.iter();
        let len = self.analyzed.degree.unwrap();

        // for each row, get the value of each column
        let values = (0..len)
            .flat_map(move |i| {
                // witness values
                witness
                .clone()
                .map(move |(_, v)| cast_to_goldilocks(v[i as usize]))
                .chain(
                    publics
                    .clone()
                    .map(move |(_, idx)| match i as usize == *idx {
                        true => cast_to_goldilocks(T::one()),
                        false => cast_to_goldilocks(T::zero()),
                    })
                )}).collect();
        RowMajorMatrix::new(values, self.width())
    }
}

pub fn cast_to_goldilocks<T: FieldElement>(v: T) -> Val {
    assert_eq!(TypeId::of::<T>(), TypeId::of::<GoldilocksField>());
    Val::from_canonical_u64(v.to_integer().try_into_u64().unwrap())
}

fn get_publics<T: FieldElement>(analyzed: &Analyzed<T>) -> Vec<(String, usize)> {
    let mut publics = analyzed
        .public_declarations
        .values()
        .map(|public_declaration| {
            let witness_name = public_declaration.referenced_poly_name();
            let witness_offset = public_declaration.index as usize;
            (witness_name, witness_offset)
        })
        .collect::<Vec<_>>();

    // Sort, so that the order is deterministic
    publics.sort();
    publics
}

impl<'a, T: FieldElement> PowdrCircuit<'a, T> {
    pub(crate) fn new(analyzed: &'a Analyzed<T>) -> Self {
        if analyzed.constant_count() > 0 {
            unimplemented!("Fixed columns are not supported in Plonky3");
        }

        // if !analyzed.public_declarations.is_empty() {
        //     unimplemented!("Public declarations are not supported in Plonky3");
        // }

        Self {
            analyzed,
            witness: None,
            publics: get_publics(analyzed),
            _witgen_callback: None,
        }
    }

    fn witness(&self) -> &'a [(String, Vec<T>)] {
        self.witness.as_ref().unwrap()
    }

    pub(crate) fn with_witness(self, witness: &'a [(String, Vec<T>)]) -> Self {
        Self {
            witness: Some(witness),
            ..self
        }
    }

    pub(crate) fn with_witgen_callback(self, witgen_callback: WitgenCallback<T>) -> Self {
        Self {
            _witgen_callback: Some(witgen_callback),
            ..self
        }
    }

    pub(crate) fn publics_idxs(&self) -> Vec<usize> {
        // self.publics -> idx of the witness col
        // TODO: return actual pubval from this
        let witness = self
            .witness
            .as_ref()
            .expect("Witness needs to be set")
            .iter()
            .enumerate()
            .map(|(idx, (name, _))| (name, idx))
            .collect::<BTreeMap<_, _>>();

        self.publics
            .iter()
            .map(|(col_name, _)| *witness.get(col_name).unwrap())
            .collect()
    }

    /// Conversion to plonky3 expression
    fn to_plonky3_expr<AB: AirBuilder<F = Val>>(
        &self,
        e: &AlgebraicExpression<T>,
        matrix: &AB::M,
    ) -> AB::Expr {
        let res = match e {
            AlgebraicExpression::Reference(r) => {
                let poly_id = r.poly_id;

                let row = match r.next {
                    true => matrix.row_slice(1),
                    false => matrix.row_slice(0),
                };

                // witness columns indexes are unchanged, fixed ones are offset by `commitment_count`
                let index = match poly_id.ptype {
                    PolynomialType::Committed => {
                        assert!(
                            r.poly_id.id < self.analyzed.commitment_count() as u64,
                            "Plonky3 expects `poly_id` to be contiguous"
                        );
                        r.poly_id.id as usize
                    }
                    PolynomialType::Constant => {
                        unreachable!(
                            "fixed columns are not supported, should have been checked earlier"
                        )
                    }
                    PolynomialType::Intermediate => {
                        unreachable!("intermediate polynomials should have been inlined")
                    }
                };

                row[index].into()
            }
            AlgebraicExpression::PublicReference(_) => unimplemented!(
                "public references are not supported inside algebraic expressions in plonky3"
            ),
            AlgebraicExpression::Number(n) => AB::Expr::from(cast_to_goldilocks(*n)),
            AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation { left, op, right }) => {
                let left = self.to_plonky3_expr::<AB>(left, matrix);
                let right = self.to_plonky3_expr::<AB>(right, matrix);

                match op {
                    AlgebraicBinaryOperator::Add => left + right,
                    AlgebraicBinaryOperator::Sub => left - right,
                    AlgebraicBinaryOperator::Mul => left * right,
                    AlgebraicBinaryOperator::Pow => {
                        unreachable!("exponentiations should have been evaluated")
                    }
                }
            }
            AlgebraicExpression::UnaryOperation(AlgebraicUnaryOperation { op, expr }) => {
                let expr: <AB as AirBuilder>::Expr = self.to_plonky3_expr::<AB>(expr, matrix);

                match op {
                    AlgebraicUnaryOperator::Minus => -expr,
                }
            }
            AlgebraicExpression::Challenge(challenge) => {
                unimplemented!("Challenge API for {challenge:?} not accessible in plonky3")
            }
        };
        res
    }
}

impl<'a, T: FieldElement> BaseAir<Val> for PowdrCircuit<'a, T> {
    fn width(&self) -> usize {
        assert_eq!(self.analyzed.constant_count(), 0);
        self.analyzed.commitment_count() + self.analyzed.publics_count()
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<Val>> {
        panic!()
    }
}

impl<'a, T: FieldElement, AB: AirBuilderWithPublicValues<F = Val>> Air<AB> for PowdrCircuit<'a, T> {
    fn eval(&self, builder: &mut AB) {
        let matrix = builder.main();
        let pi = builder.public_values();

        // public constraints
        let pi_moved = pi.into_iter()
            .map(|itm| *itm)
            .collect::<Vec<<AB as AirBuilderWithPublicValues>::PublicVar>>();
        let local = matrix.row_slice(0);

        // constraining Pi * (Ci - pub[i]) = 0
        let mut pub_idx = 0;
        for witness_col_idx in self.publics_idxs() {
            builder.assert_zero(local[self.analyzed.commitment_count() + pub_idx] * (local[witness_col_idx] - pi_moved[pub_idx].into()));
            pub_idx +=1
        }

        // circuit constraints
        for identity in &self
            .analyzed
            .identities_with_inlined_intermediate_polynomials()
        {
            match identity.kind {
                IdentityKind::Polynomial => {
                    assert_eq!(identity.left.expressions.len(), 0);
                    assert_eq!(identity.right.expressions.len(), 0);
                    assert!(identity.right.selector.is_none());

                    let left = self
                        .to_plonky3_expr::<AB>(identity.left.selector.as_ref().unwrap(), &matrix);

                    builder.assert_zero(left);
                }
                IdentityKind::Plookup => unimplemented!("Plonky3 does not support plookup"),
                IdentityKind::Permutation => {
                    unimplemented!("Plonky3 does not support permutations")
                }
                IdentityKind::Connect => unimplemented!("Plonky3 does not support connections"),
            }
        }
    }
}

//! PIL-based optimizer
#![deny(clippy::print_stdout)]

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::iter::once;

use powdr_ast::analyzed::{
    AlgebraicBinaryOperation, AlgebraicBinaryOperator, AlgebraicExpression, AlgebraicReference,
    AlgebraicUnaryOperation, AlgebraicUnaryOperator, Analyzed, Expression, FunctionValueDefinition,
    IdentityKind, PolyID, PolynomialReference, PolynomialType, Reference, SymbolKind,
    TypeConstructor, TypeDeclaration, TypedExpression,
};
use powdr_ast::parsed::types::Type;
use powdr_ast::parsed::visitor::{AllChildren, Children, ExpressionVisitable};
use powdr_ast::parsed::{EnumDeclaration, Number, StructDeclaration};
use powdr_number::{BigUint, FieldElement};

pub fn optimize<T: FieldElement>(mut pil_file: Analyzed<T>) -> Analyzed<T> {
    let col_count_pre = (pil_file.commitment_count(), pil_file.constant_count());
    remove_unreferenced_definitions(&mut pil_file);
    remove_constant_fixed_columns(&mut pil_file);
    simplify_identities(&mut pil_file);
    extract_constant_lookups(&mut pil_file);
    remove_constant_witness_columns(&mut pil_file);
    simplify_identities(&mut pil_file);
    remove_trivial_selectors(&mut pil_file);
    remove_trivial_identities(&mut pil_file);
    remove_duplicate_identities(&mut pil_file);
    remove_unreferenced_definitions(&mut pil_file);
    let col_count_post = (pil_file.commitment_count(), pil_file.constant_count());
    log::info!(
        "Removed {} witness and {} fixed columns. Total count now: {} witness and {} fixed columns.",
        col_count_pre.0 - col_count_post.0,
        col_count_pre.1 - col_count_post.1,
        col_count_post.0,
        col_count_post.1
    );
    pil_file
}

/// Removes all definitions that are not referenced by an identity, public declaration
/// or witness column hint.
fn remove_unreferenced_definitions<T: FieldElement>(pil_file: &mut Analyzed<T>) {
    let poly_id_to_definition_name = build_poly_id_to_definition_name_lookup(pil_file);
    let mut required_names = collect_required_names(pil_file, &poly_id_to_definition_name);
    let mut to_process = required_names.iter().cloned().collect::<Vec<_>>();
    while let Some(n) = to_process.pop() {
        let symbols: Box<dyn Iterator<Item = Cow<'_, str>>> = if let Some((sym, value)) =
            pil_file.definitions.get(n.as_ref())
        {
            // TODO remove this.
            let set_hint = (sym.kind == SymbolKind::Poly(PolynomialType::Committed)
                && value.is_some())
            .then_some(Cow::from("std::prelude::set_hint"));
            Box::new(
                value
                    .iter()
                    .flat_map(|v| v.symbols())
                    .chain(set_hint.into_iter()),
            )
        } else if let Some((_, value)) = pil_file.intermediate_columns.get(n.as_ref()) {
            Box::new(value.iter().flat_map(|v| {
                v.all_children().flat_map(|e| {
                    if let AlgebraicExpression::Reference(AlgebraicReference { poly_id, .. }) = e {
                        Some(poly_id_to_definition_name[poly_id].into())
                    } else {
                        None
                    }
                })
            }))
        } else {
            panic!("Symbol not found: {n}");
        };
        for s in symbols {
            if required_names.insert(s.clone()) {
                to_process.push(s);
            }
        }
    }

    let definitions_to_remove: BTreeSet<_> = pil_file
        .definitions
        .keys()
        .chain(pil_file.intermediate_columns.keys())
        .filter(|name| !required_names.contains(&Cow::from(*name)))
        .cloned()
        .collect();
    pil_file.remove_definitions(&definitions_to_remove);
}

trait ReferencedSymbols {
    /// Returns an iterator over all referenced symbols in self including type names.
    fn symbols(&self) -> Box<dyn Iterator<Item = Cow<'_, str>> + '_>;
}

impl ReferencedSymbols for FunctionValueDefinition {
    fn symbols(&self) -> Box<dyn Iterator<Item = Cow<'_, str>> + '_> {
        match self {
            FunctionValueDefinition::TypeDeclaration(TypeDeclaration::Enum(enum_decl)) => {
                enum_decl.symbols()
            }
            FunctionValueDefinition::TypeDeclaration(TypeDeclaration::Struct(struct_decl)) => {
                struct_decl.symbols()
            }
            FunctionValueDefinition::TypeConstructor(TypeConstructor::Enum(enum_decl, _)) => {
                // This is the type constructor of an enum variant, it references the enum itself.
                Box::new(once(enum_decl.name.as_str().into()))
            }
            FunctionValueDefinition::TypeConstructor(TypeConstructor::Struct(struct_decl, _)) => {
                Box::new(once(struct_decl.name.as_str().into()))
            }
            FunctionValueDefinition::Expression(TypedExpression {
                type_scheme: Some(type_scheme),
                e,
            }) => Box::new(type_scheme.ty.symbols().chain(e.symbols())),
            _ => Box::new(self.children().flat_map(|e| e.symbols())),
        }
    }
}

impl ReferencedSymbols for EnumDeclaration {
    fn symbols(&self) -> Box<dyn Iterator<Item = Cow<'_, str>> + '_> {
        Box::new(
            self.variants
                .iter()
                .flat_map(|v| &v.fields)
                .flat_map(|t| t.iter())
                .flat_map(|t| t.symbols()),
        )
    }
}

impl ReferencedSymbols for StructDeclaration {
    fn symbols(&self) -> Box<dyn Iterator<Item = Cow<'_, str>> + '_> {
        Box::new(self.fields.iter().flat_map(|t| t.1.symbols()))
    }
}

impl ReferencedSymbols for Expression {
    fn symbols(&self) -> Box<dyn Iterator<Item = Cow<'_, str>> + '_> {
        Box::new(
            self.all_children()
                .flat_map(|e| match e {
                    Expression::Reference(
                        _,
                        Reference::Poly(PolynomialReference { name, type_args }),
                    ) => Some(
                        type_args
                            .iter()
                            .flat_map(|t| t.iter())
                            .flat_map(|t| t.symbols())
                            .chain(once(name.into())),
                    ),
                    _ => None,
                })
                .flatten(),
        )
    }
}

impl ReferencedSymbols for Type {
    fn symbols(&self) -> Box<dyn Iterator<Item = Cow<'_, str>> + '_> {
        Box::new(self.contained_named_types().map(|n| n.to_string().into()))
    }
}

/// Builds a lookup-table that can be used to turn array elements
/// (in form of their poly ids) into the names of the arrays.
fn build_poly_id_to_definition_name_lookup(
    pil_file: &Analyzed<impl FieldElement>,
) -> BTreeMap<PolyID, &String> {
    let mut poly_id_to_definition_name = BTreeMap::new();
    for (name, (symbol, _)) in &pil_file.definitions {
        if matches!(symbol.kind, SymbolKind::Poly(_)) {
            symbol.array_elements().for_each(|(_, id)| {
                poly_id_to_definition_name.insert(id, name);
            });
        }
    }
    for (name, (symbol, _)) in &pil_file.intermediate_columns {
        symbol.array_elements().for_each(|(_, id)| {
            poly_id_to_definition_name.insert(id, name);
        });
    }
    poly_id_to_definition_name
}

/// Collect all names that are referenced in identities and public declarations.
fn collect_required_names<'a, T: FieldElement>(
    pil_file: &'a Analyzed<T>,
    poly_id_to_definition_name: &BTreeMap<PolyID, &'a String>,
) -> HashSet<Cow<'a, str>> {
    let mut required_names: HashSet<Cow<'a, str>> = Default::default();
    required_names.extend(
        pil_file
            .public_declarations
            .values()
            .map(|p| p.polynomial.name.as_str().into()),
    );
    for fun in &pil_file.prover_functions {
        for e in fun.all_children() {
            if let Expression::Reference(_, Reference::Poly(PolynomialReference { name, .. })) = e {
                required_names.insert(Cow::from(name));
            }
        }
    }
    for id in &pil_file.identities {
        id.pre_visit_expressions(&mut |e: &AlgebraicExpression<T>| {
            if let AlgebraicExpression::Reference(AlgebraicReference { poly_id, .. }) = e {
                required_names.insert(poly_id_to_definition_name[poly_id].into());
            }
        });
    }
    required_names
}

/// Identifies fixed columns that only have a single value, replaces every
/// reference to this column by the value and deletes the column.
fn remove_constant_fixed_columns<T: FieldElement>(pil_file: &mut Analyzed<T>) {
    let constant_polys = pil_file
        .constant_polys_in_source_order()
        .iter()
        .filter(|(p, _)| !p.is_array())
        .filter_map(|(poly, definition)| {
            let definition = definition.as_ref()?;
            let value = constant_value(definition)?;
            log::debug!(
                "Determined fixed column {} to be constant {value}. Removing.",
                poly.absolute_name
            );
            Some(((poly.absolute_name.clone(), poly.into()), value))
        })
        .collect::<Vec<((String, PolyID), _)>>();

    substitute_polynomial_references(pil_file, constant_polys);
}

/// Checks if a fixed column defined through a function has a constant
/// value and returns it in that case.
fn constant_value(function: &FunctionValueDefinition) -> Option<BigUint> {
    match function {
        FunctionValueDefinition::Array(expression) => {
            // TODO use a proper evaluator at some point,
            // combine with constant_evaluator
            let mut values = expression.children().map(|e| match e {
                Expression::Number(_, Number { value: n, .. }) => Some(n),
                _ => None,
            });
            let first = values.next()??;
            if values.all(|x| x == Some(first)) {
                Some(first.clone())
            } else {
                None
            }
        }
        FunctionValueDefinition::Expression(_)
        | FunctionValueDefinition::TypeDeclaration(_)
        | FunctionValueDefinition::TypeConstructor(_)
        | FunctionValueDefinition::TraitDeclaration(_)
        | FunctionValueDefinition::TraitFunction(_, _) => None,
    }
}

/// Simplifies multiplications by zero and one.
fn simplify_identities<T: FieldElement>(pil_file: &mut Analyzed<T>) {
    pil_file.post_visit_expressions_in_identities_mut(&mut simplify_expression_single);
}

fn simplify_expression<T: FieldElement>(mut e: AlgebraicExpression<T>) -> AlgebraicExpression<T> {
    e.post_visit_expressions_mut(&mut simplify_expression_single);
    e
}

fn simplify_expression_single<T: FieldElement>(e: &mut AlgebraicExpression<T>) {
    if let AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation { left, op, right }) = e {
        if let (AlgebraicExpression::Number(l), AlgebraicExpression::Number(r)) =
            (left.as_ref(), right.as_ref())
        {
            if let Some(v) = match op {
                AlgebraicBinaryOperator::Add => Some(*l + *r),
                AlgebraicBinaryOperator::Sub => Some(*l - *r),
                AlgebraicBinaryOperator::Mul => Some(*l * *r),
                // TODO we might do some more operations later.
                _ => None,
            } {
                *e = AlgebraicExpression::Number(v);
                return;
            }
        }
    }
    if let AlgebraicExpression::UnaryOperation(AlgebraicUnaryOperation { op, expr: inner }) = e {
        if let AlgebraicExpression::Number(inner) = **inner {
            *e = AlgebraicExpression::Number(match op {
                AlgebraicUnaryOperator::Minus => -inner,
            });
            return;
        }
    }
    match e {
        AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation {
            left,
            op: AlgebraicBinaryOperator::Mul,
            right,
        }) => {
            if let AlgebraicExpression::Number(n) = left.as_mut() {
                if *n == 0.into() {
                    *e = AlgebraicExpression::Number(0.into());
                    return;
                }
            }
            if let AlgebraicExpression::Number(n) = right.as_mut() {
                if *n == 0.into() {
                    *e = AlgebraicExpression::Number(0.into());
                    return;
                }
            }
            if let AlgebraicExpression::Number(n) = left.as_mut() {
                if *n == 1.into() {
                    let mut tmp = AlgebraicExpression::Number(1.into());
                    std::mem::swap(&mut tmp, right);
                    std::mem::swap(e, &mut tmp);
                    return;
                }
            }
            if let AlgebraicExpression::Number(n) = right.as_mut() {
                if *n == 1.into() {
                    let mut tmp = AlgebraicExpression::Number(1.into());
                    std::mem::swap(&mut tmp, left);
                    std::mem::swap(e, &mut tmp);
                }
            }
        }
        AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation {
            left,
            op: AlgebraicBinaryOperator::Add,
            right,
        }) => {
            if let AlgebraicExpression::Number(n) = left.as_mut() {
                if *n == 0.into() {
                    let mut tmp = AlgebraicExpression::Number(1.into());
                    std::mem::swap(&mut tmp, right);
                    std::mem::swap(e, &mut tmp);
                    return;
                }
            }
            if let AlgebraicExpression::Number(n) = right.as_mut() {
                if *n == 0.into() {
                    let mut tmp = AlgebraicExpression::Number(1.into());
                    std::mem::swap(&mut tmp, left);
                    std::mem::swap(e, &mut tmp);
                }
            }
        }
        AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation {
            left,
            op: AlgebraicBinaryOperator::Sub,
            right,
        }) => {
            if let AlgebraicExpression::Number(n) = right.as_mut() {
                if *n == 0.into() {
                    let mut tmp = AlgebraicExpression::Number(1.into());
                    std::mem::swap(&mut tmp, left);
                    std::mem::swap(e, &mut tmp);
                }
            }
        }
        _ => {}
    }
}

/// Removes lookup and permutation selectors which are equal to 1
/// TODO: refactor `SelectedExpression` to not use an optional selector
fn remove_trivial_selectors<T: FieldElement>(pil_file: &mut Analyzed<T>) {
    let one = AlgebraicExpression::from(T::from(1));

    for identity in &mut pil_file
        .identities
        .iter_mut()
        .filter(|id| id.kind == IdentityKind::Plookup || id.kind == IdentityKind::Permutation)
    {
        if identity.left.selector.as_ref() == Some(&one) {
            identity.left.selector = None;
        }

        if identity.right.selector.as_ref() == Some(&one) {
            identity.right.selector = None;
        }
    }
}

/// Extracts columns from lookups that are matched against constants and turns
/// them into polynomial identities.
fn extract_constant_lookups<T: FieldElement>(pil_file: &mut Analyzed<T>) {
    let mut new_identities = vec![];
    for identity in &mut pil_file
        .identities
        .iter_mut()
        .filter(|id| id.kind == IdentityKind::Plookup)
    {
        let mut extracted = HashSet::new();
        for (i, (l, r)) in identity
            .left
            .expressions
            .iter()
            .zip(&identity.right.expressions)
            .enumerate()
            .filter_map(|(i, (l, r))| {
                if let AlgebraicExpression::Number(n) = r {
                    Some((i, (l, n)))
                } else {
                    None
                }
            })
        {
            // TODO remove clones
            let l_sel = identity
                .left
                .selector
                .clone()
                .unwrap_or_else(|| AlgebraicExpression::from(T::one()));
            let r_sel = identity
                .right
                .selector
                .clone()
                .unwrap_or_else(|| AlgebraicExpression::from(T::one()));
            let pol_id = (l_sel * l.clone()) - (r_sel * AlgebraicExpression::from(*r));
            new_identities.push((simplify_expression(pol_id), identity.source.clone()));

            extracted.insert(i);
        }
        // TODO rust-ize this.
        let mut c = 0usize;
        identity.left.expressions.retain(|_i| {
            c += 1;
            !extracted.contains(&(c - 1))
        });
        let mut c = 0usize;
        identity.right.expressions.retain(|_i| {
            c += 1;

            !extracted.contains(&(c - 1))
        });
    }
    for (identity, source) in new_identities {
        pil_file.append_polynomial_identity(identity, source);
    }
}

/// Identifies witness columns that are constrained to a single value, replaces every
/// reference to this column by the value and deletes the column.
fn remove_constant_witness_columns<T: FieldElement>(pil_file: &mut Analyzed<T>) {
    let mut constant_polys = pil_file
        .identities
        .iter()
        .filter(|&id| (id.kind == IdentityKind::Polynomial))
        .map(|id| id.expression_for_poly_id())
        .filter_map(constrained_to_constant)
        .collect::<Vec<((String, PolyID), _)>>();
    // We cannot remove arrays or array elements, so filter them out.
    let columns = pil_file
        .committed_polys_in_source_order()
        .iter()
        .filter(|&(s, _)| (!s.is_array()))
        .map(|(s, _)| s.into())
        .collect::<HashSet<PolyID>>();
    constant_polys.retain(|((_, id), _)| columns.contains(id));

    substitute_polynomial_references(pil_file, constant_polys);
}

/// Substitutes all references to certain polynomials by the given field elements.
fn substitute_polynomial_references<T: FieldElement>(
    pil_file: &mut Analyzed<T>,
    substitutions: Vec<((String, PolyID), BigUint)>,
) {
    let substitutions_by_id = substitutions
        .iter()
        .map(|((_, id), value)| (*id, value.clone()))
        .collect::<HashMap<PolyID, _>>();
    let substitutions_by_name = substitutions
        .into_iter()
        .map(|((name, _), value)| (name, value))
        .collect::<HashMap<String, _>>();
    pil_file.post_visit_expressions_in_definitions_mut(&mut |e: &mut Expression| {
        if let Expression::Reference(
            _,
            Reference::Poly(PolynomialReference { name, type_args: _ }),
        ) = e
        {
            if let Some(value) = substitutions_by_name.get(name) {
                *e = Number {
                    value: (*value).clone(),
                    type_: Some(Type::Expr),
                }
                .into();
            }
        }
    });
    pil_file.post_visit_expressions_in_identities_mut(&mut |e: &mut AlgebraicExpression<_>| {
        if let AlgebraicExpression::Reference(AlgebraicReference { poly_id, .. }) = e {
            if let Some(value) = substitutions_by_id.get(poly_id) {
                *e = AlgebraicExpression::Number(T::checked_from((*value).clone()).unwrap());
            }
        }
    });
}

fn constrained_to_constant<T: FieldElement>(
    expr: &AlgebraicExpression<T>,
) -> Option<((String, PolyID), BigUint)> {
    match expr {
        AlgebraicExpression::BinaryOperation(AlgebraicBinaryOperation {
            left,
            op: AlgebraicBinaryOperator::Sub,
            right,
        }) => {
            match (left.as_ref(), right.as_ref()) {
                (AlgebraicExpression::Number(n), AlgebraicExpression::Reference(poly))
                | (AlgebraicExpression::Reference(poly), AlgebraicExpression::Number(n)) => {
                    if poly.is_witness() {
                        // This also works if "next" is true.
                        return Some(((poly.name.clone(), poly.poly_id), n.to_arbitrary_integer()));
                    }
                }
                _ => {}
            }
        }
        AlgebraicExpression::Reference(poly) => {
            if poly.is_witness() {
                return Some(((poly.name.clone(), poly.poly_id), 0u32.into()));
            }
        }
        _ => {}
    }
    None
}

/// Removes identities that evaluate to zero and lookups with empty columns.
fn remove_trivial_identities<T: FieldElement>(pil_file: &mut Analyzed<T>) {
    let to_remove = pil_file
        .identities
        .iter()
        .enumerate()
        .filter_map(|(index, identity)| match identity.kind {
            IdentityKind::Polynomial => {
                if let AlgebraicExpression::Number(n) = identity.expression_for_poly_id() {
                    if *n == 0.into() {
                        return Some(index);
                    }
                    // Otherwise the constraint is not satisfiable,
                    // but better to get the error elsewhere.
                }
                None
            }
            IdentityKind::Plookup => {
                assert_eq!(
                    identity.left.expressions.len(),
                    identity.right.expressions.len()
                );
                identity.left.expressions.is_empty().then_some(index)
            }
            IdentityKind::Permutation => None,
            IdentityKind::Connect => None,
        })
        .collect();
    pil_file.remove_identities(&to_remove);
}

fn remove_duplicate_identities<T: FieldElement>(pil_file: &mut Analyzed<T>) {
    // Set of (left, right) tuples.
    let mut identity_expressions = BTreeSet::new();
    let to_remove = pil_file
        .identities
        .iter()
        .enumerate()
        .filter_map(|(index, identity)| {
            match identity_expressions.insert((&identity.left, &identity.right)) {
                false => Some(index),
                true => None,
            }
        })
        .collect();
    pil_file.remove_identities(&to_remove);
}

#[cfg(test)]
mod test {
    use powdr_number::GoldilocksField;
    use powdr_pil_analyzer::analyze_string;

    use crate::optimize;

    use pretty_assertions::assert_eq;

    #[test]
    fn replace_fixed() {
        let input = r#"namespace N(65536);
    col fixed one = [1]*;
    col fixed zero = [0]*;
    col witness X;
    col witness Y;
    X * one = X * zero - zero + Y;
    one * Y = zero * Y + 7 * X;
"#;
        let expectation = r#"namespace N(65536);
    col witness X;
    col witness Y;
    N::X = N::Y;
    N::Y = 7 * N::X;
"#;
        let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
        assert_eq!(optimized, expectation);
    }

    #[test]
    fn replace_lookup() {
        let input = r#"namespace N(65536);
    col fixed one = [1]*;
    col fixed zero = [0]*;
    col fixed two = [2]*;
    col fixed cnt(i) { i };
    col witness X;
    col witness Y;
    col witness W;
    col witness Z;
    col witness A;
    (1 - A) $ [ X, Y, A ] in [ zero, one, cnt ];
    [ Y, W, Z, A ] in (1 + A) $ [ cnt, zero, two, one ];
    [ W, Z ] in (1 + A) $ [ zero, one ];
"#;
        let expectation = r#"namespace N(65536);
    col fixed cnt(i) { i };
    col witness X;
    col witness Y;
    col witness Z;
    col witness A;
    1 - N::A $ [N::A] in [N::cnt];
    [N::Y] in 1 + N::A $ [N::cnt];
    (1 - N::A) * N::X = 0;
    (1 - N::A) * N::Y = 1;
    N::Z = (1 + N::A) * 2;
    N::A = 1 + N::A;
    N::Z = 1 + N::A;
"#;
        let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
        assert_eq!(optimized, expectation);
    }

    #[test]
    fn intermediate() {
        let input = r#"namespace N(65536);
        col witness x;
        col intermediate = x;
        intermediate = intermediate;
    "#;
        let expectation = r#"namespace N(65536);
    col witness x;
    col intermediate = N::x;
    N::intermediate = N::intermediate;
"#;
        let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
        assert_eq!(optimized, expectation);
    }

    #[test]
    fn zero_sized_array() {
        let input = r#"
        namespace std::array(65536);
            let<T> len: T[] -> int = [];
        namespace N(65536);
            col witness x[1];
            col witness y[0];
            let t: col = |i| std::array::len(y);
            x[0] = t;
    "#;
        let expectation = r#"namespace std::array(65536);
    let<T> len: T[] -> int = [];
namespace N(65536);
    col witness x[1];
    col witness y[0];
    col fixed t(i) { std::array::len::<expr>(N::y) };
    N::x[0] = N::t;
"#;
        let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
        assert_eq!(optimized, expectation);
    }

    #[test]
    fn remove_duplicates() {
        let input = r#"namespace N(65536);
        col witness x;
        col fixed cnt(i) { i };

        x * (x - 1) = 0;
        x * (x - 1) = 0;
        x * (x - 1) = 0;

        [ x ] in [ cnt ];
        [ x ] in [ cnt ];
        [ x ] in [ cnt ];

        [ x + 1 ] in [ cnt ];
        [ x ] in [ cnt + 1 ];
    "#;
        let expectation = r#"namespace N(65536);
    col witness x;
    col fixed cnt(i) { i };
    N::x * (N::x - 1) = 0;
    [N::x] in [N::cnt];
    [N::x + 1] in [N::cnt];
    [N::x] in [N::cnt + 1];
"#;
        let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
        assert_eq!(optimized, expectation);
    }

    #[test]
    fn remove_unreferenced() {
        let input = r#"namespace N(65536);
        col witness x;
        col fixed cnt(i) { inc(i) };
        let inc = |x| x + 1;
        // these are removed
        col witness k;
        col k2 = k;
        let rec: -> int = || rec();
        let a: int -> int = |i| b(i + 1);
        let b: int -> int = |j| 8;
        // identity
        [ x ] in [ cnt ];

    "#;
        let expectation = r#"namespace N(65536);
    col witness x;
    col fixed cnt(i) { N::inc(i) };
    let inc: int -> int = |x| x + 1;
    [N::x] in [N::cnt];
"#;
        let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
        assert_eq!(optimized, expectation);
    }

    #[test]
    fn remove_unreferenced_parts_of_arrays() {
        let input = r#"namespace N(65536);
        col witness x[5];
        let inte: inter[5] = x;
        x[2] = inte[4];
    "#;
        let expectation = r#"namespace N(65536);
    col witness x[5];
    col inte[5] = [N::x[0], N::x[1], N::x[2], N::x[3], N::x[4]];
    N::x[2] = N::inte[4];
"#;
        let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap());
        assert_eq!(optimized.intermediate_count(), 5);
        assert_eq!(optimized.to_string(), expectation);
    }

    #[test]
    fn remove_unreferenced_keep_enums() {
        let input = r#"namespace N(65536);
        enum X { A, B, C }
        enum Y { D, E, F(R[]) }
        enum R { T }
        let t: X[] -> int = |r| 1;
        // This references Y::F but even after type checking, the type
        // Y is not mentioned anywhere.
        let f: col = |i| if i == 0 { t([]) } else { (|x| 1)(Y::F([])) };
        let x;
        x = f;
    "#;
        let expectation = r#"namespace N(65536);
    enum X {
        A,
        B,
        C,
    }
    enum Y {
        D,
        E,
        F(N::R[]),
    }
    enum R {
        T,
    }
    let t: N::X[] -> int = |r| 1;
    col fixed f(i) { if i == 0 { N::t([]) } else { (|x| 1)(N::Y::F([])) } };
    col witness x;
    N::x = N::f;
"#;
        let optimized = optimize(analyze_string::<GoldilocksField>(input).unwrap()).to_string();
        assert_eq!(optimized, expectation);
    }
}

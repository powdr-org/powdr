use std::check::assert;
use std::array;
use std::math::extension_field::Ext;
use std::math::extension_field::add_ext;
use std::math::extension_field::sub_ext;
use std::math::extension_field::mul_ext;
use std::math::extension_field::inv_ext;
use std::math::extension_field::eval_ext;
use std::math::extension_field::unpack_ext_array;
use std::math::extension_field::next_ext;
use std::math::extension_field::from_base;
use std::math::extension_field::from_array;
use std::math::extension_field::constrain_eq_ext;
use std::protocols::fingerprint::fingerprint_with_id;
use std::protocols::fingerprint::fingerprint_with_id_inter;
use std::math::extension_field::required_extension_size;
use std::prover::eval;
use std::field::known_field;
use std::field::KnownField;
use std::check::panic;

/// Sends the payload (id, payload...) to the bus by adding
/// `multiplicity / (beta - fingerprint(id, payload...))` to `acc`
/// It is the callers responsibility to properly constrain the multiplicity (e.g. constrain
/// it to be boolean) if needed.
///
/// # Arguments:
/// - id: Interaction Id
/// - payload: An array of expressions to be sent to the bus
/// - multiplicity: The multiplicity which shows how many times a column will be sent
/// - latch: a binary expression which indicates where the multiplicity can be non-zero.
let bus_interaction: expr, expr[], expr, expr -> () = constr |id, payload, multiplicity, latch| {

    // Add phantom bus interaction
    let full_payload = [id] + payload;
    Constr::PhantomBusInteraction(multiplicity, full_payload, latch);

    let extension_field_size = required_extension_size();

    // Alpha is used to compress the LHS and RHS arrays.
    let alpha = from_array(array::new(extension_field_size, |i| challenge(0, i + 1)));
    // Beta is used to update the accumulator.
    let beta = from_array(array::new(extension_field_size, |i| challenge(0, i + 1 + extension_field_size)));

    // Implemented as: folded = (beta - fingerprint(id, payload...));
    let materialize_folded = match known_field() {
        // Materialized as a witness column for two reasons:
        // - It makes sure the constraint degree is independent of the input payload.
        // - We can access folded', even if the payload contains next references.
        // Note that if all expressions are degree-1 and there is no next reference,
        // this is wasteful, but we can't check that here.
        Option::Some(KnownField::Goldilocks) => true,
        Option::Some(KnownField::BabyBear) => true,
        Option::Some(KnownField::KoalaBear) => true,
        Option::Some(KnownField::M31) => true,
        // The case above triggers our hand-written witness generation, but on Bn254, we'd not be
        // on the extension field and use the automatic witness generation.
        // However, it does not work with a materialized folded payload. At the same time, Halo2
        // (the only prover that supports BN254) does not have a hard degree bound. So, we can
        // in-line the expression here.
        Option::Some(KnownField::BN254) => false,
        _ => panic("Unexpected field!")
    };
    let folded = if materialize_folded {
        let folded = from_array(
            array::new(extension_field_size,
                    |i| std::prover::new_witness_col_at_stage("folded", 1))
        );
        constrain_eq_ext(folded, sub_ext(beta, fingerprint_with_id_inter(id, payload, alpha)));
        folded
    } else {
        sub_ext(beta, fingerprint_with_id_inter(id, payload, alpha))
    };

    let folded_next = next_ext(folded);

    let m_ext = from_base(multiplicity);
    let m_ext_next = next_ext(m_ext);

    let acc = array::new(extension_field_size, |i| std::prover::new_witness_col_at_stage("acc", 1));
    let acc_ext = from_array(acc);
    let next_acc = next_ext(acc_ext);

    let is_first: col = std::well_known::is_first;
    let is_first_next = from_base(is_first');

    // Update rule:
    // acc' =  acc * (1 - is_first') + multiplicity' / folded'
    // or equivalently:
    // folded' * (acc' - acc * (1 - is_first')) - multiplicity' = 0
    let update_expr = sub_ext(
        mul_ext(folded_next, sub_ext(next_acc, mul_ext(acc_ext, sub_ext(from_base(1), is_first_next)))), m_ext_next
    );
    
    constrain_eq_ext(update_expr, from_base(0));
};

/// Compute acc' = acc * (1 - is_first') + multiplicity' / fingerprint(id, payload...),
/// using extension field arithmetic.
/// This is intended to be used as a hint in the extension field case; for the base case
/// automatic witgen is smart enough to figure out the value of the accumulator.
let compute_next_z: expr, expr, expr[], expr, Ext<expr>, Ext<expr>, Ext<expr> -> fe[] = query |is_first, id, payload, multiplicity, acc, alpha, beta| {

    let m_next = eval(multiplicity');
    let m_ext_next = from_base(m_next);

    let is_first_next = eval(is_first');
    let current_acc = if is_first_next == 1 {from_base(0)} else {eval_ext(acc)};
    
    // acc' = current_acc + multiplicity' / folded'
    let res = if m_next == 0 {
        current_acc
    } else {
        // Implemented as: folded = (beta - fingerprint(id, payload...));
        // `multiplicity / (beta - fingerprint(id, payload...))` to `acc`
        let folded_next = sub_ext(eval_ext(beta), fingerprint_with_id(eval(id'), array::eval(array::next(payload)), alpha));
        add_ext(
            current_acc,
            mul_ext(m_ext_next, inv_ext(folded_next))
        )
    };

    unpack_ext_array(res)
};

/// Convenience function for bus interaction to send columns
let bus_send: expr, expr[], expr -> () = constr |id, payload, multiplicity| {
    // For bus sends, the multiplicity always equals the latch
    bus_interaction(id, payload, multiplicity, multiplicity);
};

/// Convenience function for bus interaction to receive columns
let bus_receive: expr, expr[], expr, expr -> () = constr |id, payload, multiplicity, latch| {
    bus_interaction(id, payload, -multiplicity, latch);
};
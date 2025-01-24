/// Like in Rust, all symbols from this file are available in all modules,
/// meaning that a failed symbol resolution always re-tries relative to this module.

use std::convert::expr as to_expr;
use std::convert::fe as to_fe;
use std::convert::int as to_int;

let true: bool = "" == "";
let false: bool = !true;

enum Option<T> {
    None,
    Some(T)
}

/// The "constraint" type, i.e. the result of the operators
/// "=", "in", "is" and "connect".
enum Constr {
    /// A polynomial identity, result of the "=" operator.
    Identity(expr, expr),

    /// A lookup constraint with selectors, result of the "in" operator.
    Lookup((Option<expr>, Option<expr>), (expr, expr)[]),

    /// A "phantom" lookup constraint, i.e., an annotation for witness generation.
    /// The actual constraint should be enforced via other constraints.
    /// Contains:
    /// - The selectors (if any) for the left and right hand side.
    /// - The LHS and RHS values.
    /// - The multiplicity column.
    PhantomLookup((Option<expr>, Option<expr>), (expr, expr)[], expr),

    /// A permutation constraint with selectors, result of the "is" operator.
    Permutation((Option<expr>, Option<expr>), (expr, expr)[]),

    /// A "phantom" permutation constraint, i.e., an annotation for witness generation.
    /// The actual constraint should be enforced via other constraints.
    /// Contains:
    /// - The selectors (if any) for the left and right hand side.
    /// - The LHS and RHS values.
    PhantomPermutation((Option<expr>, Option<expr>), (expr, expr)[]),

    /// A connection constraint (copy constraint), result of the "connect" operator.
    Connection((expr, expr)[]),

    /// A "phantom" bus interaction, i.e., an annotation for witness generation.
    /// The actual constraint should be enforced via other constraints.
    /// Contains:
    /// - An expression for the multiplicity. Negative for bus receives.
    /// - The tuple added to the bus.
    /// - An expression for the latch. This should be exactly what the RHS selector
    ///   would be in an equivalent lookup or permutation:
    ///   - It should always evaluate to a binary value.
    ///   - If it evaluates to zero, the multiplicity must be zero.
    PhantomBusInteraction(expr, expr[], expr)
}

/// This is the result of the "$" operator. It can be used as the left and
/// right hand side of a lookup or permutation constraint.
enum SelectedExprs {
    SelectedExprs(expr, expr[]),
    JustExprs(expr[]),
}


/// The return type of a prover query function.
enum Query {
    /// Generate a hint to fill a witness column with.
    Hint(fe),
    /// Query a prover input (field element) by channel id and index.
    Input(int, int),
    /// Writes a field element (second argument) to an output channel (first argument).
    /// It is the host's responsibility to give semantics to each channel.
    Output(int, fe),
    /// This value is not (additionally) constrained by the query.
    None,
}

/// Adds a hint / query function to an existing witness column.
let set_hint: expr, (int -> std::prelude::Query) -> () = [];

/// Constructs a challenge object.
/// The arguments are the proof stage and the id of the challenge, in this order.
/// This is a built-in function.
let challenge: int, int -> expr = [];

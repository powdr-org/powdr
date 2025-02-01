/// Evaluates to folder(...folder(folder(initial, f(0)), f(1)) ..., f(length - 1)),
/// i.e. calls f(0), f(1), ..., f(length - 1) and combines the results
/// using the function `folder`, starting with the value `initial`.
///
/// See `sum` for an example use.
let<T1, T2>
    fold: int, (int -> T1), T2, (T2, T1 -> T2) -> T2 = |length, f, initial, folder|
        if length <= 0 {
            initial
        } else {
            folder(fold((length - 1), f, initial, folder), f((length - 1)))
        };

/// Evaluates to f(0) + f(1) + ... + f(length - 1).
let<T: Add + FromLiteral> sum: int, (int -> T) -> T = |length, f| fold(length, f, 0, |acc, e| (acc + e));

let<T: Ord> max: T, T -> T = |a, b| if a < b { b } else { a };
let<T: Ord> min: T, T -> T = |a, b| if a < b { a } else { b };

/// Returns x for Some(x) and f() otherwise.
let<T> unwrap_or_else: Option<T>, (-> T) -> T = |o, f| match o {
    Option::None => f(),
    Option::Some(x) => x,
};

let<T> unwrap: Option<T> -> T = |o| unwrap_or_else(o, || std::check::panic("unwrap called on None"));

/// Evaluates to a constraint that forces the witness column `c` to stay constant
/// until `latch` is 1. In the row following the row where `latch` is 1,
/// `c` is allowed to change.
///
/// Note: `latch` needs to be equal to `1`, and not merely non-zero for `c` to be able to change.
let unchanged_until: expr, expr -> Constr = |c, latch| (c' - c) * (1 - latch) = 0;

/// Evaluates to a constraint that forces `c` to be either 0 or 1.
let force_bool: expr -> Constr = |c| c * (1 - c) = 0;

/// Creates a new witness column that is constrained to the values 0 and 1.
let new_bool: -> expr = constr || {
    let x;
    force_bool(x);
    x
};

/// Returns a 2nd degree boolean expression that is 1 if and only if `x` is not zero.
///
/// Introduces one new witness column and one new constraint.
let is_not_zero: expr -> expr = constr |x| {
    // The inverse of "x" if it is not zero, otherwise unconstrained.
    let inverse;

    // Ensures that "inverse * x" is either 0 or 1:
    (inverse * x - 1) * x = 0;

    inverse * x
};

/// Returns a 2nd degree boolean expression that is 1 if and only if `x` is zero.
///
/// Introduces one new witness column and one new constraint.
let is_zero: expr -> expr = constr |x| {
    1 - is_not_zero(x)
};

/// Returns an array of functions such that the range of the `i`th function is exactly the
/// first `size[i]` numbers (i.e. `0` until `size[i] - 1`, inclusive), such that all combinations
/// of values of these functions appear as combined outputs.
/// Each of the functions cycles through its values, advancing to the next number whenever the
/// previous function has completed a cycle (or always advancing if it is the first function).
/// This function is useful for combined range checks or building the inputs for function
/// that is implemented in a lookup.
/// See binary.asm for an example.
let cross_product: int[] -> (int -> int)[] = |sizes| cross_product_internal(1, 0, sizes);

let cross_product_internal: int, int, int[] -> (int -> int)[] = |cycle_len, pos, sizes|
    if pos >= std::array::len(sizes) {
        // We could assert here that the degree is at least `cycle_len`
        []
    } else {
        [|i| (i / cycle_len) % sizes[pos]] +
            cross_product_internal(cycle_len * sizes[pos], pos + 1, sizes)
    };

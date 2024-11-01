/// A function that takes a field element or integer and converts
/// it to a (non-negative) integer.
/// The actual implementation is replaced by a built-in function.
let int = [];

/// A function that takes a field element or integer and converts
/// it to a field element.
/// Panics if the input is negative or larger or equal to the field modulus.
/// The actual implementation is replaced by a built-in function.
let fe = [];

/// A function that takes an integer or a field element and converts it to an expression.
/// The actual implementation is replaced by a built-in function.
let expr = [];

impl std::prelude::ToCol<(int -> int)> {
    to_col: |c| |i| fe(c(i)),
}

impl std::prelude::ToColArray<(int -> int)[]> {
    to_col_array: |arr| std::array::map(arr, std::prelude::ToCol::to_col)
}
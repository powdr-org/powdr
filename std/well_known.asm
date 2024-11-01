/// Evaluates to 1 on the first row and 0 on all other rows.
/// Useful to define a fixed column of that property.
let is_first: int -> int = |i| if i == 0 { 1 } else { 0 };

/// The constant one.
let one: int -> int = |i| 1;
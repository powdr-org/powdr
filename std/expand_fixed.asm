use std::result::Result;
use std::check::panic;

/// A term in an array expression
enum ArrayTerm {
    Repeat(int[]),
    Once(int[])
}

let MORE_THAN_ONE_REPEATED_ERROR = "unsolvable because more than one term is repeated";
let NON_REPEATED_SIZE_EXCEEDS_DEGREE_ERROR = "non repeated array terms do not fit in degree";

// returns the total size of the repeated array in this array expression
let compute_length_of_repeated_part: ArrayTerm[], (-> int) -> Result<int, string> = |terms, degree| {
    let (_, res) = std::array::fold(terms, (false, Result::Ok(0)), |(found_repeated, l), term| {
        match l {
            Result::Err(e) => (found_repeated, Result::Err(e)),
            Result::Ok(len) => match term {
                // we can have `[]*` as many times as we want
                ArrayTerm::Repeat([]) => (found_repeated, Result::Ok(len)),
                ArrayTerm::Repeat(a) => {
                    if found_repeated {
                        (true, Result::Err(MORE_THAN_ONE_REPEATED_ERROR))
                    } else {
                        (true, Result::Ok(len))
                    }
                },
                ArrayTerm::Once(a) => (found_repeated, Result::Ok(len + std::array::len(a)))
            }
        }
    });
    match res {
        Result::Ok(total_size_of_non_repeated) => if total_size_of_non_repeated <= degree() {
            Result::Ok(degree() - total_size_of_non_repeated)
        } else {
            Result::Err(NON_REPEATED_SIZE_EXCEEDS_DEGREE_ERROR)
        },
        Result::Err(e) => Result::Err(e)
    }
};

enum OffsetSearch {
    Offset(int),
    Value(int),
}

// returns a function representing the array expression
let expand: ArrayTerm[], (-> int) -> Result<(int -> int), string> = |terms, degree| {
    // return early if all terms are constant with the same value
    let (constant_value, found_repeated_item) = std::array::fold(terms, (Result::Ok(Option::None), Result::Ok(false)), |(r, found), term| {
        let (a, is_repeated) = match term {
            ArrayTerm::Once(a) => (a, false),
            ArrayTerm::Repeat(a) => (a, std::array::len(a) > 0),
        };

        (match r {
            Result::Ok(c) => {
                std::array::fold(a, Result::Ok(c), |e, value| {
                    match e {
                        Result::Ok(Option::None) => Result::Ok(Option::Some(value)),
                        Result::Ok(Option::Some(prev_value)) => if value == prev_value { Result::Ok(Option::Some(value)) } else { Result::Err(()) },
                        Result::Err(()) => Result::Err(())
                    }
                })
            },
            Result::Err(()) => Result::Err(())
        }, match found {
            Result::Ok(v) => if v && is_repeated { Result::Err(MORE_THAN_ONE_REPEATED_ERROR) } else { Result::Ok(v || is_repeated) },
            Result::Err(e) => Result::Err(e),
        })
    });

    match (constant_value, found_repeated_item) {
        // we found more than one repeated term, error out
        (_, Result::Err(s)) => Result::Err(s),
        // This is not strict enough and would allow expressions whose size does not match the degree
        // We should fix this by ensuring that:
        // - the minimum size of the expanded expression is smaller than the minimum degree of the machine
        (Result::Ok(Option::Some(v)), _) => Result::Ok(|_| v),
        _ => {
            // get the total size of the repeated term
            match compute_length_of_repeated_part(terms, degree) {
                Result::Ok(size_of_repeated) => {

                    let terms_preprocessed = std::array::map(terms, |term| match term {
                        ArrayTerm::Repeat([]) => ([], 0),
                        ArrayTerm::Repeat(a) => (a, size_of_repeated),
                        ArrayTerm::Once(a) => (a, std::array::len(a))
                    });

                    Result::Ok(|i| {
                        let res = std::array::fold(terms_preprocessed, OffsetSearch::Offset(i), |val, (a, len)| {
                            match val {
                                OffsetSearch::Offset(index) => {
                                    if index < len {
                                        OffsetSearch::Value(a[index % std::array::len(a)])
                                    } else {
                                        OffsetSearch::Offset(index - len)
                                    }
                                },
                                // found the result, just keep returning it
                                _ => val,
                            }
                        });
                        // unwrap
                        match res {
                            OffsetSearch::Value(r) => r,
                            _ => panic("unreachable")
                        }
                    })
                },
                Result::Err(e) => Result::Err(e)
            }
        }
    }
};

let expand_unwrapped: ArrayTerm[], (-> int) -> (int -> int) = |terms, degree| {
    match expand(terms, degree) {
        Result::Ok(r) => r,
        Result::Err(e) => panic(e)
    }
};

let repeat: int[] -> ArrayTerm = |a| ArrayTerm::Repeat(a);

let once: int[] -> ArrayTerm = |a| ArrayTerm::Once(a);
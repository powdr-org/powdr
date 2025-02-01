/// This is a built-in function taking an array argument and returning
/// the length of the array.
/// This symbol is not an empty array, the actual semantics are overridden.
let<T> len: T[] -> int = [];

/// Evaluates to the array [f(0), f(1), ..., f(length - 1)].
let<T> new: int, (int -> T) -> T[] = |length, f| std::utils::fold(length, f, [], |acc, e| (acc + [e]));

/// Returns a new array equal to arr except that the element at index i is x.
let<T> set_element: T[], int, T -> T[] = |arr, i, x| {
    let _ = std::check::assert(i < len(arr), || "Index out of bounds");
    map_enumerated(arr, |j, y| if i == j { x } else { y })
};

/// Returns a new array of length l containing the elements of arr starting at index start.
let<T> sub_array: T[], int, int -> T[] = |arr, start, l| std::array::new(l, |i| arr[start + i]);

/// Returns a new array that reverses the input array.
let<T> reverse: T[] -> T[] = |arr| new(len(arr), |i| arr[len(arr) - i - 1]);

/// Evaluates to the array [f(arr[0]), f(arr[1]), ..., f(arr[len(arr) - 1])].
let<T1, T2> map: T1[], (T1 -> T2) -> T2[] = |arr, f| new(len(arr), |i| f(arr[i]));

/// Evaluates to the array [f(0, arr[0]), f(1, arr[1]), ..., f(len(arr) - 1, arr[len(arr) - 1])].
let<T1, T2> map_enumerated: T1[], (int, T1 -> T2) -> T2[] = |arr, f| new(len(arr), |i| f(i, arr[i]));

/// Computes folder(...folder(folder(initial, arr[0]), arr[1]) ..., arr[len(arr) - 1])
let<T1, T2> fold: T1[], T2, (T2, T1 -> T2) -> T2 = |arr, initial, folder| std::utils::fold(len(arr), |i| arr[i], initial, folder);

/// Turns an array of arrays into a single array by concatenating the arrays.
let<T> flatten: T[][] -> T[] = |arr| fold(arr, [], |a, b| a + b);

/// Returns the sum of the array elements.
// TODO: Should make use of the Default or Zero trait instead of FromLiteral (then we can also
// use this function to flatten an array of arrays.
let<T: Add + FromLiteral> sum: T[] -> T = |arr| fold(arr, 0, |a, b| a + b);

/// Returns the product of the array elements.
let<T: Mul + FromLiteral> product: T[] -> T = |arr| fold(arr, 1, |a, b| a * b);

/// Zips two arrays
let<T1, T2, T3> zip: T1[], T2[], (T1, T2 -> T3) -> T3[] = |array1, array2, fn| {
    std::check::assert(len(array1) == len(array2), || "Array lengths do not match");
    new(len(array1), |i| fn(array1[i], array2[i]))
};

/// Returns f(i, arr[i]) for the first i where this is not None, or None if no such i exists.
let<T1, T2> find_map_enumerated: T1[], (int, T1 -> Option<T2>) -> Option<T2> =
    |arr, f| find_internal::find_map_enumerated(arr, 0, len(arr), f);
/// Returns f(arr[i]) for the first i where this is not None, or None if no such i exists.
let<T1, T2> find_map: T1[], (T1 -> Option<T2>) -> Option<T2> =
    |arr, f| find_map_enumerated(arr, |_, x| f(x));

/// Returns Some(i) for the first index i where f(arr[i]) is true, or None if no such i exists.
let<T> find_index: T[], (T -> bool) -> Option<int>
    = |arr, f| find_map_enumerated(arr, |i, x| if f(x) { Option::Some(i) } else { Option::None });

mod find_internal {
    let<T1, T2> find_map_enumerated: T1[], int, int, (int, T1 -> Option<T2>) -> Option<T2> =
        |arr, i, l, f| if i >= l { Option::None } else {
            match f(i, arr[i]) {
                Option::Some(x) => Option::Some(x),
                Option::None => find_map_enumerated(arr, i + 1, l, f),
            }
        };
}

let<T> sort: T[], (T, T -> bool) -> T[] = |arr, lt| internal::sort(to_slice(arr), lt);

// TODO turn this into a struct once we have structs.
enum Slice<T> {
    // data, start, len
    S(T[], int, int)
}

let<T> to_slice: T[] -> Slice<T> = |x| Slice::S(x, 0, len(x));
let<T> to_array: Slice<T> -> T[] = |s| match s {
    Slice::S(arr, start, l) => if start == 0 && l == len(arr) {
        arr
    } else {
        std::array::new(l, |i| arr[start + i])
    }
};
let<T> split_slice_half: Slice<T> -> (Slice<T>, Slice<T>) = |s| match s {
    Slice::S(arr, start, l) => {
        let half_len = l / 2;
        (
            Slice::S(arr, start, half_len),
            Slice::S(arr, start + half_len, l - half_len)
        )
    }
};
let<T> slice_pop: Slice<T> -> (Slice<T>, Option<T>) = |s| match s {
    Slice::S(_, _, 0) => (s, Option::None),
    Slice::S(arr, start, l) => (Slice::S(arr, start, l - 1), Option::Some(arr[start + l - 1])),
};

mod internal {
    use super::Slice;
    use super::split_slice_half;
    use super::slice_pop;
    use super::to_slice;
    use super::to_array;

    let<T> sort: Slice<T>, (T, T -> bool) -> T[] = |slice, lt| match slice {
        Slice::S(_, _, 0) => [],
        Slice::S(_, _, 1) => to_array(slice),
        s => {
            let (left, right) = split_slice_half(s);
            let left_sorted = to_slice(sort(left, lt));
            let right_sorted = to_slice(sort(right, lt));
            merge(left_sorted, right_sorted, lt)
        }
    };

    /// Merge part of merge sort. We merge right-to-left because this is
    /// more efficient to concatenate arrays.
    let<T> merge: Slice<T>, Slice<T>, (T, T -> bool) -> T[] = |left, right, lt|
        match (slice_pop(left), slice_pop(right)) {
            ((_, Option::None), _) => to_array(right),
            (_, (_, Option::None)) => to_array(left),
            ((l_short, Option::Some(l_last)), (r_short, Option::Some(r_last))) =>
                if lt(l_last, r_last) {
                    merge(left, r_short, lt) + [r_last]
                } else {
                    merge(l_short, right, lt) + [l_last]
                }
        };
}

/// Applies the next operator to all elements of the array.
let next: expr[] -> expr[] = query |arr| new(len(arr), |i| arr[i]');

/// Evaluates an array of expressions
let eval: expr[] -> fe[] = query |arr| new(len(arr), |i| std::prover::eval(arr[i]));
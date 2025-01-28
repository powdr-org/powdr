/// A function that evaluates an algebraic expression on the current row.
/// Since this needs the concept of a "current row", it is only
/// valid in query functions.
let eval: expr -> fe = [];

/// Returns the value of the algebraic expression on the current row if it is
/// known, otherwise returns None.
/// This function is only valid in query functions.
let try_eval: expr -> Option<fe> = [];

/// A function that can be used to set a cell value.
/// The parameters are column, row index and value.
/// It is an error to provide a value that is different to one already provided or determined.
/// This function is only valid in query functions.
let provide_value: expr, int, fe -> () = [];

/// Provide a value to a column only if it has not been set yet.
let provide_if_unknown: expr, int, (-> fe) -> () = query |column, row, f| match try_eval(column) {
    Option::None => provide_value(column, row, f()),
    _ => (),
};

/// Computes the value of a column based on the values of other columns.
let compute_from: expr, int, expr[], (fe[] -> fe) -> () = query |dest_col, row, input_cols, f|
    match try_eval(dest_col) {
        // If the destination column is already known, do nothing.
        Option::Some(_) => (),
        Option::None => {
            // Try to evaluate the input columns.
            let maybe_values = std::array::map(input_cols, |c| try_eval(c));
            // Collect the values into an Option<fe[]>.
            let values = std::array::fold(maybe_values, Option::Some([]), |acc, value| match (acc, value) {
                (Option::Some(a), Option::Some(v)) => Option::Some(a + [v]),
                _ => Option::None,
            });
            match values {
                // If all input columns are known, compute the value and provide it.
                Option::Some(vals) => provide_value(dest_col, row, f(vals)),
                Option::None => (),
            }
        }
    };

/// Retrieves a field element from a prover-provided (untrusted and not committed) input channel.
/// The parameters are the channel id and the index in the channel.
/// Index zero is the length of the channel (number of bytes) and index 1 is the first element.
let input_from_channel: int, int -> fe = [];

/// Writes a field element to the given output channel.
/// The first parameter is the channel id, the second is the element to write.
let output_to_channel: int, fe -> () = [];

let handle_query: expr, int, std::prelude::Query -> () = query |column, row, v| match v {
    Query::Hint(h) => provide_if_unknown(column, row, || h),
    Query::Input(i, j) => provide_if_unknown(column, row, || input_from_channel(i, j)),
    Query::Output(channel, e) => provide_if_unknown(column, row, || { output_to_channel(channel, e); 0 }),
    Query::None => (),
};

/// Constructs a challenge object.
/// The arguments are the proof stage and the id of the challenge, in this order.
let challenge: int, int -> expr = constr |st, id| std::prelude::challenge(st, id);

/// Creates a witness column at a given stage.
/// The first argument is a name suggestion, but it will be made unique.
/// The second argument is the stage.
let new_witness_col_at_stage: string, int -> expr = [];

/// Returns the minimum number of rows in this namespace, sometimes known as the minimum "degree".
let min_degree: -> int = [];
/// Returns the maximum number of rows in this namespace, sometimes known as the maximum "degree".
let max_degree: -> int = [];
/// Returns the number of rows in this namespace, sometimes known as the "degree". Fails if the minimum and maximum degree are not equal.
let degree: -> int = [];

/// Asserts that the current degree or row count is at least m.
let require_min_degree: int -> () = |m| std::check::assert(degree() >= m, || "Degree too small.");

/// Asserts that the current degree or row count is at most m;
let require_max_degree: int -> () = |m| std::check::assert(degree() <= m, || "Degree too large.");

/// Calls the argument and returns all constraints that were generated during the call.
/// If the constraints are not added to the global set again, they are ignored.
let capture_constraints: (-> ()) -> Constr[] = [];

/// Calls the argument with the current stage counter incremented. This means that columns created during
/// the call will be next-stage columns. The stage counter is reset afterwards.
let at_next_stage: (-> ()) -> () = [];

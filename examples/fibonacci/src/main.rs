use powdr::Session;

fn main() {
    env_logger::init();

    let n = 22;
    let mut session = Session::builder()
        .guest_path("./guest")
        .out_path("powdr-target")
        .chunk_size_log2(18)
        .build()
        // Compute Fibonacci of 21 in the guest.
        .write(&n);

    // Fast dry run to test execution.
    //session.run();

    session.optimize_autoprecompile();

    session.prove();
}

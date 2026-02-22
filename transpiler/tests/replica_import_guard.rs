#[test]
fn test_replica_gen_no_acceptor_log_truncation_helper_import() {
    let generated = std::fs::read_to_string("../src/generated/RSL/replica_gen.rs")
        .expect("Failed to read replica_gen.rs");
    assert!(
        !generated.contains("acceptorimpl::CIsLogTruncationPointValid"),
        "replica_gen.rs should not import legacy CIsLogTruncationPointValid from acceptorimpl"
    );
}

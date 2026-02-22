use std::fs;

#[test]
fn test_acceptor_helpers_owns_log_truncation_validity_logic() {
    let helpers = fs::read_to_string("../src/implementation/RSL/acceptor_helpers.rs")
        .expect("Failed to read acceptor_helpers.rs");
    assert!(
        helpers.contains("pub fn CIsLogTruncationPointValid"),
        "acceptor_helpers.rs should define CIsLogTruncationPointValid"
    );
    assert!(
        helpers.contains("pub fn CCountLargerInSeq"),
        "acceptor_helpers.rs should define CCountLargerInSeq"
    );
    assert!(
        helpers.contains("pub fn CCountLargerOrEqualInSeq"),
        "acceptor_helpers.rs should define CCountLargerOrEqualInSeq"
    );
    assert!(
        helpers.contains("pub fn CIsNthHighestValueInSequence"),
        "acceptor_helpers.rs should define CIsNthHighestValueInSequence"
    );
}

#[test]
fn test_acceptorimpl_exposes_only_compatibility_wrappers_for_log_truncation_helpers() {
    let impl_source = fs::read_to_string("../src/implementation/RSL/acceptorimpl.rs")
        .expect("Failed to read acceptorimpl.rs");
    assert!(
        impl_source.contains("pub fn CIsLogTruncationPointValid"),
        "acceptorimpl.rs should retain CIsLogTruncationPointValid symbol for compatibility"
    );
    assert!(
        impl_source.contains("acceptor_helpers::CIsLogTruncationPointValid"),
        "acceptorimpl.rs should delegate CIsLogTruncationPointValid to acceptor_helpers"
    );
    assert!(
        impl_source.contains("acceptor_helpers::CCountLargerInSeq"),
        "acceptorimpl.rs should delegate CCountLargerInSeq to acceptor_helpers"
    );
    assert!(
        impl_source.contains("acceptor_helpers::CCountLargerOrEqualInSeq"),
        "acceptorimpl.rs should delegate CCountLargerOrEqualInSeq to acceptor_helpers"
    );
    assert!(
        impl_source.contains("acceptor_helpers::CIsNthHighestValueInSequence"),
        "acceptorimpl.rs should delegate CIsNthHighestValueInSequence to acceptor_helpers"
    );
}

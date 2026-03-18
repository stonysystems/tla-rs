use std::fs;
use std::path::Path;

#[test]
fn test_generated_rsl_modules_keep_legacy_impl_imports_constrained() {
    let generated_dir = Path::new("../src/generated/RSL");
    let disallowed_legacy_imports = [
        "acceptorimpl::",
        "ExecutorImpl::",
        "ElectionImpl::",
        "ProposerImpl::",
        "ReplicaImpl::",
    ];

    for entry in fs::read_dir(generated_dir).expect("Failed to list generated RSL directory") {
        let entry = entry.expect("Failed to read generated RSL directory entry");
        let path = entry.path();
        if !path
            .file_name()
            .and_then(|name| name.to_str())
            .map(|name| name.ends_with("_gen.rs"))
            .unwrap_or(false)
        {
            continue;
        }
        let filename = path
            .file_name()
            .and_then(|name| name.to_str())
            .expect("generated file name should be valid UTF-8");
        if filename == "types_gen.rs" {
            continue;
        }

        let source = fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("Failed to read {}: {}", path.display(), e));
        for needle in disallowed_legacy_imports {
            assert!(
                !source.contains(needle),
                "{} should not directly import legacy implementation path `{}`",
                filename,
                needle
            );
        }
    }
}

#[test]
fn test_types_gen_is_the_only_generated_legacy_type_bridge() {
    let source = fs::read_to_string("../src/generated/RSL/types_gen.rs")
        .expect("Failed to read types_gen.rs");
    assert!(
        source.contains("pub use crate::implementation::RSL::acceptorimpl::CAcceptor;"),
        "types_gen.rs should keep CAcceptor ownership bridge"
    );
    assert!(
        source.contains(
            "pub use crate::implementation::RSL::ExecutorImpl::{CExecutor, CIncompleteBatchTimer};"
        ),
        "types_gen.rs should keep CExecutor ownership bridge"
    );
    assert!(
        source.contains("pub use crate::implementation::RSL::ProposerImpl::CProposer;"),
        "types_gen.rs should keep CProposer ownership bridge"
    );
    assert!(
        source.contains("pub use crate::implementation::RSL::ElectionImpl::{"),
        "types_gen.rs should keep CElectionState ownership bridge"
    );
    assert!(
        source.contains("pub use crate::implementation::RSL::ReplicaImpl::{"),
        "types_gen.rs should keep CReplica ownership bridge"
    );
}

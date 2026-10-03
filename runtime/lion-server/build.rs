use std::path::PathBuf;

fn main() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let root = root
        .canonicalize()
        .expect("resolving the tla-rs repository root");
    let protocol_library = root.join("bin/libtla_protocol.rlib");
    assert!(
        protocol_library.is_file(),
        "build the native protocol library with scripts/build_lion_runtime.sh"
    );
    println!("cargo:rerun-if-changed={}", protocol_library.display());
    println!("cargo:rerun-if-env-changed=VERUS_PATH");
}

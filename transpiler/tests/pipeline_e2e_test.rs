//! End-to-end tests for the TLA+ to Verus transpilation pipeline.
//!
//! These tests verify that:
//! 1. TLA+ specifications can be parsed
//! 2. Types are correctly inferred
//! 3. Verus spec code is generated
//! 4. Mode annotations are generated
//! 5. The full pipeline produces valid Verus code
//!
//! Tests in this module correspond to task T9.1.

use verus_transpiler::tla::{
    generate_mode_annotations, parse_module, ModuleConfig, ModuleTranslator, TypeInference,
};
use verus_transpiler::AnnotationParser;

/// Read a TLA+ file from the examples directory
fn read_example(name: &str) -> String {
    let path = format!("tests/tla_examples/{}.tla", name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("Failed to read {}: {}", path, e))
}

/// Helper: Run the full TLA+ to Verus spec pipeline
fn tla_to_verus_spec(source: &str) -> (String, String) {
    let module = parse_module(source).expect("Failed to parse TLA+ module");

    // Infer types
    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(&module);

    // Translate to Verus spec
    let config = ModuleConfig::default();
    let mut translator = ModuleTranslator::with_config(config).with_types(type_env);
    let verus_code = translator.translate(&module);

    // Generate mode annotations
    let mode_annotations = generate_mode_annotations(&module);

    (verus_code, mode_annotations)
}

// =============================================================================
// End-to-End Pipeline Tests
// =============================================================================

/// Test that SimpleCounter can go through the full pipeline
#[test]
fn test_e2e_simplecounter_pipeline() {
    let source = read_example("SimpleCounter");

    // Step 1: TLA+ → Verus spec
    let (verus_spec, mode_annotations) = tla_to_verus_spec(&source);

    // Verify spec structure
    assert!(
        verus_spec.contains("verus!"),
        "Generated code should contain verus! block"
    );
    assert!(
        verus_spec.contains("pub struct LState"),
        "Should contain state struct"
    );
    assert!(
        verus_spec.contains("pub struct LConstants"),
        "Should contain constants struct"
    );
    assert!(
        verus_spec.contains("pub open spec fn LInit"),
        "Should contain Init spec"
    );
    assert!(
        verus_spec.contains("pub open spec fn LNext"),
        "Should contain Next spec"
    );

    // Verify mode annotations structure
    assert!(
        mode_annotations.contains("module SimpleCounter"),
        "Mode annotations should have module name"
    );
    assert!(
        mode_annotations.contains("LInit"),
        "Mode annotations should have Init"
    );

    // Step 2: Parse mode annotations
    let parser = AnnotationParser::new(mode_annotations);
    let parsed_modules = parser.parse().expect("Failed to parse mode annotations");
    assert!(
        !parsed_modules.is_empty(),
        "Should parse at least one module"
    );
}

/// Test that DieHard puzzle can go through the full pipeline
#[test]
fn test_e2e_diehard_pipeline() {
    let source = read_example("DieHard");

    // Step 1: TLA+ → Verus spec
    let (verus_spec, mode_annotations) = tla_to_verus_spec(&source);

    // Verify spec structure - DieHard has IF-THEN-ELSE operators
    assert!(
        verus_spec.contains("verus!"),
        "Generated code should contain verus! block"
    );
    assert!(
        verus_spec.contains("pub open spec fn LSmallToBig"),
        "Should contain SmallToBig spec with conditional"
    );
    assert!(
        verus_spec.contains("pub open spec fn LBigToSmall"),
        "Should contain BigToSmall spec with conditional"
    );

    // Verify conditionals are translated
    assert!(
        verus_spec.contains("if") || verus_spec.contains("=>"),
        "Should contain conditional logic"
    );

    // Step 2: Parse mode annotations
    let parser = AnnotationParser::new(mode_annotations);
    let parsed_modules = parser.parse().expect("Failed to parse mode annotations");
    assert!(
        !parsed_modules.is_empty(),
        "Should parse at least one module"
    );
}

/// Test that TwoPhase commit can go through the full pipeline
#[test]
fn test_e2e_twophase_pipeline() {
    let source = read_example("TwoPhase");

    // Step 1: TLA+ → Verus spec
    let (verus_spec, mode_annotations) = tla_to_verus_spec(&source);

    // Verify spec structure - TwoPhase has parameterized operators
    assert!(
        verus_spec.contains("verus!"),
        "Generated code should contain verus! block"
    );

    // TwoPhase has operators with parameters (TMRcvPrepared(r))
    assert!(
        verus_spec.contains("pub open spec fn LTMRcvPrepared"),
        "Should contain parameterized operator"
    );

    // Should have set operations
    assert!(
        verus_spec.contains("union") || verus_spec.contains("cup") || verus_spec.contains("+"),
        "Should contain set union operations"
    );

    // Step 2: Parse mode annotations
    let parser = AnnotationParser::new(mode_annotations);
    let parsed_modules = parser.parse().expect("Failed to parse mode annotations");
    assert!(
        !parsed_modules.is_empty(),
        "Should parse at least one module"
    );
}

/// Test that EWD840 termination detection can go through the full pipeline
#[test]
fn test_e2e_ewd840_pipeline() {
    let source = read_example("EWD840");

    // Step 1: TLA+ → Verus spec
    let (verus_spec, mode_annotations) = tla_to_verus_spec(&source);

    // Verify spec structure
    assert!(
        verus_spec.contains("verus!"),
        "Generated code should contain verus! block"
    );

    // EWD840 has multiple variables including token position
    assert!(
        verus_spec.contains("pub tpos:"),
        "Should contain token position variable"
    );
    assert!(
        verus_spec.contains("pub tcolor:"),
        "Should contain token color variable"
    );

    // Should have parameterized operators
    assert!(
        verus_spec.contains("pub open spec fn LTerminate"),
        "Should contain Terminate operator"
    );

    // Step 2: Parse mode annotations
    let parser = AnnotationParser::new(mode_annotations);
    let parsed_modules = parser.parse().expect("Failed to parse mode annotations");
    assert!(
        !parsed_modules.is_empty(),
        "Should parse at least one module"
    );
}

/// Test that Raft leader election can go through the full pipeline
#[test]
fn test_e2e_raft_pipeline() {
    let source = read_example("Raft");

    // Step 1: TLA+ → Verus spec
    let (verus_spec, mode_annotations) = tla_to_verus_spec(&source);

    // Verify spec structure
    assert!(
        verus_spec.contains("verus!"),
        "Generated code should contain verus! block"
    );

    // Raft has string constants for states
    assert!(
        verus_spec.contains("pub open spec fn LFollower"),
        "Should contain Follower constant operator"
    );
    assert!(
        verus_spec.contains("pub open spec fn LCandidate"),
        "Should contain Candidate constant operator"
    );
    assert!(
        verus_spec.contains("pub open spec fn LLeader"),
        "Should contain Leader constant operator"
    );

    // Should have state transitions
    assert!(
        verus_spec.contains("pub open spec fn LBecomeCandidate"),
        "Should contain BecomeCandidate"
    );
    assert!(
        verus_spec.contains("pub open spec fn LBecomeLeader"),
        "Should contain BecomeLeader"
    );

    // Step 2: Parse mode annotations
    let parser = AnnotationParser::new(mode_annotations);
    let parsed_modules = parser.parse().expect("Failed to parse mode annotations");
    assert!(
        !parsed_modules.is_empty(),
        "Should parse at least one module"
    );
}

/// Test that Paxos consensus can go through the full pipeline
#[test]
fn test_e2e_paxos_pipeline() {
    let source = read_example("Paxos");

    // Step 1: TLA+ → Verus spec
    let (verus_spec, mode_annotations) = tla_to_verus_spec(&source);

    // Verify spec structure
    assert!(
        verus_spec.contains("verus!"),
        "Generated code should contain verus! block"
    );

    // Paxos has message phase constants
    assert!(
        verus_spec.contains("pub open spec fn LPhase1a"),
        "Should contain Phase1a constant"
    );
    assert!(
        verus_spec.contains("pub open spec fn LPhase2b"),
        "Should contain Phase2b constant"
    );

    // Should have send operations with parameters
    assert!(
        verus_spec.contains("pub open spec fn LSend1a"),
        "Should contain Send1a"
    );
    assert!(
        verus_spec.contains("pub open spec fn LSend2b"),
        "Should contain Send2b"
    );

    // Should have a Chosen predicate
    assert!(
        verus_spec.contains("pub open spec fn LChosen"),
        "Should contain Chosen predicate"
    );

    // Step 2: Parse mode annotations
    let parser = AnnotationParser::new(mode_annotations);
    let parsed_modules = parser.parse().expect("Failed to parse mode annotations");
    assert!(
        !parsed_modules.is_empty(),
        "Should parse at least one module"
    );
}

/// Test that PBFT can go through the full pipeline
#[test]
fn test_e2e_pbft_pipeline() {
    let source = read_example("PBFT");

    // Step 1: TLA+ → Verus spec
    let (verus_spec, mode_annotations) = tla_to_verus_spec(&source);

    // Verify spec structure
    assert!(
        verus_spec.contains("verus!"),
        "Generated code should contain verus! block"
    );

    // PBFT has phase constants
    assert!(
        verus_spec.contains("pub open spec fn LPrePrepare"),
        "Should contain PrePrepare constant"
    );
    assert!(
        verus_spec.contains("pub open spec fn LPrepare"),
        "Should contain Prepare constant"
    );
    assert!(
        verus_spec.contains("pub open spec fn LCommit"),
        "Should contain Commit constant"
    );

    // Should have quorum calculations
    assert!(
        verus_spec.contains("pub open spec fn LQuorumSize"),
        "Should contain QuorumSize"
    );

    // Should have prepared/committed predicates
    assert!(
        verus_spec.contains("pub open spec fn LPrepared"),
        "Should contain Prepared predicate"
    );
    assert!(
        verus_spec.contains("pub open spec fn LCommitted"),
        "Should contain Committed predicate"
    );

    // Should have view change
    assert!(
        verus_spec.contains("pub open spec fn LViewChange"),
        "Should contain ViewChange"
    );

    // Step 2: Parse mode annotations
    let parser = AnnotationParser::new(mode_annotations);
    let parsed_modules = parser.parse().expect("Failed to parse mode annotations");
    assert!(
        !parsed_modules.is_empty(),
        "Should parse at least one module"
    );
}

// =============================================================================
// Generated Code Quality Tests
// =============================================================================

/// Test that generated code has proper Verus structure
#[test]
fn test_generated_code_structure() {
    let source = read_example("SimpleCounter");
    let (verus_spec, _) = tla_to_verus_spec(&source);

    // Should start with imports
    assert!(
        verus_spec.contains("use vstd::prelude::*"),
        "Should have vstd prelude import"
    );

    // Should have verus! block
    assert!(
        verus_spec.starts_with("use vstd::prelude::*;")
            || verus_spec.starts_with("//")
            || verus_spec.starts_with("/*"),
        "Should start with imports or comments"
    );

    // Should properly close the verus! block
    assert!(
        verus_spec.contains("} // verus!") || verus_spec.ends_with("}\n"),
        "Should properly close verus! block"
    );
}

/// Test that action operators have proper s and s_ parameters
#[test]
fn test_action_operators_have_state_params() {
    let source = read_example("SimpleCounter");
    let (verus_spec, _) = tla_to_verus_spec(&source);

    // Action operators (those with primed variables) should have s and s_ params
    // Increment modifies count' so it's an action
    assert!(
        verus_spec.contains("fn LIncrement(s: LState, s_: LState)")
            || verus_spec.contains("fn LIncrement(s: LState, s_: LState,"),
        "Action operator Increment should have s and s_ parameters"
    );

    // Init has state param + constants (SimpleCounter has CONSTANT MaxCount)
    assert!(
        verus_spec.contains("fn LInit(s: LState") || verus_spec.contains("fn LInit(s_: LState"),
        "Init should have state parameter"
    );
}

/// Test that mode annotations have proper structure
#[test]
fn test_mode_annotations_structure() {
    let source = read_example("TwoPhase");
    let (_, mode_annotations) = tla_to_verus_spec(&source);

    // Should have module declaration
    assert!(
        mode_annotations.contains("module TwoPhase"),
        "Should have module declaration"
    );

    // Should have function annotations
    assert!(
        mode_annotations.contains("LInit")
            || mode_annotations.contains("Init")
            || mode_annotations.contains("spec fn"),
        "Should have function annotations"
    );
}

// =============================================================================
// Custom Configuration Tests
// =============================================================================

/// Test pipeline with custom spec prefix
#[test]
fn test_pipeline_custom_prefix() {
    let source = read_example("SimpleCounter");
    let module = parse_module(&source).expect("Failed to parse");

    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(&module);

    // Use custom prefix "Spec" instead of "L"
    let config = ModuleConfig {
        spec_prefix: "Spec".to_string(),
        ..ModuleConfig::default()
    };
    let mut translator = ModuleTranslator::with_config(config).with_types(type_env);
    let verus_code = translator.translate(&module);

    assert!(
        verus_code.contains("pub struct SpecState"),
        "Should use custom prefix for state struct"
    );
    assert!(
        verus_code.contains("pub open spec fn SpecInit"),
        "Should use custom prefix for operators"
    );
}

/// Test pipeline with custom state name
#[test]
fn test_pipeline_custom_state_name() {
    let source = read_example("SimpleCounter");
    let module = parse_module(&source).expect("Failed to parse");

    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(&module);

    // Use custom state name "Counter" instead of "State"
    let config = ModuleConfig {
        state_name: "Counter".to_string(),
        ..ModuleConfig::default()
    };
    let mut translator = ModuleTranslator::with_config(config).with_types(type_env);
    let verus_code = translator.translate(&module);

    assert!(
        verus_code.contains("pub struct LCounter"),
        "Should use custom state name"
    );
}

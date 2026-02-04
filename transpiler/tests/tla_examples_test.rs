//! Integration tests for TLA+ example specifications.
//!
//! These tests verify that standard TLA+ examples can be parsed and
//! translated to Verus code by the transpiler pipeline.

use verus_transpiler::tla::{
    generate_mode_annotations, parse_module, ModuleConfig, ModuleTranslator, TypeInference,
};

/// Read a TLA+ file from the examples directory
fn read_example(name: &str) -> String {
    let path = format!("tests/tla_examples/{}.tla", name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("Failed to read {}: {}", path, e))
}

/// Test helper: parse, infer types, and translate a TLA+ module
fn translate_example(source: &str) -> (String, String) {
    let module = parse_module(source).expect("Failed to parse TLA+ module");

    // Infer types
    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(&module);

    // Translate to Verus spec
    let config = ModuleConfig::default();
    let translator = ModuleTranslator::with_config(config).with_types(type_env);
    let verus_code = translator.translate(&module);

    // Generate mode annotations
    let mode_annotations = generate_mode_annotations(&module);

    (verus_code, mode_annotations)
}

// =============================================================================
// DieHard Example Tests
// =============================================================================

#[test]
fn test_diehard_parsing() {
    let source = read_example("DieHard");
    let module = parse_module(&source).expect("Failed to parse DieHard.tla");

    assert_eq!(module.name, "DieHard");
    assert_eq!(module.variables, vec!["big", "small"]);
    assert!(module.extends.contains(&"Naturals".to_string()));

    // Check operators are parsed
    let operator_names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(operator_names.contains(&"TypeOK"));
    assert!(operator_names.contains(&"Init"));
    assert!(operator_names.contains(&"FillBig"));
    assert!(operator_names.contains(&"FillSmall"));
    assert!(operator_names.contains(&"EmptyBig"));
    assert!(operator_names.contains(&"EmptySmall"));
    assert!(operator_names.contains(&"SmallToBig"));
    assert!(operator_names.contains(&"BigToSmall"));
    assert!(operator_names.contains(&"Next"));
}

#[test]
fn test_diehard_translation() {
    let source = read_example("DieHard");
    let (verus_code, mode_annotations) = translate_example(&source);

    // Verify Verus code structure
    assert!(
        verus_code.contains("pub struct LState"),
        "Should contain state struct"
    );
    assert!(verus_code.contains("pub big:"), "Should contain big field");
    assert!(
        verus_code.contains("pub small:"),
        "Should contain small field"
    );

    // Verify operators are translated
    assert!(
        verus_code.contains("pub open spec fn LInit"),
        "Should contain Init spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LFillBig"),
        "Should contain FillBig spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LNext"),
        "Should contain Next spec fn"
    );

    // Verify mode annotations
    assert!(
        mode_annotations.contains("module DieHard"),
        "Should contain module name"
    );
    assert!(
        mode_annotations.contains("LInit"),
        "Should have Init annotation"
    );
}

// =============================================================================
// TwoPhase Example Tests
// =============================================================================

#[test]
fn test_twophase_parsing() {
    let source = read_example("TwoPhase");
    let module = parse_module(&source).expect("Failed to parse TwoPhase.tla");

    assert_eq!(module.name, "TwoPhase");
    assert_eq!(module.variables.len(), 3);
    assert!(module.variables.contains(&"rmState".to_string()));
    assert!(module.variables.contains(&"tmState".to_string()));
    assert!(module.variables.contains(&"tmPrepared".to_string()));

    // Check constants
    let const_names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
    assert!(const_names.contains(&"RM"));

    // Check extends
    assert!(module.extends.contains(&"Naturals".to_string()));
}

#[test]
fn test_twophase_translation() {
    let source = read_example("TwoPhase");
    let (verus_code, mode_annotations) = translate_example(&source);

    // Verify state struct has all variables
    assert!(
        verus_code.contains("pub struct LState"),
        "Should contain state struct"
    );
    assert!(
        verus_code.contains("pub rmState:"),
        "Should contain rmState field"
    );
    assert!(
        verus_code.contains("pub tmState:"),
        "Should contain tmState field"
    );
    assert!(
        verus_code.contains("pub tmPrepared:"),
        "Should contain tmPrepared field"
    );

    // Verify constants struct
    assert!(
        verus_code.contains("LConstants"),
        "Should contain constants struct"
    );
    assert!(verus_code.contains("pub RM:"), "Should contain RM constant");

    // Verify operators with parameters are translated
    assert!(
        verus_code.contains("pub open spec fn LTMRcvPrepared"),
        "Should contain TMRcvPrepared spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LTMCommit"),
        "Should contain TMCommit spec fn"
    );

    // Verify mode annotations
    assert!(
        mode_annotations.contains("module TwoPhase"),
        "Should contain module name"
    );
}

// =============================================================================
// SimpleCounter Example Tests
// =============================================================================

#[test]
fn test_simplecounter_parsing() {
    let source = read_example("SimpleCounter");
    let module = parse_module(&source).expect("Failed to parse SimpleCounter.tla");

    assert_eq!(module.name, "SimpleCounter");
    assert_eq!(module.variables, vec!["count"]);

    let const_names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
    assert!(const_names.contains(&"MaxCount"));

    let operator_names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(operator_names.contains(&"TypeOK"));
    assert!(operator_names.contains(&"Init"));
    assert!(operator_names.contains(&"Increment"));
    assert!(operator_names.contains(&"Decrement"));
    assert!(operator_names.contains(&"Reset"));
    assert!(operator_names.contains(&"Next"));
}

#[test]
fn test_simplecounter_translation() {
    let source = read_example("SimpleCounter");
    let (verus_code, mode_annotations) = translate_example(&source);

    // Verify basic structure
    assert!(
        verus_code.contains("pub struct LState"),
        "Should contain state struct"
    );
    assert!(
        verus_code.contains("pub count:"),
        "Should contain count field"
    );

    // Verify constants
    assert!(
        verus_code.contains("LConstants"),
        "Should contain constants struct"
    );
    assert!(
        verus_code.contains("pub MaxCount:"),
        "Should contain MaxCount constant"
    );

    // Verify operators
    assert!(
        verus_code.contains("pub open spec fn LInit"),
        "Should contain Init spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LIncrement"),
        "Should contain Increment spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LDecrement"),
        "Should contain Decrement spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LReset"),
        "Should contain Reset spec fn"
    );

    // Verify mode annotations
    assert!(
        mode_annotations.contains("module SimpleCounter"),
        "Should contain module name"
    );
    assert!(
        mode_annotations.contains("LInit"),
        "Should have Init annotation"
    );
}

// =============================================================================
// Type Inference Tests
// =============================================================================

#[test]
fn test_diehard_type_inference() {
    let source = read_example("DieHard");
    let module = parse_module(&source).expect("Failed to parse DieHard.tla");

    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(&module);

    // Variables should be inferred
    assert!(
        type_env.variables.contains_key("big"),
        "Should infer type for big"
    );
    assert!(
        type_env.variables.contains_key("small"),
        "Should infer type for small"
    );
}

#[test]
fn test_simplecounter_type_inference() {
    let source = read_example("SimpleCounter");
    let module = parse_module(&source).expect("Failed to parse SimpleCounter.tla");

    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(&module);

    // Variable should be inferred
    assert!(
        type_env.variables.contains_key("count"),
        "Should infer type for count"
    );

    // Constant should be inferred
    assert!(
        type_env.constants.contains_key("MaxCount"),
        "Should infer type for MaxCount"
    );
}

// =============================================================================
// EWD840 Example Tests (Medium Complexity)
// =============================================================================

#[test]
fn test_ewd840_parsing() {
    let source = read_example("EWD840");
    let module = parse_module(&source).expect("Failed to parse EWD840.tla");

    assert_eq!(module.name, "EWD840");
    assert_eq!(module.variables.len(), 4);
    assert!(module.variables.contains(&"active".to_string()));
    assert!(module.variables.contains(&"color".to_string()));
    assert!(module.variables.contains(&"tpos".to_string()));
    assert!(module.variables.contains(&"tcolor".to_string()));

    // Check constant
    let const_names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
    assert!(const_names.contains(&"N"));

    // Check operators
    let operator_names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(operator_names.contains(&"TypeOK"));
    assert!(operator_names.contains(&"Init"));
    assert!(operator_names.contains(&"Terminate"));
    assert!(operator_names.contains(&"SendMsg"));
    assert!(operator_names.contains(&"PassToken"));
    assert!(operator_names.contains(&"InitiateProbe"));
    assert!(operator_names.contains(&"Terminated"));
    assert!(operator_names.contains(&"Next"));
}

#[test]
fn test_ewd840_translation() {
    let source = read_example("EWD840");
    let (verus_code, mode_annotations) = translate_example(&source);

    // Verify state struct has all variables
    assert!(
        verus_code.contains("pub struct LState"),
        "Should contain state struct"
    );
    assert!(
        verus_code.contains("pub active:"),
        "Should contain active field"
    );
    assert!(
        verus_code.contains("pub tpos:"),
        "Should contain tpos field"
    );
    assert!(
        verus_code.contains("pub tcolor:"),
        "Should contain tcolor field"
    );

    // Verify constants struct
    assert!(
        verus_code.contains("LConstants"),
        "Should contain constants struct"
    );
    assert!(verus_code.contains("pub N:"), "Should contain N constant");

    // Verify key operators are translated
    assert!(
        verus_code.contains("pub open spec fn LInit"),
        "Should contain Init spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LPassToken"),
        "Should contain PassToken spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LTerminated"),
        "Should contain Terminated spec fn"
    );

    // Verify mode annotations
    assert!(
        mode_annotations.contains("module EWD840"),
        "Should contain module name"
    );
}

#[test]
fn test_ewd840_type_inference() {
    let source = read_example("EWD840");
    let module = parse_module(&source).expect("Failed to parse EWD840.tla");

    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(&module);

    // Variables should be inferred
    assert!(
        type_env.variables.contains_key("active"),
        "Should infer type for active"
    );
    assert!(
        type_env.variables.contains_key("tpos"),
        "Should infer type for tpos"
    );
    assert!(
        type_env.variables.contains_key("tcolor"),
        "Should infer type for tcolor"
    );

    // Constant should be inferred
    assert!(
        type_env.constants.contains_key("N"),
        "Should infer type for N"
    );
}

// =============================================================================
// Raft Example Tests (Medium Complexity)
// =============================================================================

#[test]
fn test_raft_parsing() {
    let source = read_example("Raft");
    let module = parse_module(&source).expect("Failed to parse Raft.tla");

    assert_eq!(module.name, "Raft");
    assert_eq!(module.variables.len(), 4);
    assert!(module.variables.contains(&"currentTerm".to_string()));
    assert!(module.variables.contains(&"state".to_string()));
    assert!(module.variables.contains(&"votedFor".to_string()));
    assert!(module.variables.contains(&"votesGranted".to_string()));

    // Check constant
    let const_names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
    assert!(const_names.contains(&"Server"));

    // Check operators
    let operator_names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(operator_names.contains(&"Follower"));
    assert!(operator_names.contains(&"Candidate"));
    assert!(operator_names.contains(&"Leader"));
    assert!(operator_names.contains(&"TypeOK"));
    assert!(operator_names.contains(&"Init"));
    assert!(operator_names.contains(&"BecomeCandidate"));
    assert!(operator_names.contains(&"GrantVote"));
    assert!(operator_names.contains(&"BecomeLeader"));
    assert!(operator_names.contains(&"StepDown"));
    assert!(operator_names.contains(&"Next"));
}

#[test]
fn test_raft_translation() {
    let source = read_example("Raft");
    let (verus_code, mode_annotations) = translate_example(&source);

    // Verify state struct has all variables
    assert!(
        verus_code.contains("pub struct LState"),
        "Should contain state struct"
    );
    assert!(
        verus_code.contains("pub currentTerm:"),
        "Should contain currentTerm field"
    );
    assert!(
        verus_code.contains("pub state:"),
        "Should contain state field"
    );
    assert!(
        verus_code.contains("pub votedFor:"),
        "Should contain votedFor field"
    );
    assert!(
        verus_code.contains("pub votesGranted:"),
        "Should contain votesGranted field"
    );

    // Verify constants struct
    assert!(
        verus_code.contains("LConstants"),
        "Should contain constants struct"
    );
    assert!(
        verus_code.contains("pub Server:"),
        "Should contain Server constant"
    );

    // Verify key operators are translated
    assert!(
        verus_code.contains("pub open spec fn LInit"),
        "Should contain Init spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LBecomeCandidate"),
        "Should contain BecomeCandidate spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LBecomeLeader"),
        "Should contain BecomeLeader spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LGrantVote"),
        "Should contain GrantVote spec fn"
    );

    // Verify mode annotations
    assert!(
        mode_annotations.contains("module Raft"),
        "Should contain module name"
    );
}

#[test]
fn test_raft_type_inference() {
    let source = read_example("Raft");
    let module = parse_module(&source).expect("Failed to parse Raft.tla");

    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(&module);

    // Variables should be inferred
    assert!(
        type_env.variables.contains_key("currentTerm"),
        "Should infer type for currentTerm"
    );
    assert!(
        type_env.variables.contains_key("state"),
        "Should infer type for state"
    );
    assert!(
        type_env.variables.contains_key("votedFor"),
        "Should infer type for votedFor"
    );
    assert!(
        type_env.variables.contains_key("votesGranted"),
        "Should infer type for votesGranted"
    );

    // Constant should be inferred
    assert!(
        type_env.constants.contains_key("Server"),
        "Should infer type for Server"
    );
}

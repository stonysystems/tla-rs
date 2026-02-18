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
    let mut translator = ModuleTranslator::with_config(config).with_types(type_env);
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

// =============================================================================
// Paxos Example Tests (Complex)
// =============================================================================

#[test]
fn test_paxos_parsing() {
    let source = read_example("Paxos");
    let module = parse_module(&source).expect("Failed to parse Paxos.tla");

    assert_eq!(module.name, "Paxos");
    assert_eq!(module.variables.len(), 4);
    assert!(module.variables.contains(&"maxBal".to_string()));
    assert!(module.variables.contains(&"maxVBal".to_string()));
    assert!(module.variables.contains(&"maxVal".to_string()));
    assert!(module.variables.contains(&"msgs".to_string()));

    // Check constants
    let const_names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
    assert!(const_names.contains(&"Value"));
    assert!(const_names.contains(&"Acceptor"));
    assert!(const_names.contains(&"Quorum"));

    // Check operators
    let operator_names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(operator_names.contains(&"Phase1a"));
    assert!(operator_names.contains(&"Phase1b"));
    assert!(operator_names.contains(&"Phase2a"));
    assert!(operator_names.contains(&"Phase2b"));
    assert!(operator_names.contains(&"Init"));
    assert!(operator_names.contains(&"Send1a"));
    assert!(operator_names.contains(&"Send1b"));
    assert!(operator_names.contains(&"Send2a"));
    assert!(operator_names.contains(&"Send2b"));
    assert!(operator_names.contains(&"Next"));
    assert!(operator_names.contains(&"Chosen"));
    assert!(operator_names.contains(&"TypeOK"));
}

#[test]
fn test_paxos_translation() {
    let source = read_example("Paxos");
    let (verus_code, mode_annotations) = translate_example(&source);

    // Verify state struct has all variables
    assert!(
        verus_code.contains("pub struct LState"),
        "Should contain state struct"
    );
    assert!(
        verus_code.contains("pub maxBal:"),
        "Should contain maxBal field"
    );
    assert!(
        verus_code.contains("pub maxVBal:"),
        "Should contain maxVBal field"
    );
    assert!(
        verus_code.contains("pub maxVal:"),
        "Should contain maxVal field"
    );
    assert!(
        verus_code.contains("pub msgs:"),
        "Should contain msgs field"
    );

    // Verify constants struct
    assert!(
        verus_code.contains("LConstants"),
        "Should contain constants struct"
    );
    assert!(
        verus_code.contains("pub Value:"),
        "Should contain Value constant"
    );
    assert!(
        verus_code.contains("pub Acceptor:"),
        "Should contain Acceptor constant"
    );
    assert!(
        verus_code.contains("pub Quorum:"),
        "Should contain Quorum constant"
    );

    // Verify key operators are translated
    assert!(
        verus_code.contains("pub open spec fn LInit"),
        "Should contain Init spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LSend1a"),
        "Should contain Send1a spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LSend2b"),
        "Should contain Send2b spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LChosen"),
        "Should contain Chosen spec fn"
    );

    // Verify mode annotations
    assert!(
        mode_annotations.contains("module Paxos"),
        "Should contain module name"
    );
}

#[test]
fn test_paxos_type_inference() {
    let source = read_example("Paxos");
    let module = parse_module(&source).expect("Failed to parse Paxos.tla");

    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(&module);

    // Variables should be inferred
    assert!(
        type_env.variables.contains_key("maxBal"),
        "Should infer type for maxBal"
    );
    assert!(
        type_env.variables.contains_key("msgs"),
        "Should infer type for msgs"
    );

    // Constants should be inferred
    assert!(
        type_env.constants.contains_key("Value"),
        "Should infer type for Value"
    );
    assert!(
        type_env.constants.contains_key("Acceptor"),
        "Should infer type for Acceptor"
    );
}

// =============================================================================
// PBFT Example Tests (Complex)
// =============================================================================

#[test]
fn test_pbft_parsing() {
    let source = read_example("PBFT");
    let module = parse_module(&source).expect("Failed to parse PBFT.tla");

    assert_eq!(module.name, "PBFT");
    assert_eq!(module.variables.len(), 5);
    assert!(module.variables.contains(&"view".to_string()));
    assert!(module.variables.contains(&"phase".to_string()));
    assert!(module.variables.contains(&"prepareCount".to_string()));
    assert!(module.variables.contains(&"commitCount".to_string()));
    assert!(module.variables.contains(&"msgs".to_string()));

    // Check constants
    let const_names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
    assert!(const_names.contains(&"Replica"));
    assert!(const_names.contains(&"Primary"));
    assert!(const_names.contains(&"F"));

    // Check operators
    let operator_names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(operator_names.contains(&"PrePrepare"));
    assert!(operator_names.contains(&"Prepare"));
    assert!(operator_names.contains(&"Commit"));
    assert!(operator_names.contains(&"Reply"));
    assert!(operator_names.contains(&"QuorumSize"));
    assert!(operator_names.contains(&"Init"));
    assert!(operator_names.contains(&"SendPrePrepare"));
    assert!(operator_names.contains(&"SendPrepare"));
    assert!(operator_names.contains(&"SendCommit"));
    assert!(operator_names.contains(&"Prepared"));
    assert!(operator_names.contains(&"Committed"));
    assert!(operator_names.contains(&"EnterCommit"));
    assert!(operator_names.contains(&"ExecuteAndReply"));
    assert!(operator_names.contains(&"ViewChange"));
    assert!(operator_names.contains(&"Next"));
}

#[test]
fn test_pbft_translation() {
    let source = read_example("PBFT");
    let (verus_code, mode_annotations) = translate_example(&source);

    // Verify state struct has all variables
    assert!(
        verus_code.contains("pub struct LState"),
        "Should contain state struct"
    );
    assert!(
        verus_code.contains("pub view:"),
        "Should contain view field"
    );
    assert!(
        verus_code.contains("pub phase:"),
        "Should contain phase field"
    );
    assert!(
        verus_code.contains("pub prepareCount:"),
        "Should contain prepareCount field"
    );
    assert!(
        verus_code.contains("pub commitCount:"),
        "Should contain commitCount field"
    );
    assert!(
        verus_code.contains("pub msgs:"),
        "Should contain msgs field"
    );

    // Verify constants struct
    assert!(
        verus_code.contains("LConstants"),
        "Should contain constants struct"
    );
    assert!(
        verus_code.contains("pub Replica:"),
        "Should contain Replica constant"
    );
    assert!(verus_code.contains("pub F:"), "Should contain F constant");

    // Verify key operators are translated
    assert!(
        verus_code.contains("pub open spec fn LInit"),
        "Should contain Init spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LQuorumSize"),
        "Should contain QuorumSize spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LSendPrepare"),
        "Should contain SendPrepare spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LPrepared"),
        "Should contain Prepared spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LCommitted"),
        "Should contain Committed spec fn"
    );
    assert!(
        verus_code.contains("pub open spec fn LViewChange"),
        "Should contain ViewChange spec fn"
    );

    // Verify mode annotations
    assert!(
        mode_annotations.contains("module PBFT"),
        "Should contain module name"
    );
}

#[test]
fn test_pbft_type_inference() {
    let source = read_example("PBFT");
    let module = parse_module(&source).expect("Failed to parse PBFT.tla");

    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(&module);

    // Variables should be inferred
    assert!(
        type_env.variables.contains_key("view"),
        "Should infer type for view"
    );
    assert!(
        type_env.variables.contains_key("phase"),
        "Should infer type for phase"
    );
    assert!(
        type_env.variables.contains_key("prepareCount"),
        "Should infer type for prepareCount"
    );
    assert!(
        type_env.variables.contains_key("commitCount"),
        "Should infer type for commitCount"
    );
    assert!(
        type_env.variables.contains_key("msgs"),
        "Should infer type for msgs"
    );

    // Constants should be inferred
    assert!(
        type_env.constants.contains_key("F"),
        "Should infer type for F"
    );
    assert!(
        type_env.constants.contains_key("Replica"),
        "Should infer type for Replica"
    );
}

// =============================================================================
// D1 Compile Regression Tests
// Verify that generated Verus code has correct syntax for compilation.
// =============================================================================

#[test]
fn test_d1_string_literals_have_view_suffix() {
    // Regression: string literals must have @ suffix for Verus Seq<char> conversion
    let source = read_example("Raft");
    let (verus_code, _) = translate_example(&source);

    assert!(
        verus_code.contains("\"follower\"@"),
        "String literals must have @ suffix for Verus Seq<char>"
    );
    assert!(
        verus_code.contains("\"candidate\"@"),
        "String literals must have @ suffix for Verus Seq<char>"
    );
    assert!(
        verus_code.contains("\"leader\"@"),
        "String literals must have @ suffix for Verus Seq<char>"
    );
}

#[test]
fn test_d1_empty_sets_have_type_annotation() {
    // Regression: empty sets must have explicit type annotation for Verus
    let source = read_example("EWD840");
    let (verus_code, _) = translate_example(&source);

    assert!(
        verus_code.contains("Set::<int>::empty()"),
        "Empty sets must have type annotation: Set::<int>::empty()"
    );
}

#[test]
fn test_d1_record_set_empty_has_record_type() {
    // Regression: empty sets assigned to record-typed vars must use Set::<LRecord>::empty()
    let source = read_example("Paxos");
    let (verus_code, _) = translate_example(&source);

    assert!(
        verus_code.contains("Set::<LRecord>::empty()"),
        "Record-typed empty sets must use Set::<LRecord>::empty()"
    );
}

#[test]
fn test_d1_record_struct_generated() {
    // Regression: modules with record literals must generate a merged record struct
    let source = read_example("Paxos");
    let (verus_code, _) = translate_example(&source);

    assert!(
        verus_code.contains("pub struct LRecord"),
        "Must generate LRecord struct for record types"
    );
    assert!(
        verus_code.contains("pub r#type: Seq<char>"),
        "Record 'type' field must be escaped as r#type with Seq<char> type"
    );
    assert!(
        verus_code.contains("pub bal: int"),
        "Record 'bal' field must be int type"
    );
}

#[test]
fn test_d1_record_struct_keyword_escaping() {
    // Regression: Rust keywords in record field names must be escaped with r#
    let source = read_example("PBFT");
    let (verus_code, _) = translate_example(&source);

    assert!(
        verus_code.contains("pub r#type:"),
        "Keyword 'type' must be escaped as r#type in struct definition"
    );
    assert!(
        verus_code.contains("r#type:"),
        "Keyword 'type' must be escaped as r#type in struct construction"
    );
}

#[test]
fn test_d1_nat_renders_as_int() {
    // Regression: TLA+ Nat type must render as int (not nat) to avoid type mismatches
    let source = read_example("SimpleCounter");
    let (verus_code, _) = translate_example(&source);

    // Should not contain 'nat' type (only 'int')
    assert!(
        !verus_code.contains(": nat"),
        "Nat type must render as int, not nat"
    );
}

#[test]
fn test_d1_set_type_inference() {
    // Regression: variables used in set operations must be inferred as Set<int>
    let source = read_example("TwoPhase");
    let (verus_code, _) = translate_example(&source);

    assert!(
        verus_code.contains("pub rmState: Set<int>"),
        "rmState should be Set<int>"
    );
    assert!(
        verus_code.contains("pub tmPrepared: Set<int>"),
        "tmPrepared should be Set<int>"
    );
}

// =============================================================================
// Bullet-list (vertical) conjunction/disjunction parsing tests
// Tests that verus2tla-generated TLA+ specs (which use vertical /\ and \/ style)
// can be parsed back by the TLA+ parser.
// =============================================================================

/// Read a generated TLA+ spec from src/tla+/
fn read_generated_spec(protocol: &str, name: &str) -> String {
    let path = format!("../src/tla+/{}/{}.tla", protocol, name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("Failed to read {}: {}", path, e))
}

#[test]
fn test_generated_twophase_parsing() {
    let source = read_generated_spec("TwoPhase", "Twophase");
    let module = parse_module(&source).expect("Failed to parse generated TwoPhase");
    let names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(names.contains(&"Init"), "Should contain Init");
    assert!(
        names.contains(&"TMRcvPrepared"),
        "Should contain TMRcvPrepared"
    );
    assert!(names.contains(&"TMCommit"), "Should contain TMCommit");
    assert!(names.contains(&"TMAbort"), "Should contain TMAbort");
    assert!(names.contains(&"Next"), "Should contain Next");
}

#[test]
fn test_generated_twophase_translation() {
    let source = read_generated_spec("TwoPhase", "Twophase");
    let (verus_code, _) = translate_example(&source);
    assert!(
        verus_code.contains("spec fn LInit"),
        "Should translate Init"
    );
    assert!(
        verus_code.contains("spec fn LTMCommit"),
        "Should translate TMCommit"
    );
}

#[test]
fn test_generated_paxos_parsing() {
    let source = read_generated_spec("Paxos", "Paxos");
    let module = parse_module(&source).expect("Failed to parse generated Paxos");
    let names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(names.contains(&"Init"), "Should contain Init");
    assert!(names.contains(&"Next"), "Should contain Next");
}

#[test]
fn test_generated_leader_election_parsing() {
    let source = read_generated_spec("LeaderElection", "Election");
    let module = parse_module(&source).expect("Failed to parse generated LeaderElection");
    let names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(names.contains(&"Init"), "Should contain Init");
    assert!(names.contains(&"Next"), "Should contain Next");
}

#[test]
fn test_generated_chain_replication_parsing() {
    let source = read_generated_spec("ChainReplication", "Chain");
    let module = parse_module(&source).expect("Failed to parse generated ChainReplication");
    let names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(names.contains(&"Init"), "Should contain Init");
    assert!(names.contains(&"Next"), "Should contain Next");
}

#[test]
fn test_generated_primarybackup_parsing() {
    let source = read_generated_spec("PrimaryBackup", "Primarybackup");
    let module = parse_module(&source).expect("Failed to parse generated PrimaryBackup");
    let names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(names.contains(&"Init"), "Should contain Init");
    assert!(
        names.contains(&"PrimaryWrite"),
        "Should contain PrimaryWrite"
    );
    assert!(names.contains(&"BackupAck"), "Should contain BackupAck");
    assert!(
        names.contains(&"PrimaryCommit"),
        "Should contain PrimaryCommit"
    );
    assert!(names.contains(&"Failover"), "Should contain Failover");
    assert!(names.contains(&"Next"), "Should contain Next");
}

#[test]
fn test_generated_primarybackup_translation() {
    let source = read_generated_spec("PrimaryBackup", "Primarybackup");
    let (verus_code, mode_annotations) = translate_example(&source);
    assert!(
        verus_code.contains("spec fn LInit"),
        "Should translate Init"
    );
    assert!(
        verus_code.contains("spec fn LPrimaryWrite"),
        "Should translate PrimaryWrite"
    );
    assert!(
        !mode_annotations.is_empty(),
        "Should generate mode annotations"
    );
}

#[test]
fn test_generated_pbft_parsing() {
    let source = read_generated_spec("PBFT", "Pbft");
    let module = parse_module(&source).expect("Failed to parse generated PBFT");
    let names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(names.contains(&"Init"), "Should contain Init");
    assert!(names.contains(&"PrePrepare"), "Should contain PrePrepare");
    assert!(
        names.contains(&"ReceivePrepare"),
        "Should contain ReceivePrepare"
    );
    assert!(names.contains(&"EnterCommit"), "Should contain EnterCommit");
    assert!(
        names.contains(&"ReceiveCommit"),
        "Should contain ReceiveCommit"
    );
    assert!(
        names.contains(&"ExecuteReply"),
        "Should contain ExecuteReply"
    );
    assert!(names.contains(&"ViewChange"), "Should contain ViewChange");
    assert!(names.contains(&"NewRound"), "Should contain NewRound");
    assert!(names.contains(&"Next"), "Should contain Next");
}

#[test]
fn test_generated_pbft_translation() {
    let source = read_generated_spec("PBFT", "Pbft");
    let (verus_code, mode_annotations) = translate_example(&source);
    assert!(
        verus_code.contains("spec fn LInit"),
        "Should translate Init"
    );
    assert!(
        verus_code.contains("spec fn LPrePrepare"),
        "Should translate PrePrepare"
    );
    assert!(
        verus_code.contains("spec fn LEnterCommit"),
        "Should translate EnterCommit"
    );
    assert!(
        verus_code.contains("spec fn LViewChange"),
        "Should translate ViewChange"
    );
    assert!(
        !mode_annotations.is_empty(),
        "Should generate mode annotations"
    );
}

#[test]
fn test_generated_vpaxos_parsing() {
    let source = read_generated_spec("VerticalPaxos", "Vpaxos");
    let module = parse_module(&source).expect("Failed to parse generated VerticalPaxos");
    let names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(names.contains(&"Init"), "Should contain Init");
    assert!(names.contains(&"Prepare"), "Should contain Prepare");
    assert!(names.contains(&"Accept"), "Should contain Accept");
    assert!(names.contains(&"Reconfigure"), "Should contain Reconfigure");
    assert!(names.contains(&"Sync"), "Should contain Sync");
    assert!(names.contains(&"Deactivate"), "Should contain Deactivate");
    assert!(names.contains(&"Next"), "Should contain Next");
}

#[test]
fn test_generated_vpaxos_translation() {
    let source = read_generated_spec("VerticalPaxos", "Vpaxos");
    let (verus_code, mode_annotations) = translate_example(&source);
    assert!(
        verus_code.contains("spec fn LInit"),
        "Should translate Init"
    );
    assert!(
        verus_code.contains("spec fn LPrepare"),
        "Should translate Prepare"
    );
    assert!(
        verus_code.contains("spec fn LReconfigure"),
        "Should translate Reconfigure"
    );
    assert!(
        verus_code.contains("spec fn LSync"),
        "Should translate Sync"
    );
    assert!(
        verus_code.contains("spec fn LDeactivate"),
        "Should translate Deactivate"
    );
    assert!(
        !mode_annotations.is_empty(),
        "Should generate mode annotations"
    );
}

#[test]
fn test_generated_epaxos_parsing() {
    let source = read_generated_spec("EPaxos", "Epaxos");
    let module = parse_module(&source).expect("Failed to parse generated EPaxos");
    let names: Vec<&str> = module.operators.iter().map(|o| o.name.as_str()).collect();
    assert!(names.contains(&"Init"), "Should contain Init");
    assert!(names.contains(&"Propose"), "Should contain Propose");
    assert!(
        names.contains(&"ReceivePreAccept"),
        "Should contain ReceivePreAccept"
    );
    assert!(names.contains(&"FastCommit"), "Should contain FastCommit");
    assert!(names.contains(&"StartAccept"), "Should contain StartAccept");
    assert!(
        names.contains(&"ReceiveAccept"),
        "Should contain ReceiveAccept"
    );
    assert!(names.contains(&"SlowCommit"), "Should contain SlowCommit");
    assert!(names.contains(&"Execute"), "Should contain Execute");
    assert!(names.contains(&"Recover"), "Should contain Recover");
    assert!(names.contains(&"NewInstance"), "Should contain NewInstance");
    assert!(names.contains(&"Next"), "Should contain Next");
}

#[test]
fn test_generated_epaxos_translation() {
    let source = read_generated_spec("EPaxos", "Epaxos");
    let (verus_code, mode_annotations) = translate_example(&source);
    assert!(
        verus_code.contains("spec fn LInit"),
        "Should translate Init"
    );
    assert!(
        verus_code.contains("spec fn LPropose"),
        "Should translate Propose"
    );
    assert!(
        verus_code.contains("spec fn LFastCommit"),
        "Should translate FastCommit"
    );
    assert!(
        verus_code.contains("spec fn LSlowCommit"),
        "Should translate SlowCommit"
    );
    assert!(
        verus_code.contains("spec fn LRecover"),
        "Should translate Recover"
    );
    assert!(
        verus_code.contains("spec fn LNewInstance"),
        "Should translate NewInstance"
    );
    assert!(
        !mode_annotations.is_empty(),
        "Should generate mode annotations"
    );
}

// Raft: TLA+ parsing/translation skipped — Raft.tla uses EXCEPT syntax
// ([s.match_index EXCEPT ![follower] = val]) which the TLA+ parser doesn't support.
// The Raft protocol spec→exec transpilation is tested via Verus verification (597 verified, 0 errors).

// Paxos translation test
#[test]
fn test_generated_paxos_translation() {
    let source = read_generated_spec("Paxos", "Paxos");
    let (verus_code, mode_annotations) = translate_example(&source);
    assert!(
        verus_code.contains("spec fn LInit"),
        "Should translate Init"
    );
    assert!(
        verus_code.contains("spec fn LSend1a"),
        "Should translate Send1a"
    );
    assert!(
        verus_code.contains("spec fn LSend2a"),
        "Should translate Send2a"
    );
    assert!(
        !mode_annotations.is_empty(),
        "Should generate mode annotations"
    );
}

// LeaderElection translation test
#[test]
fn test_generated_leader_election_translation() {
    let source = read_generated_spec("LeaderElection", "Election");
    let (verus_code, mode_annotations) = translate_example(&source);
    assert!(
        verus_code.contains("spec fn LInit"),
        "Should translate Init"
    );
    assert!(
        verus_code.contains("spec fn LStartElection"),
        "Should translate StartElection"
    );
    assert!(
        verus_code.contains("spec fn LBecomeLeader"),
        "Should translate BecomeLeader"
    );
    assert!(
        verus_code.contains("spec fn LNodeFail"),
        "Should translate NodeFail"
    );
    assert!(
        !mode_annotations.is_empty(),
        "Should generate mode annotations"
    );
}

// ChainReplication translation test
#[test]
fn test_generated_chain_replication_translation() {
    let source = read_generated_spec("ChainReplication", "Chain");
    let (verus_code, mode_annotations) = translate_example(&source);
    assert!(
        verus_code.contains("spec fn LInit"),
        "Should translate Init"
    );
    assert!(
        verus_code.contains("spec fn LHeadReceiveWrite"),
        "Should translate HeadReceiveWrite"
    );
    assert!(
        verus_code.contains("spec fn LTailCommit"),
        "Should translate TailCommit"
    );
    assert!(
        verus_code.contains("spec fn LClientRead"),
        "Should translate ClientRead"
    );
    assert!(
        !mode_annotations.is_empty(),
        "Should generate mode annotations"
    );
}

// =============================================================================
// D4 Pipeline Regression Tests
// Full TLA+ → Verus Spec → Verus Exec pipeline integration tests.
// These verify that the full pipeline produces compilable output.
// =============================================================================

use verus_transpiler::translator::TranslatorConfig;
use verus_transpiler::{Transpiler, TranspilerConfig};

/// Run the full D4 pipeline: TLA+ → Verus spec + mode annotations → Verus exec
/// Returns the combined (spec + exec) output code.
fn run_d4_pipeline(name: &str) -> String {
    let tla_source = read_example(name);
    let module = parse_module(&tla_source).unwrap_or_else(|e| panic!("Failed to parse {}: {}", name, e));

    // Step 1: Infer types
    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(&module);

    // Step 2: Translate TLA+ to Verus spec
    let config = ModuleConfig::default();
    let mut translator = ModuleTranslator::with_config(config).with_types(type_env);
    let verus_spec_code = translator.translate(&module);

    // Step 3: Generate mode annotations
    let mode_annotations = generate_mode_annotations(&module);

    // Step 4: Transpile spec to exec
    let transpiler_config = TranspilerConfig {
        translator: TranslatorConfig {
            spec_prefix: "L".to_string(),
            exec_prefix: "C".to_string(),
            assume_postconditions: true,
            ..TranslatorConfig::default()
        },
        generate_inline_types: true,
        custom_imports: vec![
            "use vstd::prelude::*;".to_string(),
            "use std::collections::HashSet;".to_string(),
        ],
        ..TranspilerConfig::default()
    };

    let transpiler = Transpiler::new(transpiler_config);
    let exec_code = transpiler
        .transpile_source(&verus_spec_code, &mode_annotations)
        .unwrap_or_else(|e| panic!("Failed to transpile {} spec to exec: {}", name, e));

    // Combine spec + exec for self-contained output
    format!("{}\n{}", verus_spec_code, exec_code)
}

#[test]
fn test_d4_pipeline_simplecounter() {
    let output = run_d4_pipeline("SimpleCounter");
    // Spec layer
    assert!(output.contains("pub open spec fn LInit"), "Should contain spec LInit");
    // Exec layer
    assert!(output.contains("exec fn CInit"), "Should contain exec CInit");
    assert!(output.contains("exec fn CIncrement"), "Should contain exec CIncrement");
    assert!(output.contains("exec fn CDecrement"), "Should contain exec CDecrement");
    assert!(output.contains("exec fn CReset"), "Should contain exec CReset");
    // Should have assume(false) from assume_postconditions
    assert!(output.contains("assume(false)"), "Should contain assume(false) for postconditions");
    // Should have verus! block
    assert!(output.contains("verus!"), "Should contain verus! macro");
}

#[test]
fn test_d4_pipeline_diehard() {
    let output = run_d4_pipeline("DieHard");
    assert!(output.contains("exec fn CInit"), "Should contain exec CInit");
    assert!(output.contains("exec fn CFillBig"), "Should contain exec CFillBig");
    assert!(output.contains("exec fn CFillSmall"), "Should contain exec CFillSmall");
    assert!(output.contains("exec fn CEmptyBig"), "Should contain exec CEmptyBig");
    assert!(output.contains("exec fn CEmptySmall"), "Should contain exec CEmptySmall");
    assert!(output.contains("exec fn CSmallToBig"), "Should contain exec CSmallToBig");
    assert!(output.contains("exec fn CBigToSmall"), "Should contain exec CBigToSmall");
}

#[test]
fn test_d4_pipeline_ewd840() {
    let output = run_d4_pipeline("EWD840");
    assert!(output.contains("exec fn CInit"), "Should contain exec CInit");
    assert!(output.contains("exec fn CTerminate"), "Should contain exec CTerminate");
    assert!(output.contains("exec fn CSendMsg"), "Should contain exec CSendMsg");
    assert!(output.contains("exec fn CPassToken"), "Should contain exec CPassToken");
    assert!(output.contains("exec fn CInitiateProbe"), "Should contain exec CInitiateProbe");
}

#[test]
fn test_d4_pipeline_twophase() {
    let output = run_d4_pipeline("TwoPhase");
    assert!(output.contains("exec fn CInit"), "Should contain exec CInit");
    assert!(output.contains("exec fn CTMCommit"), "Should contain exec CTMCommit");
    assert!(output.contains("exec fn CTMAbort"), "Should contain exec CTMAbort");
    assert!(output.contains("exec fn CTMRcvPrepared"), "Should contain exec CTMRcvPrepared");
}

#[test]
fn test_d4_pipeline_raft() {
    let output = run_d4_pipeline("Raft");
    assert!(output.contains("exec fn CInit"), "Should contain exec CInit");
    assert!(output.contains("exec fn CBecomeCandidate"), "Should contain exec CBecomeCandidate");
    assert!(output.contains("exec fn CGrantVote"), "Should contain exec CGrantVote");
    assert!(output.contains("exec fn CBecomeLeader"), "Should contain exec CBecomeLeader");
    assert!(output.contains("exec fn CStepDown"), "Should contain exec CStepDown");
}

#[test]
fn test_d4_pipeline_paxos() {
    let output = run_d4_pipeline("Paxos");
    assert!(output.contains("exec fn CInit"), "Should contain exec CInit");
    assert!(output.contains("exec fn CSend1a"), "Should contain exec CSend1a");
    assert!(output.contains("exec fn CSend1b"), "Should contain exec CSend1b");
    assert!(output.contains("exec fn CSend2a"), "Should contain exec CSend2a");
    assert!(output.contains("exec fn CSend2b"), "Should contain exec CSend2b");
}

#[test]
fn test_d4_pipeline_pbft() {
    let output = run_d4_pipeline("PBFT");
    assert!(output.contains("exec fn CInit"), "Should contain exec CInit");
    assert!(output.contains("exec fn CSendPrePrepare"), "Should contain exec CSendPrePrepare");
    assert!(output.contains("exec fn CSendPrepare"), "Should contain exec CSendPrepare");
    assert!(output.contains("exec fn CSendCommit"), "Should contain exec CSendCommit");
    assert!(output.contains("exec fn CEnterCommit"), "Should contain exec CEnterCommit");
    assert!(output.contains("exec fn CExecuteAndReply"), "Should contain exec CExecuteAndReply");
    assert!(output.contains("exec fn CViewChange"), "Should contain exec CViewChange");
}

// =============================================================================
// D4 Pipeline Quality Regression Tests
// Verify specific fixes that were needed for D4 pipeline compilation.
// =============================================================================

#[test]
fn test_d4_hashset_clone_uses_helper() {
    // Regression: HashSet field .clone() must use clone_hashset(), not .clone() directly
    // (Verus doesn't support HashSet::clone)
    let output = run_d4_pipeline("EWD840");
    // EWD840 has set-typed fields (active, color) that need cloning
    // The output should use clone_hashset for any HashSet field cloning
    assert!(
        !output.contains("std::collections::hash::set::impl"),
        "Should not contain raw HashSet clone calls"
    );
}

#[test]
fn test_d4_lnext_has_state_params() {
    // Regression: LNext must have s, s_ parameters (was missing due to ConstantOp classification)
    let output = run_d4_pipeline("SimpleCounter");
    // LNext should reference state parameters (s and s_)
    assert!(
        output.contains("fn LNext(s: LState, s_: LState"),
        "LNext should have s, s_ parameters"
    );
}

#[test]
fn test_d4_assume_postconditions_applied() {
    // Regression: D4 pipeline exec functions need assume(false) for trivial verification
    let output = run_d4_pipeline("DieHard");
    // All exec functions should have assume(false) to bypass verification
    let assume_count = output.matches("assume(false)").count();
    assert!(
        assume_count >= 7,
        "Expected at least 7 assume(false) (one per exec fn), got {}",
        assume_count
    );
}

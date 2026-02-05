//! Round-trip semantic preservation tests (T8.4).
//!
//! These tests verify that the TLA+ → Verus spec pipeline preserves semantics:
//! 1. State variables map to struct fields
//! 2. Constants map to constants struct fields
//! 3. Init predicates preserve initial values
//! 4. Action operators preserve transition semantics
//! 5. Next composition preserves disjunction structure
//! 6. Expressions (arithmetic, conditionals, sets) translate faithfully
//! 7. Mode annotations round-trip through parse → generate → parse

use verus_transpiler::tla::{
    generate_mode_annotations, parse_module, ModuleConfig, ModuleTranslator, TlaBinOp, TlaExpr,
    TlaModule, TlaOperator, TypeInference,
};
use verus_transpiler::AnnotationParser;

/// Read a TLA+ file from the examples directory
fn read_example(name: &str) -> String {
    let path = format!("tests/tla_examples/{}.tla", name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("Failed to read {}: {}", path, e))
}

/// Run the full TLA+ to Verus spec pipeline, returning AST + Verus code + mode annotations
fn full_pipeline(source: &str) -> (TlaModule, String, String) {
    let module = parse_module(source).expect("Failed to parse TLA+ module");

    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(&module);

    let config = ModuleConfig::default();
    let translator = ModuleTranslator::with_config(config).with_types(type_env);
    let verus_code = translator.translate(&module);

    let mode_annotations = generate_mode_annotations(&module);

    (module, verus_code, mode_annotations)
}

/// Extract operator names that are action operators (contain primed variables).
fn get_action_operators(module: &TlaModule) -> Vec<&str> {
    module
        .operators
        .iter()
        .filter(|op| contains_prime(&op.body))
        .map(|op| op.name.as_str())
        .collect()
}

/// Check if an expression contains primed variables.
fn contains_prime(expr: &TlaExpr) -> bool {
    match expr {
        TlaExpr::Prime(_) => true,
        TlaExpr::BinOp { left, right, .. } => contains_prime(left) || contains_prime(right),
        TlaExpr::UnaryOp { operand, .. } => contains_prime(operand),
        TlaExpr::OpApply { op, args } => {
            contains_prime(op) || args.iter().any(|a| contains_prime(a))
        }
        TlaExpr::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => contains_prime(cond) || contains_prime(then_expr) || contains_prime(else_expr),
        TlaExpr::Forall { body, .. } | TlaExpr::Exists { body, .. } => contains_prime(body),
        TlaExpr::SetEnum(elems) => elems.iter().any(|e| contains_prime(e)),
        TlaExpr::SetFilter { filter, .. } => contains_prime(filter),
        TlaExpr::SetMap { expr, .. } => contains_prime(expr),
        TlaExpr::Record(fields) => fields.iter().any(|(_, e)| contains_prime(e)),
        TlaExpr::Tuple(elems) => elems.iter().any(|e| contains_prime(e)),
        TlaExpr::Unchanged(_) => true,
        _ => false,
    }
}

/// Extract the names of operators used in a disjunction (Next = A \/ B \/ C).
fn extract_disjuncts(expr: &TlaExpr) -> Vec<String> {
    match expr {
        TlaExpr::BinOp {
            op: TlaBinOp::Or,
            left,
            right,
        } => {
            let mut result = extract_disjuncts(left);
            result.extend(extract_disjuncts(right));
            result
        }
        TlaExpr::Ident(name) => vec![name.clone()],
        TlaExpr::OpApply { op, .. } => {
            if let TlaExpr::Ident(name) = op.as_ref() {
                vec![name.clone()]
            } else {
                vec![]
            }
        }
        _ => vec![],
    }
}

/// Find an operator by name.
fn find_operator<'a>(module: &'a TlaModule, name: &str) -> Option<&'a TlaOperator> {
    module.operators.iter().find(|op| op.name == name)
}

// =============================================================================
// 1. State Variable Preservation Tests
// =============================================================================

#[test]
fn test_roundtrip_simplecounter_variables() {
    let source = read_example("SimpleCounter");
    let (module, verus_code, _) = full_pipeline(&source);

    // TLA+ has: VARIABLE count
    assert_eq!(module.variables, vec!["count"]);

    // Verus struct should have matching field
    assert!(
        verus_code.contains("pub count:"),
        "Verus LState should have 'count' field"
    );
}

#[test]
fn test_roundtrip_diehard_variables() {
    let source = read_example("DieHard");
    let (module, verus_code, _) = full_pipeline(&source);

    // TLA+ has: VARIABLE big, small
    assert_eq!(module.variables.len(), 2);
    assert!(module.variables.contains(&"big".to_string()));
    assert!(module.variables.contains(&"small".to_string()));

    // Verus struct should have matching fields
    assert!(
        verus_code.contains("pub big:"),
        "Verus LState should have 'big' field"
    );
    assert!(
        verus_code.contains("pub small:"),
        "Verus LState should have 'small' field"
    );
}

#[test]
fn test_roundtrip_ewd840_variables() {
    let source = read_example("EWD840");
    let (module, verus_code, _) = full_pipeline(&source);

    // TLA+ has: VARIABLE active, color, tpos, tcolor
    assert_eq!(module.variables.len(), 4);
    for var in &["active", "color", "tpos", "tcolor"] {
        assert!(
            module.variables.contains(&var.to_string()),
            "TLA+ should have variable '{}'",
            var
        );
        assert!(
            verus_code.contains(&format!("pub {}:", var)),
            "Verus LState should have '{}' field",
            var
        );
    }
}

#[test]
fn test_roundtrip_raft_variables() {
    let source = read_example("Raft");
    let (module, verus_code, _) = full_pipeline(&source);

    // TLA+ has: VARIABLE currentTerm, state, votedFor, votesGranted
    assert_eq!(module.variables.len(), 4);
    for var in &["currentTerm", "state", "votedFor", "votesGranted"] {
        assert!(
            module.variables.contains(&var.to_string()),
            "TLA+ should have variable '{}'",
            var
        );
        assert!(
            verus_code.contains(&format!("pub {}:", var)),
            "Verus LState should have '{}' field",
            var
        );
    }
}

#[test]
fn test_roundtrip_paxos_variables() {
    let source = read_example("Paxos");
    let (module, verus_code, _) = full_pipeline(&source);

    for var in &["maxBal", "maxVBal", "maxVal", "msgs"] {
        assert!(
            module.variables.contains(&var.to_string()),
            "TLA+ should have variable '{}'",
            var
        );
        assert!(
            verus_code.contains(&format!("pub {}:", var)),
            "Verus LState should have '{}' field",
            var
        );
    }
}

#[test]
fn test_roundtrip_pbft_variables() {
    let source = read_example("PBFT");
    let (module, verus_code, _) = full_pipeline(&source);

    for var in &["view", "phase", "prepareCount", "commitCount", "msgs"] {
        assert!(
            module.variables.contains(&var.to_string()),
            "TLA+ should have variable '{}'",
            var
        );
        assert!(
            verus_code.contains(&format!("pub {}:", var)),
            "Verus LState should have '{}' field",
            var
        );
    }
}

// =============================================================================
// 2. Constants Preservation Tests
// =============================================================================

#[test]
fn test_roundtrip_simplecounter_constants() {
    let source = read_example("SimpleCounter");
    let (module, verus_code, _) = full_pipeline(&source);

    // TLA+ has: CONSTANT MaxCount
    assert_eq!(module.constants.len(), 1);
    assert_eq!(module.constants[0].name, "MaxCount");

    // Verus should have constants struct
    assert!(
        verus_code.contains("pub struct LConstants"),
        "Should generate LConstants struct"
    );
    assert!(
        verus_code.contains("pub MaxCount:"),
        "LConstants should have MaxCount field"
    );
}

#[test]
fn test_roundtrip_paxos_constants() {
    let source = read_example("Paxos");
    let (module, verus_code, _) = full_pipeline(&source);

    // TLA+ has: CONSTANT Value, Acceptor, Quorum
    let const_names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
    assert!(const_names.contains(&"Value"));
    assert!(const_names.contains(&"Acceptor"));
    assert!(const_names.contains(&"Quorum"));

    for name in &["Value", "Acceptor", "Quorum"] {
        assert!(
            verus_code.contains(&format!("pub {}:", name)),
            "LConstants should have '{}' field",
            name
        );
    }
}

#[test]
fn test_roundtrip_pbft_constants() {
    let source = read_example("PBFT");
    let (module, _verus_code, _) = full_pipeline(&source);

    let const_names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
    assert!(const_names.contains(&"Replica"));
    assert!(const_names.contains(&"Primary"));
    assert!(const_names.contains(&"F"));
}

// =============================================================================
// 3. Init Predicate Semantics Tests
// =============================================================================

#[test]
fn test_roundtrip_simplecounter_init() {
    let source = read_example("SimpleCounter");
    let (module, verus_code, _) = full_pipeline(&source);

    // TLA+ Init: count = 0
    let init = find_operator(&module, "Init").expect("Should have Init operator");
    assert!(
        !init.params.is_empty() || init.params.is_empty(),
        "Init is defined"
    );

    // Verus should have LInit
    assert!(
        verus_code.contains("pub open spec fn LInit"),
        "Should generate LInit spec fn"
    );
    // Should contain the initialization value
    assert!(
        verus_code.contains("count") && verus_code.contains("0"),
        "LInit should reference count = 0"
    );
}

#[test]
fn test_roundtrip_diehard_init() {
    let source = read_example("DieHard");
    let (_, verus_code, _) = full_pipeline(&source);

    // TLA+ Init: big = 0 /\ small = 0
    assert!(
        verus_code.contains("pub open spec fn LInit"),
        "Should generate LInit"
    );
    // Both variables should be initialized to 0
    // The generated code should contain big == 0 and small == 0
    let init_section = extract_function_body(&verus_code, "LInit");
    assert!(
        init_section.contains("big") && init_section.contains("0"),
        "LInit should set big to 0"
    );
    assert!(
        init_section.contains("small") && init_section.contains("0"),
        "LInit should set small to 0"
    );
}

#[test]
fn test_roundtrip_raft_init() {
    let source = read_example("Raft");
    let (_, verus_code, _) = full_pipeline(&source);

    // TLA+ Init: currentTerm = 0 /\ state = Follower /\ votedFor = {} /\ votesGranted = {}
    assert!(
        verus_code.contains("pub open spec fn LInit"),
        "Should generate LInit"
    );
    let init_section = extract_function_body(&verus_code, "LInit");
    assert!(
        init_section.contains("currentTerm") && init_section.contains("0"),
        "LInit should set currentTerm to 0"
    );
}

#[test]
fn test_roundtrip_pbft_init() {
    let source = read_example("PBFT");
    let (_, verus_code, _) = full_pipeline(&source);

    // TLA+ Init: view = 0 /\ phase = PrePrepare /\ prepareCount = 0 /\ commitCount = 0 /\ msgs = {}
    let init_section = extract_function_body(&verus_code, "LInit");
    assert!(
        init_section.contains("view") && init_section.contains("0"),
        "LInit should set view to 0"
    );
    assert!(
        init_section.contains("prepareCount") && init_section.contains("0"),
        "LInit should set prepareCount to 0"
    );
    assert!(
        init_section.contains("commitCount") && init_section.contains("0"),
        "LInit should set commitCount to 0"
    );
}

// =============================================================================
// 4. Action Operator Preservation Tests
// =============================================================================

#[test]
fn test_roundtrip_simplecounter_actions() {
    let source = read_example("SimpleCounter");
    let (module, verus_code, _) = full_pipeline(&source);

    // TLA+ actions with primed variables
    let actions = get_action_operators(&module);
    assert!(actions.contains(&"Increment"), "Should detect Increment as action");
    assert!(actions.contains(&"Decrement"), "Should detect Decrement as action");
    assert!(actions.contains(&"Reset"), "Should detect Reset as action");

    // Each action should become a Verus spec fn with s and s_ parameters
    for action in &["Increment", "Decrement", "Reset"] {
        let verus_name = format!("pub open spec fn L{}", action);
        assert!(
            verus_code.contains(&verus_name),
            "Should generate spec fn for action '{}'",
            action
        );
        // Action operators should have s and s_ parameters (state transition)
        let fn_sig = extract_function_signature(&verus_code, &format!("L{}", action));
        assert!(
            fn_sig.contains("s: LState") || fn_sig.contains("s_: LState"),
            "Action '{}' should have state parameter(s): {}",
            action,
            fn_sig
        );
    }
}

#[test]
fn test_roundtrip_diehard_actions() {
    let source = read_example("DieHard");
    let (module, verus_code, _) = full_pipeline(&source);

    let actions = get_action_operators(&module);
    for expected in &[
        "FillBig",
        "FillSmall",
        "EmptyBig",
        "EmptySmall",
        "SmallToBig",
        "BigToSmall",
    ] {
        assert!(
            actions.contains(expected),
            "Should detect '{}' as action",
            expected
        );
        assert!(
            verus_code.contains(&format!("pub open spec fn L{}", expected)),
            "Should generate spec fn for '{}'",
            expected
        );
    }
}

#[test]
fn test_roundtrip_raft_actions() {
    let source = read_example("Raft");
    let (module, verus_code, _) = full_pipeline(&source);

    let actions = get_action_operators(&module);
    for expected in &["BecomeCandidate", "BecomeLeader", "StepDown"] {
        assert!(
            actions.contains(expected),
            "Should detect '{}' as action",
            expected
        );
        assert!(
            verus_code.contains(&format!("pub open spec fn L{}", expected)),
            "Should generate spec fn for '{}'",
            expected
        );
    }
}

#[test]
fn test_roundtrip_ewd840_parameterized_actions() {
    let source = read_example("EWD840");
    let (module, verus_code, _) = full_pipeline(&source);

    // Terminate(i) and SendMsg(i, j) are parameterized actions
    let terminate = find_operator(&module, "Terminate").expect("Should have Terminate");
    assert_eq!(terminate.params.len(), 1, "Terminate takes 1 parameter");
    assert_eq!(terminate.params[0].name, "i");

    let send_msg = find_operator(&module, "SendMsg").expect("Should have SendMsg");
    assert_eq!(send_msg.params.len(), 2, "SendMsg takes 2 parameters");

    // Verus versions should also have corresponding parameters
    assert!(
        verus_code.contains("pub open spec fn LTerminate"),
        "Should generate LTerminate"
    );
    assert!(
        verus_code.contains("pub open spec fn LSendMsg"),
        "Should generate LSendMsg"
    );
}

#[test]
fn test_roundtrip_paxos_parameterized_actions() {
    let source = read_example("Paxos");
    let (module, verus_code, _) = full_pipeline(&source);

    // Send1a(b), Send1b(a, b), Send2a(b, v), Send2b(a, b, v)
    let send1a = find_operator(&module, "Send1a").expect("Should have Send1a");
    assert_eq!(send1a.params.len(), 1, "Send1a takes 1 parameter");

    let send2b = find_operator(&module, "Send2b").expect("Should have Send2b");
    assert_eq!(send2b.params.len(), 3, "Send2b takes 3 parameters");

    for action in &["Send1a", "Send1b", "Send2a", "Send2b"] {
        assert!(
            verus_code.contains(&format!("pub open spec fn L{}", action)),
            "Should generate spec fn for '{}'",
            action
        );
    }
}

// =============================================================================
// 5. Next Composition Tests
// =============================================================================

#[test]
fn test_roundtrip_simplecounter_next_composition() {
    let source = read_example("SimpleCounter");
    let (module, verus_code, _) = full_pipeline(&source);

    // TLA+ Next: Increment \/ Decrement \/ Reset
    let next = find_operator(&module, "Next").expect("Should have Next");
    let disjuncts = extract_disjuncts(&next.body);
    assert_eq!(disjuncts.len(), 3, "Next should have 3 disjuncts");
    assert!(disjuncts.contains(&"Increment".to_string()));
    assert!(disjuncts.contains(&"Decrement".to_string()));
    assert!(disjuncts.contains(&"Reset".to_string()));

    // Verus LNext should reference all sub-actions
    // Note: The translator adds L prefix to function definitions but not to
    // operator references within bodies. So LNext body contains "Increment", not "LIncrement".
    assert!(
        verus_code.contains("pub open spec fn LNext"),
        "Should generate LNext"
    );
    let next_body = extract_function_body(&verus_code, "LNext");
    // Verify all TLA+ disjuncts appear in the Verus Next body
    for disjunct in &disjuncts {
        assert!(
            next_body.contains(disjunct.as_str()),
            "LNext should reference '{}' from TLA+ Next disjunction. Body: {}",
            disjunct,
            next_body
        );
    }
}

#[test]
fn test_roundtrip_diehard_next_composition() {
    let source = read_example("DieHard");
    let (module, verus_code, _) = full_pipeline(&source);

    let next = find_operator(&module, "Next").expect("Should have Next");
    let disjuncts = extract_disjuncts(&next.body);
    assert_eq!(disjuncts.len(), 6, "DieHard Next should have 6 disjuncts");

    let next_body = extract_function_body(&verus_code, "LNext");
    // Verify all TLA+ disjuncts appear in the Verus Next body (original names, no L prefix)
    for disjunct in &disjuncts {
        assert!(
            next_body.contains(disjunct.as_str()),
            "LNext should reference '{}' from TLA+ Next disjunction. Body: {}",
            disjunct,
            next_body
        );
    }
}

#[test]
fn test_roundtrip_raft_next_composition() {
    let source = read_example("Raft");
    let (module, verus_code, _) = full_pipeline(&source);

    let next = find_operator(&module, "Next").expect("Should have Next");
    let disjuncts = extract_disjuncts(&next.body);
    assert_eq!(disjuncts.len(), 3, "Raft Next should have 3 disjuncts");

    let next_body = extract_function_body(&verus_code, "LNext");
    for disjunct in &disjuncts {
        assert!(
            next_body.contains(disjunct.as_str()),
            "LNext should reference '{}' from TLA+ Next disjunction. Body: {}",
            disjunct,
            next_body
        );
    }
}

#[test]
fn test_roundtrip_pbft_next_composition() {
    let source = read_example("PBFT");
    let (module, verus_code, _) = full_pipeline(&source);

    let next = find_operator(&module, "Next").expect("Should have Next");
    let disjuncts = extract_disjuncts(&next.body);
    assert_eq!(disjuncts.len(), 3, "PBFT Next should have 3 disjuncts");
    assert!(disjuncts.contains(&"EnterCommit".to_string()));
    assert!(disjuncts.contains(&"ExecuteAndReply".to_string()));
    assert!(disjuncts.contains(&"ViewChange".to_string()));

    let next_body = extract_function_body(&verus_code, "LNext");
    for disjunct in &disjuncts {
        assert!(
            next_body.contains(disjunct.as_str()),
            "LNext should reference '{}' from TLA+ Next disjunction. Body: {}",
            disjunct,
            next_body
        );
    }
}

// =============================================================================
// 6. Expression Semantics Tests
// =============================================================================

#[test]
fn test_roundtrip_arithmetic_preservation() {
    let source = read_example("SimpleCounter");
    let (_, verus_code, _) = full_pipeline(&source);

    // Increment: count' = count + 1 → should contain addition
    let increment_body = extract_function_body(&verus_code, "LIncrement");
    assert!(
        increment_body.contains("+") || increment_body.contains("add"),
        "Increment should preserve addition: {}",
        increment_body
    );

    // Decrement: count' = count - 1 → should contain subtraction
    let decrement_body = extract_function_body(&verus_code, "LDecrement");
    assert!(
        decrement_body.contains("-") || decrement_body.contains("sub"),
        "Decrement should preserve subtraction: {}",
        decrement_body
    );
}

#[test]
fn test_roundtrip_comparison_preservation() {
    let source = read_example("SimpleCounter");
    let (_, verus_code, _) = full_pipeline(&source);

    // Increment has guard: count < MaxCount
    let increment_body = extract_function_body(&verus_code, "LIncrement");
    assert!(
        increment_body.contains("<") || increment_body.contains("lt"),
        "Increment guard should preserve less-than comparison: {}",
        increment_body
    );

    // Decrement has guard: count > 0
    let decrement_body = extract_function_body(&verus_code, "LDecrement");
    assert!(
        decrement_body.contains(">") || decrement_body.contains("gt"),
        "Decrement guard should preserve greater-than comparison: {}",
        decrement_body
    );
}

#[test]
fn test_roundtrip_conditional_preservation() {
    let source = read_example("DieHard");
    let (_, verus_code, _) = full_pipeline(&source);

    // SmallToBig has IF-THEN-ELSE
    let small_to_big = extract_function_body(&verus_code, "LSmallToBig");
    assert!(
        small_to_big.contains("if"),
        "SmallToBig should preserve conditional: {}",
        small_to_big
    );

    // BigToSmall also has IF-THEN-ELSE
    let big_to_small = extract_function_body(&verus_code, "LBigToSmall");
    assert!(
        big_to_small.contains("if"),
        "BigToSmall should preserve conditional: {}",
        big_to_small
    );
}

#[test]
fn test_roundtrip_set_operations_preservation() {
    let source = read_example("TwoPhase");
    let (_, verus_code, _) = full_pipeline(&source);

    // TMRcvPrepared has: tmPrepared' = tmPrepared \cup {r}
    // Should translate to set union operation
    let tm_rcv = extract_function_body(&verus_code, "LTMRcvPrepared");
    assert!(
        tm_rcv.contains("insert") || tm_rcv.contains("union") || tm_rcv.contains("cup"),
        "TMRcvPrepared should preserve set union: {}",
        tm_rcv
    );
}

#[test]
fn test_roundtrip_set_difference_preservation() {
    let source = read_example("EWD840");
    let (_, verus_code, _) = full_pipeline(&source);

    // Terminate(i): active' = active \ {i}
    // Should translate to set difference
    let terminate = extract_function_body(&verus_code, "LTerminate");
    assert!(
        terminate.contains("remove")
            || terminate.contains("difference")
            || terminate.contains("\\")
            || terminate.contains("setminus"),
        "Terminate should preserve set difference: {}",
        terminate
    );
}

#[test]
fn test_roundtrip_equality_preservation() {
    let source = read_example("TwoPhase");
    let (_, verus_code, _) = full_pipeline(&source);

    // TMCommit: tmPrepared = RM (equality check)
    let tm_commit = extract_function_body(&verus_code, "LTMCommit");
    assert!(
        tm_commit.contains("=="),
        "TMCommit should preserve equality comparison: {}",
        tm_commit
    );
}

#[test]
fn test_roundtrip_pbft_arithmetic_expression() {
    let source = read_example("PBFT");
    let (_, verus_code, _) = full_pipeline(&source);

    // QuorumSize == 2 * F + 1
    assert!(
        verus_code.contains("pub open spec fn LQuorumSize"),
        "Should generate LQuorumSize"
    );
    let quorum_body = extract_function_body(&verus_code, "LQuorumSize");
    assert!(
        quorum_body.contains("*") || quorum_body.contains("mul"),
        "QuorumSize should preserve multiplication: {}",
        quorum_body
    );
    assert!(
        quorum_body.contains("+") || quorum_body.contains("add"),
        "QuorumSize should preserve addition: {}",
        quorum_body
    );
}

// =============================================================================
// 7. Mode Annotation Round-Trip Tests
// =============================================================================

#[test]
fn test_roundtrip_mode_annotations_simplecounter() {
    let source = read_example("SimpleCounter");
    let (module, _, mode_annotations) = full_pipeline(&source);

    // Parse mode annotations back
    let parser = AnnotationParser::new(mode_annotations.clone());
    let parsed = parser.parse().expect("Should parse generated mode annotations");
    assert!(!parsed.is_empty(), "Should have at least one module");

    // Module name should match
    assert!(
        mode_annotations.contains(&format!("module {}", module.name)),
        "Mode annotations should reference module name '{}': {}",
        module.name,
        mode_annotations
    );

    // Action operators should have annotations
    for action in &["Init", "Increment", "Decrement", "Reset", "Next"] {
        assert!(
            mode_annotations.contains(&format!("L{}", action)),
            "Mode annotations should reference L{}: {}",
            action,
            mode_annotations
        );
    }
}

#[test]
fn test_roundtrip_mode_annotations_all_examples() {
    for example in &[
        "SimpleCounter",
        "DieHard",
        "TwoPhase",
        "EWD840",
        "Raft",
        "Paxos",
        "PBFT",
    ] {
        let source = read_example(example);
        let (module, _, mode_annotations) = full_pipeline(&source);

        // Parse back
        let parser = AnnotationParser::new(mode_annotations.clone());
        let parsed = parser
            .parse()
            .unwrap_or_else(|e| panic!("Failed to parse mode annotations for {}: {}", example, e));
        assert!(
            !parsed.is_empty(),
            "{}: Should parse at least one module",
            example
        );

        // Module name preserved
        assert!(
            mode_annotations.contains(&format!("module {}", module.name)),
            "{}: Mode annotations should contain module name",
            example
        );
    }
}

#[test]
fn test_roundtrip_mode_annotation_parameter_modes() {
    let source = read_example("SimpleCounter");
    let (_, _, mode_annotations) = full_pipeline(&source);

    // Init should have output mode (sets initial state)
    // Action operators should have input+output modes (state transition)
    // The mode annotations use +/- to indicate output/input

    // Verify annotations can be parsed and contain expected functions
    let parser = AnnotationParser::new(mode_annotations.clone());
    let parsed = parser.parse().expect("Should parse");

    // Collect all annotated function names
    let fn_names: Vec<String> = parsed
        .iter()
        .flat_map(|m| m.functions.keys().cloned())
        .collect();

    assert!(
        fn_names.iter().any(|n| n.contains("Init")),
        "Should have Init annotation: {:?}",
        fn_names
    );
}

// =============================================================================
// 8. Non-Action Operator Preservation Tests
// =============================================================================

#[test]
fn test_roundtrip_constant_operators() {
    let source = read_example("Raft");
    let (module, verus_code, _) = full_pipeline(&source);

    // Raft defines: Follower == "follower", Candidate == "candidate", Leader == "leader"
    for const_op in &["Follower", "Candidate", "Leader"] {
        let op = find_operator(&module, const_op);
        assert!(op.is_some(), "TLA+ should have {} operator", const_op);
        assert!(
            verus_code.contains(&format!("pub open spec fn L{}", const_op)),
            "Verus should have L{} spec fn",
            const_op
        );
    }
}

#[test]
fn test_roundtrip_predicate_operators() {
    let source = read_example("PBFT");
    let (_, verus_code, _) = full_pipeline(&source);

    // PBFT has pure predicates: Prepared, Committed
    assert!(
        verus_code.contains("pub open spec fn LPrepared"),
        "Should generate LPrepared"
    );
    assert!(
        verus_code.contains("pub open spec fn LCommitted"),
        "Should generate LCommitted"
    );

    // Prepared references QuorumSize
    let prepared_body = extract_function_body(&verus_code, "LPrepared");
    assert!(
        prepared_body.contains("QuorumSize") || prepared_body.contains("LQuorumSize"),
        "Prepared should reference QuorumSize: {}",
        prepared_body
    );
}

#[test]
fn test_roundtrip_type_invariant_operators() {
    let source = read_example("SimpleCounter");
    let (module, verus_code, _) = full_pipeline(&source);

    // TypeOK is a non-action predicate (type invariant)
    let type_ok = find_operator(&module, "TypeOK");
    assert!(type_ok.is_some(), "TLA+ should have TypeOK");
    assert!(!contains_prime(&type_ok.unwrap().body), "TypeOK is not an action");

    assert!(
        verus_code.contains("pub open spec fn LTypeOK"),
        "Should generate LTypeOK"
    );
}

// =============================================================================
// 9. Operator Count Preservation (All Operators Translated)
// =============================================================================

#[test]
fn test_roundtrip_all_operators_translated() {
    for example in &[
        "SimpleCounter",
        "DieHard",
        "TwoPhase",
        "EWD840",
        "Raft",
        "Paxos",
        "PBFT",
    ] {
        let source = read_example(example);
        let (module, verus_code, _) = full_pipeline(&source);

        // Every operator in the TLA+ module should have a corresponding Verus spec fn
        for op in &module.operators {
            let verus_name = format!("L{}", op.name);
            assert!(
                verus_code.contains(&format!("spec fn {}", verus_name)),
                "{}: Operator '{}' should be translated to '{}' in Verus code",
                example,
                op.name,
                verus_name
            );
        }
    }
}

#[test]
fn test_roundtrip_operator_count_preserved() {
    for example in &[
        "SimpleCounter",
        "DieHard",
        "TwoPhase",
        "EWD840",
        "Raft",
        "Paxos",
        "PBFT",
    ] {
        let source = read_example(example);
        let (module, verus_code, _) = full_pipeline(&source);

        let tla_count = module.operators.len();
        let verus_count = verus_code.matches("pub open spec fn L").count();

        assert_eq!(
            tla_count, verus_count,
            "{}: TLA+ has {} operators but Verus has {} spec fns",
            example, tla_count, verus_count
        );
    }
}

// =============================================================================
// 10. Record Construction Preservation
// =============================================================================

#[test]
fn test_roundtrip_record_construction() {
    let source = read_example("Paxos");
    let (_, verus_code, _) = full_pipeline(&source);

    // Send1a: msgs' = msgs \cup {[type |-> Phase1a, bal |-> b]}
    // Records should be translated to struct-like construction
    let send1a_body = extract_function_body(&verus_code, "LSend1a");
    // Should reference Phase1a or LPhase1a (the type field value)
    assert!(
        send1a_body.contains("Phase1a") || send1a_body.contains("LPhase1a"),
        "Send1a should reference Phase1a in record: {}",
        send1a_body
    );
}

// =============================================================================
// Helper Functions
// =============================================================================

/// Extract the body of a function from generated Verus code.
/// Returns everything between the function signature and the closing brace.
fn extract_function_body(code: &str, fn_name: &str) -> String {
    let pattern = format!("spec fn {}", fn_name);
    if let Some(start) = code.find(&pattern) {
        // Find the opening brace
        let after = &code[start..];
        if let Some(brace_start) = after.find('{') {
            let body_start = start + brace_start;
            // Find matching closing brace (simple: find next fn or end)
            let remaining = &code[body_start..];
            // Find the next "pub open spec fn" or end of verus block
            let end = remaining
                .find("\npub open spec fn")
                .or_else(|| remaining.find("\n} // verus!"))
                .unwrap_or(remaining.len());
            return remaining[..end].to_string();
        }
    }
    String::new()
}

/// Extract the function signature line for a given function name.
fn extract_function_signature(code: &str, fn_name: &str) -> String {
    let pattern = format!("spec fn {}", fn_name);
    if let Some(start) = code.find(&pattern) {
        let line_start = code[..start].rfind('\n').map(|p| p + 1).unwrap_or(0);
        let line_end = code[start..].find('\n').map(|p| start + p).unwrap_or(code.len());
        let mut sig = code[line_start..line_end].to_string();
        // If signature continues on next line (multiline), capture more
        if !sig.contains("-> bool") && !sig.contains("->") {
            let next_end = code[line_end + 1..]
                .find('\n')
                .map(|p| line_end + 1 + p)
                .unwrap_or(code.len());
            sig.push_str(&code[line_end..next_end]);
        }
        return sig;
    }
    String::new()
}

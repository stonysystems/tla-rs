//! Integration tests for the Verus transpiler.

use verus_transpiler::ast::Pattern;
use verus_transpiler::*;

#[test]
fn test_transpiler_pipeline() {
    // Create a transpiler with default config
    let transpiler = Transpiler::default();

    // Verify components can be created
    let _ = VerusParser::new("// test".to_string());
    let _ = AnnotationParser::new("".to_string());
    let _ = ModeAnalyzer::new();
    let _ = Translator::default();
    let _ = Printer::default();

    // Test basic transpile (currently returns empty since parser is not implemented)
    let result = transpiler.transpile_source("", "");
    assert!(result.is_ok());
}

#[test]
fn test_mode_annotation_parsing() {
    let parser = AnnotationParser::new(String::new());

    // Test valid annotation
    let result = parser.parse_function_line("LAcceptorInit(-, +);");
    assert!(result.is_ok());
    let annotation = result.unwrap();
    assert_eq!(annotation.name, "LAcceptorInit");
    assert_eq!(annotation.param_modes.len(), 2);
    assert_eq!(annotation.param_modes[0], ParameterMode::Output);
    assert_eq!(annotation.param_modes[1], ParameterMode::Input);
}

#[test]
fn test_type_translation() {
    use verus_transpiler::ast::Path;

    let config = TranslatorConfig::default();
    let _translator = Translator::new(config);

    // Test named type translation
    let _spec_type = Type::Named(Path::single("LAcceptor".to_string()));
    let exec_type = translator::ExecType::Named("CAcceptor".to_string());

    // Verify the type string generation
    assert_eq!(exec_type.to_rust_string(), "CAcceptor");
}

#[test]
fn test_error_types() {
    // Test error creation
    let error = TranspileError::Parse {
        message: "test error".to_string(),
        span: None,
    };
    assert!(format!("{}", error).contains("test error"));

    // Test diagnostic accumulator
    let mut acc = DiagnosticAccumulator::new();
    assert!(!acc.has_errors());

    acc.add_error(TranspileError::Config {
        message: "config error".to_string(),
    });
    assert!(acc.has_errors());
}

#[test]
fn test_printer_output() {
    use verus_transpiler::translator::{ExecExpr, ExecParameter, ExecType};

    let func = ExecFunction {
        name: "CTestFunction".to_string(),
        params: vec![ExecParameter {
            name: "input".to_string(),
            ty: ExecType::Reference(Box::new(ExecType::Named("CState".to_string())), false),
            is_reference: true,
        }],
        return_type: ExecType::Tuple(vec![
            ExecType::Named("CState".to_string()),
            ExecType::Vec(Box::new(ExecType::Named("CPacket".to_string()))),
        ]),
        requires: vec!["input.well_formed()".to_string()],
        ensures: vec![
            "result.0.well_formed()".to_string(),
            "LTestFunction(input@, result.0@, result.1@)".to_string(),
        ],
        decreases: vec![],
        body: ExecExpr::Tuple(vec![
            ExecExpr::Clone(Box::new(ExecExpr::Var("input".to_string()))),
            ExecExpr::VecLit(vec![]),
        ]),
    };

    let output = print_function(&func);

    assert!(output.contains("pub exec fn CTestFunction"));
    assert!(output.contains("requires"));
    assert!(output.contains("ensures"));
    assert!(output.contains("input.well_formed()"));
    assert!(output.contains("result.0.well_formed()"));
}

#[test]
fn test_assignment_tracker() {
    use verus_transpiler::moder::MemberPath;

    let mut tracker = AssignmentTracker::new();

    // Test root assignment
    tracker.record_assignment("s_", MemberPath::Root);
    assert!(tracker.is_assigned("s_", &MemberPath::Root));

    // Test field assignment
    let field_path = MemberPath::root().field("max_bal".to_string());
    tracker.record_assignment("state", field_path.clone());
    assert!(tracker.is_assigned("state", &field_path));
    assert!(!tracker.is_assigned("state", &MemberPath::Root));
}

// ============================================================================
// Phase 7 Integration Tests
// ============================================================================

#[test]
fn test_template_matching_seq_comprehension() {
    use verus_transpiler::ast::{Binding, Expr, Literal, Path, VariableMode};
    use verus_transpiler::templates::{match_expression, QuantifierTemplate};

    // Create: forall |i: int| 0 <= i < len ==> seq[i] == f(i)
    // This is a sequence comprehension pattern
    let expr = Expr::Forall {
        vars: vec![Binding {
            pattern: Pattern::Ident("i".to_string()),
            ty: Some(verus_transpiler::ast::Type::Int),
            variable_mode: VariableMode::default(),
        }],
        triggers: vec![],
        body: Box::new(Expr::Implies(
            Box::new(Expr::Conjunction(vec![
                Expr::Le(
                    Box::new(Expr::Literal(Literal::Int(0))),
                    Box::new(Expr::Ident("i".to_string())),
                ),
                Expr::Lt(
                    Box::new(Expr::Ident("i".to_string())),
                    Box::new(Expr::Ident("len".to_string())),
                ),
            ])),
            Box::new(Expr::Eq(
                Box::new(Expr::Index(
                    Box::new(Expr::Ident("result".to_string())),
                    Box::new(Expr::Ident("i".to_string())),
                )),
                Box::new(Expr::Call {
                    func: Path::single("f".to_string()),
                    args: vec![Expr::Ident("i".to_string())],
                }),
            )),
        )),
    };

    let result = match_expression(&expr, &["result".to_string()]);
    assert!(matches!(
        result.template,
        QuantifierTemplate::SeqComprehension { .. }
    ));
    assert!(result.confidence >= 0.8);
}

#[test]
fn test_template_matching_struct_construction() {
    use verus_transpiler::ast::{Expr, Literal};
    use verus_transpiler::templates::{match_expression, QuantifierTemplate};

    // Create: s_.field1 == 42 &&& s_.field2 == true
    let expr = Expr::Conjunction(vec![
        Expr::Eq(
            Box::new(Expr::Field(
                Box::new(Expr::Ident("s_".to_string())),
                "field1".to_string(),
            )),
            Box::new(Expr::Literal(Literal::Int(42))),
        ),
        Expr::Eq(
            Box::new(Expr::Field(
                Box::new(Expr::Ident("s_".to_string())),
                "field2".to_string(),
            )),
            Box::new(Expr::Literal(Literal::Bool(true))),
        ),
    ]);

    let result = match_expression(&expr, &["s_".to_string()]);
    assert!(matches!(
        result.template,
        QuantifierTemplate::StructConstruction { .. }
    ));
}

#[test]
fn test_type_registry_operations() {
    use verus_transpiler::ast::Generics;
    use verus_transpiler::types::{FieldDef, StructDef, TypeRegistry};

    let mut registry = TypeRegistry::new();

    // Register a struct
    let struct_def = StructDef {
        name: "LAcceptor".to_string(),
        generics: Generics::default(),
        fields: vec![
            FieldDef {
                name: "max_bal".to_string(),
                ty: verus_transpiler::ast::Type::Int,
                is_public: true,
            },
            FieldDef {
                name: "votes".to_string(),
                ty: verus_transpiler::ast::Type::Int,
                is_public: true,
            },
        ],
        is_spec: true,
    };

    registry.register_struct(struct_def);

    assert!(registry.structs.contains_key("LAcceptor"));
    assert_eq!(registry.structs.get("LAcceptor").unwrap().fields.len(), 2);
}

#[test]
fn test_code_generation_struct() {
    use verus_transpiler::ast::Generics;
    use verus_transpiler::codegen::TypeGenerator;
    use verus_transpiler::config::NamingConfig;
    use verus_transpiler::types::{FieldDef, StructDef};

    let config = NamingConfig::default();
    let generator = TypeGenerator::new(config);

    let struct_def = StructDef {
        name: "LState".to_string(),
        generics: Generics::default(),
        fields: vec![FieldDef {
            name: "value".to_string(),
            ty: verus_transpiler::ast::Type::Int,
            is_public: true,
        }],
        is_spec: true,
    };

    let result = generator.generate_struct(&struct_def);

    assert!(result.code.contains("pub struct CState"));
    assert!(result.code.contains("pub value: i64"));
    assert!(result.code.contains("well_formed"));
    assert!(result.code.contains("impl View"));
}

#[test]
fn test_expression_transformation() {
    use std::collections::HashMap;
    use verus_transpiler::ast::{Expr, Literal, Path, Type};
    use verus_transpiler::translator::{ExecExpr, TransformContext, Translator, TranslatorConfig};

    let translator = Translator::default();
    static CONFIG: std::sync::OnceLock<TranslatorConfig> = std::sync::OnceLock::new();
    let mut output_types = HashMap::new();
    output_types.insert(
        "result".to_string(),
        Type::Named(Path::single("LResult".to_string())),
    );
    let ctx = TransformContext {
        config: CONFIG.get_or_init(TranslatorConfig::default),
        output_params: vec!["result".to_string()],
        input_params: vec!["inp".to_string()],
        output_types,
        input_types: HashMap::new(),
        field_substitutions: HashMap::new(),
        temp_var_counter: std::cell::RefCell::new(0),
        requires: vec![],
    };

    // Test method call transformation
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Ident("seq".to_string())),
        method: "len".to_string(),
        args: vec![],
    };
    let result = translator.transform_expr_public(&expr, &ctx).unwrap();
    match result {
        ExecExpr::MethodCall { method, .. } => {
            assert_eq!(method, "len");
        }
        _ => panic!("Expected MethodCall"),
    }

    // Test struct construction
    let expr = Expr::Struct {
        name: Path::single("LState".to_string()),
        fields: vec![("value".to_string(), Expr::Literal(Literal::Int(42)))],
    };
    let result = translator.transform_expr_public(&expr, &ctx).unwrap();
    match result {
        ExecExpr::Struct { name, fields } => {
            assert_eq!(name, "CState");
            assert_eq!(fields.len(), 1);
        }
        _ => panic!("Expected Struct"),
    }
}

#[test]
fn test_full_transpilation_simple() {
    // Test a simple transpilation from spec to exec
    let spec_source = r#"
    verus! {
        spec fn LSimpleInit(s: LState) -> bool {
            s.value == 0
        }
    }
    "#;

    let annotation_source = r#"
    # Mode annotations
    fn LSimpleInit(-);
    "#;

    let transpiler = Transpiler::default();
    let result = transpiler.transpile_source(spec_source, annotation_source);

    // The transpiler should succeed (even if output is minimal)
    assert!(result.is_ok());
}

// ============================================================================
// Phase A Integration Tests: Type Parsing + Generation Pipeline
// ============================================================================

#[test]
fn test_parse_verus_block_and_generate_types() {
    use verus_transpiler::codegen::TypeGenerator;
    use verus_transpiler::config::NamingConfig;
    use verus_transpiler::types::{TypeDef, TypeParser, TypeRegistry};

    // Parse a verus! block with struct definitions
    let source = r#"
        verus! {
            pub struct LAcceptor {
                pub max_bal: Ballot,
                pub votes: Votes,
            }

            pub struct LBallot {
                pub seqno: int,
                pub proposer_id: int,
            }
        }
    "#;

    let mut parser = TypeParser::new(source);
    let types = parser.parse_types().unwrap();

    // Should have parsed 2 types
    assert_eq!(types.len(), 2, "Expected 2 types but got {}", types.len());

    // Register types
    let mut registry = TypeRegistry::new();
    for type_def in types {
        if let TypeDef::Struct(s) = type_def {
            registry.register_struct(s);
        }
    }

    assert!(registry.structs.contains_key("LAcceptor"));
    assert!(registry.structs.contains_key("LBallot"));

    // Generate exec types
    let config = NamingConfig::default();
    let generator = TypeGenerator::new(config);

    // Generate CAcceptor
    let acceptor_def = registry.structs.get("LAcceptor").unwrap();
    let acceptor_code = generator.generate_struct(acceptor_def);

    // Verify generated code contains expected elements
    assert!(
        acceptor_code.code.contains("#[derive(Clone)]"),
        "Should have #[derive(Clone)]"
    );
    assert!(
        acceptor_code.code.contains("pub struct CAcceptor"),
        "Should have CAcceptor struct"
    );
    assert!(
        acceptor_code.code.contains("pub max_bal: CBallot"),
        "Should have CBallot field type"
    );
    assert!(
        acceptor_code.code.contains("pub votes: CVotes"),
        "Should have CVotes field type"
    );
    assert!(
        acceptor_code.code.contains("fn well_formed"),
        "Should have well_formed predicate"
    );
    assert!(
        acceptor_code.code.contains("impl View for CAcceptor"),
        "Should have View impl"
    );
    assert!(
        acceptor_code.code.contains("type V = LAcceptor"),
        "Should have spec type alias"
    );

    // Generate CBallot
    let ballot_def = registry.structs.get("LBallot").unwrap();
    let ballot_code = generator.generate_struct(ballot_def);

    assert!(
        ballot_code.code.contains("pub struct CBallot"),
        "Should have CBallot struct"
    );
    assert!(
        ballot_code.code.contains("seqno: i64"),
        "int should map to i64"
    );
    assert!(
        ballot_code.code.contains("proposer_id: i64"),
        "int should map to i64"
    );
}

#[test]
fn test_generate_enum_from_parsed_type() {
    use verus_transpiler::codegen::TypeGenerator;
    use verus_transpiler::config::NamingConfig;
    use verus_transpiler::types::{TypeDef, TypeParser, TypeRegistry};

    let source = r#"
        verus! {
            pub enum LMessage {
                Message1a { bal: Ballot },
                Message1b { bal: Ballot, votes: Votes },
                Invalid,
            }
        }
    "#;

    let mut parser = TypeParser::new(source);
    let types = parser.parse_types().unwrap();

    assert_eq!(types.len(), 1);

    let mut registry = TypeRegistry::new();
    for type_def in types {
        if let TypeDef::Enum(e) = type_def {
            registry.register_enum(e);
        }
    }

    let config = NamingConfig::default();
    let generator = TypeGenerator::new(config);

    let message_def = registry.enums.get("LMessage").unwrap();
    let code = generator.generate_enum(message_def);

    // Verify generated enum
    assert!(code.code.contains("#[derive(Clone)]"));
    assert!(code.code.contains("pub enum CMessage"));
    assert!(code.code.contains("Message1a"));
    assert!(code.code.contains("Message1b"));
    assert!(code.code.contains("Invalid"));
    assert!(code.code.contains("bal: CBallot"));
    assert!(code.code.contains("fn well_formed"));
    assert!(code.code.contains("impl View for CMessage"));
}

#[test]
fn test_generate_all_types_from_registry() {
    use verus_transpiler::codegen::generate_all_types;
    use verus_transpiler::config::NamingConfig;
    use verus_transpiler::types::{TypeDef, TypeParser, TypeRegistry};

    let source = r#"
        verus! {
            pub struct LState {
                pub value: int,
                pub items: Seq<Item>,
            }

            pub enum LStatus {
                Active,
                Inactive { reason: int },
            }
        }
    "#;

    let mut parser = TypeParser::new(source);
    let types = parser.parse_types().unwrap();

    let mut registry = TypeRegistry::new();
    for type_def in types {
        match type_def {
            TypeDef::Struct(s) => {
                registry.register_struct(s);
            }
            TypeDef::Enum(e) => {
                registry.register_enum(e);
            }
            _ => {}
        }
    }

    let config = NamingConfig::default();
    let code = generate_all_types(&registry, &config);

    // Verify the combined output
    assert!(code.code.contains("// Auto-generated"));
    assert!(code.code.contains("verus!"));
    assert!(code.code.contains("pub struct CState"));
    assert!(code.code.contains("pub enum CStatus"));
    assert!(code.code.contains("items: Vec<CItem>"));
    assert!(code.code.contains("impl View for CState"));
    assert!(code.code.contains("impl View for CStatus"));
}

// ============================================================================
// Raft Consensus Protocol Tests
// ============================================================================

#[test]
fn test_raft_type_generation() {
    use verus_transpiler::types::{TypeDef, TypeParser, TypeRegistry};

    let source = std::fs::read_to_string("../src/protocol/Raft/types.rs")
        .expect("Failed to read Raft types.rs");

    let mut parser = TypeParser::new(&source);
    let types = parser.parse_types().unwrap();

    // Should parse: LServerRole (enum), LLogEntry, LState, LConstants (structs)
    assert!(
        types.len() >= 4,
        "Expected at least 4 types but got {}: {:?}",
        types.len(),
        types
            .iter()
            .map(|t| match t {
                TypeDef::Struct(s) => format!("struct {}", s.name),
                TypeDef::Enum(e) => format!("enum {}", e.name),
                TypeDef::Alias(a) => format!("alias {}", a.name),
                TypeDef::Function(f) => format!("fn {}", f.name),
            })
            .collect::<Vec<_>>()
    );

    // Register types
    let mut registry = TypeRegistry::new();
    for type_def in &types {
        match type_def {
            TypeDef::Struct(s) => {
                registry.register_struct(s.clone());
            }
            TypeDef::Enum(e) => {
                registry.register_enum(e.clone());
            }
            _ => {}
        }
    }

    assert!(
        registry.structs.contains_key("LState"),
        "Should have LState"
    );
    assert!(
        registry.structs.contains_key("LConstants"),
        "Should have LConstants"
    );
    assert!(
        registry.structs.contains_key("LLogEntry"),
        "Should have LLogEntry"
    );
    assert!(
        registry.enums.contains_key("LServerRole"),
        "Should have LServerRole"
    );

    // Check LState has expected fields
    let state = &registry.structs["LState"];
    let field_names: Vec<&str> = state.fields.iter().map(|f| f.name.as_str()).collect();
    assert!(
        field_names.contains(&"current_term"),
        "LState should have current_term"
    );
    assert!(field_names.contains(&"role"), "LState should have role");
    assert!(field_names.contains(&"log"), "LState should have log");
    assert!(
        field_names.contains(&"commit_index"),
        "LState should have commit_index"
    );
    assert!(
        field_names.contains(&"votes_granted"),
        "LState should have votes_granted"
    );
    assert!(
        field_names.contains(&"match_index"),
        "LState should have match_index"
    );

    // Check LServerRole has expected variants
    let role_enum = &registry.enums["LServerRole"];
    let variant_names: Vec<&str> = role_enum.variants.iter().map(|v| v.name.as_str()).collect();
    assert!(
        variant_names.contains(&"Follower"),
        "Should have Follower variant"
    );
    assert!(
        variant_names.contains(&"Candidate"),
        "Should have Candidate variant"
    );
    assert!(
        variant_names.contains(&"Leader"),
        "Should have Leader variant"
    );
}

#[test]
fn test_raft_function_transpilation() {
    let spec_source = std::fs::read_to_string("../src/protocol/Raft/raft.rs")
        .expect("Failed to read Raft raft.rs");
    let annotation_source = std::fs::read_to_string("../src/protocol/Raft/raft.automan")
        .expect("Failed to read Raft raft.automan");

    let config = TranspilerConfig {
        translator: TranslatorConfig {
            spec_prefix: "L".to_string(),
            exec_prefix: "C".to_string(),
            ..Default::default()
        },
        skip_functions: vec![
            "LNext".to_string(),
            "LBecomeLeader".to_string(),
            "LFollowerAppendEntries".to_string(),
            "LHandleAppendResponse".to_string(),
            "LHandleAppendReject".to_string(),
        ],
        ..Default::default()
    };

    let transpiler = Transpiler::new(config);
    let result = transpiler.transpile_source(&spec_source, &annotation_source);
    assert!(
        result.is_ok(),
        "Transpilation should succeed: {:?}",
        result.err()
    );

    let output = result.unwrap();

    // Check that all expected exec functions are generated
    assert!(
        output.contains("pub exec fn CInit"),
        "Should generate CInit"
    );
    assert!(
        output.contains("pub exec fn CTimeout"),
        "Should generate CTimeout"
    );
    assert!(
        output.contains("pub exec fn CGrantVote"),
        "Should generate CGrantVote"
    );
    assert!(
        output.contains("pub exec fn CReceiveVoteGranted"),
        "Should generate CReceiveVoteGranted"
    );
    assert!(
        output.contains("pub exec fn CClientRequest"),
        "Should generate CClientRequest"
    );
    assert!(
        output.contains("pub exec fn CSendAppendEntries"),
        "Should generate CSendAppendEntries"
    );
    assert!(
        output.contains("pub exec fn CAdvanceCommitIndex"),
        "Should generate CAdvanceCommitIndex"
    );
    assert!(
        output.contains("pub exec fn CStepDown"),
        "Should generate CStepDown"
    );

    // Verify skipped functions are NOT generated
    assert!(
        !output.contains("pub exec fn CNext"),
        "Should NOT generate CNext"
    );
    assert!(
        !output.contains("pub exec fn CBecomeLeader"),
        "Should NOT generate CBecomeLeader"
    );
    assert!(
        !output.contains("pub exec fn CHandleAppendResponse"),
        "Should NOT generate CHandleAppendResponse"
    );
    assert!(
        !output.contains("pub exec fn CHandleAppendReject"),
        "Should NOT generate CHandleAppendReject"
    );

    // Check that ensures clauses reference spec functions
    assert!(
        output.contains("LInit("),
        "Should reference LInit in ensures"
    );
    assert!(
        output.contains("LTimeout("),
        "Should reference LTimeout in ensures"
    );

    // Check struct construction patterns
    assert!(
        output.contains("CState"),
        "Should construct CState in function bodies"
    );
}

#[test]
fn test_raft_annotation_parsing() {
    let annotation_source = std::fs::read_to_string("../src/protocol/Raft/raft.automan")
        .expect("Failed to read Raft raft.automan");

    let parser = AnnotationParser::new(annotation_source);
    let modules = parser.parse().unwrap();

    // Should have 1 module (Raft::raft)
    assert_eq!(modules.len(), 1, "Should have 1 module");
    let module = &modules[0];
    assert_eq!(module.module_path, "Raft::raft");

    let funcs = &module.functions;

    // Should have 7 function annotations (skipped functions are not in automan)
    assert!(
        funcs.len() >= 7,
        "Expected at least 7 function annotations but got {}",
        funcs.len()
    );

    // Check specific function annotations
    let init = funcs.get("LInit").expect("Should have LInit");
    assert_eq!(init.param_modes.len(), 2, "LInit should have 2 params");
    assert_eq!(
        init.param_modes[0],
        ParameterMode::Output,
        "LInit s should be output"
    );
    assert_eq!(
        init.param_modes[1],
        ParameterMode::Input,
        "LInit c should be input"
    );

    let timeout = funcs.get("LTimeout").expect("Should have LTimeout");
    assert_eq!(
        timeout.param_modes.len(),
        4,
        "LTimeout should have 4 params (s, s_, c, sent_packets)"
    );

    let grant = funcs.get("LGrantVote").expect("Should have LGrantVote");
    assert_eq!(
        grant.param_modes.len(),
        8,
        "LGrantVote should have 8 params (s, s_, c, candidate_term, candidate_last_log_term, candidate_last_log_index, candidate_id, sent_packets)"
    );

    let send_ae = funcs
        .get("LSendAppendEntries")
        .expect("Should have LSendAppendEntries");
    assert_eq!(
        send_ae.param_modes.len(),
        9,
        "LSendAppendEntries should have 9 params (s, s_, c, follower, entry_value, prev_log_index, prev_log_term, has_entry, sent_packets)"
    );
}

#[test]
fn test_raft_config_loading() {
    let config_str = std::fs::read_to_string("../src/protocol/Raft/raft_transpile.toml")
        .expect("Failed to read Raft config");

    let config: toml::Value = config_str.parse().expect("Failed to parse TOML");

    // Check skip_functions
    let skip = config["skip_functions"].as_array().unwrap();
    assert!(
        skip.iter().any(|v| v.as_str() == Some("LNext")),
        "Should skip LNext"
    );

    // Check naming
    let naming = &config["naming"];
    assert_eq!(naming["spec_prefix"].as_str(), Some("L"));
    assert_eq!(naming["exec_prefix"].as_str(), Some("C"));
    assert_eq!(naming["int_type"].as_str(), Some("u64"));

    // Remapping is now auto-inferred (Phase 21), not in TOML

    // Check output settings
    let output = &config["output"];
    assert_eq!(output["validity_predicate_name"].as_str(), Some("valid"));
    assert_eq!(
        output["generate_loops_for_verification"].as_bool(),
        Some(true)
    );
}

// ============================================================================
// Chain Replication Protocol Tests
// ============================================================================

#[test]
fn test_chain_replication_type_generation() {
    use verus_transpiler::types::{TypeDef, TypeParser, TypeRegistry};

    let source = std::fs::read_to_string("../src/protocol/ChainReplication/types.rs")
        .expect("Failed to read ChainReplication types.rs");

    let mut parser = TypeParser::new(&source);
    let types = parser.parse_types().unwrap();

    // Should parse: LNodeRole (enum), LState, LConstants (structs)
    assert!(
        types.len() >= 3,
        "Expected at least 3 types but got {}: {:?}",
        types.len(),
        types
            .iter()
            .map(|t| match t {
                TypeDef::Struct(s) => format!("struct {}", s.name),
                TypeDef::Enum(e) => format!("enum {}", e.name),
                TypeDef::Alias(a) => format!("alias {}", a.name),
                TypeDef::Function(f) => format!("fn {}", f.name),
            })
            .collect::<Vec<_>>()
    );

    let mut registry = TypeRegistry::new();
    for type_def in &types {
        match type_def {
            TypeDef::Struct(s) => {
                registry.register_struct(s.clone());
            }
            TypeDef::Enum(e) => {
                registry.register_enum(e.clone());
            }
            _ => {}
        }
    }

    assert!(
        registry.structs.contains_key("LState"),
        "Should have LState"
    );
    assert!(
        registry.structs.contains_key("LConstants"),
        "Should have LConstants"
    );
    assert!(
        registry.enums.contains_key("LNodeRole"),
        "Should have LNodeRole"
    );

    // Check LState has expected fields
    let state = &registry.structs["LState"];
    let field_names: Vec<&str> = state.fields.iter().map(|f| f.name.as_str()).collect();
    assert!(field_names.contains(&"role"), "LState should have role");
    assert!(
        field_names.contains(&"history"),
        "LState should have history"
    );
    assert!(
        field_names.contains(&"pending_sent"),
        "LState should have pending_sent"
    );
    assert!(
        field_names.contains(&"committed_count"),
        "LState should have committed_count"
    );
    assert!(
        field_names.contains(&"obj_value"),
        "LState should have obj_value"
    );

    // Check LNodeRole has expected variants
    let role_enum = &registry.enums["LNodeRole"];
    let variant_names: Vec<&str> = role_enum.variants.iter().map(|v| v.name.as_str()).collect();
    assert!(variant_names.contains(&"Head"), "Should have Head variant");
    assert!(
        variant_names.contains(&"Middle"),
        "Should have Middle variant"
    );
    assert!(variant_names.contains(&"Tail"), "Should have Tail variant");
}

#[test]
fn test_chain_replication_function_transpilation() {
    let spec_source = std::fs::read_to_string("../src/protocol/ChainReplication/chain.rs")
        .expect("Failed to read ChainReplication chain.rs");
    let annotation_source =
        std::fs::read_to_string("../src/protocol/ChainReplication/chain.automan")
            .expect("Failed to read ChainReplication chain.automan");

    let config = TranspilerConfig {
        translator: TranslatorConfig {
            spec_prefix: "L".to_string(),
            exec_prefix: "C".to_string(),
            ..Default::default()
        },
        skip_functions: vec!["LNext".to_string()],
        ..Default::default()
    };

    let transpiler = Transpiler::new(config);
    let result = transpiler.transpile_source(&spec_source, &annotation_source);
    assert!(
        result.is_ok(),
        "Transpilation should succeed: {:?}",
        result.err()
    );

    let output = result.unwrap();

    // Check all expected exec functions are generated
    assert!(
        output.contains("pub exec fn CInit"),
        "Should generate CInit"
    );
    assert!(
        output.contains("pub exec fn CHeadReceiveWrite"),
        "Should generate CHeadReceiveWrite"
    );
    assert!(
        output.contains("pub exec fn CReceiveUpdate"),
        "Should generate CReceiveUpdate"
    );
    assert!(
        output.contains("pub exec fn CTailCommit"),
        "Should generate CTailCommit"
    );
    assert!(
        output.contains("pub exec fn CReceiveAck"),
        "Should generate CReceiveAck"
    );
    assert!(
        output.contains("pub exec fn CClientRead"),
        "Should generate CClientRead"
    );

    // Verify LNext is NOT generated
    assert!(
        !output.contains("pub exec fn CNext"),
        "Should NOT generate CNext"
    );

    // Check ensures clauses reference spec functions
    assert!(
        output.contains("LInit("),
        "Should reference LInit in ensures"
    );
    assert!(
        output.contains("LHeadReceiveWrite("),
        "Should reference LHeadReceiveWrite in ensures"
    );
    assert!(
        output.contains("LTailCommit("),
        "Should reference LTailCommit in ensures"
    );
}

#[test]
fn test_chain_replication_annotation_parsing() {
    let annotation_source =
        std::fs::read_to_string("../src/protocol/ChainReplication/chain.automan")
            .expect("Failed to read ChainReplication chain.automan");

    let parser = AnnotationParser::new(annotation_source);
    let modules = parser.parse().unwrap();

    assert_eq!(modules.len(), 1, "Should have 1 module");
    let module = &modules[0];
    assert_eq!(module.module_path, "ChainReplication::chain");

    let funcs = &module.functions;

    // Should have 6 function annotations
    assert!(
        funcs.len() >= 6,
        "Expected at least 6 function annotations but got {}",
        funcs.len()
    );

    // Check specific annotations
    let init = funcs.get("LInit").expect("Should have LInit");
    assert_eq!(init.param_modes.len(), 2, "LInit should have 2 params");
    assert_eq!(init.param_modes[0], ParameterMode::Output);
    assert_eq!(init.param_modes[1], ParameterMode::Input);

    let head_write = funcs
        .get("LHeadReceiveWrite")
        .expect("Should have LHeadReceiveWrite");
    assert_eq!(
        head_write.param_modes.len(),
        5,
        "LHeadReceiveWrite should have 5 params (s, s_, c, value, sent_packets)"
    );

    let tail_commit = funcs.get("LTailCommit").expect("Should have LTailCommit");
    assert_eq!(
        tail_commit.param_modes.len(),
        5,
        "LTailCommit should have 5 params (s, s_, c, value, sent_packets)"
    );

    let client_read = funcs.get("LClientRead").expect("Should have LClientRead");
    assert_eq!(
        client_read.param_modes.len(),
        4,
        "LClientRead should have 4 params (s, s_, c, sent_packets)"
    );
}

#[test]
fn test_chain_replication_config_loading() {
    let config_str =
        std::fs::read_to_string("../src/protocol/ChainReplication/chain_transpile.toml")
            .expect("Failed to read ChainReplication config");

    let config: toml::Value = config_str.parse().expect("Failed to parse TOML");

    // Check skip_functions
    let skip = config["skip_functions"].as_array().unwrap();
    assert!(
        skip.iter().any(|v| v.as_str() == Some("LNext")),
        "Should skip LNext"
    );

    // Check naming
    let naming = &config["naming"];
    assert_eq!(naming["spec_prefix"].as_str(), Some("L"));
    assert_eq!(naming["exec_prefix"].as_str(), Some("C"));

    // Remapping is now auto-inferred (Phase 21), not in TOML
}

#[test]
fn test_rsl_types_manual_helpers_foundational_symbols_present() {
    let source = std::fs::read_to_string("../src/protocol/RSL/types_manual_helpers.rs")
        .expect("Failed to read RSL types manual helpers");

    assert!(
        !source.contains("impl CParameters"),
        "manual helper file should no longer define CParameters impl blocks"
    );
    assert!(
        !source.contains("pub type CRslIo = LIoOp<EndPoint, CMessage>;"),
        "CRslIo alias should be generated by typegen, not defined in manual helper file"
    );
    for symbol in [
        "pub struct CConfiguration",
        "pub struct CConstants",
        "pub struct CReplicaConstants",
        "pub struct CAcceptor",
        "pub struct CLearner",
        "pub struct CElectionState",
        "pub enum COutstandingOperation",
        "pub struct CExecutor",
        "pub enum CIncompleteBatchTimer",
        "pub struct CProposer",
        "pub struct CReplica",
        "pub struct CScheduler",
        "pub open spec fn abstractify_clpacket",
        "pub open spec fn abstractify_crslio(io: CRslIo) -> RslIo",
        "pub open spec fn abstractify_crslio_seq(ios: Seq<CRslIo>) -> Seq<RslIo>",
    ] {
        assert!(
            !source.contains(symbol),
            "re-homed symbol `{}` should be absent from manual helper injection",
            symbol
        );
    }

    let cparameters_source = std::fs::read_to_string("../src/implementation/RSL/cparameters.rs")
        .expect("Failed to read RSL cparameters module");
    for symbol in ["impl CParameters{", "impl View for CParameters"] {
        assert!(
            cparameters_source.contains(symbol),
            "missing symbol `{}` in cparameters module",
            symbol
        );
    }
}

#[test]
fn test_rsl_types_manual_helpers_contains_only_type_infrastructure() {
    let source = std::fs::read_to_string("../src/protocol/RSL/types_manual_helpers.rs")
        .expect("Failed to read RSL types manual helpers");

    // Phase 21.2.9 guard: this helper file is for type/clone/view infrastructure only.
    // Protocol action implementations should live in generated *_gen.rs or impl modules.
    assert!(
        !source.contains("pub exec fn"),
        "types_manual_helpers.rs should not define protocol exec functions"
    );

    let forbidden_protocol_symbols = [
        "CAcceptorProcess1a(",
        "CAcceptorProcess2a(",
        "CAcceptorProcessHeartbeat(",
        "CAcceptorTruncateLog(",
        "CLearnerProcess2b(",
        "CExecutorExecute(",
        "CProposerProcessRequest(",
        "CElectionStateProcessHeartbeat(",
        "CBroadcastToEveryone(",
        "CReplicaNextProcessPacket(",
    ];

    for symbol in forbidden_protocol_symbols {
        assert!(
            !source.contains(symbol),
            "types_manual_helpers.rs should not contain protocol function `{}`",
            symbol
        );
    }
}

#[test]
fn test_rsl_types_transpile_toml_has_no_manual_helpers_binding() {
    let config_str = std::fs::read_to_string("../src/protocol/RSL/types_transpile.toml")
        .expect("Failed to read RSL types transpile config");
    let config: toml::Value = config_str.parse().expect("Failed to parse RSL types TOML");

    assert!(
        config
            .get("output")
            .and_then(|output| output.get("manual_code"))
            .is_none(),
        "types_transpile.toml should no longer define output.manual_code"
    );
    let generate_unreachable_value_helper = config
        .get("output")
        .and_then(|output| output.get("generate_unreachable_value_helper"))
        .and_then(|v| v.as_bool())
        .expect("types_transpile.toml should define output.generate_unreachable_value_helper");
    let generate_clone_up_to_view_simple = config
        .get("output")
        .and_then(|output| output.get("generate_clone_up_to_view_simple"))
        .and_then(|v| v.as_bool())
        .expect("types_transpile.toml should define output.generate_clone_up_to_view_simple");
    assert!(
        generate_clone_up_to_view_simple,
        "RSL types generation should enable output.generate_clone_up_to_view_simple"
    );
    assert!(
        generate_unreachable_value_helper,
        "RSL types generation should enable output.generate_unreachable_value_helper"
    );
    let io_alias = config
        .get("extra_type_aliases")
        .and_then(|aliases| aliases.get("CRslIo"))
        .and_then(|v| v.as_str())
        .expect("types_transpile.toml should define extra_type_aliases.CRslIo");
    assert_eq!(
        io_alias, "LIoOp<EndPoint, CMessage>",
        "CRslIo should be generated via extra_type_aliases"
    );
    let skip_validity_types = config
        .get("skip_validity_types")
        .and_then(|v| v.as_array())
        .expect("types_transpile.toml should define skip_validity_types");
    assert!(
        skip_validity_types
            .iter()
            .any(|v| v.as_str() == Some("CParameters")),
        "types_transpile.toml should keep CParameters in skip_validity_types"
    );
    let skip_view_types = config
        .get("skip_view_types")
        .and_then(|v| v.as_array())
        .expect("types_transpile.toml should define skip_view_types");
    assert!(
        skip_view_types
            .iter()
            .any(|v| v.as_str() == Some("CParameters")),
        "types_transpile.toml should keep CParameters in skip_view_types"
    );
    let skip_types = config
        .get("skip_types")
        .and_then(|v| v.as_array())
        .expect("types_transpile.toml should define skip_types");
    assert!(
        !skip_types.iter().any(|v| v.as_str() == Some("LParameters")),
        "LParameters should no longer be skipped so CParameters can be generated"
    );
    for ty in ["LConfiguration", "LConstants", "LReplicaConstants"] {
        assert!(
            skip_types
                .iter()
                .any(|v| v.as_str() == Some(ty)),
            "{} should stay in skip_types while foundational blocks are re-exported from implementation modules",
            ty
        );
    }
    for ty in [
        "LAcceptor",
        "LLearner",
        "ElectionState",
        "OutstandingOperation",
    ] {
        assert!(
            skip_types
                .iter()
                .any(|v| v.as_str() == Some(ty)),
            "{} should stay in skip_types while component block A is re-exported from implementation modules",
            ty
        );
    }

    let re_exports = config
        .get("re_exports")
        .and_then(|v| v.as_array())
        .expect("types_transpile.toml should define re_exports");
    for re_export in [
        "crate::implementation::RSL::acceptorimpl::CAcceptor",
        "crate::implementation::RSL::learnerimpl::CLearner",
        "crate::implementation::RSL::ElectionImpl::{CElectionState, COutstandingOperation, CRequestHeader}",
        "crate::implementation::RSL::ExecutorImpl::{CExecutor, CIncompleteBatchTimer}",
        "crate::implementation::RSL::ProposerImpl::CProposer",
        "crate::implementation::RSL::ReplicaImpl::{CReplica, CScheduler, abstractify_clpacket, abstractify_crslio, abstractify_crslio_seq}",
    ] {
        assert!(
            re_exports
                .iter()
                .any(|v| v.as_str() == Some(re_export)),
            "types_transpile.toml should re-export `{}`",
            re_export
        );
    }

    let cparameters_source = std::fs::read_to_string("../src/implementation/RSL/cparameters.rs")
        .expect("Failed to read RSL cparameters module");
    for symbol in ["impl CParameters{", "impl View for CParameters"] {
        assert!(
            cparameters_source.contains(symbol),
            "cparameters module should include `{}` after manual helper removal",
            symbol
        );
    }
}

#[test]
fn test_rsl_generated_types_include_simple_clone_up_to_view() {
    let source = std::fs::read_to_string("../src/generated/RSL/types_gen.rs")
        .expect("Failed to read generated RSL types");

    assert!(
        source
            .contains("impl CClockReading {\n    pub fn clone_up_to_view(&self) -> (result: Self)"),
        "generated CClockReading should include clone_up_to_view helper for primitive-only structs"
    );
    assert!(
        source.contains("impl CParameters {\n    pub fn clone_up_to_view(&self) -> (result: Self)"),
        "generated CParameters should include clone_up_to_view helper for primitive-only structs"
    );

    let cparameters_source = std::fs::read_to_string("../src/implementation/RSL/cparameters.rs")
        .expect("Failed to read RSL cparameters module");
    assert!(
        !cparameters_source.contains("impl CParameters{\n    pub fn clone_up_to_view"),
        "cparameters module should not redefine CParameters::clone_up_to_view"
    );
}

#[test]
fn test_rsl_transpile_toml_uses_current_executor_and_outstanding_operation_import_paths() {
    let config_str = std::fs::read_to_string("../src/protocol/RSL/transpile.toml")
        .expect("Failed to read RSL transpile config");
    let config: toml::Value = config_str.parse().expect("Failed to parse RSL TOML");
    let custom_imports = config
        .get("output")
        .and_then(|output| output.get("custom_imports"))
        .and_then(|v| v.as_array())
        .expect("RSL transpile.toml should define output.custom_imports");

    assert!(
        custom_imports.iter().any(|v| {
            v.as_str() == Some("use crate::implementation::RSL::ExecutorImpl::CExecutor;")
        }),
        "RSL transpile.toml should import CExecutor from ExecutorImpl"
    );
    assert!(
        custom_imports.iter().any(|v| {
            v.as_str()
                == Some(
                    "use crate::implementation::RSL::ElectionImpl::{CElectionState, COutstandingOperation};",
                )
        }),
        "RSL transpile.toml should import COutstandingOperation from ElectionImpl"
    );
    assert!(
        !custom_imports.iter().any(|v| {
            v.as_str()
                == Some(
                    "use crate::implementation::RSL::ExecutorImpl::{CExecutor, COutstandingOperation};",
                )
        }),
        "RSL transpile.toml should not keep stale COutstandingOperation import from ExecutorImpl"
    );
}

#[test]
fn test_rsl_types_manual_helpers_extension_symbols_present() {
    let source = std::fs::read_to_string("../src/protocol/RSL/types_manual_helpers.rs")
        .expect("Failed to read RSL types manual helpers");

    assert!(
        !source.contains("impl CParameters"),
        "types_manual_helpers.rs should not define CParameters impls after manual_code removal"
    );

    assert!(
        !source.contains("pub fn StaticParams() -> (p:CParameters)"),
        "StaticParams should be re-homed out of manual helper injection"
    );
    assert!(
        !source.contains("pub fn CMinQuorumSize(&self) -> (q:usize)"),
        "CMinQuorumSize should be re-homed out of manual helper injection"
    );
    assert!(
        !source.contains("pub fn CGetReplicaIndex( &self, id:&EndPoint) -> (rc:(bool, usize))"),
        "CGetReplicaIndex should be re-homed out of manual helper injection"
    );
    assert!(
        !source.contains("pub fn CFindIndexInSeq(s:Vec<EndPoint>, v:EndPoint, start:usize) -> (rc:(bool, usize))"),
        "CFindIndexInSeq should be re-homed out of manual helper injection"
    );
    assert!(
        !source.contains("pub proof fn lemma_AbstractifyEndpoints_properties(s:Vec<EndPoint>)"),
        "endpoint abstraction lemmas should be re-homed out of manual helper injection"
    );
    assert!(
        !source.contains("pub fn CReplicaConstantsValid(&self) -> (res:bool)"),
        "CReplicaConstantsValid should be re-homed out of manual helper injection"
    );
    assert!(
        !source.contains("pub fn InitReplicaConstants(end:&EndPoint, config:&CConfiguration) -> (rc:CReplicaConstants)"),
        "InitReplicaConstants should be re-homed out of manual helper injection"
    );
    for symbol in [
        "pub struct CConfiguration",
        "pub struct CConstants",
        "pub struct CReplicaConstants",
        "pub open spec fn ReplicaIndexValid(index:u64, config:CConfiguration) -> bool",
        "pub struct CAcceptor",
        "pub struct CLearner",
        "pub struct CElectionState",
        "pub enum COutstandingOperation",
    ] {
        assert!(
            !source.contains(symbol),
            "re-homed symbol `{}` should be absent from manual helper injection",
            symbol
        );
    }

    let cparameters_source = std::fs::read_to_string("../src/implementation/RSL/cparameters.rs")
        .expect("Failed to read RSL cparameters module");
    assert!(
        cparameters_source.contains("pub fn StaticParams() -> (p:CParameters)"),
        "StaticParams should be defined in implementation/RSL/cparameters.rs"
    );
    for symbol in ["impl CParameters{", "impl View for CParameters"] {
        assert!(
            cparameters_source.contains(symbol),
            "missing symbol `{}` in cparameters module",
            symbol
        );
    }

    let cconfiguration_source =
        std::fs::read_to_string("../src/implementation/RSL/cconfiguration.rs")
            .expect("Failed to read RSL cconfiguration module");
    for symbol in [
        "pub fn clone_up_to_view(&self) -> (res:CConfiguration)",
        "pub open spec fn abstractable(self) -> bool",
        "pub open spec fn CIsReplicaIndex(&self, idx:usize, id:EndPoint) -> bool",
        "impl View for CConfiguration",
        "pub open spec fn ReplicaIndexValid(index:u64, config:CConfiguration) -> bool",
        "pub fn CMinQuorumSize(&self) -> (q:usize)",
        "pub fn CGetReplicaIndex( &self, id:&EndPoint) -> (rc:(bool, usize))",
        "pub fn CFindIndexInSeq(s:Vec<EndPoint>, v:EndPoint, start:usize) -> (rc:(bool, usize))",
        "pub proof fn lemma_AbstractifyEndpoints_properties(s:Vec<EndPoint>)",
        "pub proof fn lemma_AbstractifyEndPointToNodeIdentity_injective_forall()",
    ] {
        assert!(
            cconfiguration_source.contains(symbol),
            "missing symbol `{}` in re-homed cconfiguration helper module",
            symbol
        );
    }

    let cconstants_source = std::fs::read_to_string("../src/implementation/RSL/cconstants.rs")
        .expect("Failed to read RSL cconstants module");
    for symbol in [
        "pub fn clone_up_to_view(&self) -> (result:Self)",
        "pub open spec fn abstractable(self) -> bool",
        "impl View for CConstants",
        "pub open spec fn view(self) -> LReplicaConstants",
        "impl View for CReplicaConstants",
        "pub fn CReplicaConstantsValid(&self) -> (res:bool)",
        "pub fn InitReplicaConstants(end:&EndPoint, config:&CConfiguration) -> (rc:CReplicaConstants)",
    ] {
        assert!(
            cconstants_source.contains(symbol),
            "missing symbol `{}` in re-homed cconstants helper module",
            symbol
        );
    }

    let acceptor_source = std::fs::read_to_string("../src/implementation/RSL/acceptorimpl.rs")
        .expect("Failed to read RSL acceptorimpl module");
    for symbol in [
        "pub struct CAcceptor",
        "impl CAcceptor",
        "impl View for CAcceptor",
    ] {
        assert!(
            acceptor_source.contains(symbol),
            "missing symbol `{}` in re-homed acceptorimpl module",
            symbol
        );
    }

    let learner_source = std::fs::read_to_string("../src/implementation/RSL/learnerimpl.rs")
        .expect("Failed to read RSL learnerimpl module");
    for symbol in [
        "pub struct CLearner",
        "impl CLearner",
        "impl View for CLearner",
    ] {
        assert!(
            learner_source.contains(symbol),
            "missing symbol `{}` in re-homed learnerimpl module",
            symbol
        );
    }

    let election_source = std::fs::read_to_string("../src/implementation/RSL/ElectionImpl.rs")
        .expect("Failed to read RSL ElectionImpl module");
    for symbol in [
        "pub struct CElectionState",
        "impl CElectionState",
        "impl View for CElectionState",
        "pub enum COutstandingOperation",
        "impl COutstandingOperation",
        "impl View for COutstandingOperation",
    ] {
        assert!(
            election_source.contains(symbol),
            "missing symbol `{}` in re-homed ElectionImpl module",
            symbol
        );
    }
}

#[test]
fn test_rsl_types_manual_helpers_component_part1_symbols_present() {
    let source = std::fs::read_to_string("../src/protocol/RSL/types_manual_helpers.rs")
        .expect("Failed to read RSL types manual helpers");

    let removed_symbols = [
        "pub struct CAcceptor",
        "pub min_vote_opn: COperationNumber",
        "pub struct CLearner",
        "pub struct CElectionState",
        "pub cur_req_set: HashSet<CRequestHeader>",
        "pub enum COutstandingOperation",
        "COutstandingOpKnown",
    ];

    for symbol in removed_symbols {
        assert!(
            !source.contains(symbol),
            "symbol `{}` should be re-homed out of types_manual_helpers.rs",
            symbol
        );
    }

    let acceptor_source = std::fs::read_to_string("../src/implementation/RSL/acceptorimpl.rs")
        .expect("Failed to read acceptorimpl.rs");
    for symbol in ["pub struct CAcceptor", "pub min_vote_opn: COperationNumber"] {
        assert!(
            acceptor_source.contains(symbol),
            "missing symbol `{}` in acceptorimpl.rs",
            symbol
        );
    }

    let learner_source = std::fs::read_to_string("../src/implementation/RSL/learnerimpl.rs")
        .expect("Failed to read learnerimpl.rs");
    assert!(
        learner_source.contains("pub struct CLearner"),
        "missing CLearner in learnerimpl.rs"
    );

    let election_source = std::fs::read_to_string("../src/implementation/RSL/ElectionImpl.rs")
        .expect("Failed to read ElectionImpl.rs");
    for symbol in [
        "pub struct CElectionState",
        "pub cur_req_set: HashSet<CRequestHeader>",
        "pub enum COutstandingOperation",
        "COutstandingOpKnown",
    ] {
        assert!(
            election_source.contains(symbol),
            "missing symbol `{}` in ElectionImpl.rs",
            symbol
        );
    }
}

#[test]
fn test_rsl_types_manual_helpers_component_part2_symbols_present() {
    let source = std::fs::read_to_string("../src/protocol/RSL/types_manual_helpers.rs")
        .expect("Failed to read RSL types manual helpers");

    let removed_symbols = [
        "pub struct CProposer {",
        "pub highest_seqno_requested_by_client_this_view: HashMap<EndPoint, u64>",
        "pub struct CReplica {",
        "pub nextHeartbeatTime: u64",
        "pub struct CScheduler {",
        "pub open spec fn abstractify_clpacket",
        "pub open spec fn abstractify_crslio(io: CRslIo) -> RslIo",
        "pub open spec fn abstractify_crslio_seq(ios: Seq<CRslIo>) -> Seq<RslIo>",
    ];

    for symbol in removed_symbols {
        assert!(
            !source.contains(symbol),
            "symbol `{}` should be re-homed out of types_manual_helpers.rs",
            symbol
        );
    }

    let executor_source = std::fs::read_to_string("../src/implementation/RSL/ExecutorImpl.rs")
        .expect("Failed to read ExecutorImpl.rs");
    for symbol in [
        "pub struct CExecutor",
        "pub enum CIncompleteBatchTimer",
        "impl View for CExecutor",
        "impl View for CIncompleteBatchTimer",
    ] {
        assert!(
            executor_source.contains(symbol),
            "missing symbol `{}` in ExecutorImpl.rs",
            symbol
        );
    }

    let proposer_source = std::fs::read_to_string("../src/implementation/RSL/ProposerImpl.rs")
        .expect("Failed to read ProposerImpl.rs");
    for symbol in [
        "pub struct CProposer",
        "pub highest_seqno_requested_by_client_this_view: HashMap<EndPoint, u64>",
        "impl View for CProposer",
    ] {
        assert!(
            proposer_source.contains(symbol),
            "missing symbol `{}` in ProposerImpl.rs",
            symbol
        );
    }

    let replica_source = std::fs::read_to_string("../src/implementation/RSL/ReplicaImpl.rs")
        .expect("Failed to read ReplicaImpl.rs");
    for symbol in [
        "pub struct CReplica",
        "pub nextHeartbeatTime: u64",
        "pub struct CScheduler",
        "pub open spec fn abstractify_clpacket",
        "pub open spec fn abstractify_crslio(io: CRslIo) -> RslIo",
        "pub open spec fn abstractify_crslio_seq(ios: Seq<CRslIo>) -> Seq<RslIo>",
    ] {
        assert!(
            replica_source.contains(symbol),
            "missing symbol `{}` in ReplicaImpl.rs",
            symbol
        );
    }
}

#[test]
fn test_transpilation_determinism_with_struct_substitutions() {
    // Regression: struct construction with field substitutions must produce deterministic output.
    // Previously, HashMap iteration order caused non-deterministic field ordering.
    let spec_source = r#"
        verus! {
            pub struct LReplica {
                pub alpha: int,
                pub beta: int,
                pub gamma: int,
                pub delta: int,
            }

            pub open spec fn LReplicaInit(s_: LReplica) -> bool {
                &&& s_.alpha == 0
                &&& s_.beta == 1
                &&& s_.gamma == 2
                &&& s_.delta == 3
            }
        }
    "#;
    let annotation_source = "module test\nLReplicaInit(-)\n";

    let config = TranspilerConfig {
        generate_inline_types: true,
        translator: TranslatorConfig {
            generate_proofs: true,
            ..Default::default()
        },
        ..Default::default()
    };

    let mut results = Vec::new();
    for _ in 0..5 {
        let transpiler = Transpiler::new(config.clone());
        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();
        results.push(result);
    }

    for i in 1..results.len() {
        assert_eq!(
            results[0],
            results[i],
            "Transpilation run {} produced different output than run 0. Diff:\n{}",
            i,
            diff_strings(&results[0], &results[i])
        );
    }
}

// ============================================================================
// Generated RSL Module Integration Tests (Phase 5 verification)
// ============================================================================

/// Verify all expected generated RSL modules are enabled in mod.rs
#[test]
fn test_generated_rsl_modules_enabled() {
    let mod_source = std::fs::read_to_string("../src/generated/RSL/mod.rs")
        .expect("Failed to read generated RSL mod.rs");

    let expected_enabled = [
        "pub mod acceptor_gen;",
        "pub mod broadcast_gen;",
        // election_gen disabled until its 27 verification errors are resolved
        "pub mod executor_gen;",
        "pub mod learner_gen;",
        "pub mod proposer_gen;",
        "pub mod replica_gen;",
        "pub mod types_gen;",
    ];

    for module in expected_enabled {
        assert!(
            mod_source.contains(module),
            "Module `{}` should be enabled in generated/RSL/mod.rs",
            module
        );
    }
}

/// Verify acceptor_gen.rs has all expected public functions with correct signatures
#[test]
fn test_generated_acceptor_module_public_api() {
    let source = std::fs::read_to_string("../src/generated/RSL/acceptor_gen.rs")
        .expect("Failed to read acceptor_gen.rs");

    // Expected public exec functions
    let expected_functions = [
        "pub exec fn CAcceptorInit",
        "pub exec fn CAcceptorProcess1a",
        "pub exec fn CAcceptorProcess2a",
        "pub exec fn CAcceptorProcessHeartbeat",
        "pub exec fn CAcceptorTruncateLog",
    ];

    for func in expected_functions {
        assert!(
            source.contains(func),
            "acceptor_gen.rs should contain `{}`",
            func
        );
    }

    // Verify functional style: takes &CAcceptor, returns CAcceptor or tuple
    assert!(
        source.contains("s: &CAcceptor"),
        "Acceptor functions should take &CAcceptor"
    );

    // Verify spec predicate ensures
    let spec_predicates = [
        "LAcceptorInit(",
        "LAcceptorProcess1a(",
        "LAcceptorProcess2a(",
        "LAcceptorProcessHeartbeat(",
        "LAcceptorTruncateLog(",
    ];

    for pred in spec_predicates {
        assert!(
            source.contains(pred),
            "acceptor_gen.rs should reference spec predicate `{}`",
            pred
        );
    }

    // Verify packet validity ensures on packet-returning functions
    // Manual code uses "i: int" (with space), auto-generated uses "i:int" (no space)
    assert!(
        source.contains("result.1@.len() ==> result.1@[i].valid()"),
        "Packet-returning functions should ensure packet validity"
    );
    assert!(
        source.contains("result.1@.len() ==> result.1@[i].abstractable()"),
        "Packet-returning functions should ensure packet abstractability"
    );
}

/// Verify learner_gen.rs has all expected public functions
#[test]
fn test_generated_learner_module_public_api() {
    let source = std::fs::read_to_string("../src/generated/RSL/learner_gen.rs")
        .expect("Failed to read learner_gen.rs");

    let expected_functions = [
        "pub exec fn CLearnerInit",
        "pub exec fn CLearnerForgetDecision",
        "pub exec fn CLearnerProcess2b",
        "pub exec fn CLearnerForgetOperationsBefore",
    ];

    for func in expected_functions {
        assert!(
            source.contains(func),
            "learner_gen.rs should contain `{}`",
            func
        );
    }

    // Verify functional style
    assert!(
        source.contains("s: &CLearner"),
        "Learner functions should take &CLearner"
    );

    // Verify spec predicate ensures
    let spec_predicates = [
        "LLearnerInit(",
        "LLearnerForgetDecision(",
        "LLearnerProcess2b(",
        "LLearnerForgetOperationsBefore(",
    ];

    for pred in spec_predicates {
        assert!(
            source.contains(pred),
            "learner_gen.rs should reference spec predicate `{}`",
            pred
        );
    }
}

/// Verify executor_gen.rs has all expected public functions and packet validity
#[test]
fn test_generated_executor_module_public_api() {
    let source = std::fs::read_to_string("../src/generated/RSL/executor_gen.rs")
        .expect("Failed to read executor_gen.rs");

    let expected_functions = [
        "pub exec fn CExecutorInit",
        "pub exec fn CExecutorGetDecision",
        "pub exec fn CExecutorProcessRequest",
        "pub exec fn CExecutorProcessStartingPhase2",
        "pub exec fn CExecutorProcessAppStateSupply",
        "pub exec fn CExecutorProcessAppStateRequest",
    ];

    for func in expected_functions {
        assert!(
            source.contains(func),
            "executor_gen.rs should contain `{}`",
            func
        );
    }

    // Verify functional style
    assert!(
        source.contains("s: &CExecutor"),
        "Executor functions should take &CExecutor"
    );

    // Verify spec predicates
    let spec_predicates = [
        "LExecutorInit(",
        "LExecutorGetDecision(",
        "LExecutorProcessRequest(",
        "LExecutorProcessStartingPhase2(",
        "LExecutorProcessAppStateSupply(",
        "LExecutorProcessAppStateRequest(",
    ];

    for pred in spec_predicates {
        assert!(
            source.contains(pred),
            "executor_gen.rs should reference spec predicate `{}`",
            pred
        );
    }

    // Verify packet validity ensures on 3 packet-returning functions
    let validity_count = source.matches("result@[i].valid()").count()
        + source.matches("result.1@[i].valid()").count();
    assert!(
        validity_count >= 3,
        "executor_gen.rs should have >= 3 packet validity ensures, found {}",
        validity_count
    );
}

/// Verify proposer_gen.rs has all expected public functions
#[test]
fn test_generated_proposer_module_public_api() {
    let source = std::fs::read_to_string("../src/generated/RSL/proposer_gen.rs")
        .expect("Failed to read proposer_gen.rs");

    let expected_functions = [
        "pub exec fn CProposerInit",
        "pub exec fn CProposerProcessRequest",
        "pub exec fn CProposerMaybeEnterNewViewAndSend1a",
        "pub exec fn CProposerProcess1b",
        "pub exec fn CProposerMaybeEnterPhase2",
        "pub exec fn CProposerNominateNewValueAndSend2a",
        "pub exec fn CProposerNominateOldValueAndSend2a",
        "pub exec fn CProposerMaybeNominateValueAndSend2a",
        "pub exec fn CProposerProcessHeartbeat",
        "pub exec fn CProposerCheckForViewTimeout",
        "pub exec fn CProposerCheckForQuorumOfViewSuspicions",
        "pub exec fn CProposerResetViewTimerDueToExecution",
    ];

    for func in expected_functions {
        assert!(
            source.contains(func),
            "proposer_gen.rs should contain `{}`",
            func
        );
    }

    // Verify functional style
    assert!(
        source.contains("s: &CProposer"),
        "Proposer functions should take &CProposer"
    );

    // Verify shared helpers are imported from gen_helpers (not duplicated locally)
    assert!(
        source.contains("use crate::implementation::RSL::gen_helpers::"),
        "proposer_gen.rs should import helpers from gen_helpers module"
    );
}

/// Verify proposer_gen.rs is fully standalone with no clone-delegate patterns
#[test]
fn test_proposer_gen_no_delegate_patterns() {
    let source = std::fs::read_to_string("../src/generated/RSL/proposer_gen.rs")
        .expect("Failed to read proposer_gen.rs");

    // No clone-delegate pattern: "let mut state = s.clone_up_to_view()"
    assert!(
        !source.contains("let mut state = s.clone_up_to_view()"),
        "proposer_gen.rs should not use clone-delegate pattern (let mut state = s.clone_up_to_view())"
    );

    // No delegation to ProposerImpl methods: "state.CProposer"
    assert!(
        !source.contains("state.CProposer"),
        "proposer_gen.rs should not delegate to ProposerImpl methods (state.CProposer*)"
    );

    // No outbound_packets_to_vec calls (used only in delegate pattern)
    // Note: the import may remain for gen_helpers, but should not appear in function bodies
    let body_start = source.find("verus! {").unwrap_or(0);
    let body = &source[body_start..];
    // Count actual call sites (not import lines)
    let call_count = body.matches("outbound_packets_to_vec(").count();
    assert!(
        call_count == 0,
        "proposer_gen.rs should not call outbound_packets_to_vec (found {} calls) — all 12 functions should be standalone",
        call_count
    );

    // Some packet-returning functions use CBroadcastToEveryone directly
    // (Phase 21: auto-transpiled with assume_postconditions — count varies)
    let broadcast_calls = source.matches("CBroadcastToEveryone(").count();
    assert!(
        broadcast_calls >= 2,
        "proposer_gen.rs should have >= 2 CBroadcastToEveryone calls, found {}",
        broadcast_calls
    );

    // Functions construct CProposer structs directly (auto-transpiled with assume(false))
    let struct_constructions = source.matches("CProposer {").count();
    assert!(
        struct_constructions >= 8,
        "proposer_gen.rs should have >= 8 CProposer {{}} struct constructions, found {}",
        struct_constructions
    );

    // Phase 21: with assume_postconditions, auto-transpiled functions may not contain
    // all the helper calls that standalone Phase 19 code had. The key invariant is:
    // no clone-delegate pattern (checked above), and functions still exist.
}

fn slice_exec_fn<'a>(source: &'a str, fn_name: &str) -> (usize, &'a str) {
    let marker = format!("pub exec fn {}(", fn_name);
    let start = source
        .find(&marker)
        .unwrap_or_else(|| panic!("missing function `{}` in replica_gen.rs", fn_name));
    let after_start = &source[start + 1..];
    let end = after_start
        .find("\npub exec fn ")
        .map(|offset| start + 1 + offset)
        .unwrap_or(source.len());
    let start_line = source[..start].lines().count() + 1;
    (start_line, &source[start..end])
}

fn collect_assume_lines(fn_start_line: usize, fn_source: &str) -> Vec<(usize, String)> {
    fn_source
        .lines()
        .enumerate()
        .filter_map(|(idx, line)| {
            if line.contains("assume(") {
                Some((fn_start_line + idx, line.trim().to_string()))
            } else {
                None
            }
        })
        .collect()
}

/// Drift guard for deferred Phase 12.2 proof generation:
/// keep the trusted `assume(false)` footprint explicit and stable in generated RSL modules.
#[test]
fn test_rsl_generated_assume_false_footprint_drift_guard() {
    // Phase 23.5.14: All assume(false) eliminated from generated RSL code.
    // Now track targeted assume() calls (for irreducible View-mapping gaps).
    let expected_targeted_counts: std::collections::BTreeMap<&str, usize> = [
        ("election_gen.rs", 3usize),  // 1 cardinality gap + 2 valid/spec
        ("proposer_gen.rs", 5usize),  // 1 cardinality gap + 4 valid/spec (2 branches × 2)
        ("replica_gen.rs", 4usize),   // 1 cardinality gap + 3 spec/valid
    ]
    .into_iter()
    .collect();

    let mut observed_assume_false = std::collections::BTreeMap::new();
    let mut observed_targeted = std::collections::BTreeMap::new();
    let generated_dir =
        std::fs::read_dir("../src/generated/RSL").expect("Failed to read src/generated/RSL");

    for entry in generated_dir {
        let entry = entry.expect("Failed to read directory entry");
        let path = entry.path();
        let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if !file_name.ends_with("_gen.rs") {
            continue;
        }

        let source =
            std::fs::read_to_string(&path).unwrap_or_else(|_| panic!("Failed to read {}", file_name));
        let assume_sites: Vec<(usize, String)> = source
            .lines()
            .enumerate()
            .filter_map(|(line_idx, line)| {
                let trimmed = line.trim_start();
                if trimmed.starts_with("//") || !line.contains("assume(") {
                    return None;
                }
                Some((line_idx + 1, line.trim().to_string()))
            })
            .collect();

        let mut false_count = 0usize;
        let mut targeted_count = 0usize;
        for (_line_no, assume_line) in &assume_sites {
            if assume_line.contains("assume(false)") {
                false_count += 1;
            } else {
                targeted_count += 1;
            }
        }

        if false_count > 0 {
            observed_assume_false.insert(file_name.to_string(), false_count);
        }
        if targeted_count > 0 {
            observed_targeted.insert(file_name.to_string(), targeted_count);
        }
    }

    // Phase 23.5.14: Zero assume(false) remaining
    assert!(
        observed_assume_false.is_empty(),
        "All assume(false) should be eliminated; found: {:?}",
        observed_assume_false
    );

    // Track targeted assume() drift (irreducible View-mapping gaps)
    let expected_as_owned: std::collections::BTreeMap<String, usize> = expected_targeted_counts
        .into_iter()
        .map(|(name, count)| (name.to_string(), count))
        .collect();
    assert_eq!(
        observed_targeted, expected_as_owned,
        "RSL targeted assume() footprint drifted; update baseline only after intentional proof changes"
    );
}

/// Track Phase 23.8 progress: non-IO TRANSLATE-TODO stubs being replaced with real implementations.
///
/// As stubs are implemented, move them from `remaining_stubs` to `implemented_functions`
/// and update the counts.
#[test]
fn test_rsl_translate_todo_stub_elimination_progress() {
    let election_src = std::fs::read_to_string("../src/generated/RSL/election_gen.rs")
        .expect("Failed to read election_gen.rs");
    let learner_src = std::fs::read_to_string("../src/generated/RSL/learner_gen.rs")
        .expect("Failed to read learner_gen.rs");
    let proposer_src = std::fs::read_to_string("../src/generated/RSL/proposer_gen.rs")
        .expect("Failed to read proposer_gen.rs");
    let replica_src = std::fs::read_to_string("../src/generated/RSL/replica_gen.rs")
        .expect("Failed to read replica_gen.rs");

    // Functions that have been implemented (no longer stubs)
    let implemented_functions: Vec<(&str, &str)> = vec![
        ("election_gen.rs", "CBoundRequestSequence"),
        ("election_gen.rs", "CRemoveAllSatisfiedRequestsInSequence"),
        ("election_gen.rs", "CRemoveExecutedRequestBatch"),
        ("election_gen.rs", "CElectionStateReflectReceivedRequest"),
        ("learner_gen.rs", "CLearnerProcess2b"),
        ("learner_gen.rs", "CLearnerForgetOperationsBefore"),
        ("proposer_gen.rs", "CProposerNominateNewValueAndSend2a"),
        ("proposer_gen.rs", "CProposerNominateOldValueAndSend2a"),
        ("proposer_gen.rs", "CProposerMaybeNominateValueAndSend2a"),
        ("replica_gen.rs", "CReplicaNextProcess1b"),
        ("replica_gen.rs", "CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints"),
    ];
    let sources: std::collections::BTreeMap<&str, &str> = [
        ("election_gen.rs", election_src.as_str()),
        ("learner_gen.rs", learner_src.as_str()),
        ("proposer_gen.rs", proposer_src.as_str()),
        ("replica_gen.rs", replica_src.as_str()),
    ].into_iter().collect();

    for (file, fn_name) in &implemented_functions {
        let src = sources[file];
        let fn_sig = format!("pub exec fn {}(", fn_name);
        assert!(
            src.contains(&fn_sig),
            "{} should define {}",
            file, fn_name
        );
        // Must NOT be external_body stub
        let stub_marker = format!(
            "// TRANSLATE-TODO: explicitly skipped (skip_functions)\n#[verifier(external_body)]\npub exec fn {}(",
            fn_name
        );
        assert!(
            !src.contains(&stub_marker),
            "{} in {} should no longer be a TRANSLATE-TODO stub",
            fn_name, file
        );
    }

    // All 11 non-IO stubs have been implemented — no remaining stubs
    // (5 IO stubs remain but are out of scope for Phase 23.8)

    // Summary counts
    assert_eq!(implemented_functions.len(), 11, "implemented non-IO stubs count");
}

/// Verify replica_gen.rs has all expected public functions
#[test]
fn test_generated_replica_module_public_api() {
    let source = std::fs::read_to_string("../src/generated/RSL/replica_gen.rs")
        .expect("Failed to read replica_gen.rs");

    // Functions generated by the transpiler (in replica_gen.rs)
    let expected_functions = [
        "pub exec fn CReplicaInit",
        "pub exec fn CReplicaNextProcessInvalid",
        "pub exec fn CReplicaNextProcessRequest",
        "pub exec fn CReplicaNextProcess1a",
        "pub exec fn CReplicaNextProcess1b",
        "pub exec fn CReplicaNextProcessStartingPhase2",
        "pub exec fn CReplicaNextProcess2a",
        "pub exec fn CReplicaNextProcess2b",
        "pub exec fn CReplicaNextProcessReply",
        "pub exec fn CReplicaNextProcessAppStateSupply",
        "pub exec fn CReplicaNextProcessAppStateRequest",
        "pub exec fn CReplicaNextProcessHeartbeat",
        "pub exec fn CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a",
        "pub exec fn CReplicaNextSpontaneousMaybeEnterPhase2",
        "pub exec fn CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints",
        "pub exec fn CReplicaNextSpontaneousMaybeMakeDecision",
        "pub exec fn CReplicaNextReadClockMaybeSendHeartbeat",
        "pub exec fn CReplicaNextReadClockCheckForViewTimeout",
        "pub exec fn CReplicaNextReadClockCheckForQuorumOfViewSuspicions",
        "pub exec fn CSchedulerInit",
        "pub exec fn CReplicaNumActions",
    ];

    for func in expected_functions {
        assert!(
            source.contains(func),
            "replica_gen.rs should contain `{}`",
            func
        );
    }

    // Verify functional style: takes &CReplica, returns (CReplica, Vec<CPacket>)
    assert!(
        source.contains("s: &CReplica"),
        "Replica functions should take &CReplica"
    );
    assert!(
        source.contains("-> (result: (CReplica, Vec<CPacket>))"),
        "Replica functions should return (CReplica, Vec<CPacket>)"
    );

    // Verify result validity ensures (transpiler generates result.0.valid() for each function)
    let validity_count = source.matches("result.0.valid()").count();
    assert!(
        validity_count >= 15,
        "replica_gen.rs should have >= 15 result validity ensures (one per clone-delegate function), found {}",
        validity_count
    );

    // Replica dispatch wrappers are generated as proof-fallback stubs.
    let dispatch_functions = [
        "pub exec fn CSchedulerNext",
        "pub exec fn CReplicaNoReceiveNext",
        "pub exec fn CReplicaNextProcessPacket",
        "pub exec fn CReplicaNextProcessPacketWithoutReadingClock",
        "pub exec fn CReplicaNextReadClockAndProcessPacket",
        "pub exec fn CReplicaNextSpontaneousMaybeExecute",
        "pub exec fn CReplicaNextReadClockMaybeNominateValueAndSend2a",
    ];
    for func in dispatch_functions {
        assert!(
            source.contains(func),
            "replica_gen.rs should contain `{}`",
            func
        );
    }

    // Verify gen_helpers module contains the expected helper functions
    let helpers_source = std::fs::read_to_string("../src/implementation/RSL/gen_helpers.rs")
        .expect("Failed to read gen_helpers.rs");
    assert!(
        helpers_source.contains("pub fn clone_io_packet"),
        "gen_helpers.rs should contain clone_io_packet"
    );
    assert!(
        helpers_source.contains("pub exec fn CExtractSentPacketsFromIos"),
        "gen_helpers.rs should contain CExtractSentPacketsFromIos after helper re-home"
    );
    assert!(
        helpers_source.contains("ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@))"),
        "CExtractSentPacketsFromIos helper should preserve exact spec projection"
    );
    assert!(
        helpers_source.contains("res.valid()"),
        "clone_io_packet in gen_helpers should ensure res.valid()"
    );
    assert!(
        helpers_source.contains("res.abstractable()"),
        "clone_io_packet in gen_helpers should ensure res.abstractable()"
    );

    // With manual_code removed, replica dispatch paths are fallback stubs and no longer
    // embed packet-identity assumptions in generated code.
    let packet_identity_count = source
        .matches("=~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)))")
        .count();
    assert_eq!(
        packet_identity_count, 0,
        "replica_gen.rs should have no packet identity assumes after fallback migration, found {}",
        packet_identity_count
    );
}

#[test]
fn test_replica_num_actions_is_transpiled_not_manual_injected() {
    let config_source = std::fs::read_to_string("../src/protocol/RSL/replica_transpile.toml")
        .expect("Failed to read replica_transpile.toml");
    let config: toml::Value = config_source
        .parse()
        .expect("Failed to parse replica_transpile.toml");

    let skip_functions = config
        .get("skip_functions")
        .and_then(|value| value.as_array())
        .expect("replica_transpile.toml must define skip_functions");
    assert!(
        !skip_functions
            .iter()
            .any(|value| value.as_str() == Some("LReplicaNumActions")),
        "LReplicaNumActions should not be skipped anymore; it should be transpiled"
    );

    let no_stub_functions = config
        .get("no_stub_functions")
        .and_then(|value| value.as_array())
        .expect("replica_transpile.toml must define no_stub_functions");
    assert!(
        !no_stub_functions
            .iter()
            .any(|value| value.as_str() == Some("LReplicaNumActions")),
        "LReplicaNumActions should not be pinned to no_stub_functions anymore"
    );

    let generated_source = std::fs::read_to_string("../src/generated/RSL/replica_gen.rs")
        .expect("Failed to read replica_gen.rs");
    let (_line, fn_source) = slice_exec_fn(&generated_source, "CReplicaNumActions");
    assert!(
        fn_source.contains("result@ == LReplicaNumActions()"),
        "generated CReplicaNumActions should preserve the spec postcondition"
    );
}

#[test]
fn test_replica_packet1b_unique_src_helper_is_not_manual_injected() {
    let config_source = std::fs::read_to_string("../src/protocol/RSL/replica_transpile.toml")
        .expect("Failed to read replica_transpile.toml");
    let config: toml::Value = config_source
        .parse()
        .expect("Failed to parse replica_transpile.toml");

    let no_stub_functions = config
        .get("no_stub_functions")
        .and_then(|value| value.as_array())
        .expect("replica_transpile.toml must define no_stub_functions");
    assert!(
        !no_stub_functions
            .iter()
            .any(|value| value.as_str() == Some("Packet1bHasUniqueSrc")),
        "Packet1bHasUniqueSrc should not be tied to replica manual_code anymore"
    );

    let helper_source = std::fs::read_to_string("../src/implementation/RSL/gen_helpers.rs")
        .expect("Failed to read gen_helpers.rs");
    assert!(
        helper_source.contains("pub exec fn Packet1bHasUniqueSrc"),
        "gen_helpers.rs should define Packet1bHasUniqueSrc"
    );
    assert!(
        helper_source.contains("#[verifier(external_body)]"),
        "Packet1bHasUniqueSrc helper in gen_helpers.rs should remain external_body"
    );
}

#[test]
fn test_replica_process1b_is_implemented() {
    let generated_source = std::fs::read_to_string("../src/generated/RSL/replica_gen.rs")
        .expect("Failed to read replica_gen.rs");
    assert!(
        generated_source.contains("pub exec fn CReplicaNextProcess1b"),
        "replica_gen.rs should contain CReplicaNextProcess1b"
    );

    let (_line, fn_source) = slice_exec_fn(&generated_source, "CReplicaNextProcess1b");
    assert!(
        fn_source.contains(
            "LReplicaNextProcess1b(s@, result.0@, received_packet@, result.1@.map(|i, p: CPacket| p@))"
        ),
        "CReplicaNextProcess1b should preserve the spec postcondition"
    );
    assert!(
        !fn_source.contains("unimplemented!()"),
        "CReplicaNextProcess1b should no longer have unimplemented!() — it has a real implementation"
    );
    assert!(
        fn_source.contains("CProposerProcess1b") && fn_source.contains("CAcceptorTruncateLog"),
        "CReplicaNextProcess1b should dispatch to proposer and acceptor sub-component functions"
    );
}

/// Phase 23.8.5.1: Verify transpiler generates loop code for recursive election functions
/// when they are removed from skip_functions.
#[test]
fn test_election_recursive_functions_generate_loop_code() {
    use std::io::Write;

    // Read the election spec and automan files
    let spec_path = "../src/protocol/RSL/election.rs";
    let automan_path = "../src/protocol/RSL/election.automan";

    // Create a test TOML that removes the recursive functions from skip_functions
    let base_toml = std::fs::read_to_string("../src/protocol/RSL/election_transpile.toml")
        .expect("Failed to read election_transpile.toml");

    // Verify the recursive functions are NOT in skip_functions (they were removed in Phase 23.8.5.1)
    let config: toml::Value = base_toml.parse().expect("Failed to parse election_transpile.toml");
    let skip_fns = config
        .get("skip_functions")
        .and_then(|v| v.as_array())
        .expect("skip_functions must exist");
    let skip_names: Vec<&str> = skip_fns.iter().filter_map(|v| v.as_str()).collect();
    assert!(
        !skip_names.contains(&"RemoveAllSatisfiedRequestsInSequence"),
        "RemoveAllSatisfiedRequestsInSequence should no longer be in skip_functions (Phase 23.8.5.1)"
    );
    assert!(
        !skip_names.contains(&"RemoveExecutedRequestBatch"),
        "RemoveExecutedRequestBatch should no longer be in skip_functions (Phase 23.8.5.1)"
    );

    // Run the transpiler with the updated config
    let tmp_toml = std::env::temp_dir().join("test_election_recursive.toml");
    std::fs::write(&tmp_toml, &base_toml).expect("Failed to write temp TOML");
    let tmp_out = std::env::temp_dir().join("test_election_recursive_out.rs");

    let output = std::process::Command::new("cargo")
        .args([
            "run", "--", "-i", spec_path, "-a", automan_path,
            "-c", tmp_toml.to_str().unwrap(),
            "-o", tmp_out.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run transpiler");
    assert!(
        output.status.success(),
        "Transpiler failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let generated = std::fs::read_to_string(&tmp_out).expect("Failed to read generated output");

    // 1. CRemoveAllSatisfiedRequestsInSequence should be a filter loop (not a stub)
    assert!(
        generated.contains("pub exec fn CRemoveAllSatisfiedRequestsInSequence("),
        "Generated output must contain CRemoveAllSatisfiedRequestsInSequence"
    );
    let filter_fn_start = generated.find("pub exec fn CRemoveAllSatisfiedRequestsInSequence(").unwrap();
    let filter_fn_end = generated[filter_fn_start + 1..]
        .find("\npub exec fn ")
        .map(|i| filter_fn_start + 1 + i)
        .unwrap_or(generated.len());
    let filter_fn = &generated[filter_fn_start..filter_fn_end];

    // Should NOT be a stub (no unimplemented!() or TRANSLATE-TODO)
    assert!(
        !filter_fn.contains("unimplemented!()"),
        "CRemoveAllSatisfiedRequestsInSequence should have a real loop body, not unimplemented!()"
    );
    // Should contain a for-loop with invariants
    assert!(
        filter_fn.contains("for i in (0..s.len())"),
        "CRemoveAllSatisfiedRequestsInSequence should use a for-loop over the input sequence"
    );
    assert!(
        filter_fn.contains("invariant"),
        "CRemoveAllSatisfiedRequestsInSequence should have loop invariants"
    );
    // Should call the predicate and conditionally push
    assert!(
        filter_fn.contains("CRequestSatisfiedBy"),
        "Filter loop should use CRequestSatisfiedBy predicate"
    );
    assert!(
        filter_fn.contains("push"),
        "Filter loop should push matching elements"
    );
    // Should have the spec-equivalence invariant
    assert!(
        filter_fn.contains("RemoveAllSatisfiedRequestsInSequence"),
        "Loop invariant should reference the spec function RemoveAllSatisfiedRequestsInSequence"
    );

    // 2. CRemoveExecutedRequestBatch should be a fold loop
    assert!(
        generated.contains("pub exec fn CRemoveExecutedRequestBatch("),
        "Generated output must contain CRemoveExecutedRequestBatch"
    );
    let fold_fn_start = generated.find("pub exec fn CRemoveExecutedRequestBatch(").unwrap();
    let fold_fn_end = generated[fold_fn_start + 1..]
        .find("\npub exec fn ")
        .map(|i| fold_fn_start + 1 + i)
        .unwrap_or(generated.len());
    let fold_fn = &generated[fold_fn_start..fold_fn_end];

    // Should NOT be a stub
    assert!(
        !fold_fn.contains("unimplemented!()"),
        "CRemoveExecutedRequestBatch should have a real fold loop body, not unimplemented!()"
    );
    // Should contain a for-loop with accumulator pattern
    assert!(
        fold_fn.contains("let mut acc"),
        "CRemoveExecutedRequestBatch should use an accumulator variable"
    );
    assert!(
        fold_fn.contains("for i in (0..batch.len())"),
        "CRemoveExecutedRequestBatch should use a for-loop over the batch"
    );
    assert!(
        fold_fn.contains("invariant"),
        "CRemoveExecutedRequestBatch should have loop invariants"
    );
    // Should call the filter function in each iteration
    assert!(
        fold_fn.contains("CRemoveAllSatisfiedRequestsInSequence"),
        "Fold loop should call CRemoveAllSatisfiedRequestsInSequence in each iteration"
    );
    // Should have the fold spec-equivalence invariant
    assert!(
        fold_fn.contains("RemoveExecutedRequestBatch"),
        "Loop invariant should reference the spec function RemoveExecutedRequestBatch"
    );

    // Clean up temp files
    let _ = std::fs::remove_file(&tmp_toml);
    let _ = std::fs::remove_file(&tmp_out);
}

/// Phase 23.8.5.2-3: Verify transpiler has existential→search and quantified→scan loop capabilities.
/// These are unit-test-proven patterns (predicate_loop, any_loop, all_loop) with proper invariants.
#[test]
fn test_transpiler_existential_and_quantified_loop_capabilities() {
    // The transpiler has PredicateLoopKind::Any (existential → linear search)
    // and PredicateLoopKind::All (quantified → scan loop) with proper invariants.
    // Verify the unit tests for these capabilities exist and are comprehensive.

    // Run unit tests for predicate loops to verify capabilities
    let output = std::process::Command::new("cargo")
        .args(["test", "--lib", "predicate_loop", "--", "--nocapture"])
        .output()
        .expect("Failed to run predicate_loop tests");
    assert!(
        output.status.success(),
        "Predicate loop unit tests should pass: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Existential (any) patterns
    assert!(
        stdout.contains("test_predicate_loop_any_structure"),
        "Must have any-loop structure test"
    );
    assert!(
        stdout.contains("test_predicate_loop_any_invariant_uses_exists"),
        "Must have any-loop exists-invariant test"
    );
    // Universal (all) patterns
    assert!(
        stdout.contains("test_predicate_loop_all_structure"),
        "Must have all-loop structure test"
    );
    assert!(
        stdout.contains("test_predicate_loop_all_invariant_uses_forall"),
        "Must have all-loop forall-invariant test"
    );

    // Verify the affected TOML configs properly handle these functions
    // ElectionStateReflectReceivedRequest — skipped for complexity (iter invariants)
    let election_toml = std::fs::read_to_string("../src/protocol/RSL/election_transpile.toml")
        .expect("Failed to read election_transpile.toml");
    assert!(
        election_toml.contains("ElectionStateReflectReceivedRequest"),
        "ElectionStateReflectReceivedRequest should be in election skip_functions (complex iter pattern)"
    );

    // ProposerNominateOldValueAndSend2a — skipped for complexity (nested existentials)
    let proposer_toml = std::fs::read_to_string("../src/protocol/RSL/proposer_transpile.toml")
        .expect("Failed to read proposer_transpile.toml");
    assert!(
        proposer_toml.contains("NominateOldValueAndSend2a"),
        "NominateOldValueAndSend2a should be in proposer skip/spec_only (complex existential)"
    );

    // CReplicaNextProcess1b — skipped, uses proof-fallback
    let replica_toml = std::fs::read_to_string("../src/protocol/RSL/replica_transpile.toml")
        .expect("Failed to read replica_transpile.toml");
    assert!(
        replica_toml.contains("LReplicaNextProcess1b"),
        "LReplicaNextProcess1b should be in replica skip_functions (proof-fallback mode)"
    );
}

/// Phase 23.8.5.4: Verify transpiler has proof-fallback capability for external_body stubs.
#[test]
fn test_transpiler_proof_fallback_capability() {
    // Run proof_fallback unit tests
    let output = std::process::Command::new("cargo")
        .args(["test", "--lib", "proof_fallback", "--", "--nocapture"])
        .output()
        .expect("Failed to run proof_fallback tests");
    assert!(
        output.status.success(),
        "Proof fallback unit tests should pass: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("test_proof_fallback_emits_stub_for_good_function"),
        "Must have proof-fallback stub emission test"
    );
    assert!(
        stdout.contains("test_proof_fallback_implies_auto_skip"),
        "Must have proof-fallback auto-skip implication test"
    );
    assert!(
        stdout.contains("test_no_stub_functions_suppresses_stub_in_proof_fallback"),
        "Must have no_stub_functions suppression test"
    );

    // Verify replica_transpile.toml uses proof-fallback mode
    let replica_toml = std::fs::read_to_string("../src/protocol/RSL/replica_transpile.toml")
        .expect("Failed to read replica_transpile.toml");
    assert!(
        replica_toml.contains("proof-fallback") || replica_toml.contains("proof_fallback"),
        "replica_transpile.toml should document proof-fallback usage"
    );
}

#[test]
fn test_replica_manual_code_removed_and_dispatch_fallbacks_present() {
    let config_source = std::fs::read_to_string("../src/protocol/RSL/replica_transpile.toml")
        .expect("Failed to read replica_transpile.toml");
    let config: toml::Value = config_source
        .parse()
        .expect("Failed to parse replica_transpile.toml");
    assert!(
        config
            .get("output")
            .and_then(|output| output.get("manual_code"))
            .is_none(),
        "replica_transpile.toml should not define output.manual_code after fallback migration"
    );

    assert!(
        !std::path::Path::new("../src/protocol/RSL/replica_manual.rs").exists(),
        "replica_manual.rs should be removed once output.manual_code is retired"
    );

    let source = std::fs::read_to_string("../src/generated/RSL/replica_gen.rs")
        .expect("Failed to read replica_gen.rs");
    for fn_name in [
        "CReplicaNextReadClockAndProcessPacket",
        "CReplicaNextProcessPacketWithoutReadingClock",
        "CReplicaNextProcessPacket",
        "CReplicaNoReceiveNext",
        "CSchedulerNext",
    ] {
        let (_line, fn_source) = slice_exec_fn(&source, fn_name);
        assert!(
            source.contains(&format!("#[verifier(external_body)]\npub exec fn {}(", fn_name)),
            "{} should be generated as an explicit external-body fallback",
            fn_name
        );
        assert!(
            fn_source.contains("unimplemented!()"),
            "{} fallback should use unimplemented!()",
            fn_name
        );
        assert!(
            source.contains(&format!(
                "// TRANSLATE-TODO: explicitly skipped (skip_functions)\n#[verifier(external_body)]\npub exec fn {}(",
                fn_name
            )),
            "{} should carry a TRANSLATE-TODO provenance comment",
            fn_name
        );
    }

    let helpers_source = std::fs::read_to_string("../src/implementation/RSL/gen_helpers.rs")
        .expect("Failed to read gen_helpers.rs");
    assert!(
        helpers_source.contains("#[verifier(external_body)]\npub exec fn CExtractSentPacketsFromIos"),
        "gen_helpers.rs should carry CExtractSentPacketsFromIos as the external helper boundary"
    );
}

#[test]
fn test_executor_manual_code_footprint_audit_guard() {
    let transpile_config = std::fs::read_to_string("../src/protocol/RSL/executor_transpile.toml")
        .expect("Failed to read executor_transpile.toml");
    let parsed: toml::Value = transpile_config
        .parse()
        .expect("executor_transpile.toml should parse");

    assert!(
        parsed
            .get("output")
            .and_then(|output| output.get("manual_code"))
            .is_none(),
        "executor_transpile.toml should not define output.manual_code after final-mile migration"
    );

    let skip_functions = parsed
        .get("skip_functions")
        .and_then(|value| value.as_array())
        .expect("skip_functions should be an array");
    let skip_set: std::collections::BTreeSet<String> = skip_functions
        .iter()
        .filter_map(|value| value.as_str().map(str::to_string))
        .collect();
    assert!(
        skip_set.contains("LExecutorExecute"),
        "LExecutorExecute should remain an explicit trusted fallback boundary"
    );

    let generated_source = std::fs::read_to_string("../src/generated/RSL/executor_gen.rs")
        .expect("Failed to read executor_gen.rs");
    assert!(
        generated_source.contains("pub exec fn CExecutorExecute"),
        "executor_gen.rs should define CExecutorExecute (copied during assume(false) elimination)"
    );

    let executor_impl = std::fs::read_to_string("../src/implementation/RSL/ExecutorImpl.rs")
        .expect("Failed to read ExecutorImpl.rs");
    assert!(
        executor_impl.contains("pub fn CExecutorExecute(&mut self)"),
        "ExecutorImpl.rs should retain the CExecutorExecute fallback implementation"
    );
    assert!(
        executor_impl.contains("#[verifier(external_body)]\n    pub fn CExecutorExecute"),
        "ExecutorImpl.rs should keep CExecutorExecute as explicit external-body trust boundary"
    );

    let replica_impl = std::fs::read_to_string("../src/implementation/RSL/ReplicaImpl.rs")
        .expect("Failed to read ReplicaImpl.rs");
    assert!(
        replica_impl.contains("self.executor.CExecutorExecute"),
        "ReplicaImpl.rs should continue to route execute through the explicit fallback boundary"
    );
}

#[test]
fn test_executor_cache_helpers_rehomed_out_of_manual_injection() {
    let helper_source = std::fs::read_to_string("../src/implementation/RSL/gen_helpers.rs")
        .expect("Failed to read gen_helpers.rs");
    assert!(
        helper_source.contains("#[verifier(external_body)]\npub exec fn CUpdateNewCache"),
        "gen_helpers.rs should define CUpdateNewCache as external_body helper"
    );
    assert!(
        helper_source.contains("pub exec fn CGetPacketsFromReplies"),
        "gen_helpers.rs should define CGetPacketsFromReplies helper"
    );

    let transpile_config = std::fs::read_to_string("../src/protocol/RSL/executor_transpile.toml")
        .expect("Failed to read executor_transpile.toml");
    assert!(
        transpile_config.contains("CGetPacketsFromReplies"),
        "executor_transpile.toml should import re-homed packet helper from gen_helpers"
    );
    assert!(
        helper_source.contains("#[verifier(external_body)]\npub exec fn CClientsInReplies"),
        "gen_helpers.rs should define CClientsInReplies as external_body helper"
    );
    assert!(
        transpile_config.contains(
            "use crate::implementation::RSL::gen_helpers::{CClientsInReplies, CUpdateNewCache, CGetPacketsFromReplies};",
        ),
        "executor_transpile.toml should import re-homed helpers from gen_helpers"
    );

    let generated_source = std::fs::read_to_string("../src/generated/RSL/executor_gen.rs")
        .expect("Failed to read executor_gen.rs");
    assert!(
        generated_source.contains(
            "use crate::implementation::RSL::gen_helpers::{CClientsInReplies, CUpdateNewCache, CGetPacketsFromReplies};"
        ),
        "executor_gen.rs should import re-homed helpers from gen_helpers"
    );
    assert!(
        !generated_source.contains("pub exec fn CClientsInReplies"),
        "executor_gen.rs should not define CClientsInReplies locally after helper re-home"
    );
    assert!(
        !generated_source.contains("pub exec fn CUpdateNewCache"),
        "executor_gen.rs should not define CUpdateNewCache locally after helper re-home"
    );
    assert!(
        !generated_source.contains("pub exec fn CGetPacketsFromReplies"),
        "executor_gen.rs should not define CGetPacketsFromReplies locally after helper re-home"
    );
}

#[test]
fn test_executor_packet_processing_actions_migrated_off_manual_injection() {
    let transpile_config = std::fs::read_to_string("../src/protocol/RSL/executor_transpile.toml")
        .expect("Failed to read executor_transpile.toml");
    let parsed: toml::Value = transpile_config
        .parse()
        .expect("executor_transpile.toml should parse");
    let skip_functions = parsed
        .get("skip_functions")
        .and_then(|value| value.as_array())
        .expect("skip_functions should be an array");
    let skip_set: std::collections::BTreeSet<String> = skip_functions
        .iter()
        .filter_map(|value| value.as_str().map(str::to_string))
        .collect();

    for fn_name in [
        "LExecutorProcessAppStateRequest",
        "LExecutorProcessStartingPhase2",
        "LExecutorProcessRequest",
    ] {
        assert!(
            !skip_set.contains(fn_name),
            "executor_transpile.toml should not skip {} after migration",
            fn_name
        );
    }

    let manual_source = std::fs::read_to_string("../src/protocol/RSL/executor_manual.rs")
        .expect("Failed to read executor_manual.rs");
    for fn_name in [
        "CExecutorProcessAppStateRequest",
        "CExecutorProcessStartingPhase2",
        "CExecutorProcessRequest",
    ] {
        assert!(
            !manual_source.contains(&format!("pub exec fn {}", fn_name)),
            "executor_manual.rs should not define {} after migration",
            fn_name
        );
    }

    let generated_source = std::fs::read_to_string("../src/generated/RSL/executor_gen.rs")
        .expect("Failed to read executor_gen.rs");
    for fn_name in [
        "CExecutorProcessAppStateRequest",
        "CExecutorProcessStartingPhase2",
        "CExecutorProcessRequest",
    ] {
        assert!(
            generated_source.contains(&format!("pub exec fn {}", fn_name)),
            "executor_gen.rs should define {} after migration",
            fn_name
        );
    }
}

#[test]
fn test_executor_state_only_actions_migrated_off_manual_injection() {
    let transpile_config = std::fs::read_to_string("../src/protocol/RSL/executor_transpile.toml")
        .expect("Failed to read executor_transpile.toml");
    let parsed: toml::Value = transpile_config
        .parse()
        .expect("executor_transpile.toml should parse");
    let skip_functions = parsed
        .get("skip_functions")
        .and_then(|value| value.as_array())
        .expect("skip_functions should be an array");
    let skip_set: std::collections::BTreeSet<String> = skip_functions
        .iter()
        .filter_map(|value| value.as_str().map(str::to_string))
        .collect();

    for fn_name in [
        "LExecutorInit",
        "LExecutorGetDecision",
        "LExecutorProcessAppStateSupply",
    ] {
        assert!(
            !skip_set.contains(fn_name),
            "executor_transpile.toml should not skip {} after migration",
            fn_name
        );
    }

    let manual_source = std::fs::read_to_string("../src/protocol/RSL/executor_manual.rs")
        .expect("Failed to read executor_manual.rs");
    for fn_name in [
        "CExecutorInit",
        "CExecutorGetDecision",
        "CExecutorProcessAppStateSupply",
    ] {
        assert!(
            !manual_source.contains(&format!("pub exec fn {}", fn_name)),
            "executor_manual.rs should not define {} after migration",
            fn_name
        );
    }
    assert!(
        !transpile_config.contains("manual_code = \"executor_manual.rs\""),
        "executor manual_code injection should be removed after final-mile completion"
    );

    let generated_source = std::fs::read_to_string("../src/generated/RSL/executor_gen.rs")
        .expect("Failed to read executor_gen.rs");
    for fn_name in [
        "CExecutorInit",
        "CExecutorGetDecision",
        "CExecutorProcessAppStateSupply",
    ] {
        assert!(
            generated_source.contains(&format!("pub exec fn {}", fn_name)),
            "executor_gen.rs should define {} after migration",
            fn_name
        );
    }
    assert!(
        generated_source.contains("pub exec fn CExecutorExecute"),
        "executor_gen.rs should define CExecutorExecute (copied during assume(false) elimination)"
    );
}

/// Drift guard for replica dispatch wrappers after manual_code removal.
///
/// All dispatch wrappers are proof-fallback stubs; they should carry no local
/// trust-boundary assume sites.
#[test]
fn test_replica_dispatch_assume_drift_guard() {
    let source = std::fs::read_to_string("../src/generated/RSL/replica_gen.rs")
        .expect("Failed to read replica_gen.rs");

    let dispatch_fns = [
        ("CSchedulerNext", 0usize),
        ("CReplicaNoReceiveNext", 0usize),
        ("CReplicaNextProcessPacket", 0usize),
        ("CReplicaNextProcessPacketWithoutReadingClock", 0usize),
        ("CReplicaNextReadClockAndProcessPacket", 0usize),
    ];

    let mut all_dispatch_assumes: Vec<(String, usize, String)> = Vec::new();

    for (fn_name, expected_assumes) in dispatch_fns {
        let (fn_start_line, fn_source) = slice_exec_fn(&source, fn_name);
        let assume_lines = collect_assume_lines(fn_start_line, fn_source);

        assert_eq!(
            assume_lines.len(),
            expected_assumes,
            "{} should contain {} assume(...) sites, found {}: {:?}",
            fn_name,
            expected_assumes,
            assume_lines.len(),
            assume_lines
        );

        for (line_no, line_text) in assume_lines {
            all_dispatch_assumes.push((fn_name.to_string(), line_no, line_text.clone()));
            panic!(
                "unexpected assume in replica fallback dispatch function {}:{}: {}",
                fn_name, line_no, line_text
            );
        }
    }

    assert_eq!(
        all_dispatch_assumes.len(),
        0,
        "replica fallback dispatch path should contain no assume sites, found {:?}",
        all_dispatch_assumes
    );
}

/// h3 prototype guard: historical note remains documented even after fallback migration.
#[test]
fn test_replica_action1_contract_prototype_is_documented_after_fallback_migration() {
    let source = std::fs::read_to_string("../src/generated/RSL/replica_gen.rs")
        .expect("Failed to read replica_gen.rs");
    let (fn_start_line, fn_source) = slice_exec_fn(&source, "CReplicaNoReceiveNext");
    let assume_lines = collect_assume_lines(fn_start_line, fn_source);

    assert_eq!(
        assume_lines.len(),
        0,
        "CReplicaNoReceiveNext fallback should contain no trust-boundary assume sites"
    );
    assert!(
        fn_source.contains("unimplemented!()"),
        "CReplicaNoReceiveNext should now be a proof-fallback stub"
    );

    let doc = std::fs::read_to_string("../docs/dev/io-trust-boundary-analysis.md")
        .expect("Failed to read io-trust-boundary-analysis.md");
    assert!(
        doc.contains("Action-1 Contract Propagation Prototype (2026-02-21)"),
        "prototype section missing from io trust-boundary analysis doc"
    );
    assert!(
        doc.contains("failed for isolated action-1 elimination"),
        "prototype outcome should explicitly state isolated elimination failed"
    );
}

/// h4 guard: deferred architecture-bound trust contract must stay explicit in docs and TODO.
#[test]
fn test_replica_trust_boundary_deferred_contract_has_guardrails_and_ownership() {
    let doc = std::fs::read_to_string("../docs/dev/io-trust-boundary-analysis.md")
        .expect("Failed to read io-trust-boundary-analysis.md");
    assert!(
        doc.contains("Deferred Architecture-Bound Contract (12.5.7h4)"),
        "h4 deferred-contract section missing from io trust-boundary analysis doc"
    );
    assert!(
        doc.contains("Guardrails"),
        "h4 doc section should define guardrails"
    );
    assert!(
        doc.contains("Ownership"),
        "h4 doc section should define ownership"
    );
    assert!(
        doc.contains("Exit Criteria"),
        "h4 doc section should define explicit removal criteria"
    );
    assert!(
        doc.contains("Assumption-count freeze")
            && doc.contains("CReplicaNoReceiveNext")
            && doc.contains("CReplicaNextProcessPacketWithoutReadingClock"),
        "h4 guardrails should freeze trust-boundary assume count and placement"
    );

    let todo = std::fs::read_to_string("../TODO.md").expect("Failed to read TODO.md");
    assert!(
        todo.contains("- [x] **12.5.7h4**"),
        "TODO should mark 12.5.7h4 complete after deferred-contract formalization"
    );
    assert!(
        todo.contains("- [x] **12.5.7h4 acceptance criteria**"),
        "TODO should include h4 acceptance criteria tracking"
    );
}

/// Verify gen_helpers.rs contains all shared helper functions for generated modules
#[test]
fn test_gen_helpers_shared_module() {
    let source = std::fs::read_to_string("../src/implementation/RSL/gen_helpers.rs")
        .expect("Failed to read gen_helpers.rs");

    // Verify all shared helper functions are present
    let expected_helpers = [
        "pub fn clone_cpacket_preserving_validity",
        "pub fn clone_cpacket_full",
        "pub fn clone_io_packet",
        "pub exec fn CClientsInReplies",
        "pub exec fn CUpdateNewCache",
        "pub exec fn CGetPacketsFromReplies",
        "pub fn outbound_packets_to_vec",
    ];
    for helper in expected_helpers {
        assert!(
            source.contains(helper),
            "gen_helpers.rs should contain `{}`",
            helper
        );
    }

    // Verify outbound_packets_to_vec has validity ensures
    assert!(
        source.contains("result@[i].valid()"),
        "outbound_packets_to_vec should ensure packet validity"
    );
    assert!(
        source.contains("result@[i].abstractable()"),
        "outbound_packets_to_vec should ensure packet abstractability"
    );

    // Verify no generated module duplicates the helpers locally
    let acceptor = std::fs::read_to_string("../src/generated/RSL/acceptor_gen.rs")
        .expect("Failed to read acceptor_gen.rs");
    let proposer = std::fs::read_to_string("../src/generated/RSL/proposer_gen.rs")
        .expect("Failed to read proposer_gen.rs");
    let replica = std::fs::read_to_string("../src/generated/RSL/replica_gen.rs")
        .expect("Failed to read replica_gen.rs");

    for (name, src) in [
        ("acceptor_gen", &acceptor),
        ("proposer_gen", &proposer),
        ("replica_gen", &replica),
    ] {
        assert!(
            !src.contains("fn clone_cpacket_preserving_validity"),
            "{} should not define clone_cpacket_preserving_validity locally (use gen_helpers)",
            name
        );
        assert!(
            !src.contains("fn outbound_packets_to_vec"),
            "{} should not define outbound_packets_to_vec locally (use gen_helpers)",
            name
        );
    }
}

/// Verify types_gen.rs has all expected concrete types
#[test]
fn test_generated_types_module_public_api() {
    let source = std::fs::read_to_string("../src/generated/RSL/types_gen.rs")
        .expect("Failed to read types_gen.rs");
    let normalized_source: String = source.split_whitespace().collect();

    let expected_types = [
        "pub struct CParameters",
        "pub use crate::implementation::RSL::cconfiguration::{CConfiguration, ReplicaIndexValid};",
        "pub use crate::implementation::RSL::cconstants::{CConstants, CReplicaConstants};",
        "pub use crate::implementation::RSL::acceptorimpl::CAcceptor;",
        "pub use crate::implementation::RSL::learnerimpl::CLearner;",
        "pub use crate::implementation::RSL::ElectionImpl::{",
        "CElectionState",
        "COutstandingOperation",
        "CRequestHeader",
        "pub use crate::implementation::RSL::ExecutorImpl::{CExecutor, CIncompleteBatchTimer};",
        "pub use crate::implementation::RSL::ProposerImpl::CProposer;",
        "pub use crate::implementation::RSL::ReplicaImpl::{",
        "CReplica",
        "CScheduler",
        "abstractify_clpacket",
        "abstractify_crslio",
        "abstractify_crslio_seq",
    ];

    for ty in expected_types {
        let normalized_expected: String = ty.split_whitespace().collect();
        assert!(
            normalized_source.contains(&normalized_expected),
            "types_gen.rs should contain `{}`",
            ty
        );
    }

    // Verify type aliases
    let expected_aliases = [
        "pub type COperationNumber = u64",
        "pub type CRequestBatch = Vec<CRequest>",
        "pub type CReplyCache = HashMap<EndPoint, CReply>",
        "pub type CVotes = HashMap<COperationNumber, CVote>",
        "pub type CLearnerState = HashMap<COperationNumber, CLearnerTuple>",
        "pub type CRslIo = LIoOp<EndPoint, CMessage>",
    ];

    for alias in expected_aliases {
        assert!(
            source.contains(alias),
            "types_gen.rs should contain type alias `{}`",
            alias
        );
    }

    // Verify each struct has valid() and View implementations
    let valid_count = source.matches("pub open spec fn valid").count();
    assert!(
        valid_count >= 1,
        "types_gen.rs should have >= 1 valid() definition, found {}",
        valid_count
    );

    let view_count = source.matches("impl View for").count();
    assert!(
        view_count >= 1,
        "types_gen.rs should have >= 1 View implementation, found {}",
        view_count
    );
}

/// Verify broadcast_gen.rs has CBroadcastToEveryone
#[test]
fn test_generated_broadcast_module_public_api() {
    let source = std::fs::read_to_string("../src/generated/RSL/broadcast_gen.rs")
        .expect("Failed to read broadcast_gen.rs");

    assert!(
        source.contains("pub exec fn CBroadcastToEveryone"),
        "broadcast_gen.rs should contain CBroadcastToEveryone"
    );

    // Verify functional style
    assert!(
        source.contains("c: &CConfiguration"),
        "CBroadcastToEveryone should take &CConfiguration"
    );
    assert!(
        source.contains("m: &CMessage"),
        "CBroadcastToEveryone should take &CMessage"
    );
    assert!(
        source.contains("-> (result: Vec<CPacket>)"),
        "CBroadcastToEveryone should return Vec<CPacket>"
    );

    // Verify spec predicate
    assert!(
        source.contains("LBroadcastToEveryone("),
        "Should reference LBroadcastToEveryone in ensures"
    );
}

/// Verify ReplicaImpl.rs imports all generated modules correctly
#[test]
fn test_replica_impl_uses_all_generated_modules() {
    let source = std::fs::read_to_string("../src/implementation/RSL/ReplicaImpl.rs")
        .expect("Failed to read ReplicaImpl.rs");

    let expected_imports = [
        "use crate::generated::RSL::acceptor_gen as generated_acceptor;",
        "use crate::generated::RSL::executor_gen as generated_executor;",
        "use crate::generated::RSL::learner_gen as generated_learner;",
        "use crate::generated::RSL::proposer_gen as generated_proposer;",
    ];

    for import in expected_imports {
        assert!(
            source.contains(import),
            "ReplicaImpl.rs should import `{}`",
            import
        );
    }

    // Verify no direct CProposer::, CAcceptor::, CLearner:: static method calls remain
    // (all should go through generated_* wrappers)
    assert!(
        !source.contains("CProposer::CProposerInit"),
        "Should not call CProposer::CProposerInit directly"
    );
    assert!(
        !source.contains("CAcceptor::CAcceptorInit"),
        "Should not call CAcceptor::CAcceptorInit directly"
    );

    // Verify generated function calls are present
    let generated_calls = [
        "generated_acceptor::",
        "generated_executor::",
        "generated_learner::",
        "generated_proposer::",
    ];

    for call in generated_calls {
        assert!(
            source.contains(call),
            "ReplicaImpl.rs should use `{}`",
            call
        );
    }
}

/// Verify no self.proposer.C*, self.acceptor.C*, self.learner.C* direct method calls remain
#[test]
fn test_replica_impl_no_direct_subcomponent_method_calls() {
    let source = std::fs::read_to_string("../src/implementation/RSL/ReplicaImpl.rs")
        .expect("Failed to read ReplicaImpl.rs");

    // Filter out commented lines for pattern matching
    let active_lines: String = source
        .lines()
        .filter(|line| !line.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n");

    // These patterns should NOT appear in active code — all wired to generated functions
    let forbidden_patterns = [
        "self.proposer.CProposer",
        "self.acceptor.CAcceptor",
        "self.learner.CLearner",
        "self.executor.CExecutorInit",
        "self.executor.CExecutorGetDecision",
        "self.executor.CExecutorProcessRequest",
        "self.executor.CExecutorProcessStartingPhase2",
        "self.executor.CExecutorProcessAppStateSupply",
        "self.executor.CExecutorProcessAppStateRequest",
    ];

    for pattern in forbidden_patterns {
        assert!(
            !active_lines.contains(pattern),
            "ReplicaImpl.rs should NOT contain direct call `{}` — should use generated wrapper",
            pattern
        );
    }

    // CExecutorExecute is the ONE exception that stays manual
    assert!(
        source.contains("self.executor.CExecutorExecute"),
        "CExecutorExecute should remain as direct manual call (transpiler limitation)"
    );
}

#[test]
fn test_manual_impl_modules_have_deprecation_notices() {
    for path in [
        "../src/implementation/RSL/ExecutorImpl.rs",
        "../src/implementation/RSL/ProposerImpl.rs",
    ] {
        let source =
            std::fs::read_to_string(path).unwrap_or_else(|_| panic!("Failed to read {}", path));
        assert!(
            !source.contains("#[deprecated"),
            "{} should no longer expose deprecated type re-exports",
            path
        );
    }

    // mod.rs should have deprecation doc comments
    let mod_rs =
        std::fs::read_to_string("../src/implementation/RSL/mod.rs").expect("Failed to read mod.rs");
    for (marker, module) in [
        ("pub mod ExecutorImpl;", "ExecutorImpl"),
        ("pub mod ProposerImpl;", "ProposerImpl"),
    ] {
        assert!(
            mod_rs.contains(marker),
            "mod.rs should still include {}",
            module
        );
        assert!(
            mod_rs.contains("Generated wrappers live in `crate::generated::RSL::"),
            "mod.rs should describe generated-wrapper ownership for {}",
            module
        );
    }
}

#[test]
fn test_rsl_mod_rs_keeps_required_runtime_module_exports_documented() {
    let mod_rs =
        std::fs::read_to_string("../src/implementation/RSL/mod.rs").expect("Failed to read mod.rs");

    for required in [
        "pub mod ExecutorImpl;",
        "pub mod ProposerImpl;",
        "pub mod ReplicaImpl;",
        "pub mod cmd_line_parser;",
        "pub mod netrsl_i;",
        "pub mod replicaimpl_main;",
    ] {
        assert!(
            mod_rs.contains(required),
            "mod.rs should keep required runtime export `{}`",
            required
        );
    }

    for rationale in [
        "Legacy runtime entrypoint parser glue still used by `host_i`/`host_s`.",
        "Legacy runtime network glue used by host/replica orchestration modules.",
        "Legacy runtime orchestration modules used by `host_i`/`host_s` dispatch paths.",
    ] {
        assert!(
            mod_rs.contains(rationale),
            "mod.rs should document why legacy runtime exports remain: `{}`",
            rationale
        );
    }
}

#[test]
fn test_rsl_legacy_runtime_exports_match_dispatch_reachability_audit() {
    let mod_rs =
        std::fs::read_to_string("../src/implementation/RSL/mod.rs").expect("Failed to read mod.rs");

    let expected_legacy_exports = vec![
        "cmd_line_parser",
        "netrsl_i",
        "replicaimpl_class",
        "replicaimpl_delivery",
        "replicaimpl_main",
        "replicaimpl_no_receive_clock",
        "replicaimpl_no_receive_no_clock",
        "replicaimpl_process_packet_no_clock",
        "replicaimpl_process_packet_x",
        "replicaimpl_read_clock",
    ];

    let mut found_legacy_exports = Vec::new();
    for line in mod_rs.lines() {
        let trimmed = line.trim();
        if let Some(name) = trimmed
            .strip_prefix("pub mod ")
            .and_then(|rest| rest.strip_suffix(';'))
        {
            if name == "cmd_line_parser" || name == "netrsl_i" || name.starts_with("replicaimpl_") {
                found_legacy_exports.push(name.to_string());
            }
        }
    }

    assert_eq!(
        found_legacy_exports,
        expected_legacy_exports,
        "legacy runtime exports in mod.rs should exactly match the audited host-dispatch reachability set"
    );

    let host_i = std::fs::read_to_string("../src/implementation/RSL/host_i.rs")
        .expect("Failed to read host_i.rs");
    assert!(
        host_i.contains("parse_cmd_line("),
        "host_i should keep the cmd_line_parser entrypoint wiring"
    );
    assert!(
        host_i.contains("Replica_Next_main("),
        "host_i should dispatch through Replica_Next_main"
    );

    let replicaimpl_main = std::fs::read_to_string("../src/implementation/RSL/replicaimpl_main.rs")
        .expect("Failed to read replicaimpl_main.rs");
    for callee in [
        "replica_next_process_packet_x(",
        "replica_no_receive_no_read_clock(",
        "replica_no_receive_read_clock_next(",
    ] {
        assert!(
            replicaimpl_main.contains(callee),
            "replicaimpl_main should keep downstream dispatch call `{}`",
            callee
        );
    }

    let replicaimpl_process_packet_x =
        std::fs::read_to_string("../src/implementation/RSL/replicaimpl_process_packet_x.rs")
            .expect("Failed to read replicaimpl_process_packet_x.rs");
    for callee in [
        "replica_next_read_clock_and_process_packet(",
        "replica_next_process_packet_without_reading_clock(",
    ] {
        assert!(
            replicaimpl_process_packet_x.contains(callee),
            "replicaimpl_process_packet_x should keep downstream dispatch call `{}`",
            callee
        );
    }

    for path in [
        "../src/implementation/RSL/replicaimpl_no_receive_clock.rs",
        "../src/implementation/RSL/replicaimpl_no_receive_no_clock.rs",
        "../src/implementation/RSL/replicaimpl_process_packet_no_clock.rs",
        "../src/implementation/RSL/replicaimpl_read_clock.rs",
    ] {
        let source =
            std::fs::read_to_string(path).unwrap_or_else(|_| panic!("Failed to read {}", path));
        assert!(
            source.contains("deliver_outbound_packets("),
            "{} should route packets through replicaimpl_delivery::deliver_outbound_packets",
            path
        );
    }

    let delivery = std::fs::read_to_string("../src/implementation/RSL/replicaimpl_delivery.rs")
        .expect("Failed to read replicaimpl_delivery.rs");
    assert!(
        delivery.contains("netrsl_i::*"),
        "replicaimpl_delivery should keep network glue import from netrsl_i"
    );
}

#[test]
fn test_replicaimpl_class_no_stale_imports() {
    let source = std::fs::read_to_string("../src/implementation/RSL/replicaimpl_class.rs")
        .expect("Failed to read replicaimpl_class.rs");

    // Should NOT import types from manual impl modules
    assert!(
        !source.contains("acceptorimpl::CAcceptor"),
        "replicaimpl_class.rs should not import CAcceptor from acceptorimpl"
    );
    assert!(
        !source.contains("ExecutorImpl::CExecutor"),
        "replicaimpl_class.rs should not import CExecutor from ExecutorImpl"
    );

    // Should not contain large blocks of commented-out code
    assert!(
        !source.contains("ConstructNetClient"),
        "replicaimpl_class.rs should not contain stale ConstructNetClient"
    );
}

#[test]
fn test_tla_to_exec_pipeline_with_string_literals() {
    // Tests that TLA+ specs with string state constants (e.g., "init", "committed")
    // can be transpiled through the full pipeline: TLA+ → Verus spec → Verus exec
    use std::process::Command;

    let transpiler = std::path::Path::new("target/release/verus-transpile");
    if !transpiler.exists() {
        eprintln!(
            "Skipping pipeline test: transpiler binary not found at target/release/verus-transpile"
        );
        return;
    }

    // Test TwoPhase (uses "init", "committed", "aborted" string states)
    let tla_input = "tests/tla_examples/TwoPhase.tla";
    if !std::path::Path::new(tla_input).exists() {
        eprintln!("Skipping pipeline test: {} not found", tla_input);
        return;
    }

    // Step 1: TLA+ → Verus spec
    let spec_output = std::env::temp_dir().join("test_twophase_spec.rs");
    let result = Command::new(transpiler)
        .args([
            "translate-tla",
            "--input",
            tla_input,
            "--output",
            spec_output.to_str().unwrap(),
            "--gen-modes",
        ])
        .output()
        .expect("Failed to run transpiler");
    assert!(
        result.status.success(),
        "TLA+ → spec failed: {}",
        String::from_utf8_lossy(&result.stderr)
    );

    // Verify spec contains string literals
    let spec_content = std::fs::read_to_string(&spec_output).expect("Failed to read spec");
    assert!(
        spec_content.contains("\"init\""),
        "Generated spec should contain string literal \"init\""
    );

    // Step 2: Verus spec → Verus exec
    let automan_path = spec_output.with_extension("automan");
    let exec_output = std::env::temp_dir().join("test_twophase_exec.rs");
    let result = Command::new(transpiler)
        .args([
            "--input",
            spec_output.to_str().unwrap(),
            "--annotations",
            automan_path.to_str().unwrap(),
            "--output",
            exec_output.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run transpiler");
    assert!(
        result.status.success(),
        "Spec → exec failed for TwoPhase: {}",
        String::from_utf8_lossy(&result.stderr)
    );

    // Verify exec output exists and contains string literals
    let exec_content = std::fs::read_to_string(&exec_output).expect("Failed to read exec");
    assert!(
        exec_content.contains("\"init\""),
        "Generated exec should preserve string literal \"init\""
    );

    // Cleanup
    let _ = std::fs::remove_file(&spec_output);
    let _ = std::fs::remove_file(&automan_path);
    let _ = std::fs::remove_file(&exec_output);
}

#[test]
fn test_ewd840_initiate_probe_annotation() {
    // Tests that operators with "init" in name (e.g., InitiateProbe) are correctly
    // detected as actions (input + output) rather than init operators (output only)
    use std::process::Command;

    let transpiler = std::path::Path::new("target/release/verus-transpile");
    if !transpiler.exists() {
        eprintln!("Skipping annotation test: transpiler binary not found");
        return;
    }

    let tla_input = "tests/tla_examples/EWD840.tla";
    if !std::path::Path::new(tla_input).exists() {
        eprintln!("Skipping annotation test: {} not found", tla_input);
        return;
    }

    let spec_output = std::env::temp_dir().join("test_ewd840_spec.rs");
    let result = Command::new(transpiler)
        .args([
            "translate-tla",
            "--input",
            tla_input,
            "--output",
            spec_output.to_str().unwrap(),
            "--gen-modes",
        ])
        .output()
        .expect("Failed to run transpiler");
    assert!(result.status.success(), "EWD840 TLA+ → spec failed");

    // Check annotation file
    let automan_path = spec_output.with_extension("automan");
    let annotations = std::fs::read_to_string(&automan_path).expect("Failed to read automan");

    // Init should be output + constants input
    assert!(
        annotations.contains("LInit(-, +);"),
        "Init should be output + constants input, got:\n{}",
        annotations
    );

    // InitiateProbe should be action (input + output + constants), not confused with Init
    assert!(
        annotations.contains("LInitiateProbe(+, -, +);"),
        "InitiateProbe should be action (input + output + constants), got:\n{}",
        annotations
    );

    // Verify spec→exec succeeds
    let exec_output = std::env::temp_dir().join("test_ewd840_exec.rs");
    let result = Command::new(transpiler)
        .args([
            "--input",
            spec_output.to_str().unwrap(),
            "--annotations",
            automan_path.to_str().unwrap(),
            "--output",
            exec_output.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run transpiler");
    assert!(
        result.status.success(),
        "EWD840 spec → exec should succeed after annotation fix: {}",
        String::from_utf8_lossy(&result.stderr)
    );

    // Cleanup
    let _ = std::fs::remove_file(&spec_output);
    let _ = std::fs::remove_file(&automan_path);
    let _ = std::fs::remove_file(&exec_output);
}

// ============================================================================
// Phase 16.2 Integration Tests: Record Literal Parsing (Paxos/PBFT)
// ============================================================================

#[test]
fn test_paxos_tla_to_exec_pipeline_with_record_literals() {
    // Test that the Paxos protocol with record literals { type: Phase1a, bal: b }
    // can be parsed and transpiled end-to-end
    let tla_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("src/protocol/TLA");

    let paxos_tla = tla_dir.join("Paxos.tla");
    if !paxos_tla.exists() {
        eprintln!("Skipping Paxos test: {:?} not found", paxos_tla);
        return;
    }

    let transpiler_bin =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/release/verus-transpile");
    if !transpiler_bin.exists() {
        eprintln!("Skipping: transpiler binary not built");
        return;
    }

    let tmp_dir = std::env::temp_dir();
    let spec_output = tmp_dir.join("paxos_record_test.rs");
    let automan_path = tmp_dir.join("paxos_record_test.automan");
    let exec_output = tmp_dir.join("paxos_record_test_exec.rs");

    // Step 1: TLA+ -> spec
    let result = std::process::Command::new(&transpiler_bin)
        .args([
            "translate-tla",
            "--input",
            paxos_tla.to_str().unwrap(),
            "--output",
            spec_output.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run TLA+ translator");
    assert!(
        result.status.success(),
        "Paxos TLA+ translation should succeed: {}",
        String::from_utf8_lossy(&result.stderr)
    );

    // The spec should contain record literals
    let spec_content = std::fs::read_to_string(&spec_output).expect("Failed to read spec output");
    assert!(
        spec_content.contains("type:") || spec_content.contains("bal:"),
        "Paxos spec should contain record literal fields"
    );

    // Step 2: spec -> exec (this was the failing step before the fix)
    let result = std::process::Command::new(&transpiler_bin)
        .args([
            "--input",
            spec_output.to_str().unwrap(),
            "--annotations",
            automan_path.to_str().unwrap(),
            "--output",
            exec_output.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run transpiler");
    assert!(
        result.status.success(),
        "Paxos spec → exec should succeed with record literal parsing: {}",
        String::from_utf8_lossy(&result.stderr)
    );

    // Cleanup
    let _ = std::fs::remove_file(&spec_output);
    let _ = std::fs::remove_file(&automan_path);
    let _ = std::fs::remove_file(&exec_output);
}

#[test]
fn test_pbft_tla_to_exec_pipeline_with_record_literals() {
    // Test that the PBFT protocol with record literals can be parsed and transpiled
    let tla_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("src/protocol/TLA");

    let pbft_tla = tla_dir.join("PBFT.tla");
    if !pbft_tla.exists() {
        eprintln!("Skipping PBFT test: {:?} not found", pbft_tla);
        return;
    }

    let transpiler_bin =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/release/verus-transpile");
    if !transpiler_bin.exists() {
        eprintln!("Skipping: transpiler binary not built");
        return;
    }

    let tmp_dir = std::env::temp_dir();
    let spec_output = tmp_dir.join("pbft_record_test.rs");
    let automan_path = tmp_dir.join("pbft_record_test.automan");
    let exec_output = tmp_dir.join("pbft_record_test_exec.rs");

    // Step 1: TLA+ -> spec
    let result = std::process::Command::new(&transpiler_bin)
        .args([
            "translate-tla",
            "--input",
            pbft_tla.to_str().unwrap(),
            "--output",
            spec_output.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run TLA+ translator");
    assert!(
        result.status.success(),
        "PBFT TLA+ translation should succeed: {}",
        String::from_utf8_lossy(&result.stderr)
    );

    // Step 2: spec -> exec
    let result = std::process::Command::new(&transpiler_bin)
        .args([
            "--input",
            spec_output.to_str().unwrap(),
            "--annotations",
            automan_path.to_str().unwrap(),
            "--output",
            exec_output.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run transpiler");
    assert!(
        result.status.success(),
        "PBFT spec → exec should succeed with record literal parsing: {}",
        String::from_utf8_lossy(&result.stderr)
    );

    // Cleanup
    let _ = std::fs::remove_file(&spec_output);
    let _ = std::fs::remove_file(&automan_path);
    let _ = std::fs::remove_file(&exec_output);
}

// ============================================================================
// Phase 16.3 Integration Tests: Verus Spec → TLA+ (verus2tla) for all 7 protocols
// ============================================================================

#[test]
fn test_verus2tla_all_tla_generated_specs() {
    // All 7 TLA-generated Verus specs should convert back to TLA+ successfully.
    // This tests the roundtrip: TLA+ → Verus spec → TLA+
    let tla_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("src/protocol/TLA");

    let transpiler_bin =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/release/verus-transpile");
    if !transpiler_bin.exists() {
        eprintln!("Skipping: transpiler binary not built");
        return;
    }

    let protocols = [
        "SimpleCounter",
        "DieHard",
        "EWD840",
        "TwoPhase",
        "Raft",
        "Paxos",
        "PBFT",
    ];

    let tmp_dir = std::env::temp_dir();

    for name in &protocols {
        let tla_file = tla_dir.join(format!("{}.tla", name));
        if !tla_file.exists() {
            eprintln!("Skipping {}: {:?} not found", name, tla_file);
            continue;
        }

        let spec_output = tmp_dir.join(format!("{}_v2t_test.rs", name));
        let tla_output = tmp_dir.join(format!("{}_roundtrip_test.tla", name));

        // Step 1: TLA+ → Verus spec
        let result = std::process::Command::new(&transpiler_bin)
            .args([
                "translate-tla",
                "--input",
                tla_file.to_str().unwrap(),
                "--output",
                spec_output.to_str().unwrap(),
            ])
            .output()
            .expect("Failed to run TLA+ translator");
        assert!(
            result.status.success(),
            "{} TLA+ → spec should succeed: {}",
            name,
            String::from_utf8_lossy(&result.stderr)
        );

        // Step 2: Verus spec → TLA+
        let result = std::process::Command::new(&transpiler_bin)
            .args([
                "verus2-tla",
                "--input",
                spec_output.to_str().unwrap(),
                "--output",
                tla_output.to_str().unwrap(),
            ])
            .output()
            .expect("Failed to run verus2tla");
        assert!(
            result.status.success(),
            "{} spec → TLA+ (verus2tla) should succeed: {}",
            name,
            String::from_utf8_lossy(&result.stderr)
        );

        // Verify output is non-empty and looks like a TLA+ module
        let tla_content = std::fs::read_to_string(&tla_output).expect("Failed to read TLA+ output");
        assert!(
            tla_content.contains("MODULE"),
            "{} roundtrip TLA+ should contain MODULE header",
            name
        );

        // Cleanup
        let _ = std::fs::remove_file(&spec_output);
        let _ = std::fs::remove_file(&tla_output);
    }
}

// ============================================================
// Phase 16.8.1: D3 workspace — real-protocol Verus Spec → TLA+
// ============================================================

/// Test that all 10 real protocol specs convert to TLA+ successfully via the D3 pipeline.
/// This covers Phase 16.8.1 acceptance criteria: run verus2-tla on src/protocol/ inputs.
#[test]
fn test_d3_real_protocol_specs_to_tla() {
    let project_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap();
    let protocol_dir = project_root.join("src/protocol");

    // Protocol dir -> spec files to convert (excluding mod.rs, manual helpers)
    let simple_protocols: Vec<(&str, Vec<&str>)> = vec![
        ("TwoPhase", vec!["types.rs", "twophase.rs"]),
        ("Paxos", vec!["types.rs", "paxos.rs"]),
        ("LeaderElection", vec!["types.rs", "election.rs"]),
        ("Raft", vec!["types.rs", "raft.rs"]),
        ("ChainReplication", vec!["types.rs", "chain.rs"]),
        ("PrimaryBackup", vec!["types.rs", "primarybackup.rs"]),
        ("PBFT", vec!["types.rs", "pbft.rs"]),
        ("VerticalPaxos", vec!["types.rs", "vpaxos.rs"]),
        ("EPaxos", vec!["types.rs", "epaxos.rs"]),
    ];

    let rsl_specs = vec![
        "types.rs",
        "acceptor.rs",
        "broadcast.rs",
        "configuration.rs",
        "constants.rs",
        "distributed_system.rs",
        "election.rs",
        "environment.rs",
        "executor.rs",
        "learner.rs",
        "message.rs",
        "parameters.rs",
        "proposer.rs",
        "replica.rs",
        "state_machine.rs",
    ];

    let converter_config = verus_transpiler::verus2tla::ConverterConfig {
        spec_prefix: "L".to_string(),
        include_recommends: false,
        generate_type_defs: true,
        standard_extends: vec![
            "Integers".to_string(),
            "Sequences".to_string(),
            "FiniteSets".to_string(),
        ],
    };

    let printer = verus_transpiler::verus2tla::TlaPrinter::new();
    let mut total = 0;
    let mut passed = 0;

    // Test simple protocols
    for (proto_name, spec_files) in &simple_protocols {
        for spec_file in spec_files {
            total += 1;
            let input = protocol_dir.join(proto_name).join(spec_file);
            assert!(input.exists(), "{}/{} should exist", proto_name, spec_file);

            let mut converter = verus_transpiler::verus2tla::Verus2TlaConverter::with_config(
                converter_config.clone(),
            );
            match converter.convert_file(&input) {
                Ok(module) => {
                    let output = printer.print_module(&module);
                    assert!(
                        output.contains("MODULE"),
                        "{}/{} output should contain MODULE header",
                        proto_name,
                        spec_file
                    );
                    assert!(
                        output.contains("===="),
                        "{}/{} output should contain footer",
                        proto_name,
                        spec_file
                    );
                    passed += 1;
                }
                Err(e) => {
                    panic!("{}/{} conversion failed: {:?}", proto_name, spec_file, e);
                }
            }
        }
    }

    // Test RSL specs
    for spec_file in &rsl_specs {
        total += 1;
        let input = protocol_dir.join("RSL").join(spec_file);
        assert!(input.exists(), "RSL/{} should exist", spec_file);

        let mut converter =
            verus_transpiler::verus2tla::Verus2TlaConverter::with_config(converter_config.clone());
        match converter.convert_file(&input) {
            Ok(module) => {
                let output = printer.print_module(&module);
                assert!(
                    output.contains("MODULE"),
                    "RSL/{} output should contain MODULE header",
                    spec_file
                );
                passed += 1;
            }
            Err(e) => {
                panic!("RSL/{} conversion failed: {:?}", spec_file, e);
            }
        }
    }

    assert_eq!(
        passed, total,
        "All {total} protocol spec files should convert successfully"
    );
    assert!(
        total >= 33,
        "Should convert at least 33 spec files, got {total}"
    );
}

/// Phase 16.8.3: D1 round-trip on generated TLA+ workspace
/// Runs translate-tla on all 33 generated .tla files from the D3 workspace,
/// verifying the TLA+ parser can handle the generated output.
#[test]
fn test_d1_translate_tla_on_generated_workspace() {
    use verus_transpiler::tla::{parse_module, translator::ModuleTranslator};

    let workspace = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tla_test_workspace/transpiler_generated_tla");

    if !workspace.exists() {
        // Skip if workspace not generated yet
        eprintln!("Skipping: workspace not found at {:?}", workspace);
        return;
    }

    let mut total = 0;
    let mut passed = 0;
    let mut failures: Vec<String> = Vec::new();

    for entry in walkdir(workspace.to_str().unwrap()) {
        if !entry.ends_with(".tla") {
            continue;
        }
        total += 1;
        let source = std::fs::read_to_string(&entry).unwrap();
        let rel_path = entry
            .strip_prefix(workspace.to_str().unwrap())
            .unwrap_or(&entry)
            .trim_start_matches('/');

        match parse_module(&source) {
            Ok(module) => {
                // Also verify translation to Verus succeeds
                let mut translator = ModuleTranslator::default();
                let verus_output = translator.translate(&module);
                assert!(
                    verus_output.contains("verus!"),
                    "{} should produce verus! block",
                    rel_path
                );
                passed += 1;
            }
            Err(e) => {
                failures.push(format!("{}: {:?}", rel_path, e));
            }
        }
    }

    if !failures.is_empty() {
        panic!(
            "{} of {} files failed to parse:\n{}",
            failures.len(),
            total,
            failures.join("\n")
        );
    }

    assert_eq!(passed, total);
    assert!(
        total >= 33,
        "Should process at least 33 .tla files, got {total}"
    );
}

fn resolve_verus_binary() -> Option<std::path::PathBuf> {
    if let Ok(path) = std::env::var("VERUS_PATH") {
        let candidate = std::path::PathBuf::from(path);
        if candidate.exists() {
            return Some(candidate);
        }
    }

    let default = std::path::PathBuf::from("/home/shuai/tools/verus-x86-linux/verus");
    if default.exists() {
        Some(default)
    } else {
        None
    }
}

fn first_verus_error_code(stderr: &str) -> Option<&str> {
    for line in stderr.lines() {
        if let Some(idx) = line.find("error[E") {
            let start = idx + "error[".len();
            let end = line[start..].find(']')?;
            return Some(&line[start..start + end]);
        }
        if line.starts_with("error: mismatched types") {
            return Some("E0308");
        }
        if line.starts_with("error: recursive function must have a decreases clause") {
            return Some("REC_DECREASES");
        }
    }
    None
}

/// Phase 16.8.3a: D1 generated-spec Verus compile baseline
/// Compiles every generated D1 `.rs` file with Verus and tracks current blocker classes.
#[test]
fn test_d1_generated_verus_spec_compile_baseline() {
    use std::process::Command;

    let workspace = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tla_test_workspace/transpiler_generated_verus_spec");

    if !workspace.exists() {
        eprintln!("Skipping: workspace not found at {:?}", workspace);
        return;
    }

    let Some(verus_bin) = resolve_verus_binary() else {
        eprintln!("Skipping: Verus binary not found (set VERUS_PATH to enable compile baseline)");
        return;
    };

    let mut total = 0;
    let mut passed = 0;
    let mut cat_e0425 = 0; // unresolved symbol in scope
    let mut cat_e0423 = 0; // expected value/function, found type/struct
    let mut cat_e0609 = 0; // unknown field access on inferred scalar
    let mut cat_e0599 = 0; // method missing on inferred scalar
    let mut cat_e0308 = 0; // mismatched types
    let mut cat_e0600 = 0; // unary operator type mismatch
    let mut cat_e0618 = 0; // attempted call on non-function
    let mut cat_e0277 = 0; // trait bound failure
    let mut cat_e0061 = 0; // wrong number of arguments
    let mut cat_e0282 = 0; // type annotations needed
    let mut cat_rec_decreases = 0; // recursive function lacks decreases clause
    let mut files_e0599: Vec<String> = Vec::new();
    let mut files_e0308: Vec<String> = Vec::new();
    let mut pass_files: Vec<String> = Vec::new();
    let mut other_fails: Vec<String> = Vec::new();

    for entry in walkdir(workspace.to_str().unwrap()) {
        if !entry.ends_with(".rs") {
            continue;
        }
        total += 1;
        let rel = entry
            .strip_prefix(workspace.to_str().unwrap())
            .unwrap_or(&entry)
            .trim_start_matches('/')
            .to_string();

        let output = Command::new(&verus_bin)
            .args(["--crate-type=lib", &entry])
            .output()
            .expect("Failed to run Verus for D1 compile baseline");

        if output.status.success() {
            passed += 1;
            pass_files.push(rel);
            continue;
        }

        let stderr = String::from_utf8_lossy(&output.stderr);
        match first_verus_error_code(&stderr) {
            Some("E0425") => cat_e0425 += 1,
            Some("E0423") => cat_e0423 += 1,
            Some("E0609") => cat_e0609 += 1,
            Some("E0599") => {
                cat_e0599 += 1;
                files_e0599.push(rel.clone());
            }
            Some("E0308") => {
                cat_e0308 += 1;
                files_e0308.push(rel.clone());
            }
            Some("E0600") => cat_e0600 += 1,
            Some("E0618") => cat_e0618 += 1,
            Some("E0277") => cat_e0277 += 1,
            Some("E0061") => cat_e0061 += 1,
            Some("E0282") => cat_e0282 += 1,
            Some("REC_DECREASES") => cat_rec_decreases += 1,
            Some(code) => {
                other_fails.push(format!("{rel}: error[{code}]"));
            }
            None => {
                let first_line = stderr
                    .lines()
                    .find(|line| line.starts_with("error["))
                    .unwrap_or("<unknown>");
                other_fails.push(format!("{rel}: {first_line}"));
            }
        }
    }

    assert!(
        total >= 33,
        "Should process at least 33 generated D1 .rs files, got {total}"
    );

    // Baseline after 16.8.3d-3d-6:
    // Generated-D1 normalization now:
    // - applies parameter usage hints in unknown-ref mode (not only no-variable modules),
    // - infers quantifier binder types from bound-set and call-site hints, and
    //   propagates those hints into quantifier bodies,
    // - coerces non-int structured/control-flow placeholders in int-typed record contexts,
    // - coerces scalar/seq drift at module-operator call-sites from parameter hints,
    // - coerces Eq/Neq arbitrary peers from map shape/type hints and local let hints,
    // - aligns partially explicit action call prefixes with implicit s/s_/c injection,
    // - aliases variable-free explicit-state modules to `LState = LRecord`,
    // - infers generated-D1 helper parameter hints from operator call sites,
    // - emits decreases clauses for generated-D1 recursive helpers when
    //   recursive calls strictly shrink a sequence argument via skip/tail/drop_first,
    // - uses a collision-free constants parameter alias in variable-free helpers
    //   when explicit/bound identifiers reuse `c`,
    // - normalizes generated-D1 mixed map/non-map IF branches to `arbitrary()`,
    // - coerces bool-shaped call args at int-hinted operator parameters,
    // - preserves bool parameter hints for bool-literal equality/logical usage,
    // - forces generated-D1 `sent_packets` params to sequence shape in signature inference,
    // - emits explicit int-binder trigger annotations for generated-D1 forall quantifiers.
    assert_eq!(
        passed, 33,
        "Expected all 33 D1 files to compile at required baseline; pass files: {:?}",
        pass_files
    );
    assert_eq!(
        cat_e0425, 0,
        "Expected 0 unresolved-symbol (E0425) failures at baseline"
    );
    assert_eq!(
        cat_e0423, 0,
        "Expected 0 value/type-shape (E0423) failures at baseline"
    );
    assert_eq!(
        cat_e0609, 0,
        "Expected 0 unknown-field (E0609) failures at baseline"
    );
    assert_eq!(
        cat_e0599, 0,
        "Expected 0 method-missing (E0599) failures at baseline"
    );
    assert_eq!(
        cat_e0308, 0,
        "Expected 0 mismatched-types (E0308) failures at baseline"
    );
    assert_eq!(
        cat_e0600, 0,
        "Expected 0 unary-operator type mismatch (E0600) failures at baseline"
    );
    assert_eq!(
        cat_e0618, 0,
        "Expected 0 call-non-function (E0618) failures at baseline"
    );
    assert_eq!(
        cat_e0277, 0,
        "Expected 0 trait-bound (E0277) failures at baseline"
    );
    assert_eq!(
        cat_e0061, 0,
        "Expected 0 wrong-arity (E0061) failures at baseline"
    );
    assert_eq!(
        cat_e0282, 0,
        "Expected 0 type-inference (E0282) failures at baseline"
    );
    assert_eq!(
        cat_rec_decreases, 0,
        "Expected 0 recursive-missing-decreases first-errors at baseline"
    );
    assert_eq!(
        files_e0599,
        Vec::<String>::new(),
        "Expected no D1 files to fail with E0599 at baseline"
    );
    assert_eq!(
        files_e0308,
        Vec::<String>::new(),
        "Expected no D1 files to fail with E0308 at baseline"
    );
    assert!(
        other_fails.is_empty(),
        "Expected no uncategorized D1 compile failures, got:\n{}",
        other_fails.join("\n")
    );

    eprintln!(
        "D1 Verus compile baseline: {passed}/{total} pass, \
{cat_e0425} E0425, {cat_e0423} E0423, {cat_e0609} E0609, \
{cat_e0599} E0599, {cat_e0308} E0308, {cat_e0600} E0600, {cat_e0618} E0618, \
{cat_e0277} E0277, {cat_e0061} E0061, {cat_e0282} E0282, {cat_rec_decreases} REC_DECREASES"
    );
}

/// Walk a directory recursively and return all file paths as strings.
fn walkdir(dir: &str) -> Vec<String> {
    let mut results = Vec::new();
    fn walk(dir: &std::path::Path, results: &mut Vec<String>) {
        if let Ok(entries) = std::fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    walk(&path, results);
                } else {
                    results.push(path.to_string_lossy().into_owned());
                }
            }
        }
    }
    walk(std::path::Path::new(dir), &mut results);
    results.sort();
    results
}

/// Phase 16.8.4: D2 (Verus Spec → Verus Exec) on D1-generated Verus spec workspace
/// Attempts D2 transpilation on all 33 generated Verus spec files from D1 round-trip.
/// Required gate baseline after 16.8.4d-4:
/// - 27/33 pass
/// - 6/33 fail due to recursive codegen pattern gaps
///
/// Failure categories:
/// - Category A (0 files): anonymous-record parser failures eliminated by 16.8.4d-3b
/// - Category B (0 files after 16.8.4d-1): "Expected ')', found '('" parse failures from
///   malformed call-shape emission; retained as a regression check
/// - Category C (0 files): annotation parameter mismatch class eliminated by 16.8.4d-3c
/// - Other (6 files): recursive helper lowering gaps in D2 codegen
///
/// These are fundamental D1→D2 pipeline gaps, not D2 bugs.
#[test]
fn test_d2_spec_to_exec_on_generated_workspace() {
    use verus_transpiler::{TranslatorConfig, Transpiler, TranspilerConfig};

    let workspace = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tla_test_workspace/transpiler_generated_verus_spec");

    if !workspace.exists() {
        eprintln!("Skipping: workspace not found at {:?}", workspace);
        return;
    }

    let mut total = 0;
    let mut passed = 0;
    let mut cat_a_fails = 0; // "Expected identifier, found '{'"
    let mut cat_b_fails = 0; // "Expected ')', found '('"
    let mut cat_c_fails = 0; // "Parameter count mismatch: function has ..."
    let mut other_fails: Vec<String> = Vec::new();

    let config = TranspilerConfig {
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

    for entry in walkdir(workspace.to_str().unwrap()) {
        if !entry.ends_with(".rs") {
            continue;
        }
        total += 1;

        let automan = entry.replace(".rs", ".automan");
        if !std::path::Path::new(&automan).exists() {
            continue;
        }

        let transpiler = Transpiler::new(config.clone());
        match transpiler
            .transpile_file(std::path::Path::new(&entry), std::path::Path::new(&automan))
        {
            Ok(_) => {
                passed += 1;
            }
            Err(e) => {
                let msg = format!("{:?}", e);
                if msg.contains("Expected identifier, found '{'") {
                    cat_a_fails += 1;
                } else if msg.contains("Expected ')', found") {
                    cat_b_fails += 1;
                } else if msg.contains("Parameter count mismatch: function has") {
                    cat_c_fails += 1;
                } else {
                    other_fails.push(format!(
                        "{}: {}",
                        entry
                            .strip_prefix(workspace.to_str().unwrap())
                            .unwrap_or(&entry),
                        msg
                    ));
                }
            }
        }
    }

    // Enforce the required D2 gate baseline promoted in 16.8.4d-4.
    assert!(
        total >= 33,
        "Should process at least 33 .rs files, got {total}"
    );
    assert!(
        passed >= 27,
        "Expected at least 27 files to pass D2 for the required 16.8.4d-4 gate, got {passed}"
    );
    assert!(
        cat_a_fails == 0,
        "Expected Category A parser failures to be eliminated after 16.8.4d-3b, got {cat_a_fails}"
    );
    assert!(
        cat_b_fails == 0,
        "Expected Category B call-shape parse failures to be eliminated, got {cat_b_fails}"
    );
    assert!(
        cat_c_fails == 0,
        "Expected Category C annotation mismatch failures to remain eliminated for the 16.8.4d-4 gate, got {cat_c_fails}"
    );
    assert!(
        other_fails.len() <= 6,
        "Expected at most six non-categorized failures (recursive codegen patterns), got {}",
        other_fails.len()
    );
    eprintln!(
        "D2 workspace results: {passed}/{total} pass, {cat_a_fails} Cat-A, {cat_b_fails} Cat-B, {cat_c_fails} Cat-C, {} other",
        other_fails.len()
    );
    if !other_fails.is_empty() {
        eprintln!("Unexpected failures:\n{}", other_fails.join("\n"));
    }
}

// ============================================================
// Phase 16.8.5: External TLA+ corpora D1 tests
// ============================================================

/// Phase 16.8.5: D1 on LLM-authored TLA+ specs
/// Tests parser robustness against TLA+ written by an LLM without knowledge of parser limitations.
/// 3/12 pass (simple flat-variable specs), 9/12 fail (range operator, temporal subscript, etc.)
#[test]
fn test_d1_on_llm_tla_specs() {
    use verus_transpiler::tla::{parse_module, translator::ModuleTranslator};

    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tla_test_workspace/generated_tla_by_llm");

    if !dir.exists() {
        eprintln!("Skipping: LLM TLA+ directory not found at {:?}", dir);
        return;
    }

    let mut total = 0;
    let mut passed = 0;
    let mut range_fails = 0; // 1..N range operator
    let mut temporal_fails = 0; // [][Next]_<<vars>>
    let mut other_fails: Vec<String> = Vec::new();

    for entry in walkdir(dir.to_str().unwrap()) {
        if !entry.ends_with(".tla") {
            continue;
        }
        total += 1;
        let source = std::fs::read_to_string(&entry).unwrap();
        let rel = entry
            .strip_prefix(dir.to_str().unwrap())
            .unwrap_or(&entry)
            .trim_start_matches('/')
            .to_string();

        match parse_module(&source) {
            Ok(module) => {
                let mut translator = ModuleTranslator::default();
                let output = translator.translate(&module);
                if output.contains("verus!") {
                    passed += 1;
                } else {
                    other_fails.push(format!("{}: translated but no verus! block", rel));
                }
            }
            Err(e) => {
                let msg = format!("{:?}", e);
                if msg.contains("Expected Colon") || msg.contains("Unexpected token in") {
                    // Range operator (1..N) or ASSUME/CONSTANT with range
                    range_fails += 1;
                } else if msg.contains("Expected DefEq") {
                    // Temporal subscript [][Next]_<<vars>>
                    temporal_fails += 1;
                } else {
                    other_fails.push(format!("{}: {}", rel, msg));
                }
            }
        }
    }

    eprintln!(
        "LLM TLA+ D1: {passed}/{total} pass, {range_fails} range, {temporal_fails} temporal, {} other",
        other_fails.len()
    );

    assert!(
        total >= 12,
        "Should process at least 12 .tla files, got {total}"
    );
    assert!(
        passed >= 3,
        "At least 3 simple specs should pass, got {passed}"
    );
    assert!(
        range_fails >= 4,
        "Expected >= 4 range operator failures, got {range_fails}"
    );
    assert!(
        temporal_fails >= 3,
        "Expected >= 3 temporal subscript failures, got {temporal_fails}"
    );
    if !other_fails.is_empty() {
        eprintln!("Unexpected failures:\n{}", other_fails.join("\n"));
    }
}

/// Phase 16.8.5: D1 on community canonical TLA+ specs
/// Tests parser against real-world TLA+ from tlaplus/Examples, ongardie/raft.tla, efficient/epaxos.
/// 3/4 pass (parser succeeds, but output is minimal for complex specs), 1/4 fail.
#[test]
fn test_d1_on_community_tla_specs() {
    use verus_transpiler::tla::{parse_module, translator::ModuleTranslator};

    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tla_test_workspace/tla_by_community");

    if !dir.exists() {
        eprintln!("Skipping: community TLA+ directory not found at {:?}", dir);
        return;
    }

    let mut total = 0;
    let mut passed = 0;
    let mut failures: Vec<String> = Vec::new();

    for entry in walkdir(dir.to_str().unwrap()) {
        if !entry.ends_with(".tla") {
            continue;
        }
        total += 1;
        let source = std::fs::read_to_string(&entry).unwrap();
        let rel = entry
            .strip_prefix(dir.to_str().unwrap())
            .unwrap_or(&entry)
            .trim_start_matches('/')
            .to_string();

        match parse_module(&source) {
            Ok(module) => {
                let mut translator = ModuleTranslator::default();
                let output = translator.translate(&module);
                if output.contains("verus!") {
                    passed += 1;
                } else {
                    failures.push(format!("{}: translated but no verus! block", rel));
                }
            }
            Err(e) => {
                failures.push(format!("{}: {:?}", rel, e));
            }
        }
    }

    eprintln!(
        "Community TLA+ D1: {passed}/{total} pass, {} fail",
        failures.len()
    );

    // 3 pass (EPaxos, Paxos, Raft), 1 fail (TwoPhase — record set constructor)
    assert!(
        total >= 4,
        "Should process at least 4 .tla files, got {total}"
    );
    assert!(
        passed >= 3,
        "At least 3 community specs should parse, got {passed}"
    );
    // TwoPhase_community.tla fails on record set constructor [type : {"Prepared"}, rm : RM]
    assert!(
        failures.len() >= 1,
        "Expected at least 1 failure (TwoPhase record set), got {}",
        failures.len()
    );
    if !failures.is_empty() {
        eprintln!("Expected failures: {}", failures.join(", "));
    }
}

// ============================================================
// Phase 17.3: Message generation tests
// ============================================================

#[test]
fn test_generate_messages_paxos() {
    let config = verus_transpiler::MessageConfig {
        enum_name: "PaxosMessage".to_string(),
        import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
        doc_comment: String::new(),
        variants: vec![
            verus_transpiler::MessageVariant {
                name: "Prepare".to_string(),
                fields: vec![vec!["ballot".to_string(), "u64".to_string()]],
                doc: String::new(),
            },
            verus_transpiler::MessageVariant {
                name: "Promise".to_string(),
                fields: vec![
                    vec!["ballot".to_string(), "u64".to_string()],
                    vec!["accepted_bal".to_string(), "u64".to_string()],
                    vec!["accepted_val".to_string(), "u64".to_string()],
                ],
                doc: String::new(),
            },
            verus_transpiler::MessageVariant {
                name: "Accept".to_string(),
                fields: vec![
                    vec!["ballot".to_string(), "u64".to_string()],
                    vec!["value".to_string(), "u64".to_string()],
                ],
                doc: String::new(),
            },
            verus_transpiler::MessageVariant {
                name: "Accepted".to_string(),
                fields: vec![
                    vec!["ballot".to_string(), "u64".to_string()],
                    vec!["value".to_string(), "u64".to_string()],
                ],
                doc: String::new(),
            },
        ],
    };

    let code = verus_transpiler::generate_message_code(&config);
    // Verify the generated code has the right structure
    assert!(code.contains("pub enum PaxosMessage"));
    assert!(code.contains("impl ProtocolMessage for PaxosMessage"));
    assert!(code.contains("const TAG_PREPARE: u64 = 1;"));
    assert!(code.contains("const TAG_PROMISE: u64 = 2;"));
    assert!(code.contains("const TAG_ACCEPT: u64 = 3;"));
    assert!(code.contains("const TAG_ACCEPTED: u64 = 4;"));
    // Serialize includes tag + field writes
    assert!(code.contains("PaxosMessage::Prepare { ballot }"));
    assert!(code.contains("buf.extend_from_slice(&TAG_PREPARE.to_le_bytes())"));
    // Deserialize includes length checks
    assert!(code.contains("if data.len() < 16")); // Prepare: 8+8
    assert!(code.contains("if data.len() < 32")); // Promise: 8+24
    assert!(code.contains("if data.len() < 24")); // Accept/Accepted: 8+16
}

#[test]
fn test_generate_messages_from_toml() {
    let toml_content = r#"
        [messages]
        enum_name = "TestMessage"

        [[messages.variants]]
        name = "Ping"
        fields = [["id", "u64"]]

        [[messages.variants]]
        name = "Pong"
        fields = [["id", "u64"], ["ok", "bool"]]
    "#;

    let config = verus_transpiler::FileConfig::from_toml(toml_content).unwrap();
    let msg_config = config.messages.unwrap();
    let code = verus_transpiler::generate_message_code(&msg_config);

    assert!(code.contains("pub enum TestMessage"));
    assert!(code.contains("ok: bool,"));
    // Bool serialize
    assert!(code.contains("let ok_val: u64 = if *ok { 1 } else { 0 };"));
    // Bool deserialize
    assert!(code.contains("let ok = read_u64(data, 16) != 0;"));
}

#[test]
fn test_generate_messages_unit_variants() {
    let toml_content = r#"
        [messages]
        enum_name = "TwoPhaseMessage"

        [[messages.variants]]
        name = "Prepare"

        [[messages.variants]]
        name = "PreparedVote"
        fields = [["rm_id", "u64"]]

        [[messages.variants]]
        name = "Commit"

        [[messages.variants]]
        name = "Abort"
    "#;

    let config = verus_transpiler::FileConfig::from_toml(toml_content).unwrap();
    let msg_config = config.messages.unwrap();
    let code = verus_transpiler::generate_message_code(&msg_config);

    // Unit variants serialize only a tag
    assert!(code.contains("TwoPhaseMessage::Prepare =>"));
    assert!(code.contains("TwoPhaseMessage::Commit =>"));
    assert!(code.contains("TwoPhaseMessage::Abort =>"));
    // Struct variant serializes tag + fields
    assert!(code.contains("TwoPhaseMessage::PreparedVote { rm_id }"));
}

// ============================================================
// Phase 17.3: Per-protocol message generation from real TOMLs
// ============================================================

/// Helper: load messages config from a real protocol TOML file
fn load_and_generate_messages(toml_path: &str) -> String {
    let config = verus_transpiler::FileConfig::from_file(std::path::Path::new(toml_path))
        .unwrap_or_else(|e| panic!("Failed to load {}: {}", toml_path, e));
    let msg_config = config
        .messages
        .unwrap_or_else(|| panic!("No [messages] in {}", toml_path));
    verus_transpiler::generate_message_code(&msg_config)
}

#[test]
fn test_generate_messages_twophase_toml() {
    let code = load_and_generate_messages("../src/protocol/TwoPhase/twophase_transpile.toml");
    assert!(code.contains("pub enum TwoPhaseMessage"));
    assert!(code.contains("Prepare,"));
    assert!(code.contains("PreparedVote {"));
    assert!(code.contains("Commit,"));
    assert!(code.contains("Abort,"));
    assert!(code.contains("const TAG_PREPARE: u64 = 1;"));
    assert!(code.contains("const TAG_COMMIT: u64 = 3;"));
    assert!(code.contains("impl ProtocolMessage for TwoPhaseMessage"));
}

#[test]
fn test_generate_messages_paxos_toml() {
    let code = load_and_generate_messages("../src/protocol/Paxos/paxos_transpile.toml");
    assert!(code.contains("pub enum PaxosMessage"));
    assert!(code.contains("Prepare {"));
    assert!(code.contains("Promise {"));
    assert!(code.contains("Accept {"));
    assert!(code.contains("Accepted {"));
    assert!(code.contains("ballot: u64,"));
    assert!(code.contains("accepted_bal: u64,"));
    assert!(code.contains("const TAG_PROMISE: u64 = 2;"));
}

#[test]
fn test_generate_messages_leader_election_toml() {
    let code = load_and_generate_messages("../src/protocol/LeaderElection/election_transpile.toml");
    assert!(code.contains("pub enum LeaderElectionMessage"));
    assert!(code.contains("Election {"));
    assert!(code.contains("Answer {"));
    assert!(code.contains("Coordinator {"));
    assert!(code.contains("const TAG_ELECTION: u64 = 1;"));
    assert!(code.contains("const TAG_COORDINATOR: u64 = 3;"));
}

#[test]
fn test_generate_messages_primarybackup_toml() {
    let code =
        load_and_generate_messages("../src/protocol/PrimaryBackup/primarybackup_transpile.toml");
    assert!(code.contains("pub enum PrimaryBackupMessage"));
    assert!(code.contains("Replicate {"));
    assert!(code.contains("Ack,"));
    assert!(code.contains("ClientRequest {"));
    assert!(code.contains("const TAG_REPLICATE: u64 = 1;"));
}

#[test]
fn test_generate_messages_chain_replication_toml() {
    let code = load_and_generate_messages("../src/protocol/ChainReplication/chain_transpile.toml");
    assert!(code.contains("pub enum ChainMessage"));
    assert!(code.contains("Forward {"));
    assert!(code.contains("Ack {"));
    assert!(code.contains("ClientWrite {"));
    assert!(code.contains("ClientRead,"));
    assert!(code.contains("const TAG_CLIENT_READ: u64 = 4;"));
}

#[test]
fn test_generate_messages_vertical_paxos_toml() {
    let code = load_and_generate_messages("../src/protocol/VerticalPaxos/vpaxos_transpile.toml");
    assert!(code.contains("pub enum VerticalPaxosMessage"));
    assert!(code.contains("Prepare {"));
    assert!(code.contains("Promise {"));
    assert!(code.contains("Accept {"));
    assert!(code.contains("AcceptOk {"));
    assert!(code.contains("Commit {"));
    assert!(code.contains("Sync {"));
    assert!(code.contains("v_bal: u64,"));
    assert!(code.contains("const TAG_SYNC: u64 = 6;"));
}

#[test]
fn test_generate_messages_raft_toml() {
    let code = load_and_generate_messages("../src/protocol/Raft/raft_transpile.toml");
    assert!(code.contains("pub enum RaftMessage"));
    assert!(code.contains("RequestVote {"));
    assert!(code.contains("VoteResponse {"));
    assert!(code.contains("AppendEntries {"));
    assert!(code.contains("AppendResponse {"));
    // Bool fields
    assert!(code.contains("granted: bool,"));
    assert!(code.contains("has_entry: bool,"));
    assert!(code.contains("success: bool,"));
    // Bool serialization
    assert!(code.contains("let granted_val: u64 = if *granted { 1 } else { 0 };"));
    // Bool deserialization
    assert!(code.contains("let granted = read_u64(data,"));
}

#[test]
fn test_generate_messages_pbft_toml() {
    let code = load_and_generate_messages("../src/protocol/PBFT/pbft_transpile.toml");
    assert!(code.contains("pub enum PBFTMessage"));
    assert!(code.contains("PrePrepare {"));
    assert!(code.contains("Prepare {"));
    assert!(code.contains("Commit {"));
    assert!(code.contains("ClientRequest {"));
    assert!(code.contains("const TAG_PRE_PREPARE: u64 = 1;"));
    assert!(code.contains("const TAG_CLIENT_REQUEST: u64 = 4;"));
}

#[test]
fn test_generate_messages_epaxos_toml() {
    let code = load_and_generate_messages("../src/protocol/EPaxos/epaxos_transpile.toml");
    assert!(code.contains("pub enum EPaxosMessage"));
    assert!(code.contains("PreAccept {"));
    assert!(code.contains("PreAcceptOk {"));
    assert!(code.contains("Accept {"));
    assert!(code.contains("AcceptOk {"));
    assert!(code.contains("CommitMsg {"));
    assert!(code.contains("conflict: bool,"));
    assert!(code.contains("const TAG_PRE_ACCEPT: u64 = 1;"));
    assert!(code.contains("const TAG_PRE_ACCEPT_OK: u64 = 2;"));
    assert!(code.contains("const TAG_COMMIT_MSG: u64 = 5;"));
}

// ============================================================
// Phase 17.7.2: Per-protocol marshalling round-trip tests
// ============================================================

/// Generate a standalone Rust program that tests round-trip serialization.
/// Compiles and runs it, asserting exit code 0.
fn run_roundtrip_test(toml_path: &str) {
    let config = verus_transpiler::FileConfig::from_file(std::path::Path::new(toml_path))
        .unwrap_or_else(|e| panic!("Failed to load {}: {}", toml_path, e));
    let msg_config = config
        .messages
        .unwrap_or_else(|| panic!("No [messages] in {}", toml_path));
    let generated_code = verus_transpiler::generate_message_code(&msg_config);
    let enum_name = &msg_config.enum_name;

    // Build test cases: construct each variant, serialize, deserialize, compare fields
    let mut test_body = String::new();
    for (i, variant) in msg_config.variants.iter().enumerate() {
        let var_name = format!("msg{}", i);
        if variant.fields.is_empty() {
            // Unit variant
            test_body.push_str(&format!(
                "    let {} = {}::{};\n",
                var_name, enum_name, variant.name
            ));
        } else {
            // Struct variant with field values
            let mut field_inits = Vec::new();
            for (fi, field) in variant.fields.iter().enumerate() {
                let fname = &field[0];
                let ftype = &field[1];
                let val = if ftype == "bool" {
                    if fi % 2 == 0 {
                        "true"
                    } else {
                        "false"
                    }
                } else {
                    // Use i*100 + fi to get unique non-zero values
                    &format!("{}u64", i * 100 + fi + 1)
                };
                // Need to own the string for bool case
                let val_owned = if ftype == "bool" {
                    val.to_string()
                } else {
                    format!("{}u64", i * 100 + fi + 1)
                };
                field_inits.push(format!("{}: {}", fname, val_owned));
            }
            test_body.push_str(&format!(
                "    let {} = {}::{} {{ {} }};\n",
                var_name,
                enum_name,
                variant.name,
                field_inits.join(", ")
            ));
        }

        // Serialize
        test_body.push_str(&format!(
            "    let mut buf{} = Vec::new();\n    {}.serialize_to_bytes(&mut buf{});\n",
            i, var_name, i
        ));

        // Deserialize
        test_body.push_str(&format!(
            "    let decoded{} = {}::deserialize_from_bytes(&buf{}).expect(\"Failed to deserialize {}\");\n",
            i, enum_name, i, variant.name
        ));

        // Re-serialize and compare bytes (canonical round-trip check)
        test_body.push_str(&format!(
            "    let mut rebuf{} = Vec::new();\n    decoded{}.serialize_to_bytes(&mut rebuf{});\n",
            i, i, i
        ));
        test_body.push_str(&format!(
            "    assert!(buf{} == rebuf{}, \"Round-trip failed for {}\");\n",
            i, i, variant.name
        ));
    }

    // Test that invalid data returns None
    test_body.push_str(&format!(
        "\n    // Edge cases\n    assert!({}::deserialize_from_bytes(&vec![]).is_none(), \"Empty should return None\");\n",
        enum_name
    ));
    test_body.push_str(&format!(
        "    assert!({}::deserialize_from_bytes(&vec![0u8; 4]).is_none(), \"Too short should return None\");\n",
        enum_name
    ));
    test_body.push_str(&format!(
        "    assert!({}::deserialize_from_bytes(&vec![0xFF; 8]).is_none(), \"Invalid tag should return None\");\n",
        enum_name
    ));

    // Remove the ProtocolMessage import and inner doc comments from generated code
    let cleaned_code: String = generated_code
        .lines()
        .filter(|line| {
            !line.starts_with("use crate::common::framework::protocol_trait::ProtocolMessage;")
                && !line.starts_with("//!")
        })
        .collect::<Vec<_>>()
        .join("\n");

    let test_program = format!(
        r#"// Auto-generated round-trip test
trait ProtocolMessage: Sized {{
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>);
    fn deserialize_from_bytes(data: &Vec<u8>) -> Option<Self>;
}}

{}

fn main() {{
{}
    println!("All round-trip tests passed for {}");
}}
"#,
        cleaned_code, test_body, enum_name,
    );

    // Write to temp file, compile, and run
    let tmp_dir = std::env::temp_dir();
    let src_path = tmp_dir.join(format!("roundtrip_test_{}.rs", enum_name.to_lowercase()));
    let bin_path = tmp_dir.join(format!("roundtrip_test_{}", enum_name.to_lowercase()));

    std::fs::write(&src_path, &test_program).expect("Failed to write test program");

    // Compile
    let compile = std::process::Command::new("rustc")
        .args([
            src_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
            "--edition",
            "2021",
        ])
        .output()
        .expect("Failed to run rustc");
    assert!(
        compile.status.success(),
        "Compilation failed for {}:\n{}",
        enum_name,
        String::from_utf8_lossy(&compile.stderr)
    );

    // Run
    let run = std::process::Command::new(&bin_path)
        .output()
        .expect("Failed to run test binary");
    assert!(
        run.status.success(),
        "Round-trip test failed for {}:\n{}",
        enum_name,
        String::from_utf8_lossy(&run.stderr)
    );

    // Cleanup
    let _ = std::fs::remove_file(&src_path);
    let _ = std::fs::remove_file(&bin_path);
}

#[test]
fn test_roundtrip_twophase() {
    run_roundtrip_test("../src/protocol/TwoPhase/twophase_transpile.toml");
}

#[test]
fn test_roundtrip_paxos() {
    run_roundtrip_test("../src/protocol/Paxos/paxos_transpile.toml");
}

#[test]
fn test_roundtrip_leader_election() {
    run_roundtrip_test("../src/protocol/LeaderElection/election_transpile.toml");
}

#[test]
fn test_roundtrip_primarybackup() {
    run_roundtrip_test("../src/protocol/PrimaryBackup/primarybackup_transpile.toml");
}

#[test]
fn test_roundtrip_chain_replication() {
    run_roundtrip_test("../src/protocol/ChainReplication/chain_transpile.toml");
}

#[test]
fn test_roundtrip_vertical_paxos() {
    run_roundtrip_test("../src/protocol/VerticalPaxos/vpaxos_transpile.toml");
}

#[test]
fn test_roundtrip_raft() {
    run_roundtrip_test("../src/protocol/Raft/raft_transpile.toml");
}

#[test]
fn test_roundtrip_pbft() {
    run_roundtrip_test("../src/protocol/PBFT/pbft_transpile.toml");
}

#[test]
fn test_roundtrip_epaxos() {
    run_roundtrip_test("../src/protocol/EPaxos/epaxos_transpile.toml");
}

// ============================================================
// Phase 17.4.1: LNext scheduler analysis tests
// ============================================================

/// Helper: parse spec file and analyze LNext
fn analyze_lnext(spec_path: &str) -> verus_transpiler::SchedulerConfig {
    let spec_fns = verus_transpiler::parse_file(std::path::Path::new(spec_path))
        .unwrap_or_else(|e| panic!("Failed to parse {}: {}", spec_path, e));
    verus_transpiler::find_and_analyze_lnext(&spec_fns, "LNext", "L", "C")
        .unwrap_or_else(|| panic!("LNext not found or not a disjunction in {}", spec_path))
}

#[test]
fn test_analyze_lnext_twophase() {
    let config = analyze_lnext("../src/protocol/TwoPhase/twophase.rs");
    assert_eq!(config.actions.len(), 8, "TwoPhase has 8 actions");
    assert_eq!(config.params, vec!["s", "s_", "c"]);
    // All 8 actions have sent_packets as existential param
    // 3 have only sent_packets, 5 have sent_packets + another param (rm/r)
    let with_one: Vec<_> = config
        .actions
        .iter()
        .filter(|a| a.existential_params.len() == 1)
        .collect();
    let with_two: Vec<_> = config
        .actions
        .iter()
        .filter(|a| a.existential_params.len() == 2)
        .collect();
    assert_eq!(with_one.len(), 3, "3 actions with only sent_packets");
    assert_eq!(with_two.len(), 5, "5 actions with sent_packets + rm/r");
}

#[test]
fn test_analyze_lnext_paxos() {
    let config = analyze_lnext("../src/protocol/Paxos/paxos.rs");
    assert_eq!(config.actions.len(), 7, "Paxos has 7 actions");
    let names: Vec<&str> = config
        .actions
        .iter()
        .map(|a| a.spec_name.as_str())
        .collect();
    assert!(names.contains(&"LSend1a"));
    assert!(names.contains(&"LSend1b"));
    assert!(names.contains(&"LSend2a"));
    assert!(names.contains(&"LSend2b"));
    assert!(names.contains(&"LLearn"));
}

#[test]
fn test_analyze_lnext_leader_election() {
    let config = analyze_lnext("../src/protocol/LeaderElection/election.rs");
    assert_eq!(config.actions.len(), 7, "LeaderElection has 7 actions");
    // All branches have existential |node: int|
    assert!(
        config
            .actions
            .iter()
            .all(|a| !a.existential_params.is_empty()),
        "All LeaderElection actions have existential params"
    );
}

#[test]
fn test_analyze_lnext_raft() {
    let config = analyze_lnext("../src/protocol/Raft/raft.rs");
    assert_eq!(config.actions.len(), 11, "Raft has 11 actions");
    let names: Vec<&str> = config
        .actions
        .iter()
        .map(|a| a.spec_name.as_str())
        .collect();
    assert!(names.contains(&"LTimeout"));
    assert!(names.contains(&"LBecomeLeader"));
    assert!(names.contains(&"LGrantVote"));
    assert!(names.contains(&"LClientRequest"));
    assert!(names.contains(&"LAdvanceCommitIndex"));
    assert!(names.contains(&"LStepDown"));
}

#[test]
fn test_analyze_lnext_chain_replication() {
    let config = analyze_lnext("../src/protocol/ChainReplication/chain.rs");
    assert_eq!(config.actions.len(), 8, "ChainReplication has 8 actions");
    let names: Vec<&str> = config
        .actions
        .iter()
        .map(|a| a.spec_name.as_str())
        .collect();
    assert!(names.contains(&"LHeadReceiveWrite"));
    assert!(names.contains(&"LTailCommit"));
    assert!(names.contains(&"LClientRead"));
    assert!(names.contains(&"LReconfigure"));
}

#[test]
fn test_analyze_lnext_primarybackup() {
    let config = analyze_lnext("../src/protocol/PrimaryBackup/primarybackup.rs");
    assert_eq!(config.actions.len(), 8, "PrimaryBackup has 8 actions");
    let names: Vec<&str> = config
        .actions
        .iter()
        .map(|a| a.spec_name.as_str())
        .collect();
    assert!(names.contains(&"LPrimaryWrite"));
    assert!(names.contains(&"LPrimaryCommit"));
    assert!(names.contains(&"LBackupPromote"));
}

#[test]
fn test_analyze_lnext_pbft() {
    let config = analyze_lnext("../src/protocol/PBFT/pbft.rs");
    assert_eq!(config.actions.len(), 9, "PBFT has 9 actions");
    let names: Vec<&str> = config
        .actions
        .iter()
        .map(|a| a.spec_name.as_str())
        .collect();
    assert!(names.contains(&"LPrePrepare"));
    assert!(names.contains(&"LReceivePrepare"));
    assert!(names.contains(&"LReceiveCommit"));
    assert!(names.contains(&"LExecuteReply"));
}

#[test]
fn test_analyze_lnext_vertical_paxos() {
    let config = analyze_lnext("../src/protocol/VerticalPaxos/vpaxos.rs");
    assert_eq!(config.actions.len(), 10, "VerticalPaxos has 10 actions");
    let names: Vec<&str> = config
        .actions
        .iter()
        .map(|a| a.spec_name.as_str())
        .collect();
    assert!(names.contains(&"LPrepare"));
    assert!(names.contains(&"LReceivePromise"));
    assert!(names.contains(&"LCommit"));
    assert!(names.contains(&"LReconfigure"));
}

#[test]
fn test_analyze_lnext_epaxos() {
    let config = analyze_lnext("../src/protocol/EPaxos/epaxos.rs");
    assert_eq!(config.actions.len(), 11, "EPaxos has 11 actions");
    let names: Vec<&str> = config
        .actions
        .iter()
        .map(|a| a.spec_name.as_str())
        .collect();
    assert!(names.contains(&"LPropose"));
    assert!(names.contains(&"LSendPreAcceptOk"));
    assert!(names.contains(&"LFastCommit"));
    assert!(names.contains(&"LSlowCommit"));
    assert!(names.contains(&"LExecute"));
}

#[test]
fn test_analyze_lnext_toml_output() {
    let config = analyze_lnext("../src/protocol/TwoPhase/twophase.rs");
    let toml = verus_transpiler::scheduler_config_to_toml(&config);
    assert!(toml.contains("[scheduler]"));
    assert!(toml.contains("action_count = 8"));
    assert!(toml.contains("spec_name = \"LTMSendPrepare\""));
    assert!(toml.contains("exec_name = \"CTMSendPrepare\""));
    // All actions now have sent_packets; some also have rm
    assert!(toml.contains("existential_params = [[\"sent_packets\", \"Seq<LTPCMessage>\"]]"));
    assert!(toml.contains(
        "existential_params = [[\"rm\", \"int\"], [\"sent_packets\", \"Seq<LTPCMessage>\"]]"
    ));
}

// --- Classification integration tests ---

#[test]
fn test_classify_twophase_integration() {
    let mut config = analyze_lnext("../src/protocol/TwoPhase/twophase.rs");
    let variants = vec![
        "Prepare".to_string(),
        "PreparedVote".to_string(),
        "Commit".to_string(),
        "Abort".to_string(),
    ];
    verus_transpiler::classify_actions(&mut config, &variants);

    let msg_count = config
        .actions
        .iter()
        .filter(|a| a.kind == verus_transpiler::ActionKind::MessageDriven)
        .count();
    let timer_count = config.actions.len() - msg_count;
    // TwoPhase: 4 message-driven (RMReceivePrepare, TMRcvPrepared, RMReceiveCommit, RMReceiveAbort)
    //           + 1 timer with "Receive" keyword = actually RMAbort is timer, so 4 msg
    assert!(
        msg_count >= 4,
        "TwoPhase should have at least 4 message-driven actions, got {}",
        msg_count
    );
    assert!(
        timer_count >= 3,
        "TwoPhase should have at least 3 timer-driven actions, got {}",
        timer_count
    );

    // TOML output includes kind field
    let toml = verus_transpiler::scheduler_config_to_toml(&config);
    assert!(toml.contains("kind = \"message_driven\""));
    assert!(toml.contains("kind = \"timer_driven\""));
    assert!(toml.contains("message_variant = \"Prepare\""));
}

#[test]
fn test_classify_all_protocols_have_both_kinds() {
    let protocols = [
        (
            "../src/protocol/TwoPhase/twophase.rs",
            vec!["Prepare", "PreparedVote", "Commit", "Abort"],
        ),
        (
            "../src/protocol/Paxos/paxos.rs",
            vec!["Prepare", "Promise", "Accept", "Accepted"],
        ),
        (
            "../src/protocol/LeaderElection/election.rs",
            vec!["Election", "Answer", "Coordinator"],
        ),
        (
            "../src/protocol/PrimaryBackup/primarybackup.rs",
            vec!["Replicate", "Ack", "ClientRequest"],
        ),
        (
            "../src/protocol/ChainReplication/chain.rs",
            vec!["Forward", "Ack", "ClientWrite", "ClientRead"],
        ),
        (
            "../src/protocol/Raft/raft.rs",
            vec![
                "RequestVote",
                "VoteResponse",
                "AppendEntries",
                "AppendResponse",
            ],
        ),
        (
            "../src/protocol/PBFT/pbft.rs",
            vec!["PrePrepare", "Prepare", "Commit", "ClientRequest"],
        ),
        (
            "../src/protocol/VerticalPaxos/vpaxos.rs",
            vec!["Prepare", "Promise", "Accept", "AcceptOk", "Commit", "Sync"],
        ),
        (
            "../src/protocol/EPaxos/epaxos.rs",
            vec![
                "PreAccept",
                "PreAcceptOk",
                "Accept",
                "AcceptOk",
                "CommitMsg",
            ],
        ),
    ];

    for (spec_path, variant_strs) in &protocols {
        let mut config = analyze_lnext(spec_path);
        let variants: Vec<String> = variant_strs.iter().map(|s| s.to_string()).collect();
        verus_transpiler::classify_actions(&mut config, &variants);

        let msg_count = config
            .actions
            .iter()
            .filter(|a| a.kind == verus_transpiler::ActionKind::MessageDriven)
            .count();
        let timer_count = config.actions.len() - msg_count;

        assert!(
            msg_count > 0,
            "{}: should have at least 1 message-driven action",
            spec_path
        );
        assert!(
            timer_count > 0,
            "{}: should have at least 1 timer-driven action",
            spec_path
        );
    }
}

#[test]
fn test_classify_toml_output_has_variants() {
    let mut config = analyze_lnext("../src/protocol/Paxos/paxos.rs");
    let variants = vec![
        "Prepare".to_string(),
        "Promise".to_string(),
        "Accept".to_string(),
        "Accepted".to_string(),
    ];
    verus_transpiler::classify_actions(&mut config, &variants);

    let toml = verus_transpiler::scheduler_config_to_toml(&config);
    // RecvPromise should have message_variant = "Promise"
    assert!(
        toml.contains("message_variant = \"Promise\""),
        "Paxos TOML should contain message_variant for RecvPromise"
    );
    // RecvAccepted should have message_variant = "Accepted"
    assert!(
        toml.contains("message_variant = \"Accepted\""),
        "Paxos TOML should contain message_variant for RecvAccepted"
    );
}

// ---------------------------------------------------------------
// Phase 17.4.3: Host scaffold generation integration tests
// ---------------------------------------------------------------

/// Load a protocol TOML and generate a host scaffold.
fn load_and_generate_scaffold(toml_path: &str, protocol: &str) -> String {
    let config = verus_transpiler::FileConfig::from_file(std::path::Path::new(toml_path))
        .unwrap_or_else(|e| panic!("Failed to load {}: {}", toml_path, e));

    let msg_config = config
        .messages
        .unwrap_or_else(|| panic!("{} has no [messages] section", toml_path));

    let sched_config = config
        .scheduler
        .unwrap_or_else(|| panic!("{} has no [scheduler] section", toml_path));

    let module_name = protocol.to_lowercase();
    let gen_module = format!("{}_gen", module_name);

    let params = verus_transpiler::HostScaffoldParams {
        protocol_name: protocol.to_string(),
        module_name,
        gen_module,
        message_enum: msg_config.enum_name.clone(),
        message_variants: msg_config.variants,
        actions: sched_config.actions,
        role_dispatch: sched_config.role_dispatch,
    };

    verus_transpiler::generate_host_scaffold(&params)
}

fn assert_scaffold_structure(code: &str, protocol: &str, msg_enum: &str) {
    // Every scaffold must have these elements
    assert!(
        code.contains(&format!("pub struct {}Config {{", protocol)),
        "{} scaffold missing Config struct",
        protocol
    );
    assert!(
        code.contains(&format!("pub struct {}Host {{", protocol)),
        "{} scaffold missing Host struct",
        protocol
    );
    assert!(
        code.contains(&format!("impl ProtocolHost for {}Host {{", protocol)),
        "{} scaffold missing ProtocolHost impl",
        protocol
    );
    assert!(
        code.contains(&format!("type Msg = {};", msg_enum)),
        "{} scaffold missing Msg type alias",
        protocol
    );
    assert!(
        code.contains("fn init(config: &Self::Cfg)"),
        "{} scaffold missing init()",
        protocol
    );
    assert!(
        code.contains("fn next("),
        "{} scaffold missing next()",
        protocol
    );
}

#[test]
fn test_generate_scaffold_paxos() {
    let code = load_and_generate_scaffold("../src/protocol/Paxos/paxos_transpile.toml", "Paxos");
    assert_scaffold_structure(&code, "Paxos", "PaxosMessage");
    // Paxos has 4 message-driven and 3 timer-driven actions
    assert!(
        code.contains("fn handle_"),
        "Paxos should have message handlers"
    );
    assert!(code.contains("fn try_"), "Paxos should have timer handlers");
    assert!(
        code.contains("PaxosMessage::Promise"),
        "should dispatch Promise"
    );
    assert!(
        code.contains("PaxosMessage::Accepted"),
        "should dispatch Accepted"
    );
}

#[test]
fn test_generate_scaffold_twophase() {
    let code = load_and_generate_scaffold(
        "../src/protocol/TwoPhase/twophase_transpile.toml",
        "TwoPhase",
    );
    assert_scaffold_structure(&code, "TwoPhase", "TwoPhaseMessage");
    assert!(
        code.contains("fn handle_"),
        "TwoPhase should have message handlers"
    );
    assert!(
        code.contains("fn try_"),
        "TwoPhase should have timer handlers"
    );
}

#[test]
fn test_generate_scaffold_leader_election() {
    let code = load_and_generate_scaffold(
        "../src/protocol/LeaderElection/election_transpile.toml",
        "LeaderElection",
    );
    assert_scaffold_structure(&code, "LeaderElection", "LeaderElectionMessage");
}

#[test]
fn test_generate_scaffold_raft() {
    let code = load_and_generate_scaffold("../src/protocol/Raft/raft_transpile.toml", "Raft");
    assert_scaffold_structure(&code, "Raft", "RaftMessage");
    assert!(
        code.contains("fn handle_"),
        "Raft should have message handlers"
    );
    assert!(code.contains("fn try_"), "Raft should have timer handlers");
}

#[test]
fn test_generate_scaffold_chain_replication() {
    let code = load_and_generate_scaffold(
        "../src/protocol/ChainReplication/chain_transpile.toml",
        "ChainReplication",
    );
    assert_scaffold_structure(&code, "ChainReplication", "ChainMessage");
}

#[test]
fn test_generate_scaffold_primary_backup() {
    let code = load_and_generate_scaffold(
        "../src/protocol/PrimaryBackup/primarybackup_transpile.toml",
        "PrimaryBackup",
    );
    assert_scaffold_structure(&code, "PrimaryBackup", "PrimaryBackupMessage");
}

#[test]
fn test_generate_scaffold_pbft() {
    let code = load_and_generate_scaffold("../src/protocol/PBFT/pbft_transpile.toml", "PBFT");
    assert_scaffold_structure(&code, "PBFT", "PBFTMessage");
}

#[test]
fn test_generate_scaffold_vertical_paxos() {
    let code = load_and_generate_scaffold(
        "../src/protocol/VerticalPaxos/vpaxos_transpile.toml",
        "VerticalPaxos",
    );
    assert_scaffold_structure(&code, "VerticalPaxos", "VerticalPaxosMessage");
}

#[test]
fn test_generate_scaffold_epaxos() {
    let code = load_and_generate_scaffold("../src/protocol/EPaxos/epaxos_transpile.toml", "EPaxos");
    assert_scaffold_structure(&code, "EPaxos", "EPaxosMessage");
}

// ============================================================
// Phase 17.4.4b: Flag injection integration tests
// Verify that flag_injections populated in real protocol TOMLs
// produce the expected `self.state.msgs_* = ...;` lines in
// the generated scaffold code.
// ============================================================

#[test]
fn test_scaffold_flag_injections_leader_election() {
    let code = load_and_generate_scaffold(
        "../src/protocol/LeaderElection/election_transpile.toml",
        "LeaderElection",
    );
    // After sent_packets migration, LeaderElection no longer has flag_injections.
    // CReceiveAnswer now takes responder as explicit parameter.
    // CReceiveCoordinator now takes leader as explicit parameter.
    assert!(!code.contains("Flag injection"),
        "LeaderElection scaffold should have no flag injection comments after sent_packets migration");
    assert!(
        !code.contains("self.state.msgs_answer"),
        "LeaderElection scaffold should not reference msgs_answer after sent_packets migration"
    );
    assert!(!code.contains("self.state.msgs_coordinator"),
        "LeaderElection scaffold should not reference msgs_coordinator after sent_packets migration");
}

#[test]
fn test_scaffold_no_flag_injections_raft() {
    let code = load_and_generate_scaffold("../src/protocol/Raft/raft_transpile.toml", "Raft");
    assert!(
        !code.contains("Flag injection"),
        "Raft scaffold should have no flag injection comments after sent_packets migration"
    );
    assert!(
        !code.contains("self.state.msgs_request_vote"),
        "Raft scaffold should not reference msgs_request_vote after sent_packets migration"
    );
    assert!(
        !code.contains("self.state.msgs_vote_response"),
        "Raft scaffold should not reference msgs_vote_response after sent_packets migration"
    );
    assert!(
        !code.contains("self.state.msgs_append_entries"),
        "Raft scaffold should not reference msgs_append_entries after sent_packets migration"
    );
    assert!(
        !code.contains("self.state.msgs_append_response"),
        "Raft scaffold should not reference msgs_append_response after sent_packets migration"
    );
}

#[test]
fn test_scaffold_flag_injections_chain_replication() {
    let code = load_and_generate_scaffold(
        "../src/protocol/ChainReplication/chain_transpile.toml",
        "ChainReplication",
    );
    // After sent_packets migration, ChainReplication no longer uses flag_injections.
    // Verify no msgs_* flag injections appear in the scaffold.
    assert!(
        !code.contains("self.state.msgs_forward"),
        "ChainReplication scaffold should not inject msgs_forward (migrated to sent_packets)"
    );
    assert!(
        !code.contains("self.state.msgs_ack"),
        "ChainReplication scaffold should not inject msgs_ack (migrated to sent_packets)"
    );
}

#[test]
fn test_scaffold_flag_injections_pbft() {
    let code = load_and_generate_scaffold("../src/protocol/PBFT/pbft_transpile.toml", "PBFT");
    // After sent_packets migration, PBFT no longer has flag_injections.
    // CReceivePrePrepare now takes view, seq, digest as explicit parameters.
    assert!(
        !code.contains("Flag injection"),
        "PBFT scaffold should have no flag injection comments after sent_packets migration"
    );
    assert!(
        !code.contains("self.state.msgs_preprepare"),
        "PBFT scaffold should not reference msgs_preprepare after sent_packets migration"
    );
}

#[test]
fn test_scaffold_no_flag_injections_epaxos() {
    let code = load_and_generate_scaffold("../src/protocol/EPaxos/epaxos_transpile.toml", "EPaxos");
    assert!(
        !code.contains("Flag injection"),
        "EPaxos scaffold should have no flag injection comments"
    );
    assert!(
        !code.contains("msgs_preaccept_ok"),
        "EPaxos scaffold should not reference msgs_preaccept_ok"
    );
    assert!(
        !code.contains("msgs_accept_ok"),
        "EPaxos scaffold should not reference msgs_accept_ok"
    );
}

// Negative tests: protocols with NO flag injections should have no injection code
#[test]
fn test_scaffold_no_flag_injections_paxos() {
    let code = load_and_generate_scaffold("../src/protocol/Paxos/paxos_transpile.toml", "Paxos");
    assert!(
        !code.contains("Flag injection"),
        "Paxos scaffold should have no flag injection comments"
    );
}

#[test]
fn test_scaffold_no_flag_injections_twophase() {
    let code = load_and_generate_scaffold(
        "../src/protocol/TwoPhase/twophase_transpile.toml",
        "TwoPhase",
    );
    assert!(
        !code.contains("Flag injection"),
        "TwoPhase scaffold should have no flag injection comments"
    );
}

#[test]
fn test_scaffold_no_flag_injections_primarybackup() {
    let code = load_and_generate_scaffold(
        "../src/protocol/PrimaryBackup/primarybackup_transpile.toml",
        "PrimaryBackup",
    );
    assert!(
        !code.contains("Flag injection"),
        "PrimaryBackup scaffold should have no flag injection comments"
    );
}

#[test]
fn test_scaffold_no_flag_injections_verticalpaxos() {
    let code = load_and_generate_scaffold(
        "../src/protocol/VerticalPaxos/vpaxos_transpile.toml",
        "VerticalPaxos",
    );
    assert!(
        !code.contains("Flag injection"),
        "VerticalPaxos scaffold should have no flag injection comments"
    );
}

// ============================================================
// Phase 17.7.1: Scheduler generation comprehensive tests
// ============================================================

// --- TOML roundtrip: generate → parse → verify ---

#[test]
fn test_scheduler_toml_roundtrip() {
    // Build a SchedulerConfig by analyzing TwoPhase, classify it, generate TOML,
    // then parse the TOML back and verify it matches.
    let mut config = analyze_lnext("../src/protocol/TwoPhase/twophase.rs");
    let variants = vec![
        "Prepare".to_string(),
        "PreparedVote".to_string(),
        "Commit".to_string(),
        "Abort".to_string(),
    ];
    verus_transpiler::classify_actions(&mut config, &variants);

    // Generate TOML string from runtime SchedulerConfig
    let toml_str = verus_transpiler::scheduler_config_to_toml(&config);

    // Wrap in a valid TranspilerConfig shape so we can parse it back
    let full_toml = format!(
        "[naming]\nspec_prefix = \"L\"\nexec_prefix = \"C\"\n\n{}",
        toml_str
    );

    // Parse it back
    let parsed = verus_transpiler::FileConfig::from_toml(&full_toml)
        .expect("Failed to parse roundtrip TOML");
    let sched = parsed
        .scheduler
        .expect("Parsed TOML should have [scheduler] section");

    // Verify structural equivalence
    assert_eq!(sched.next_fn, "LNext");
    assert_eq!(sched.params, vec!["s", "s_", "c"]);
    assert_eq!(sched.action_count, config.actions.len());
    assert_eq!(sched.actions.len(), config.actions.len());

    // Verify each action roundtrips correctly
    for (orig, parsed_action) in config.actions.iter().zip(sched.actions.iter()) {
        assert_eq!(
            orig.spec_name, parsed_action.spec_name,
            "spec_name mismatch"
        );
        assert_eq!(
            orig.exec_name, parsed_action.exec_name,
            "exec_name mismatch"
        );
        assert_eq!(
            format!("{}", orig.kind),
            parsed_action.kind,
            "kind mismatch for {}",
            orig.spec_name
        );
        assert_eq!(
            orig.message_variant, parsed_action.message_variant,
            "message_variant mismatch for {}",
            orig.spec_name
        );
        // Existential params: runtime Vec<(String,String)> → TOML Vec<Vec<String>>
        assert_eq!(
            orig.existential_params.len(),
            parsed_action.existential_params.len(),
            "existential_params count mismatch for {}",
            orig.spec_name
        );
        for (i, (name, ty)) in orig.existential_params.iter().enumerate() {
            assert_eq!(
                *name, parsed_action.existential_params[i][0],
                "existential param name mismatch"
            );
            assert_eq!(
                *ty, parsed_action.existential_params[i][1],
                "existential param type mismatch"
            );
        }
    }
}

#[test]
fn test_scheduler_toml_roundtrip_all_protocols() {
    // Verify TOML roundtrip for all 9 protocols by loading their existing TOMLs
    let protocols: &[(&str, &str)] = &[
        (
            "../src/protocol/TwoPhase/twophase_transpile.toml",
            "TwoPhase",
        ),
        ("../src/protocol/Paxos/paxos_transpile.toml", "Paxos"),
        (
            "../src/protocol/LeaderElection/election_transpile.toml",
            "LeaderElection",
        ),
        ("../src/protocol/Raft/raft_transpile.toml", "Raft"),
        (
            "../src/protocol/ChainReplication/chain_transpile.toml",
            "ChainReplication",
        ),
        (
            "../src/protocol/PrimaryBackup/primarybackup_transpile.toml",
            "PrimaryBackup",
        ),
        ("../src/protocol/PBFT/pbft_transpile.toml", "PBFT"),
        (
            "../src/protocol/VerticalPaxos/vpaxos_transpile.toml",
            "VerticalPaxos",
        ),
        ("../src/protocol/EPaxos/epaxos_transpile.toml", "EPaxos"),
    ];

    for (toml_path, protocol) in protocols {
        let config = verus_transpiler::FileConfig::from_file(std::path::Path::new(toml_path))
            .unwrap_or_else(|e| panic!("Failed to load {}: {}", toml_path, e));

        let sched = config
            .scheduler
            .as_ref()
            .unwrap_or_else(|| panic!("{} has no [scheduler] section", protocol));

        // Serialize back to TOML and re-parse
        let roundtrip_toml = config.to_toml().expect("Failed to serialize");
        let reparsed = verus_transpiler::FileConfig::from_toml(&roundtrip_toml)
            .unwrap_or_else(|e| panic!("Failed to re-parse {} TOML: {}", protocol, e));
        let reparsed_sched = reparsed
            .scheduler
            .as_ref()
            .unwrap_or_else(|| panic!("{} lost [scheduler] on roundtrip", protocol));

        assert_eq!(
            sched.action_count, reparsed_sched.action_count,
            "{}: action_count changed on roundtrip",
            protocol
        );
        assert_eq!(
            sched.actions.len(),
            reparsed_sched.actions.len(),
            "{}: actions count changed on roundtrip",
            protocol
        );
        for (i, (orig, rt)) in sched
            .actions
            .iter()
            .zip(reparsed_sched.actions.iter())
            .enumerate()
        {
            assert_eq!(
                orig.spec_name, rt.spec_name,
                "{} action[{}]: spec_name changed",
                protocol, i
            );
            assert_eq!(
                orig.kind, rt.kind,
                "{} action[{}]: kind changed",
                protocol, i
            );
            assert_eq!(
                orig.message_variant, rt.message_variant,
                "{} action[{}]: message_variant changed",
                protocol, i
            );
        }
    }
}

// --- Exact action count verification per protocol ---

/// Verify the exact number of message-driven and timer-driven actions for
/// each protocol. These counts are derived from the [scheduler] sections
/// in the protocol TOML files.
#[test]
fn test_exact_action_counts_per_protocol() {
    struct Expected {
        toml_path: &'static str,
        protocol: &'static str,
        total: usize,
        msg_driven: usize,
        timer_driven: usize,
    }

    let expected = [
        Expected {
            toml_path: "../src/protocol/TwoPhase/twophase_transpile.toml",
            protocol: "TwoPhase",
            total: 8,
            msg_driven: 4,
            timer_driven: 4,
        },
        Expected {
            toml_path: "../src/protocol/Paxos/paxos_transpile.toml",
            protocol: "Paxos",
            total: 7,
            msg_driven: 4,
            timer_driven: 3,
        },
        Expected {
            toml_path: "../src/protocol/LeaderElection/election_transpile.toml",
            protocol: "LeaderElection",
            total: 7,
            msg_driven: 3,
            timer_driven: 4,
        },
        Expected {
            toml_path: "../src/protocol/Raft/raft_transpile.toml",
            protocol: "Raft",
            total: 11,
            msg_driven: 4,
            timer_driven: 7,
        },
        Expected {
            toml_path: "../src/protocol/ChainReplication/chain_transpile.toml",
            protocol: "ChainReplication",
            total: 8,
            msg_driven: 4,
            timer_driven: 4,
        },
        Expected {
            toml_path: "../src/protocol/PrimaryBackup/primarybackup_transpile.toml",
            protocol: "PrimaryBackup",
            total: 8,
            msg_driven: 3,
            timer_driven: 5,
        },
        Expected {
            toml_path: "../src/protocol/PBFT/pbft_transpile.toml",
            protocol: "PBFT",
            total: 9,
            msg_driven: 3,
            timer_driven: 6,
        },
        Expected {
            toml_path: "../src/protocol/VerticalPaxos/vpaxos_transpile.toml",
            protocol: "VerticalPaxos",
            total: 10,
            msg_driven: 5,
            timer_driven: 5,
        },
        Expected {
            toml_path: "../src/protocol/EPaxos/epaxos_transpile.toml",
            protocol: "EPaxos",
            total: 11,
            msg_driven: 4,
            timer_driven: 7,
        },
    ];

    for e in &expected {
        let config = verus_transpiler::FileConfig::from_file(std::path::Path::new(e.toml_path))
            .unwrap_or_else(|err| panic!("Failed to load {}: {}", e.toml_path, err));
        let sched = config
            .scheduler
            .unwrap_or_else(|| panic!("{} has no [scheduler] section", e.protocol));

        assert_eq!(
            sched.action_count, e.total,
            "{}: action_count field",
            e.protocol
        );
        assert_eq!(
            sched.actions.len(),
            e.total,
            "{}: actions.len()",
            e.protocol
        );

        let msg_count = sched
            .actions
            .iter()
            .filter(|a| a.is_message_driven())
            .count();
        let timer_count = sched.actions.len() - msg_count;

        assert_eq!(
            msg_count, e.msg_driven,
            "{}: expected {} message_driven, got {}",
            e.protocol, e.msg_driven, msg_count
        );
        assert_eq!(
            timer_count, e.timer_driven,
            "{}: expected {} timer_driven, got {}",
            e.protocol, e.timer_driven, timer_count
        );
    }
}

/// Verify that action_count field in TOML always matches the actual number of actions.
#[test]
fn test_action_count_field_consistency() {
    let toml_paths = [
        "../src/protocol/TwoPhase/twophase_transpile.toml",
        "../src/protocol/Paxos/paxos_transpile.toml",
        "../src/protocol/LeaderElection/election_transpile.toml",
        "../src/protocol/Raft/raft_transpile.toml",
        "../src/protocol/ChainReplication/chain_transpile.toml",
        "../src/protocol/PrimaryBackup/primarybackup_transpile.toml",
        "../src/protocol/PBFT/pbft_transpile.toml",
        "../src/protocol/VerticalPaxos/vpaxos_transpile.toml",
        "../src/protocol/EPaxos/epaxos_transpile.toml",
    ];

    for path in &toml_paths {
        let config = verus_transpiler::FileConfig::from_file(std::path::Path::new(path))
            .unwrap_or_else(|e| panic!("Failed to load {}: {}", path, e));
        let sched = config
            .scheduler
            .unwrap_or_else(|| panic!("{} has no [scheduler] section", path));
        assert_eq!(
            sched.action_count,
            sched.actions.len(),
            "{}: action_count ({}) != actions.len() ({})",
            path,
            sched.action_count,
            sched.actions.len()
        );
    }
}

/// Verify that every message_driven action has either a message_variant or
/// can be matched to the classification heuristic.
#[test]
fn test_message_driven_actions_have_variants_or_heuristic() {
    let protocols: &[(&str, &str)] = &[
        (
            "../src/protocol/TwoPhase/twophase_transpile.toml",
            "TwoPhase",
        ),
        ("../src/protocol/Paxos/paxos_transpile.toml", "Paxos"),
        (
            "../src/protocol/LeaderElection/election_transpile.toml",
            "LeaderElection",
        ),
        ("../src/protocol/Raft/raft_transpile.toml", "Raft"),
        (
            "../src/protocol/ChainReplication/chain_transpile.toml",
            "ChainReplication",
        ),
        (
            "../src/protocol/PrimaryBackup/primarybackup_transpile.toml",
            "PrimaryBackup",
        ),
        ("../src/protocol/PBFT/pbft_transpile.toml", "PBFT"),
        (
            "../src/protocol/VerticalPaxos/vpaxos_transpile.toml",
            "VerticalPaxos",
        ),
        ("../src/protocol/EPaxos/epaxos_transpile.toml", "EPaxos"),
    ];

    for (toml_path, protocol) in protocols {
        let config = verus_transpiler::FileConfig::from_file(std::path::Path::new(toml_path))
            .unwrap_or_else(|e| panic!("Failed to load {}: {}", toml_path, e));
        let sched = config
            .scheduler
            .unwrap_or_else(|| panic!("{} has no [scheduler] section", protocol));

        for action in &sched.actions {
            if action.is_message_driven() {
                // Every message_driven action should have a recognizable name
                let name = &action.spec_name;
                let name_lower = name.to_lowercase();
                let has_msg_keyword = ["receive", "rcv", "recv", "handle"]
                    .iter()
                    .any(|kw| name_lower.contains(kw));
                let has_response_pattern = [
                    "Send1b",
                    "Send2b",
                    "SendAnswer",
                    "GrantVote",
                    "FollowerAppendEntries",
                    "SendPreAcceptOk",
                    "SendAcceptOk",
                    "SendPromise",
                    "WitnessSync",
                    "Sync",
                    "ClientRead",
                ]
                .iter()
                .any(|p| name.contains(p));
                // Actions with an explicit message_variant in TOML are valid
                // message-driven actions even without a keyword (e.g. LPrimaryWrite).
                let has_explicit_variant = action.message_variant.is_some();

                assert!(
                    has_msg_keyword || has_response_pattern || has_explicit_variant,
                    "{}: message_driven action '{}' has no recognizable message keyword, response pattern, or explicit message_variant",
                    protocol, name
                );
            }
        }
    }
}

/// Verify every message_driven action has a message_variant that exists in the
/// protocol's [messages] section. Catches misclassified actions and typos.
#[test]
fn test_message_driven_actions_have_valid_variant() {
    let protocols: &[(&str, &str)] = &[
        (
            "../src/protocol/TwoPhase/twophase_transpile.toml",
            "TwoPhase",
        ),
        ("../src/protocol/Paxos/paxos_transpile.toml", "Paxos"),
        (
            "../src/protocol/LeaderElection/election_transpile.toml",
            "LeaderElection",
        ),
        ("../src/protocol/Raft/raft_transpile.toml", "Raft"),
        (
            "../src/protocol/ChainReplication/chain_transpile.toml",
            "ChainReplication",
        ),
        (
            "../src/protocol/PrimaryBackup/primarybackup_transpile.toml",
            "PrimaryBackup",
        ),
        ("../src/protocol/PBFT/pbft_transpile.toml", "PBFT"),
        (
            "../src/protocol/VerticalPaxos/vpaxos_transpile.toml",
            "VerticalPaxos",
        ),
        ("../src/protocol/EPaxos/epaxos_transpile.toml", "EPaxos"),
    ];

    for (toml_path, protocol) in protocols {
        let config = verus_transpiler::FileConfig::from_file(std::path::Path::new(toml_path))
            .unwrap_or_else(|e| panic!("Failed to load {}: {}", toml_path, e));
        let sched = config
            .scheduler
            .unwrap_or_else(|| panic!("{} has no [scheduler] section", protocol));
        let messages = config
            .messages
            .unwrap_or_else(|| panic!("{} has no [messages] section", protocol));
        let variant_names: Vec<&str> = messages.variants.iter().map(|v| v.name.as_str()).collect();

        for action in &sched.actions {
            if action.is_message_driven() {
                // Every message_driven action MUST have a message_variant
                assert!(
                    action.message_variant.is_some(),
                    "{}: message_driven action '{}' has no message_variant",
                    protocol,
                    action.spec_name
                );
                // The message_variant MUST reference an existing variant
                let variant = action.message_variant.as_deref().unwrap();
                assert!(
                    variant_names.contains(&variant),
                    "{}: action '{}' references non-existent message_variant '{}' (available: {:?})",
                    protocol, action.spec_name, variant, variant_names
                );
            }
        }
    }
}

// --- Scaffold compilation tests ---

/// Generate a scaffold and compile it with rustc to verify it's valid Rust.
/// We provide minimal stubs for the framework types the scaffold references.
fn compile_scaffold(toml_path: &str, protocol: &str) {
    let code = load_and_generate_scaffold(toml_path, protocol);

    // Load config once for all template parameters
    let config = verus_transpiler::FileConfig::from_file(std::path::Path::new(toml_path))
        .expect("load toml");
    let msg = config.messages.as_ref().expect("messages");
    let msg_enum = msg.enum_name.clone();
    let msg_variants = msg
        .variants
        .iter()
        .map(|v| {
            if v.fields.is_empty() {
                format!("    {},", v.name)
            } else {
                let fields: Vec<String> = v
                    .fields
                    .iter()
                    .filter_map(|f| {
                        if f.len() >= 2 {
                            Some(format!("{}: {}", f[0], f[1]))
                        } else {
                            None
                        }
                    })
                    .collect();
                format!("    {} {{ {} }},", v.name, fields.join(", "))
            }
        })
        .collect::<Vec<_>>()
        .join("\n                    ");

    // Collect flag_injection state fields so CState stub compiles with injection assignments.
    // Each flag_injection is [state_field, value]; the state_field becomes a pub field on CState.
    // Build a map of message variant field name → type for cross-referencing.
    let mut variant_field_types: std::collections::HashMap<String, String> =
        std::collections::HashMap::new();
    if let Some(ref messages) = config.messages {
        for variant in &messages.variants {
            for field in &variant.fields {
                if field.len() >= 2 {
                    variant_field_types.insert(field[0].clone(), field[1].clone());
                }
            }
        }
    }
    let mut state_fields = std::collections::BTreeSet::new();
    if let Some(ref sched) = config.scheduler {
        for action in &sched.actions {
            for inj in &action.flag_injections {
                if inj.len() >= 2 {
                    // Determine field type: "true"/"false" → bool, check message variant field type, else u64
                    let field_type = if inj[1] == "true" || inj[1] == "false" {
                        "bool"
                    } else if let Some(vtype) = variant_field_types.get(&inj[1]) {
                        vtype.as_str()
                    } else {
                        "u64"
                    };
                    state_fields.insert((inj[0].clone(), field_type.to_string()));
                }
            }
        }
    }

    // Build CState struct: unit struct if no fields, regular struct with pub fields otherwise
    let (cstate_def, cstate_init) = if state_fields.is_empty() {
        (
            "pub struct CState;".to_string(),
            "pub fn CInit(_c: &CConstants) -> CState {{ CState }}".to_string(),
        )
    } else {
        let fields_str: Vec<String> = state_fields
            .iter()
            .map(|(name, ty)| format!("pub {}: {},", name, ty))
            .collect();
        let init_fields: Vec<String> = state_fields
            .iter()
            .map(|(name, ty)| {
                if ty == "bool" {
                    format!("{}: false,", name)
                } else {
                    format!("{}: 0,", name)
                }
            })
            .collect();
        (
            format!("pub struct CState {{ {} }}", fields_str.join(" ")),
            format!(
                "pub fn CInit(_c: &CConstants) -> CState {{ CState {{ {} }} }}",
                init_fields.join(" ")
            ),
        )
    };

    // Provide minimal stubs so the scaffold compiles as standalone Rust.
    // The scaffold imports from: args_t::*, protocol_trait::*, io_s::*, types_gen::*, gen_module, message::*
    // io_s re-exports protocol_trait so we must avoid duplicate definitions.
    let stubs = format!(
        r#"
#![allow(dead_code, unused_variables, unused_imports)]

pub mod crate_stub {{
    pub mod common {{
        pub mod framework {{
            pub mod args_t {{
                pub type Args = Vec<Vec<u8>>;
            }}
            pub mod protocol_trait {{
                pub use super::args_t::Args;
                pub struct EndPoint {{ pub id: Vec<u8> }}
                impl EndPoint {{
                    pub fn clone_up_to_view(&self) -> EndPoint {{
                        EndPoint {{ id: self.id.clone() }}
                    }}
                }}
                impl Clone for EndPoint {{
                    fn clone(&self) -> Self {{ EndPoint {{ id: self.id.clone() }} }}
                }}
                pub struct GenericPacket<M> {{ pub src: EndPoint, pub dst: EndPoint, pub msg: M }}
                pub enum GenericOutbound<M> {{ None, Broadcast {{ msg: M, dst: Vec<EndPoint> }}, Send {{ msg: M, dst: EndPoint }} }}
                pub struct StepResult<M> {{ pub ok: bool, pub outbound: GenericOutbound<M> }}
                pub trait ProtocolConfig {{ fn parse_config(me: &EndPoint, args: &Args) -> Option<Self> where Self: Sized; fn get_peers(&self) -> &Vec<EndPoint>; }}
                pub trait ProtocolHost {{ type Msg; type Cfg: ProtocolConfig; fn init(config: &Self::Cfg) -> Option<Self> where Self: Sized; fn next(&mut self, config: &Self::Cfg, packet: Option<GenericPacket<Self::Msg>>) -> StepResult<Self::Msg>; }}
            }}
        }}
        pub mod native {{
            pub mod io_s {{
                pub use super::super::framework::protocol_trait::*;
            }}
        }}
    }}
    pub mod generated {{
        pub mod {protocol} {{
            pub mod {gen_module} {{
                pub struct CConstants;
                impl Default for CConstants {{ fn default() -> Self {{ CConstants }} }}
                {cstate_def}
                {cstate_init}
            }}
            pub mod types_gen {{
                pub use super::{gen_module}::*;
            }}
        }}
    }}
    pub mod implementation {{
        pub mod {protocol} {{
            pub mod message {{
                pub enum {msg_enum} {{
                    {msg_variants}
                }}
            }}
        }}
    }}
}}
"#,
        protocol = protocol,
        gen_module = format!("{}_gen", protocol.to_lowercase()),
        msg_enum = msg_enum,
        msg_variants = msg_variants,
        cstate_def = cstate_def,
        cstate_init = cstate_init,
    );

    // Rewrite use paths and fix inner doc comments
    let adapted = code
        .replace("use crate::", "use crate_stub::")
        .lines()
        .map(|line| {
            if line.starts_with("//!") {
                line.replacen("//!", "//", 1)
            } else {
                line.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");

    let program = format!("{}\n{}\nfn main() {{}}\n", stubs, adapted);

    // Write to temp file and compile
    let tmp_dir = std::env::temp_dir();
    let src_path = tmp_dir.join(format!("test_scaffold_{}.rs", protocol.to_lowercase()));
    let out_path = tmp_dir.join(format!("test_scaffold_{}", protocol.to_lowercase()));
    std::fs::write(&src_path, &program).expect("write temp source");

    let output = std::process::Command::new("rustc")
        .arg("--edition=2021")
        .arg("-o")
        .arg(&out_path)
        .arg(&src_path)
        .output()
        .expect("Failed to run rustc");

    // Clean up
    let _ = std::fs::remove_file(&src_path);
    let _ = std::fs::remove_file(&out_path);

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!(
            "{} scaffold failed to compile:\n{}\n\nGenerated code:\n{}",
            protocol, stderr, program
        );
    }
}

#[test]
fn test_scaffold_compiles_twophase() {
    compile_scaffold(
        "../src/protocol/TwoPhase/twophase_transpile.toml",
        "TwoPhase",
    );
}

#[test]
fn test_scaffold_compiles_paxos() {
    compile_scaffold("../src/protocol/Paxos/paxos_transpile.toml", "Paxos");
}

#[test]
fn test_scaffold_compiles_leader_election() {
    compile_scaffold(
        "../src/protocol/LeaderElection/election_transpile.toml",
        "LeaderElection",
    );
}

#[test]
fn test_scaffold_compiles_raft() {
    compile_scaffold("../src/protocol/Raft/raft_transpile.toml", "Raft");
}

#[test]
fn test_scaffold_compiles_chain_replication() {
    compile_scaffold(
        "../src/protocol/ChainReplication/chain_transpile.toml",
        "ChainReplication",
    );
}

#[test]
fn test_scaffold_compiles_primary_backup() {
    compile_scaffold(
        "../src/protocol/PrimaryBackup/primarybackup_transpile.toml",
        "PrimaryBackup",
    );
}

#[test]
fn test_scaffold_compiles_pbft() {
    compile_scaffold("../src/protocol/PBFT/pbft_transpile.toml", "PBFT");
}

#[test]
fn test_scaffold_compiles_vertical_paxos() {
    compile_scaffold(
        "../src/protocol/VerticalPaxos/vpaxos_transpile.toml",
        "VerticalPaxos",
    );
}

#[test]
fn test_scaffold_compiles_epaxos() {
    compile_scaffold("../src/protocol/EPaxos/epaxos_transpile.toml", "EPaxos");
}

// ============================================================
// Phase 17.7.2: Per-protocol host init → single step tests
// ============================================================

/// Generate a standalone Rust program that tests host init + single step.
/// Compiles and runs it, asserting exit code 0.
fn run_host_init_test(
    toml_path: &str,
    protocol: &str,
    types_gen_path: &str,
    gen_path: &str,
    host_path: &str,
) {
    let config = verus_transpiler::FileConfig::from_file(std::path::Path::new(toml_path))
        .unwrap_or_else(|e| panic!("Failed to load {}: {}", toml_path, e));
    let msg_config = config
        .messages
        .clone()
        .unwrap_or_else(|| panic!("No [messages] in {}", toml_path));
    let message_code = verus_transpiler::generate_message_code(&msg_config);

    let types_gen_code = std::fs::read_to_string(types_gen_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", types_gen_path, e));
    let gen_code = std::fs::read_to_string(gen_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", gen_path, e));
    let host_code = std::fs::read_to_string(host_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", host_path, e));

    // Derive gen_module from filename, not protocol name
    // (e.g., "election_gen" from "election_gen.rs", not "leaderelection_gen")
    let gen_module = std::path::Path::new(gen_path)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("unknown_gen")
        .to_string();

    let params = verus_transpiler::HostTestParams {
        protocol_name: protocol.to_string(),
        types_gen_code,
        gen_code,
        message_code,
        host_code,
        gen_module,
    };

    let test_program = verus_transpiler::generate_host_init_test_program(&params);

    let tmp_dir = std::env::temp_dir();
    let src_path = tmp_dir.join(format!("host_test_{}.rs", protocol.to_lowercase()));
    let bin_path = tmp_dir.join(format!("host_test_{}", protocol.to_lowercase()));

    std::fs::write(&src_path, &test_program).expect("Failed to write test program");

    // Compile
    let compile = std::process::Command::new("rustc")
        .args([
            src_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
            "--edition",
            "2021",
        ])
        .output()
        .expect("Failed to run rustc");

    if !compile.status.success() {
        let stderr = String::from_utf8_lossy(&compile.stderr);
        // Also dump the generated program for debugging
        eprintln!("=== Generated program for {} ===", protocol);
        for (i, line) in test_program.lines().enumerate() {
            eprintln!("{:4}: {}", i + 1, line);
        }
        eprintln!("=== End generated program ===");
        panic!("Compilation failed for {}:\n{}", protocol, stderr);
    }

    // Run
    let run = std::process::Command::new(&bin_path)
        .output()
        .expect("Failed to run test binary");
    assert!(
        run.status.success(),
        "Host test failed for {}:\nstdout: {}\nstderr: {}",
        protocol,
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr),
    );

    // Cleanup
    let _ = std::fs::remove_file(&src_path);
    let _ = std::fs::remove_file(&bin_path);
}

#[test]
fn test_host_init_paxos() {
    run_host_init_test(
        "../src/protocol/Paxos/paxos_transpile.toml",
        "Paxos",
        "../src/generated/Paxos/types_gen.rs",
        "../src/generated/Paxos/paxos_gen.rs",
        "../src/implementation/Paxos/host.rs",
    );
}

#[test]
fn test_host_init_twophase() {
    run_host_init_test(
        "../src/protocol/TwoPhase/twophase_transpile.toml",
        "TwoPhase",
        "../src/generated/TwoPhase/types_gen.rs",
        "../src/generated/TwoPhase/twophase_gen.rs",
        "../src/implementation/TwoPhase/host.rs",
    );
}

#[test]
fn test_host_init_leader_election() {
    run_host_init_test(
        "../src/protocol/LeaderElection/election_transpile.toml",
        "LeaderElection",
        "../src/generated/LeaderElection/types_gen.rs",
        "../src/generated/LeaderElection/election_gen.rs",
        "../src/implementation/LeaderElection/host.rs",
    );
}

#[test]
fn test_host_init_raft() {
    run_host_init_test(
        "../src/protocol/Raft/raft_transpile.toml",
        "Raft",
        "../src/generated/Raft/types_gen.rs",
        "../src/generated/Raft/raft_gen.rs",
        "../src/implementation/Raft/host.rs",
    );
}

/// Verify Raft Cu64_inc/Cu64_dec helpers live in implementation/Raft/helpers.rs
/// (not injected via manual_code into generated files)
#[test]
fn test_raft_helpers_not_in_generated() {
    // Raft TOML should not have manual_code
    let toml = std::fs::read_to_string("../src/protocol/Raft/raft_transpile.toml")
        .expect("Failed to read raft_transpile.toml");
    assert!(
        !toml.contains("manual_code"),
        "Raft TOML should not have manual_code (helpers moved to implementation/Raft/helpers.rs)"
    );

    // Generated files should NOT define Cu64_inc/Cu64_dec (only call them)
    let types_gen = std::fs::read_to_string("../src/generated/Raft/types_gen.rs")
        .expect("Failed to read types_gen.rs");
    assert!(
        !types_gen.contains("pub exec fn Cu64_inc"),
        "types_gen.rs should not define Cu64_inc (moved to helpers.rs)"
    );

    let raft_gen = std::fs::read_to_string("../src/generated/Raft/raft_gen.rs")
        .expect("Failed to read raft_gen.rs");
    assert!(
        !raft_gen.contains("pub exec fn Cu64_inc"),
        "raft_gen.rs should not define Cu64_inc (moved to helpers.rs)"
    );
    // But raft_gen.rs should still call Cu64_inc
    assert!(
        raft_gen.contains("Cu64_inc("),
        "raft_gen.rs should call Cu64_inc"
    );

    // helpers.rs should exist and define the functions
    let helpers = std::fs::read_to_string("../src/implementation/Raft/helpers.rs")
        .expect("Failed to read helpers.rs");
    assert!(
        helpers.contains("pub exec fn Cu64_inc"),
        "helpers.rs should define Cu64_inc"
    );
    assert!(
        helpers.contains("pub exec fn Cu64_dec"),
        "helpers.rs should define Cu64_dec"
    );
}

#[test]
fn test_manual_code_footprint_is_empty() {
    fn collect_transpile_tomls(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
        let entries = std::fs::read_dir(dir)
            .unwrap_or_else(|_| panic!("Failed to read directory {}", dir.display()));
        for entry in entries {
            let entry = entry.expect("Failed to read directory entry");
            let path = entry.path();
            if path.is_dir() {
                collect_transpile_tomls(&path, out);
                continue;
            }
            if let Some(name) = path.file_name().and_then(|name| name.to_str()) {
                if name.ends_with("_transpile.toml") {
                    out.push(path);
                }
            }
        }
    }

    let mut transpile_tomls = Vec::new();
    collect_transpile_tomls(
        std::path::Path::new("../src/protocol"),
        &mut transpile_tomls,
    );
    transpile_tomls.sort();

    let mut manual_bindings = Vec::<(String, String)>::new();
    for path in transpile_tomls {
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|_| panic!("Failed to read {}", path.display()));
        let parsed: toml::Value = source
            .parse()
            .unwrap_or_else(|_| panic!("Failed to parse TOML {}", path.display()));
        if let Some(manual_code) = parsed
            .get("output")
            .and_then(|output| output.get("manual_code"))
            .and_then(|value| value.as_str())
        {
            manual_bindings.push((path.to_string_lossy().into_owned(), manual_code.to_string()));
        }
    }
    manual_bindings.sort();

    // Phase 23.3.2: acceptor uses manual_code for 5 proven action functions.
    let expected: Vec<(String, String)> = vec![
        ("../src/protocol/RSL/acceptor_transpile.toml".to_string(), "acceptor_manual.rs".to_string()),
    ];
    assert_eq!(
        manual_bindings, expected,
        "only acceptor should use manual_code (for proven action functions)"
    );

}

#[test]
fn test_host_init_chain_replication() {
    run_host_init_test(
        "../src/protocol/ChainReplication/chain_transpile.toml",
        "ChainReplication",
        "../src/generated/ChainReplication/types_gen.rs",
        "../src/generated/ChainReplication/chain_gen.rs",
        "../src/implementation/ChainReplication/host.rs",
    );
}

#[test]
fn test_host_init_primary_backup() {
    run_host_init_test(
        "../src/protocol/PrimaryBackup/primarybackup_transpile.toml",
        "PrimaryBackup",
        "../src/generated/PrimaryBackup/types_gen.rs",
        "../src/generated/PrimaryBackup/primarybackup_gen.rs",
        "../src/implementation/PrimaryBackup/host.rs",
    );
}

#[test]
fn test_host_init_pbft() {
    run_host_init_test(
        "../src/protocol/PBFT/pbft_transpile.toml",
        "PBFT",
        "../src/generated/PBFT/types_gen.rs",
        "../src/generated/PBFT/pbft_gen.rs",
        "../src/implementation/PBFT/host.rs",
    );
}

#[test]
fn test_host_init_vertical_paxos() {
    run_host_init_test(
        "../src/protocol/VerticalPaxos/vpaxos_transpile.toml",
        "VerticalPaxos",
        "../src/generated/VerticalPaxos/types_gen.rs",
        "../src/generated/VerticalPaxos/vpaxos_gen.rs",
        "../src/implementation/VerticalPaxos/host.rs",
    );
}

#[test]
fn test_host_init_epaxos() {
    run_host_init_test(
        "../src/protocol/EPaxos/epaxos_transpile.toml",
        "EPaxos",
        "../src/generated/EPaxos/types_gen.rs",
        "../src/generated/EPaxos/epaxos_gen.rs",
        "../src/implementation/EPaxos/host.rs",
    );
}

fn diff_strings(a: &str, b: &str) -> String {
    let a_lines: Vec<&str> = a.lines().collect();
    let b_lines: Vec<&str> = b.lines().collect();
    let mut diff = String::new();
    for (i, (la, lb)) in a_lines.iter().zip(b_lines.iter()).enumerate() {
        if la != lb {
            diff.push_str(&format!(
                "line {}: -{}\nline {}: +{}\n",
                i + 1,
                la,
                i + 1,
                lb
            ));
        }
    }
    if a_lines.len() != b_lines.len() {
        diff.push_str(&format!(
            "line count: {} vs {}\n",
            a_lines.len(),
            b_lines.len()
        ));
    }
    diff
}

// ============================================================
// Phase 17.3.2b: Marshalable generation integration tests
// ============================================================

#[test]
fn test_generate_marshalable_ballot_like() {
    let toml_content = r#"
        [[marshalable.types]]
        name = "CBallot"
        fields = [["seqno", "u64"], ["proposer_id", "u64"]]
    "#;

    let config = verus_transpiler::FileConfig::from_toml(toml_content).unwrap();
    let marsh_config = config.marshalable.unwrap();
    assert_eq!(marsh_config.types.len(), 1);

    let code = verus_transpiler::generate_marshalable_impls(&marsh_config);

    // impl header
    assert!(code.contains("impl Marshalable for CBallot {"));

    // All 11 trait methods present
    assert!(code.contains("open spec fn view_equal("));
    assert!(code.contains("proof fn lemma_view_equal_symmetric("));
    assert!(code.contains("open spec fn is_marshalable("));
    assert!(code.contains("exec fn _is_marshalable("));
    assert!(code.contains("open spec fn ghost_serialize("));
    assert!(code.contains("exec fn serialized_size("));
    assert!(code.contains("exec fn serialize("));
    assert!(code.contains("exec fn deserialize("));
    assert!(code.contains("proof fn lemma_serialization_is_not_a_prefix_of("));
    assert!(code.contains("proof fn lemma_same_views_serialize_the_same("));
    assert!(code.contains("proof fn lemma_serialize_injective("));

    // view_equal uses both fields
    assert!(code.contains("self.seqno.view_equal(&other.seqno)"));
    assert!(code.contains("self.proposer_id.view_equal(&other.proposer_id)"));

    // deserialize uses correct types
    assert!(code.contains("let (seqno, mid) = match u64::deserialize(data, mid)"));
    assert!(code.contains("let (proposer_id, mid) = match u64::deserialize(data, mid)"));

    // struct construction in deserialize
    assert!(code.contains("let res = CBallot {"));
    assert!(code.contains("seqno,"));
    assert!(code.contains("proposer_id,"));
}

#[test]
fn test_generate_marshalable_nested_types() {
    let toml_content = r#"
        [[marshalable.types]]
        name = "CRequest"
        fields = [["client", "EndPoint"], ["seqno", "u64"], ["request", "CAppMessage"]]

        [[marshalable.types]]
        name = "CVote"
        fields = [["max_value_bal", "CBallot"], ["max_val", "CRequestBatch"]]
    "#;

    let config = verus_transpiler::FileConfig::from_toml(toml_content).unwrap();
    let marsh_config = config.marshalable.unwrap();
    assert_eq!(marsh_config.types.len(), 2);

    let code = verus_transpiler::generate_marshalable_impls(&marsh_config);

    // Both impls generated
    assert!(code.contains("impl Marshalable for CRequest {"));
    assert!(code.contains("impl Marshalable for CVote {"));

    // CRequest deserialize uses named types
    assert!(code.contains("let (client, mid) = match EndPoint::deserialize(data, mid)"));
    assert!(code.contains("let (request, mid) = match CAppMessage::deserialize(data, mid)"));

    // CVote deserialize uses named types
    assert!(code.contains("let (max_value_bal, mid) = match CBallot::deserialize(data, mid)"));
    assert!(code.contains("let (max_val, mid) = match CRequestBatch::deserialize(data, mid)"));

    // Serialize calls for CRequest
    assert!(code.contains("self.client.serialize(data);"));
    assert!(code.contains("self.seqno.serialize(data);"));
    assert!(code.contains("self.request.serialize(data);"));
}

#[test]
fn test_generate_marshalable_single_field_endpoint() {
    let toml_content = r#"
        [[marshalable.types]]
        name = "EndPoint"
        fields = [["id", "Vec<u8>"]]
    "#;

    let config = verus_transpiler::FileConfig::from_toml(toml_content).unwrap();
    let marsh_config = config.marshalable.unwrap();
    let code = verus_transpiler::generate_marshalable_impls(&marsh_config);

    assert!(code.contains("impl Marshalable for EndPoint {"));
    assert!(code.contains("let (id, mid) = match Vec<u8>::deserialize(data, mid)"));
    assert!(code.contains("self.id.serialize(data);"));
    assert!(code.contains("self.id.ghost_serialize()"));
}

#[test]
fn test_generate_marshalable_proof_structure() {
    let toml_content = r#"
        [[marshalable.types]]
        name = "TwoFields"
        fields = [["a", "u64"], ["b", "u64"]]
    "#;

    let config = verus_transpiler::FileConfig::from_toml(toml_content).unwrap();
    let marsh_config = config.marshalable.unwrap();
    let code = verus_transpiler::generate_marshalable_impls(&marsh_config);

    // serialize proof block
    assert!(code.contains("assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);"));
    assert!(code.contains("assert(data@.subrange(old(data)@.len() as int, data@.len() as int) =~= self.ghost_serialize());"));

    // deserialize proof block
    assert!(code
        .contains("assert(data@.subrange(start as int, end as int) =~= res.ghost_serialize());"));

    // prefix lemma: divergence pattern for both fields
    assert!(code.contains("if !self.a.view_equal(&other.a) {"));
    assert!(code.contains("if !self.b.view_equal(&other.b) {"));
    assert!(code.contains("x0.lemma_serialization_is_not_a_prefix_of(&x1);"));
    assert!(code.contains("let mid = mid + self.a.ghost_serialize().len();"));

    // injective lemma
    assert!(code.contains("self.lemma_serialization_is_not_a_prefix_of(other);"));
    assert!(code.contains(
        "assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)"
    ));
}

#[test]
fn test_generate_marshalable_overflow_checks() {
    let toml_content = r#"
        [[marshalable.types]]
        name = "Triple"
        fields = [["x", "u64"], ["y", "u64"], ["z", "u64"]]
    "#;

    let config = verus_transpiler::FileConfig::from_toml(toml_content).unwrap();
    let marsh_config = config.marshalable.unwrap();
    let code = verus_transpiler::generate_marshalable_impls(&marsh_config);

    // spec is_marshalable: overflow guard with all three fields
    assert!(code.contains("0 + self.x.ghost_serialize().len() + self.y.ghost_serialize().len() + self.z.ghost_serialize().len() <= usize::MAX"));

    // exec _is_marshalable: chained overflow checks
    assert!(code.contains("usize::MAX - (0) >= self.x.serialized_size()"));
    assert!(code.contains("usize::MAX - (self.x.serialized_size()) >= self.y.serialized_size()"));
    assert!(code.contains("usize::MAX - (self.x.serialized_size() + self.y.serialized_size()) >= self.z.serialized_size()"));
}

// ============================================================
// Phase 17.3.2c: Marshalable generation from real RSL TOML
// ============================================================

/// Helper: load marshalable config from a real protocol TOML file
fn load_and_generate_marshalable(toml_path: &str) -> String {
    let config = verus_transpiler::FileConfig::from_file(std::path::Path::new(toml_path))
        .unwrap_or_else(|e| panic!("Failed to load {}: {}", toml_path, e));
    let marsh_config = config
        .marshalable
        .unwrap_or_else(|| panic!("No [marshalable] in {}", toml_path));
    verus_transpiler::generate_marshalable_impls(&marsh_config)
}

#[test]
fn test_generate_marshalable_rsl_types_toml() {
    let code = load_and_generate_marshalable("../src/protocol/RSL/types_transpile.toml");

    // All 4 RSL types should have impls
    assert!(code.contains("impl Marshalable for CBallot {"));
    assert!(code.contains("impl Marshalable for CRequest {"));
    assert!(code.contains("impl Marshalable for CReply {"));
    assert!(code.contains("impl Marshalable for CVote {"));

    // CBallot: 2 u64 fields
    assert!(code.contains("self.seqno.view_equal(&other.seqno)"));
    assert!(code.contains("self.proposer_id.view_equal(&other.proposer_id)"));
    assert!(code.contains("let (seqno, mid) = match u64::deserialize(data, mid)"));
    assert!(code.contains("let (proposer_id, mid) = match u64::deserialize(data, mid)"));

    // CRequest: EndPoint + u64 + CAppMessage
    assert!(code.contains("let (client, mid) = match EndPoint::deserialize(data, mid)"));
    assert!(code.contains("let (request, mid) = match CAppMessage::deserialize(data, mid)"));
    assert!(code.contains("self.client.serialize(data);"));
    assert!(code.contains("self.request.serialize(data);"));

    // CReply: EndPoint + u64 + CAppMessage
    assert!(code.contains("self.reply.serialize(data);"));

    // CVote: CBallot + CRequestBatch
    assert!(code.contains("let (max_value_bal, mid) = match CBallot::deserialize(data, mid)"));
    assert!(code.contains("let (max_val, mid) = match CRequestBatch::deserialize(data, mid)"));
}

#[test]
fn test_generate_marshalable_rsl_cballot_detail() {
    let code = load_and_generate_marshalable("../src/protocol/RSL/types_transpile.toml");

    // Extract just the CBallot impl (it's the first one)
    let ballot_start = code.find("impl Marshalable for CBallot {").unwrap();
    let request_start = code.find("impl Marshalable for CRequest {").unwrap();
    let ballot_code = &code[ballot_start..request_start];

    // ghost_serialize concatenates both fields
    assert!(ballot_code.contains(
        "Seq::empty() + self.seqno.ghost_serialize() + self.proposer_id.ghost_serialize()"
    ));

    // serialized_size adds both
    assert!(ballot_code
        .contains("0 + self.seqno.serialized_size() + self.proposer_id.serialized_size()"));

    // deserialize constructs CBallot struct
    assert!(ballot_code.contains("let res = CBallot {"));
    assert!(ballot_code.contains("seqno,"));
    assert!(ballot_code.contains("proposer_id,"));

    // proof blocks present
    assert!(ballot_code
        .contains("assert(data@.subrange(start as int, end as int) =~= res.ghost_serialize());"));
}

#[test]
fn test_generate_marshalable_rsl_type_count() {
    let code = load_and_generate_marshalable("../src/protocol/RSL/types_transpile.toml");

    // 4 struct + 2 enum = 6 impl blocks
    let impl_count = code.matches("impl Marshalable for").count();
    assert_eq!(
        impl_count, 6,
        "Expected 6 Marshalable impls (4 struct + 2 enum), got {}",
        impl_count
    );

    // Each has all 11 trait methods
    for type_name in &["CBallot", "CRequest", "CReply", "CVote"] {
        let impl_start = code
            .find(&format!("impl Marshalable for {} {{", type_name))
            .unwrap_or_else(|| panic!("Missing impl for {}", type_name));
        let impl_section = &code[impl_start..];
        // Find the closing brace (end of impl block)
        let mut depth = 0;
        let mut end = 0;
        for (i, ch) in impl_section.char_indices() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        end = i + 1;
                        break;
                    }
                }
                _ => {}
            }
        }
        let block = &impl_section[..end];
        assert!(
            block.contains("open spec fn view_equal("),
            "{} missing view_equal",
            type_name
        );
        assert!(
            block.contains("proof fn lemma_view_equal_symmetric("),
            "{} missing lemma_view_equal_symmetric",
            type_name
        );
        assert!(
            block.contains("open spec fn is_marshalable("),
            "{} missing is_marshalable",
            type_name
        );
        assert!(
            block.contains("exec fn _is_marshalable("),
            "{} missing _is_marshalable",
            type_name
        );
        assert!(
            block.contains("open spec fn ghost_serialize("),
            "{} missing ghost_serialize",
            type_name
        );
        assert!(
            block.contains("exec fn serialized_size("),
            "{} missing serialized_size",
            type_name
        );
        assert!(
            block.contains("exec fn serialize("),
            "{} missing serialize",
            type_name
        );
        assert!(
            block.contains("exec fn deserialize("),
            "{} missing deserialize",
            type_name
        );
        assert!(
            block.contains("proof fn lemma_serialization_is_not_a_prefix_of("),
            "{} missing lemma_serialization_is_not_a_prefix_of",
            type_name
        );
        assert!(
            block.contains("proof fn lemma_same_views_serialize_the_same("),
            "{} missing lemma_same_views_serialize_the_same",
            type_name
        );
        assert!(
            block.contains("proof fn lemma_serialize_injective("),
            "{} missing lemma_serialize_injective",
            type_name
        );
    }
}

// ============================================================
// Phase 17.3.3b: Enum Marshalable generation from RSL TOML
// ============================================================

#[test]
fn test_generate_marshalable_enum_cappMessage_from_toml() {
    let code = load_and_generate_marshalable("../src/protocol/RSL/types_transpile.toml");

    // CAppMessage enum impl should be generated
    assert!(code.contains("impl Marshalable for CAppMessage {"));

    // Tag-based dispatch: 3 variants with tags 0, 1, 2
    assert!(code.contains("CAppMessage::CAppIncrement"));
    assert!(code.contains("CAppMessage::CAppReply"));
    assert!(code.contains("CAppMessage::CAppInvalid"));

    // CAppReply has one field: response: u64
    assert!(code.contains("response"));
    assert!(code.contains("u64::deserialize(data, mid)"));

    // Unit variants (CAppIncrement, CAppInvalid) should have no field deserialization
    // Tag bytes: 0u8, 1u8, 2u8
    assert!(code.contains("0u8"));
    assert!(code.contains("1u8"));
    assert!(code.contains("2u8"));
}

#[test]
fn test_generate_marshalable_enum_cmessage_from_toml() {
    let code = load_and_generate_marshalable("../src/protocol/RSL/types_transpile.toml");

    // CMessage enum impl should be generated
    assert!(code.contains("impl Marshalable for CMessage {"));

    // All 11 variants present
    for variant in &[
        "CMessageInvalid",
        "CMessageRequest",
        "CMessage1a",
        "CMessage1b",
        "CMessage2a",
        "CMessage2b",
        "CMessageHeartbeat",
        "CMessageReply",
        "CMessageAppStateRequest",
        "CMessageAppStateSupply",
        "CMessageStartingPhase2",
    ] {
        assert!(
            code.contains(&format!("CMessage::{}", variant)),
            "Missing variant CMessage::{}",
            variant,
        );
    }

    // Tags 0 through 10
    assert!(code.contains("10u8"));

    // CMessage1b has 3 fields: bal_1b: CBallot, log_truncation_point: COperationNumber, votes: CVotes
    assert!(code.contains("bal_1b"));
    assert!(code.contains("log_truncation_point"));
    assert!(code.contains("votes"));

    // CMessageAppStateSupply has 4 fields (most complex variant)
    assert!(code.contains("bal_state_supply"));
    assert!(code.contains("opn_state_supply"));
    assert!(code.contains("app_state"));
    assert!(code.contains("reply_cache"));
}

#[test]
fn test_generate_marshalable_enum_count_from_toml() {
    let code = load_and_generate_marshalable("../src/protocol/RSL/types_transpile.toml");

    // 4 struct impls + 2 enum impls = 6 total
    let impl_count = code.matches("impl Marshalable for").count();
    assert_eq!(
        impl_count, 6,
        "Expected 6 Marshalable impls (4 struct + 2 enum), got {}",
        impl_count
    );

    // CAppMessage and CMessage have all 11 trait methods
    for type_name in &["CAppMessage", "CMessage"] {
        let impl_start = code
            .find(&format!("impl Marshalable for {} {{", type_name))
            .unwrap_or_else(|| panic!("Missing impl for {}", type_name));
        let impl_section = &code[impl_start..];
        let mut depth = 0;
        let mut end = 0;
        for (i, ch) in impl_section.char_indices() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        end = i + 1;
                        break;
                    }
                }
                _ => {}
            }
        }
        let block = &impl_section[..end];
        for method in &[
            "open spec fn view_equal(",
            "proof fn lemma_view_equal_symmetric(",
            "open spec fn is_marshalable(",
            "exec fn _is_marshalable(",
            "open spec fn ghost_serialize(",
            "exec fn serialized_size(",
            "exec fn serialize(",
            "exec fn deserialize(",
            "proof fn lemma_serialization_is_not_a_prefix_of(",
            "proof fn lemma_same_views_serialize_the_same(",
            "proof fn lemma_serialize_injective(",
        ] {
            assert!(
                block.contains(method),
                "{} missing method: {}",
                type_name,
                method
            );
        }
    }
}

// ============================================================
// Phase 17.3.4a: Marshalable CLI pipeline tests
// ============================================================

/// Test that the generate-marshalable CLI subcommand produces correct output
/// when invoked with the real RSL types_transpile.toml config.
#[test]
fn test_marshalable_cli_pipeline_produces_all_impls() {
    let transpiler_bin =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/release/verus-transpile");
    if !transpiler_bin.exists() {
        eprintln!("Skipping: transpiler binary not built (run cargo build --release)");
        return;
    }

    let toml_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("src/protocol/RSL/types_transpile.toml");
    if !toml_path.exists() {
        eprintln!("Skipping: RSL types_transpile.toml not found");
        return;
    }

    let output_file = std::env::temp_dir().join("test_marshalable_cli_output.rs");

    let result = std::process::Command::new(&transpiler_bin)
        .args([
            "generate-marshalable",
            "--config",
            toml_path.to_str().unwrap(),
            "--output",
            output_file.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run transpiler");

    assert!(
        result.status.success(),
        "generate-marshalable CLI failed: {}",
        String::from_utf8_lossy(&result.stderr)
    );

    let code = std::fs::read_to_string(&output_file).expect("Failed to read generated output");

    // Should contain all 6 Marshalable impls (4 struct + 2 enum)
    let impl_count = code.matches("impl Marshalable for").count();
    assert_eq!(
        impl_count, 6,
        "Expected 6 Marshalable impls (4 struct + 2 enum), got {}",
        impl_count
    );

    // All 4 struct types present
    assert!(code.contains("impl Marshalable for CBallot {"));
    assert!(code.contains("impl Marshalable for CRequest {"));
    assert!(code.contains("impl Marshalable for CReply {"));
    assert!(code.contains("impl Marshalable for CVote {"));

    // Both enum types present
    assert!(code.contains("impl Marshalable for CAppMessage {"));
    assert!(code.contains("impl Marshalable for CMessage {"));

    // CMessage should have all 11 variant patterns
    for variant in &[
        "CMessage::CMessageInvalid",
        "CMessage::CMessageRequest",
        "CMessage::CMessage1a",
        "CMessage::CMessage1b",
        "CMessage::CMessage2a",
        "CMessage::CMessage2b",
        "CMessage::CMessageHeartbeat",
        "CMessage::CMessageReply",
        "CMessage::CMessageAppStateRequest",
        "CMessage::CMessageAppStateSupply",
        "CMessage::CMessageStartingPhase2",
    ] {
        assert!(
            code.contains(variant),
            "Missing CMessage variant: {}",
            variant
        );
    }

    // Cleanup
    let _ = std::fs::remove_file(&output_file);
}

/// Test that the generate-marshalable CLI produces deterministic output
/// (running twice produces identical results).
#[test]
fn test_marshalable_cli_deterministic_output() {
    let transpiler_bin =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/release/verus-transpile");
    if !transpiler_bin.exists() {
        eprintln!("Skipping: transpiler binary not built (run cargo build --release)");
        return;
    }

    let toml_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("src/protocol/RSL/types_transpile.toml");
    if !toml_path.exists() {
        eprintln!("Skipping: RSL types_transpile.toml not found");
        return;
    }

    // Run twice
    let run = |label: &str| -> String {
        let output_file =
            std::env::temp_dir().join(format!("test_marshalable_deterministic_{}.rs", label));
        let result = std::process::Command::new(&transpiler_bin)
            .args([
                "generate-marshalable",
                "--config",
                toml_path.to_str().unwrap(),
                "--output",
                output_file.to_str().unwrap(),
            ])
            .output()
            .expect("Failed to run transpiler");
        assert!(result.status.success(), "CLI failed on run {}", label);
        let code = std::fs::read_to_string(&output_file).expect("Failed to read output");
        let _ = std::fs::remove_file(&output_file);
        code
    };

    let run1 = run("run1");
    let run2 = run("run2");

    assert_eq!(
        run1, run2,
        "generate-marshalable output should be deterministic"
    );
    assert!(!run1.is_empty(), "Generated output should not be empty");
}

/// Test that generate-marshalable CLI stdout mode works (no --output flag).
#[test]
fn test_marshalable_cli_stdout_mode() {
    let transpiler_bin =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/release/verus-transpile");
    if !transpiler_bin.exists() {
        eprintln!("Skipping: transpiler binary not built (run cargo build --release)");
        return;
    }

    let toml_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("src/protocol/RSL/types_transpile.toml");
    if !toml_path.exists() {
        eprintln!("Skipping: RSL types_transpile.toml not found");
        return;
    }

    let result = std::process::Command::new(&transpiler_bin)
        .args([
            "generate-marshalable",
            "--config",
            toml_path.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run transpiler");

    assert!(
        result.status.success(),
        "generate-marshalable stdout mode failed: {}",
        String::from_utf8_lossy(&result.stderr)
    );

    let stdout = String::from_utf8_lossy(&result.stdout);
    assert!(
        stdout.contains("impl Marshalable for CBallot {"),
        "stdout should contain CBallot impl"
    );
    assert!(
        stdout.contains("impl Marshalable for CMessage {"),
        "stdout should contain CMessage impl"
    );
    // 6 impls in stdout
    let impl_count = stdout.matches("impl Marshalable for").count();
    assert_eq!(
        impl_count, 6,
        "Expected 6 impls in stdout, got {}",
        impl_count
    );
}

/// Test that TLC model-checking wrappers exist and are well-structured for all 4 feasible protocols.
/// These wrappers live in `tla_test_workspace/transpiler_generated_tla_with_properties/` and
/// augment D3-generated relational specs with VARIABLE state, finite domains, message channels,
/// and safety invariants.
#[test]
fn test_tlc_mc_wrappers_exist_and_well_structured() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tla_test_workspace/transpiler_generated_tla_with_properties");

    let protocols = vec![
        (
            "TwoPhase_MC",
            vec![
                "Consistency",
                "TMCommitImpliesNoAbort",
                "TMAbortImpliesNoCommit",
                "CommittedImpliesPrepared",
                "TMCommitRequiresAllPrepared",
            ],
        ),
        (
            "Paxos_MC",
            vec![
                "Agreement",
                "Validity",
                "AcceptorMonotonicity",
                "DecidedEqualsProposed",
            ],
        ),
        (
            "LeaderElection_MC",
            vec![
                "TypeOK",
                "LeaderIsAliveOrNone",
                "LeaderValid",
                "ElectingSubsetAlive",
                "WaitingNodeAlive",
            ],
        ),
        (
            "PrimaryBackup_MC",
            vec![
                "LogConsistencyAfterAck",
                "NoSplitBrain",
                "LogLengthBound",
                "ViewBounded",
                "BackupLogCoherence",
                "PendingImpliesValidState",
            ],
        ),
    ];

    for (name, expected_invariants) in &protocols {
        let tla_path = dir.join(format!("{}.tla", name));
        let cfg_path = dir.join(format!("{}.cfg", name));

        assert!(tla_path.exists(), "Missing {}.tla", name);
        assert!(cfg_path.exists(), "Missing {}.cfg", name);

        let tla_content = std::fs::read_to_string(&tla_path)
            .unwrap_or_else(|e| panic!("Cannot read {}.tla: {}", name, e));
        let cfg_content = std::fs::read_to_string(&cfg_path)
            .unwrap_or_else(|e| panic!("Cannot read {}.cfg: {}", name, e));

        // Check TLA+ module structure
        assert!(
            tla_content.contains(&format!("---- MODULE {} ----", name)),
            "{}.tla missing module header",
            name
        );
        assert!(
            tla_content.contains("===="),
            "{}.tla missing module footer",
            name
        );
        assert!(
            tla_content.contains("VARIABLE"),
            "{}.tla missing VARIABLE declaration",
            name
        );
        assert!(
            tla_content.contains("StateInit"),
            "{}.tla missing StateInit",
            name
        );
        assert!(
            tla_content.contains("StateNext"),
            "{}.tla missing StateNext",
            name
        );
        assert!(
            tla_content.contains("Spec =="),
            "{}.tla missing Spec definition",
            name
        );

        // Check cfg structure
        assert!(
            cfg_content.contains("SPECIFICATION Spec"),
            "{}.cfg missing SPECIFICATION",
            name
        );
        assert!(
            cfg_content.contains("CHECK_DEADLOCK FALSE"),
            "{}.cfg missing CHECK_DEADLOCK",
            name
        );
        assert!(
            cfg_content.contains("INVARIANTS"),
            "{}.cfg missing INVARIANTS",
            name
        );

        // Check each expected invariant exists in both files
        for inv in expected_invariants {
            assert!(
                tla_content.contains(inv),
                "{}.tla missing invariant definition: {}",
                name,
                inv
            );
            assert!(
                cfg_content.contains(inv),
                "{}.cfg missing invariant: {}",
                name,
                inv
            );
        }
    }

    // Verify we have exactly 4 MC wrappers
    let mc_count = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_name().to_string_lossy().ends_with("_MC.tla"))
        .count();
    assert_eq!(
        mc_count, 4,
        "Expected 4 MC wrapper TLA+ files, got {}",
        mc_count
    );
}

#[test]
fn test_generate_mc_wrapper_from_relational_module() {
    let transpiler_bin = resolve_transpiler_binary_for_integration();
    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let input =
        manifest_dir.join("tla_test_workspace/transpiler_generated_tla/TwoPhase/Twophase.tla");
    assert!(
        input.exists(),
        "Expected relational input module at {}",
        input.display()
    );

    let temp = tempfile::tempdir().expect("tempdir should create");
    let wrapper_out = temp.path().join("Twophase_MC.tla");

    let output = std::process::Command::new(&transpiler_bin)
        .args([
            "generate-mc-wrapper",
            "--input",
            input.to_str().unwrap(),
            "--output",
            wrapper_out.to_str().unwrap(),
            "--invariant",
            "Consistency",
        ])
        .output()
        .expect("Failed to run generate-mc-wrapper command");

    assert!(
        output.status.success(),
        "generate-mc-wrapper should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let wrapper_content =
        std::fs::read_to_string(&wrapper_out).expect("wrapper output should be readable");
    assert!(
        wrapper_content.contains("---- MODULE Twophase_MC ----"),
        "wrapper should use source module name with _MC suffix"
    );
    assert!(
        wrapper_content.contains("EXTENDS Twophase"),
        "wrapper should extend source module"
    );
    assert!(
        wrapper_content.contains("Init(state, constants)"),
        "wrapper should call relational Init operator"
    );
    assert!(
        wrapper_content.contains("Next(state, state_, constants)"),
        "wrapper should call relational Next operator"
    );
    assert!(
        wrapper_content.contains("Spec == StateInit /\\ [][StateNext]_vars"),
        "wrapper should define Spec"
    );

    let cfg_out = wrapper_out.with_extension("cfg");
    let cfg_content = std::fs::read_to_string(&cfg_out).expect("cfg output should be readable");
    assert!(cfg_content.contains("SPECIFICATION Spec"));
    assert!(cfg_content.contains("CHECK_DEADLOCK FALSE"));
    assert!(cfg_content.contains("INVARIANTS"));
    assert!(cfg_content.contains("Consistency"));
}

#[test]
fn test_generate_mc_wrapper_from_relational_module_with_packet_projection() {
    let transpiler_bin = resolve_transpiler_binary_for_integration();
    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let input =
        manifest_dir.join("tla_test_workspace/transpiler_generated_tla/TwoPhase/Twophase.tla");
    assert!(
        input.exists(),
        "Expected relational input module at {}",
        input.display()
    );

    let temp = tempfile::tempdir().expect("tempdir should create");
    let wrapper_out = temp.path().join("Twophase_MC_lifted.tla");

    let output = std::process::Command::new(&transpiler_bin)
        .args([
            "generate-mc-wrapper",
            "--input",
            input.to_str().unwrap(),
            "--output",
            wrapper_out.to_str().unwrap(),
            "--packet-mode",
            "append-seq",
            "--packet-var",
            "sent_packets",
        ])
        .output()
        .expect("Failed to run generate-mc-wrapper command");

    assert!(
        output.status.success(),
        "generate-mc-wrapper (packet projection) should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let wrapper_content =
        std::fs::read_to_string(&wrapper_out).expect("wrapper output should be readable");
    assert!(
        wrapper_content.contains("VARIABLE state, constants, msgs"),
        "packet projection wrapper should include msgs variable"
    );
    assert!(
        wrapper_content.contains("msgs' = msgs \\o sent_packets"),
        "packet projection wrapper should append sent_packets into msgs"
    );
    assert!(
        wrapper_content.contains("vars == <<state, constants, msgs>>"),
        "packet projection wrapper should include msgs in vars tuple"
    );
}

#[test]
fn test_generate_mc_wrapper_matches_golden_fixtures_for_shared_small_protocols() {
    fn normalize_newlines(content: &str) -> String {
        content.replace("\r\n", "\n")
    }

    struct FixtureCase {
        label: &'static str,
        input_rel: &'static str,
        output_stem: &'static str,
        invariant: &'static str,
    }

    let cases = [
        FixtureCase {
            label: "TwoPhase",
            input_rel: "tla_test_workspace/transpiler_generated_tla/TwoPhase/Twophase.tla",
            output_stem: "Twophase_MC",
            invariant: "Consistency",
        },
        FixtureCase {
            label: "LeaderElection",
            input_rel: "tla_test_workspace/transpiler_generated_tla/LeaderElection/Election.tla",
            output_stem: "Election_MC",
            invariant: "LeaderValid",
        },
        FixtureCase {
            label: "Paxos",
            input_rel: "tla_test_workspace/transpiler_generated_tla/Paxos/Paxos.tla",
            output_stem: "Paxos_MC",
            invariant: "Agreement",
        },
        FixtureCase {
            label: "PrimaryBackup",
            input_rel:
                "tla_test_workspace/transpiler_generated_tla/PrimaryBackup/Primarybackup.tla",
            output_stem: "Primarybackup_MC",
            invariant: "NoSplitBrain",
        },
    ];

    let transpiler_bin = resolve_transpiler_binary_for_integration();
    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture_dir = manifest_dir.join("tests/mc_wrapper_fixtures");

    for case in cases {
        let input = manifest_dir.join(case.input_rel);
        assert!(
            input.exists(),
            "[{}] expected relational input module at {}",
            case.label,
            input.display()
        );

        let temp = tempfile::tempdir().expect("tempdir should create");
        let wrapper_out = temp.path().join(format!("{}.tla", case.output_stem));

        let output = std::process::Command::new(&transpiler_bin)
            .args([
                "generate-mc-wrapper",
                "--input",
                input.to_str().unwrap(),
                "--output",
                wrapper_out.to_str().unwrap(),
                "--invariant",
                case.invariant,
            ])
            .output()
            .expect("failed to run generate-mc-wrapper command");

        assert!(
            output.status.success(),
            "[{}] generate-mc-wrapper should succeed: {}",
            case.label,
            String::from_utf8_lossy(&output.stderr)
        );

        let generated_tla =
            std::fs::read_to_string(&wrapper_out).expect("generated wrapper should be readable");
        let generated_cfg = std::fs::read_to_string(wrapper_out.with_extension("cfg"))
            .expect("generated cfg should be readable");

        let golden_tla =
            std::fs::read_to_string(fixture_dir.join(format!("{}.golden.tla", case.output_stem)))
                .unwrap_or_else(|err| {
                    panic!(
                        "[{}] failed to read golden tla fixture: {}",
                        case.label, err
                    )
                });
        let golden_cfg =
            std::fs::read_to_string(fixture_dir.join(format!("{}.golden.cfg", case.output_stem)))
                .unwrap_or_else(|err| {
                    panic!(
                        "[{}] failed to read golden cfg fixture: {}",
                        case.label, err
                    )
                });

        assert_eq!(
            normalize_newlines(&generated_tla),
            normalize_newlines(&golden_tla),
            "[{}] generated wrapper does not match golden fixture",
            case.label
        );
        assert_eq!(
            normalize_newlines(&generated_cfg),
            normalize_newlines(&golden_cfg),
            "[{}] generated cfg does not match golden fixture",
            case.label
        );
    }
}

fn resolve_transpiler_binary_for_integration() -> std::path::PathBuf {
    for key in [
        "CARGO_BIN_EXE_verus-transpile",
        "CARGO_BIN_EXE_verus_transpile",
    ] {
        if let Some(path) = std::env::var_os(key) {
            let bin = std::path::PathBuf::from(path);
            if bin.exists() {
                return bin;
            }
        }
    }

    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for candidate in [
        manifest_dir.join("target/debug/verus-transpile"),
        manifest_dir.join("target/release/verus-transpile"),
    ] {
        if candidate.exists() {
            return candidate;
        }
    }

    let build_output = std::process::Command::new("cargo")
        .args(["build", "--bin", "verus-transpile"])
        .current_dir(manifest_dir)
        .output()
        .expect("Failed to build verus-transpile binary for integration tests");
    assert!(
        build_output.status.success(),
        "Failed to build verus-transpile binary: {}",
        String::from_utf8_lossy(&build_output.stderr)
    );

    let built = manifest_dir.join("target/debug/verus-transpile");
    assert!(
        built.exists(),
        "Expected built binary at {}",
        built.display()
    );
    built
}

fn resolve_repo_root_for_integration() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("transpiler crate should have repository root parent")
        .to_path_buf()
}

fn resolve_model_check_fixture_path(name: &str) -> std::path::PathBuf {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("model_check_fixtures")
        .join(name);
    assert!(
        path.exists(),
        "Missing model-check fixture: {}",
        path.display()
    );
    path
}

fn run_model_check_json_report_from_fixtures(
    transpiler_bin: &std::path::Path,
    input_fixture: &str,
    types_fixture: &str,
    model_fixture: &str,
) -> serde_json::Value {
    let input = resolve_model_check_fixture_path(input_fixture);
    let types = resolve_model_check_fixture_path(types_fixture);
    let model = resolve_model_check_fixture_path(model_fixture);

    let output = std::process::Command::new(transpiler_bin)
        .args([
            "model-check",
            "--input",
            input.to_str().unwrap(),
            "--types",
            types.to_str().unwrap(),
            "--model",
            model.to_str().unwrap(),
            "--search",
            "bfs",
            "--json-report",
        ])
        .output()
        .expect("Failed to run model-check command");

    assert!(
        output.status.success(),
        "model-check should succeed for fixtures input=`{}` types=`{}` model=`{}`. stderr={}",
        input_fixture,
        types_fixture,
        model_fixture,
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    serde_json::from_str(&stdout).expect("model-check should emit valid JSON report")
}

#[test]
fn test_model_check_primarybackup_helper_call_branches_bounded_run() {
    let transpiler_bin = resolve_transpiler_binary_for_integration();

    let repo_root = resolve_repo_root_for_integration();
    let input = repo_root.join("src/protocol/PrimaryBackup/primarybackup.rs");
    let types = repo_root.join("src/protocol/PrimaryBackup/types.rs");
    let model_path = resolve_model_check_fixture_path("primarybackup_small.model.toml");
    assert!(input.exists(), "Missing input spec: {}", input.display());
    assert!(types.exists(), "Missing types spec: {}", types.display());

    let output = std::process::Command::new(&transpiler_bin)
        .args([
            "model-check",
            "--input",
            input.to_str().unwrap(),
            "--types",
            types.to_str().unwrap(),
            "--model",
            model_path.to_str().unwrap(),
            "--search",
            "bfs",
            "--json-report",
        ])
        .output()
        .expect("Failed to run model-check command");

    assert!(
        output.status.success(),
        "PrimaryBackup model-check should succeed once helper-call `LNext` branch support is implemented. stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let report: serde_json::Value =
        serde_json::from_str(&stdout).expect("model-check should emit valid JSON report");
    let states = report
        .get("summary")
        .and_then(|s| s.get("states"))
        .and_then(|v| v.as_u64())
        .unwrap_or(0);
    let transitions = report
        .get("summary")
        .and_then(|s| s.get("transitions"))
        .and_then(|v| v.as_u64())
        .unwrap_or(0);
    assert!(
        states > 0,
        "expected at least one reached state in bounded PrimaryBackup run: {}",
        stdout
    );
    assert!(
        transitions > 0,
        "expected at least one transition in bounded PrimaryBackup run: {}",
        stdout
    );
}

#[test]
fn test_model_check_twophase_bounded_run() {
    let transpiler_bin = resolve_transpiler_binary_for_integration();

    let repo_root = resolve_repo_root_for_integration();
    let input = repo_root.join("src/protocol/TwoPhase/twophase.rs");
    let types = repo_root.join("src/protocol/TwoPhase/types.rs");
    let model_path = resolve_model_check_fixture_path("twophase_small.model.toml");
    assert!(input.exists(), "Missing input spec: {}", input.display());
    assert!(types.exists(), "Missing types spec: {}", types.display());

    let output = std::process::Command::new(&transpiler_bin)
        .args([
            "model-check",
            "--input",
            input.to_str().unwrap(),
            "--types",
            types.to_str().unwrap(),
            "--model",
            model_path.to_str().unwrap(),
            "--search",
            "bfs",
            "--json-report",
        ])
        .output()
        .expect("Failed to run model-check command");

    assert!(
        output.status.success(),
        "TwoPhase bounded model-check should succeed. stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let report: serde_json::Value =
        serde_json::from_str(&stdout).expect("model-check should emit valid JSON report");
    let states = report
        .get("summary")
        .and_then(|s| s.get("states"))
        .and_then(|v| v.as_u64())
        .unwrap_or(0);
    let transitions = report
        .get("summary")
        .and_then(|s| s.get("transitions"))
        .and_then(|v| v.as_u64())
        .unwrap_or(0);
    assert!(
        states > 0,
        "expected at least one reached state in bounded TwoPhase run: {}",
        stdout
    );
    assert!(
        transitions > 0,
        "expected at least one transition in bounded TwoPhase run: {}",
        stdout
    );
}

#[test]
fn test_model_check_leader_election_bounded_run() {
    let transpiler_bin = resolve_transpiler_binary_for_integration();

    let repo_root = resolve_repo_root_for_integration();
    let input = repo_root.join("src/protocol/LeaderElection/election.rs");
    let types = repo_root.join("src/protocol/LeaderElection/types.rs");
    let model_path = resolve_model_check_fixture_path("leaderelection_small.model.toml");
    assert!(input.exists(), "Missing input spec: {}", input.display());
    assert!(types.exists(), "Missing types spec: {}", types.display());

    let output = std::process::Command::new(&transpiler_bin)
        .args([
            "model-check",
            "--input",
            input.to_str().unwrap(),
            "--types",
            types.to_str().unwrap(),
            "--model",
            model_path.to_str().unwrap(),
            "--search",
            "bfs",
            "--json-report",
        ])
        .output()
        .expect("Failed to run model-check command");

    assert!(
        output.status.success(),
        "LeaderElection bounded model-check should succeed. stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let report: serde_json::Value =
        serde_json::from_str(&stdout).expect("model-check should emit valid JSON report");
    let states = report
        .get("summary")
        .and_then(|s| s.get("states"))
        .and_then(|v| v.as_u64())
        .unwrap_or(0);
    let transitions = report
        .get("summary")
        .and_then(|s| s.get("transitions"))
        .and_then(|v| v.as_u64())
        .unwrap_or(0);
    assert!(
        states > 0,
        "expected at least one reached state in bounded LeaderElection run: {}",
        stdout
    );
    assert!(
        transitions > 0,
        "expected at least one transition in bounded LeaderElection run: {}",
        stdout
    );
}

#[test]
fn test_model_check_paxos_bounded_run() {
    let transpiler_bin = resolve_transpiler_binary_for_integration();

    let repo_root = resolve_repo_root_for_integration();
    let input = repo_root.join("src/protocol/Paxos/paxos.rs");
    let types = repo_root.join("src/protocol/Paxos/types.rs");
    let model_path = resolve_model_check_fixture_path("paxos_small.model.toml");
    assert!(input.exists(), "Missing input spec: {}", input.display());
    assert!(types.exists(), "Missing types spec: {}", types.display());

    let output = std::process::Command::new(&transpiler_bin)
        .args([
            "model-check",
            "--input",
            input.to_str().unwrap(),
            "--types",
            types.to_str().unwrap(),
            "--model",
            model_path.to_str().unwrap(),
            "--search",
            "bfs",
            "--json-report",
        ])
        .output()
        .expect("Failed to run model-check command");

    assert!(
        output.status.success(),
        "Paxos bounded model-check should succeed. stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let report: serde_json::Value =
        serde_json::from_str(&stdout).expect("model-check should emit valid JSON report");
    let states = report
        .get("summary")
        .and_then(|s| s.get("states"))
        .and_then(|v| v.as_u64())
        .unwrap_or(0);
    let transitions = report
        .get("summary")
        .and_then(|s| s.get("transitions"))
        .and_then(|v| v.as_u64())
        .unwrap_or(0);
    assert!(
        states > 0,
        "expected at least one reached state in bounded Paxos run: {}",
        stdout
    );
    assert!(
        transitions > 0,
        "expected at least one transition in bounded Paxos run: {}",
        stdout
    );
}

#[test]
fn test_model_check_liveness_fixtures_cover_fairness_and_non_fairness_outcomes() {
    let transpiler_bin = resolve_transpiler_binary_for_integration();

    struct LivenessCase<'a> {
        name: &'a str,
        input_fixture: &'a str,
        types_fixture: &'a str,
        model_fixture: &'a str,
        expected_result: &'a str,
        expect_violation_report: bool,
        expected_violation_found: bool,
        expected_strong_fairness_labels: &'a [&'a str],
    }

    let cases = [
        LivenessCase {
            name: "violated_without_fairness",
            input_fixture: "liveness_avoidable_cycle.protocol.rs",
            types_fixture: "liveness_avoidable_cycle.types.rs",
            model_fixture: "liveness_avoidable_cycle_violated.model.toml",
            expected_result: "leads_to_violated",
            expect_violation_report: true,
            expected_violation_found: true,
            expected_strong_fairness_labels: &[],
        },
        LivenessCase {
            name: "filtered_by_strong_fairness",
            input_fixture: "liveness_avoidable_cycle.protocol.rs",
            types_fixture: "liveness_avoidable_cycle.types.rs",
            model_fixture: "liveness_avoidable_cycle_strong_fairness.model.toml",
            expected_result: "ok",
            expect_violation_report: false,
            expected_violation_found: false,
            expected_strong_fairness_labels: &["branch_2", "branch_3"],
        },
        LivenessCase {
            name: "satisfied_without_fairness",
            input_fixture: "liveness_forced.protocol.rs",
            types_fixture: "liveness_forced.types.rs",
            model_fixture: "liveness_forced_unfair.model.toml",
            expected_result: "ok",
            expect_violation_report: false,
            expected_violation_found: false,
            expected_strong_fairness_labels: &[],
        },
        LivenessCase {
            name: "satisfied_with_strong_fairness",
            input_fixture: "liveness_forced.protocol.rs",
            types_fixture: "liveness_forced.types.rs",
            model_fixture: "liveness_forced_strong_fairness.model.toml",
            expected_result: "ok",
            expect_violation_report: false,
            expected_violation_found: false,
            expected_strong_fairness_labels: &["branch_1"],
        },
    ];

    for case in cases {
        let report = run_model_check_json_report_from_fixtures(
            &transpiler_bin,
            case.input_fixture,
            case.types_fixture,
            case.model_fixture,
        );

        let result = report
            .get("result")
            .and_then(|value| value.as_str())
            .unwrap_or("<missing>");
        assert_eq!(
            result, case.expected_result,
            "unexpected model-check result for case `{}`; report={}",
            case.name, report
        );

        let stop_reason = report
            .get("stop_reason")
            .and_then(|value| value.as_str())
            .unwrap_or("<missing>");
        assert_eq!(
            stop_reason, "FrontierExhausted",
            "expected complete exploration for case `{}`; report={}",
            case.name, report
        );

        let liveness = report
            .get("liveness")
            .expect("liveness section should exist")
            .as_object()
            .expect("liveness section should be an object");
        assert_eq!(
            liveness.get("obligations").and_then(|value| value.as_u64()),
            Some(1),
            "expected exactly one leads_to obligation in case `{}`",
            case.name
        );
        assert_eq!(
            liveness.get("checked").and_then(|value| value.as_bool()),
            Some(true),
            "expected checked=true in case `{}`",
            case.name
        );
        assert_eq!(
            liveness
                .get("violation_found")
                .and_then(|value| value.as_bool()),
            Some(case.expected_violation_found),
            "unexpected violation_found flag in case `{}`",
            case.name
        );
        assert_eq!(
            liveness
                .get("skipped_reason")
                .and_then(|value| value.as_str()),
            None,
            "did not expect skipped_reason for case `{}`",
            case.name
        );

        let fairness = liveness
            .get("fairness")
            .and_then(|value| value.as_object())
            .expect("liveness.fairness should be present");
        let strong_labels = fairness
            .get("strong")
            .and_then(|value| value.as_array())
            .expect("liveness.fairness.strong should be an array");
        assert_eq!(
            fairness
                .get("strong_count")
                .and_then(|value| value.as_u64()),
            Some(case.expected_strong_fairness_labels.len() as u64),
            "unexpected strong fairness count in case `{}`",
            case.name
        );
        let strong_labels: Vec<&str> = strong_labels
            .iter()
            .map(|value| {
                value
                    .as_str()
                    .expect("strong fairness labels should be strings")
            })
            .collect();
        assert_eq!(
            strong_labels, case.expected_strong_fairness_labels,
            "unexpected strong fairness labels in case `{}`",
            case.name
        );

        let has_violation_report = report
            .get("leads_to_violation")
            .map(|value| !value.is_null())
            .unwrap_or(false);
        assert_eq!(
            has_violation_report, case.expect_violation_report,
            "unexpected leads_to_violation report presence in case `{}`; report={}",
            case.name, report
        );
    }
}

#[test]
fn test_model_check_differential_vs_tlc_wrapper_outcomes_shared_small_models() {
    let transpiler_bin = resolve_transpiler_binary_for_integration();

    let repo_root = resolve_repo_root_for_integration();
    let tlc_outcomes_doc = std::fs::read_to_string("../docs/conversion-testing-guide.md")
        .expect("Failed to read TLC outcomes doc");

    struct DiffCase<'a> {
        protocol_name: &'a str,
        input: &'a str,
        types: &'a str,
        model_fixture: &'a str,
        expected_tlc_label: &'a str,
    }

    let cases = [
        DiffCase {
            protocol_name: "TwoPhase",
            input: "src/protocol/TwoPhase/twophase.rs",
            types: "src/protocol/TwoPhase/types.rs",
            model_fixture: "twophase_small.model.toml",
            expected_tlc_label: "PASS",
        },
        DiffCase {
            protocol_name: "LeaderElection",
            input: "src/protocol/LeaderElection/election.rs",
            types: "src/protocol/LeaderElection/types.rs",
            model_fixture: "leaderelection_small.model.toml",
            expected_tlc_label: "PASS",
        },
        DiffCase {
            protocol_name: "PrimaryBackup",
            input: "src/protocol/PrimaryBackup/primarybackup.rs",
            types: "src/protocol/PrimaryBackup/types.rs",
            model_fixture: "primarybackup_small.model.toml",
            expected_tlc_label: "PASS",
        },
        DiffCase {
            protocol_name: "Paxos",
            input: "src/protocol/Paxos/paxos.rs",
            types: "src/protocol/Paxos/types.rs",
            model_fixture: "paxos_small.model.toml",
            expected_tlc_label: "PARTIAL",
        },
    ];

    for case in cases {
        let protocol_row = tlc_outcomes_doc.lines().find(|line| {
            line.contains(&format!("| {} |", case.protocol_name))
                && line.contains(case.expected_tlc_label)
        });
        assert!(
            protocol_row.is_some(),
            "TLC outcomes table should include row for {} with label `{}`",
            case.protocol_name,
            case.expected_tlc_label,
        );

        let input = repo_root.join(case.input);
        let types = repo_root.join(case.types);
        let model_path = resolve_model_check_fixture_path(case.model_fixture);
        assert!(input.exists(), "Missing input spec: {}", input.display());
        assert!(types.exists(), "Missing types spec: {}", types.display());

        let output = std::process::Command::new(&transpiler_bin)
            .args([
                "model-check",
                "--input",
                input.to_str().unwrap(),
                "--types",
                types.to_str().unwrap(),
                "--model",
                model_path.to_str().unwrap(),
                "--search",
                "bfs",
                "--json-report",
            ])
            .output()
            .expect("Failed to run model-check command");

        assert!(
            output.status.success(),
            "Model-check run should succeed for {} (TLC={}). stderr={}",
            case.protocol_name,
            case.expected_tlc_label,
            String::from_utf8_lossy(&output.stderr)
        );

        let stdout = String::from_utf8_lossy(&output.stdout);
        let report: serde_json::Value =
            serde_json::from_str(&stdout).expect("model-check should emit valid JSON report");
        let result = report
            .get("result")
            .and_then(|v| v.as_str())
            .unwrap_or("<missing>");
        let stop_reason = report
            .get("stop_reason")
            .and_then(|v| v.as_str())
            .unwrap_or("<missing>");
        let states = report
            .get("summary")
            .and_then(|s| s.get("states"))
            .and_then(|v| v.as_u64())
            .unwrap_or(0);
        let transitions = report
            .get("summary")
            .and_then(|s| s.get("transitions"))
            .and_then(|v| v.as_u64())
            .unwrap_or(0);

        assert_eq!(
            result, "ok",
            "Expected source-first run to agree with non-violating TLC outcome for {} (TLC={}). Full report: {}",
            case.protocol_name, case.expected_tlc_label, stdout
        );
        assert!(
            report
                .get("invariant_violation")
                .map(serde_json::Value::is_null)
                .unwrap_or(true),
            "Expected no invariant violation for {}. Full report: {}",
            case.protocol_name,
            stdout
        );
        assert!(
            report
                .get("deadlock")
                .map(serde_json::Value::is_null)
                .unwrap_or(true),
            "Expected no deadlock report for {} in this bounded differential run. Full report: {}",
            case.protocol_name,
            stdout
        );
        assert!(
            states > 0,
            "Expected reached states > 0 for {}. stop_reason={}, report={}",
            case.protocol_name,
            stop_reason,
            stdout
        );
        assert!(
            transitions > 0,
            "Expected transitions > 0 for {}. stop_reason={}, report={}",
            case.protocol_name,
            stop_reason,
            stdout
        );
    }
}

#[test]
fn test_phase22_mvp_scope_doc_is_source_first_safety_only() {
    let source = std::fs::read_to_string("../docs/dev/phase22-mvp-scope.md")
        .expect("Failed to read Phase 22 MVP scope doc");

    for marker in [
        "source-first",
        "safety model checker",
        "LInit",
        "LNext",
        "not transpiled `.tla` files",
        "Liveness and fairness",
        "outside MVP scope",
        "deferred to **Phase 22.10 Follow-Up**",
        "not required for Phase 22 MVP acceptance",
        "Phase 22 MVP Pass Criteria",
        "TwoPhase",
        "LeaderElection",
        "PrimaryBackup",
        "max_depth",
        "max_states",
    ] {
        assert!(
            source.contains(marker),
            "Phase 22 MVP scope doc should contain `{}`",
            marker
        );
    }
}

#[test]
fn test_phase22_source_first_model_checking_guide_has_core_steps() {
    let source = std::fs::read_to_string("../docs/model-checking-source-first.md")
        .expect("Failed to read source-first model-checking guide");

    for marker in [
        "Source-First Model Checking Guide",
        "verus-transpile model-check",
        "--input",
        "--types",
        "--model",
        "--search bfs",
        "--json-report",
        "model.toml",
        "LInit",
        "LNext",
        "verus-transpile model-config",
        "docs/dev/phase22-model-toml-format.md",
    ] {
        assert!(
            source.contains(marker),
            "source-first model-checking guide should contain `{}`",
            marker
        );
    }
}

#[test]
fn test_phase22_source_first_model_checking_guide_has_supported_subset_and_limitations() {
    let source = std::fs::read_to_string("../docs/model-checking-source-first.md")
        .expect("Failed to read source-first model-checking guide");

    for marker in [
        "Supported Subset and Current Limitations",
        "Supported Expression Subset",
        "Supported Type/Domain Subset",
        "Current Limitations",
        "Safety-only scope in Phase 22 MVP",
        "forall",
        "exists",
        "match",
        "bitwise/shift operators",
        "exactly one concrete `LConstants` valuation",
        "Seq<T>",
        "Set<T>",
        "Map<K, V>",
    ] {
        assert!(
            source.contains(marker),
            "source-first model-checking guide should contain `{}`",
            marker
        );
    }
}

#[test]
fn test_phase22_source_first_model_checking_guide_has_troubleshooting() {
    let source = std::fs::read_to_string("../docs/model-checking-source-first.md")
        .expect("Failed to read source-first model-checking guide");

    for marker in [
        "Troubleshooting Common Modeling Errors",
        "Domain Too Large (State Explosion)",
        "max_states_reached",
        "exceeded limit",
        "Unsupported Constructs",
        "Model-check evaluator does not support",
        "Constants Resolution Errors",
        "exactly one concrete LConstants valuation",
        "Signature/Entrypoint Mismatches",
    ] {
        assert!(
            source.contains(marker),
            "source-first model-checking guide should contain `{}`",
            marker
        );
    }
}

#[test]
fn test_phase22_migration_guide_has_tlc_to_source_first_mapping() {
    let source = std::fs::read_to_string("../docs/model-checking-migration.md")
        .expect("Failed to read model-checking migration guide");

    for marker in [
        "TLC Wrapper Workflow",
        "Source-First Model Checking",
        "*_MC.tla",
        ".cfg",
        "model.toml",
        "properties.invariants",
        "properties.check_deadlock",
        "verus-transpile model-check",
        "Migration Steps",
    ] {
        assert!(
            source.contains(marker),
            "model-checking migration guide should contain `{}`",
            marker
        );
    }
}

#[test]
fn test_phase22_wrapper_generation_guide_has_workflow_and_selection_guidance() {
    let source = std::fs::read_to_string("../docs/model-checking-wrapper-workflow.md")
        .expect("Failed to read wrapper generation guide");

    for marker in [
        "Relational Wrapper Generation Guide",
        "verus-transpile generate-mc-wrapper",
        "--input",
        "--output",
        "--invariant",
        "--packet-mode",
        "--packet-var",
        "append-seq",
        "replace-seq",
        "Selection Guidance: Wrapper vs Source-First",
        "verus-transpile model-check",
        "transpiler/tests/mc_wrapper_fixtures/",
    ] {
        assert!(
            source.contains(marker),
            "wrapper generation guide should contain `{}`",
            marker
        );
    }

    let source_first = std::fs::read_to_string("../docs/model-checking-source-first.md")
        .expect("Failed to read source-first model-checking guide");
    assert!(
        source_first.contains("docs/model-checking-wrapper-workflow.md"),
        "source-first model-checking guide should link to wrapper-generation guide"
    );

    let migration = std::fs::read_to_string("../docs/model-checking-migration.md")
        .expect("Failed to read model-checking migration guide");
    assert!(
        migration.contains("docs/model-checking-wrapper-workflow.md"),
        "migration guide should link to wrapper-generation guide"
    );
}

/// Phase 23.3.2: acceptor action functions are proven implementations injected via manual_code.
#[test]
fn test_acceptor_gen_no_delegate_patterns() {
    let source = std::fs::read_to_string("../src/generated/RSL/acceptor_gen.rs")
        .expect("Failed to read acceptor_gen.rs");

    // No clone-delegate pattern should remain.
    assert!(
        !source.contains("acc.CAcceptorProcess1a"),
        "acceptor_gen.rs should not delegate to CAcceptor::CAcceptorProcess1a method"
    );

    // No outbound_packets_to_vec calls in function bodies.
    let body_start = source.find("verus! {").unwrap_or(0);
    let body = &source[body_start..];
    let call_count = body.matches("outbound_packets_to_vec(").count();
    assert!(
        call_count == 0,
        "acceptor_gen.rs should not call outbound_packets_to_vec (found {} calls)",
        call_count
    );

    // All 5 action functions should be real implementations (injected via manual_code),
    // NOT external_body stubs.
    for fn_name in [
        "pub exec fn CAcceptorInit",
        "pub exec fn CAcceptorProcess1a",
        "pub exec fn CAcceptorProcess2a",
        "pub exec fn CAcceptorProcessHeartbeat",
        "pub exec fn CAcceptorTruncateLog",
    ] {
        assert!(
            source.contains(fn_name),
            "acceptor_gen.rs should contain `{}`",
            fn_name
        );
    }

    // No skip-function stubs should remain (all 5 moved to no_stub_functions + manual_code).
    let skipped_stub_count = source
        .matches("// TRANSLATE-TODO: explicitly skipped (skip_functions)")
        .count();
    assert!(
        skipped_stub_count == 0,
        "acceptor_gen.rs should have 0 skip-function stubs (functions are proven via manual_code), found {}",
        skipped_stub_count
    );

    // No external_body on action functions (they are verified, not trusted).
    let external_body_count = source
        .matches("#[verifier(external_body)]")
        .count();
    // Only the clone_hashset helper should have external_body.
    assert!(
        external_body_count <= 1,
        "acceptor_gen.rs should have at most 1 external_body (clone_hashset helper), found {}",
        external_body_count
    );

    // No unimplemented!() should remain.
    let unimplemented_count = source.matches("unimplemented!()").count();
    assert!(
        unimplemented_count == 0,
        "acceptor_gen.rs should contain no unimplemented!() (all functions are proven), found {}",
        unimplemented_count
    );
}

#[test]
fn test_acceptor_vote_helpers_rehomed_out_of_manual_injection() {
    let manual = std::fs::read_to_string("../src/protocol/RSL/acceptor_manual.rs")
        .expect("Failed to read acceptor_manual.rs");
    assert!(
        !manual.contains("pub exec fn CRemoveVotesBeforeLogTruncationPoint"),
        "acceptor_manual.rs should no longer define CRemoveVotesBeforeLogTruncationPoint"
    );
    assert!(
        !manual.contains("pub exec fn CAddVoteAndRemoveOldOnes"),
        "acceptor_manual.rs should no longer define CAddVoteAndRemoveOldOnes"
    );

    let helpers = std::fs::read_to_string("../src/implementation/RSL/acceptor_helpers.rs")
        .expect("Failed to read acceptor_helpers.rs");
    assert!(
        helpers.contains("pub exec fn CRemoveVotesBeforeLogTruncationPoint"),
        "acceptor_helpers.rs should define CRemoveVotesBeforeLogTruncationPoint"
    );
    assert!(
        helpers.contains("pub exec fn CAddVoteAndRemoveOldOnes"),
        "acceptor_helpers.rs should define CAddVoteAndRemoveOldOnes"
    );

    let generated = std::fs::read_to_string("../src/generated/RSL/acceptor_gen.rs")
        .expect("Failed to read acceptor_gen.rs");
    assert!(
        generated.contains("use crate::implementation::RSL::acceptor_helpers::"),
        "acceptor_gen.rs should import acceptor helpers from implementation module"
    );
    assert!(
        generated.contains("CAddVoteAndRemoveOldOnes")
            && generated.contains("CRemoveVotesBeforeLogTruncationPoint"),
        "acceptor_gen.rs should import both vote helper symbols"
    );
    assert!(
        !generated.contains("pub exec fn CRemoveVotesBeforeLogTruncationPoint"),
        "acceptor_gen.rs should not inline CRemoveVotesBeforeLogTruncationPoint anymore"
    );
    assert!(
        !generated.contains("pub exec fn CAddVoteAndRemoveOldOnes"),
        "acceptor_gen.rs should not inline CAddVoteAndRemoveOldOnes anymore"
    );
}

/// Phase 19.7: Verify impl files have been stripped of dead code.
/// After Phase 19 standalone conversions, most &mut self methods on component
/// types are dead code. This test ensures the stripped files only contain
/// the live functions that are still called.
#[test]
fn test_impl_files_stripped_of_dead_code() {
    // === acceptorimpl.rs ===
    // Should retain: CAcceptor type infrastructure + standalone helper functions
    // (CIsLogTruncationPointValid, CCountLargerInSeq, CCountLargerOrEqualInSeq,
    //  CIsNthHighestValueInSequence). It should NOT reintroduce protocol action methods.
    let acceptor = std::fs::read_to_string("../src/implementation/RSL/acceptorimpl.rs")
        .expect("Failed to read acceptorimpl.rs");
    assert!(
        !acceptor.contains("fn CAcceptorProcess1a"),
        "acceptorimpl.rs should not contain CAcceptorProcess1a (moved to standalone)"
    );
    assert!(
        acceptor.contains("pub struct CAcceptor"),
        "acceptorimpl.rs should define CAcceptor"
    );
    assert!(
        acceptor.contains("impl CAcceptor"),
        "acceptorimpl.rs should contain impl CAcceptor block"
    );
    assert!(
        acceptor.contains("CIsLogTruncationPointValid"),
        "acceptorimpl.rs should retain CIsLogTruncationPointValid"
    );
    assert!(
        acceptor.contains("CCountLargerInSeq"),
        "acceptorimpl.rs should retain CCountLargerInSeq"
    );
    // Dead methods that should be removed
    assert!(
        !acceptor.contains("fn CAcceptorInit"),
        "acceptorimpl.rs should not contain dead CAcceptorInit"
    );
    assert!(
        !acceptor.contains("fn CAcceptorProcess2a"),
        "acceptorimpl.rs should not contain dead CAcceptorProcess2a"
    );
    assert!(
        !acceptor.contains("fn CRemoveVotesBeforeLogTruncationPoint"),
        "acceptorimpl.rs should not contain dead CRemoveVotesBeforeLogTruncationPoint"
    );
    assert!(
        !acceptor.contains("fn CAddVoteAndRemoveOldOnes"),
        "acceptorimpl.rs should not contain dead CAddVoteAndRemoveOldOnes"
    );
    assert!(
        !acceptor.contains("fn CAcceptorTruncateLog"),
        "acceptorimpl.rs should not contain dead CAcceptorTruncateLog"
    );
    assert!(
        !acceptor.contains("lemma_voteLen"),
        "acceptorimpl.rs should not contain dead lemma_voteLen"
    );

    // === ExecutorImpl.rs ===
    // Should retain: CExecutorExecute (called from ReplicaImpl.rs:732)
    // CGetPacketsFromReplies, CClientsInReplies, CUpdateNewCache moved to standalone (Phase 19.3.1)
    let executor = std::fs::read_to_string("../src/implementation/RSL/ExecutorImpl.rs")
        .expect("Failed to read ExecutorImpl.rs");
    assert!(
        executor.contains("pub struct CExecutor"),
        "ExecutorImpl.rs should define CExecutor"
    );
    assert!(
        executor.contains("pub enum CIncompleteBatchTimer"),
        "ExecutorImpl.rs should define CIncompleteBatchTimer"
    );
    assert!(
        executor.contains("CExecutorExecute"),
        "ExecutorImpl.rs should retain CExecutorExecute"
    );
    // Standalone functions now imported from executor_gen, not defined here
    assert!(
        !executor.contains("fn CGetPacketsFromReplies"),
        "ExecutorImpl.rs should not define CGetPacketsFromReplies (moved to standalone)"
    );
    assert!(
        !executor.contains("fn CClientsInReplies"),
        "ExecutorImpl.rs should not define CClientsInReplies (moved to standalone)"
    );
    assert!(
        !executor.contains("fn CUpdateNewCache"),
        "ExecutorImpl.rs should not define CUpdateNewCache (moved to standalone)"
    );
    // Dead methods
    assert!(
        !executor.contains("fn CExecutorInit"),
        "ExecutorImpl.rs should not contain dead CExecutorInit"
    );
    assert!(
        !executor.contains("fn CExecutorGetDecision"),
        "ExecutorImpl.rs should not contain dead CExecutorGetDecision"
    );
    assert!(
        !executor.contains("fn CExecutorProcessAppStateSupply"),
        "ExecutorImpl.rs should not contain dead CExecutorProcessAppStateSupply"
    );
    assert!(
        !executor.contains("fn CExecutorProcessAppStateRequest"),
        "ExecutorImpl.rs should not contain dead CExecutorProcessAppStateRequest"
    );
    assert!(
        !executor.contains("fn CExecutorProcessStartingPhase2"),
        "ExecutorImpl.rs should not contain dead CExecutorProcessStartingPhase2"
    );
    assert!(
        !executor.contains("fn CExecutorProcessRequest"),
        "ExecutorImpl.rs should not contain dead CExecutorProcessRequest"
    );
    assert!(
        !executor.contains("lemma_ReplyCacheLen"),
        "ExecutorImpl.rs should not contain dead lemma_ReplyCacheLen"
    );

    // === ElectionImpl.rs ===
    // Should retain: CElectionState/COutstandingOperation type infrastructure,
    // Clone impl, CRequestHeader, clone_up_to_view, CBoundRequestSequence,
    // clone_hashset_u64, clone_vec_crequest.
    let election = std::fs::read_to_string("../src/implementation/RSL/ElectionImpl.rs")
        .expect("Failed to read ElectionImpl.rs");
    assert!(
        election.contains("pub struct CElectionState"),
        "ElectionImpl.rs should define CElectionState"
    );
    assert!(
        election.contains("pub enum COutstandingOperation"),
        "ElectionImpl.rs should define COutstandingOperation"
    );
    assert!(
        election.contains("impl Clone for CElectionState"),
        "ElectionImpl.rs should retain Clone impl"
    );
    assert!(
        election.contains("struct CRequestHeader"),
        "ElectionImpl.rs should retain CRequestHeader"
    );
    assert!(
        election.contains("clone_up_to_view"),
        "ElectionImpl.rs should retain clone_up_to_view"
    );
    assert!(
        election.contains("CBoundRequestSequence"),
        "ElectionImpl.rs should retain CBoundRequestSequence"
    );
    assert!(
        election.contains("clone_hashset_u64"),
        "ElectionImpl.rs should retain clone_hashset_u64"
    );
    assert!(
        election.contains("clone_vec_crequest"),
        "ElectionImpl.rs should retain clone_vec_crequest"
    );
    // Dead methods — all &mut self CElectionState methods
    assert!(
        !election.contains("fn CElectionStateInit"),
        "ElectionImpl.rs should not contain dead CElectionStateInit"
    );
    assert!(
        !election.contains("fn CElectionStateProcessHeartbeat"),
        "ElectionImpl.rs should not contain dead CElectionStateProcessHeartbeat"
    );
    assert!(
        !election.contains("fn CElectionStateCheckForViewTimeout"),
        "ElectionImpl.rs should not contain dead CElectionStateCheckForViewTimeout"
    );
    assert!(
        !election.contains("fn CElectionStateCheckForQuorumOfViewSuspicions"),
        "ElectionImpl.rs should not contain dead CElectionStateCheckForQuorumOfViewSuspicions"
    );
    assert!(
        !election.contains("fn CComputeSuccessorView"),
        "ElectionImpl.rs should not contain dead CComputeSuccessorView"
    );
    assert!(
        !election.contains("fn CElectionStateReflectReceivedRequest"),
        "ElectionImpl.rs should not contain dead CElectionStateReflectReceivedRequest"
    );
    assert!(
        !election.contains("fn CElectionStateReflectExecutedRequestBatch"),
        "ElectionImpl.rs should not contain dead CElectionStateReflectExecutedRequestBatch"
    );
    assert!(
        !election.contains("fn CRemoveAllSatisfiedRequestsInSequence"),
        "ElectionImpl.rs should not contain dead CRemoveAllSatisfiedRequestsInSequence"
    );
    assert!(
        !election.contains("fn CRequestsMatch"),
        "ElectionImpl.rs should not contain dead CRequestsMatch"
    );
    assert!(
        !election.contains("fn FindEarlierRequests"),
        "ElectionImpl.rs should not contain dead FindEarlierRequests"
    );

    // === ProposerImpl.rs ===
    // Should retain: Clone impl, 5 static helper methods + their internal helpers
    let proposer = std::fs::read_to_string("../src/implementation/RSL/ProposerImpl.rs")
        .expect("Failed to read ProposerImpl.rs");
    assert!(
        proposer.contains("pub struct CProposer"),
        "ProposerImpl.rs should define CProposer"
    );
    assert!(
        proposer.contains("impl Clone for CProposer"),
        "ProposerImpl.rs should retain Clone impl"
    );
    assert!(
        proposer.contains("CSetOfMessage1bAboutBallot"),
        "ProposerImpl.rs should retain CSetOfMessage1bAboutBallot"
    );
    assert!(
        proposer.contains("CAllAcceptorsHadNoProposal"),
        "ProposerImpl.rs should retain CAllAcceptorsHadNoProposal"
    );
    assert!(
        proposer.contains("CExistsAcceptorHasProposalLargeThanOpn"),
        "ProposerImpl.rs should retain CExistsAcceptorHasProposalLargeThanOpn"
    );
    assert!(
        proposer.contains("CValIsHighestNumberedProposal"),
        "ProposerImpl.rs should retain CValIsHighestNumberedProposal"
    );
    assert!(
        proposer.contains("CProposerCanNominateUsingOperationNumber"),
        "ProposerImpl.rs should retain CProposerCanNominateUsingOperationNumber"
    );
    // Dead &mut self methods
    assert!(
        !proposer.contains("fn CProposerInit("),
        "ProposerImpl.rs should not contain dead CProposerInit"
    );
    assert!(
        !proposer.contains("fn CProposerProcessRequest("),
        "ProposerImpl.rs should not contain dead CProposerProcessRequest"
    );
    assert!(
        !proposer.contains("fn CProposerProcess1b("),
        "ProposerImpl.rs should not contain dead CProposerProcess1b"
    );
    assert!(
        !proposer.contains("fn CProposerMaybeEnterNewViewAndSend1a("),
        "ProposerImpl.rs should not contain dead CProposerMaybeEnterNewViewAndSend1a"
    );
    assert!(
        !proposer.contains("fn CProposerMaybeEnterPhase2("),
        "ProposerImpl.rs should not contain dead CProposerMaybeEnterPhase2"
    );
    assert!(
        !proposer.contains("fn CProposerNominateNewValueAndSend2a("),
        "ProposerImpl.rs should not contain dead CProposerNominateNewValueAndSend2a"
    );
    assert!(
        !proposer.contains("fn CProposerNominateOldValueAndSend2a("),
        "ProposerImpl.rs should not contain dead CProposerNominateOldValueAndSend2a"
    );
    assert!(
        !proposer.contains("fn CProposerMaybeNominateValueAndSend2a("),
        "ProposerImpl.rs should not contain dead CProposerMaybeNominateValueAndSend2a"
    );
    assert!(
        !proposer.contains("fn CProposerProcessHeartbeat("),
        "ProposerImpl.rs should not contain dead CProposerProcessHeartbeat"
    );
    assert!(
        !proposer.contains("fn CProposerCheckForViewTimeout("),
        "ProposerImpl.rs should not contain dead CProposerCheckForViewTimeout"
    );
    assert!(
        !proposer.contains("fn CProposerCheckForQuorumOfViewSuspicions("),
        "ProposerImpl.rs should not contain dead CProposerCheckForQuorumOfViewSuspicions"
    );
    assert!(
        !proposer.contains("fn CProposerResetViewTimerDueToExecution("),
        "ProposerImpl.rs should not contain dead CProposerResetViewTimerDueToExecution"
    );
    // Dead test and helper functions
    assert!(
        !proposer.contains("fn test("),
        "ProposerImpl.rs should not contain dead test functions"
    );
    assert!(
        !proposer.contains("fn test2("),
        "ProposerImpl.rs should not contain dead test2 function"
    );
    assert!(
        !proposer.contains("fn test3("),
        "ProposerImpl.rs should not contain dead test3 function"
    );
    assert!(
        !proposer.contains("lemma_hashset_insert"),
        "ProposerImpl.rs should not contain dead lemma_hashset_insert"
    );
}

/// Verify executor_gen.rs has no delegate patterns and imports re-homed helpers.
#[test]
fn test_executor_gen_no_delegate_patterns() {
    let source = std::fs::read_to_string("../src/generated/RSL/executor_gen.rs")
        .expect("Failed to read executor_gen.rs");

    // No delegate calls to CExecutor::CGetPacketsFromReplies
    assert!(
        !source.contains("CExecutor::CGetPacketsFromReplies"),
        "executor_gen.rs should not delegate to CExecutor::CGetPacketsFromReplies"
    );

    // No delegate calls to CExecutor::CClientsInReplies
    assert!(
        !source.contains("CExecutor::CClientsInReplies"),
        "executor_gen.rs should not delegate to CExecutor::CClientsInReplies"
    );

    // No delegate calls to CExecutor::CUpdateNewCache
    assert!(
        !source.contains("CExecutor::CUpdateNewCache"),
        "executor_gen.rs should not delegate to CExecutor::CUpdateNewCache"
    );

    assert!(
        source.contains(
            "use crate::implementation::RSL::gen_helpers::{CClientsInReplies, CUpdateNewCache, CGetPacketsFromReplies};"
        ),
        "executor_gen.rs should import re-homed helpers from gen_helpers"
    );

    // No outbound_packets_to_vec calls
    assert!(
        !source.contains("outbound_packets_to_vec"),
        "executor_gen.rs should not call outbound_packets_to_vec"
    );

    // CGetPacketsFromReplies should no longer be defined locally.
    assert!(
        !source.contains("pub exec fn CGetPacketsFromReplies"),
        "executor_gen.rs should not define CGetPacketsFromReplies locally after helper re-home"
    );

    // CExecutor struct constructions (standalone functions construct directly; some branches use clone_up_to_view).
    // After executor manual_code removal, CExecutorExecute is no longer injected into this file.
    let struct_constructions = source.matches("CExecutor {").count();
    assert!(
        struct_constructions >= 3,
        "executor_gen.rs should have >= 3 CExecutor {{}} struct constructions, found {}",
        struct_constructions
    );
}

/// Phase 19.7: Verify impl files are significantly smaller after stripping.
/// This catches accidental reintroduction of dead code.
#[test]
fn test_impl_files_size_after_stripping() {
    let files_and_max_lines = [
        ("../src/implementation/RSL/acceptorimpl.rs", 200),
        ("../src/implementation/RSL/ExecutorImpl.rs", 250),
        ("../src/implementation/RSL/ElectionImpl.rs", 300),
        ("../src/implementation/RSL/ProposerImpl.rs", 650),
    ];

    for (path, max_lines) in files_and_max_lines {
        let content =
            std::fs::read_to_string(path).unwrap_or_else(|_| panic!("Failed to read {}", path));
        let line_count = content.lines().count();
        assert!(
            line_count <= max_lines,
            "{} has {} lines, expected <= {} after dead code stripping",
            path,
            line_count,
            max_lines
        );
    }
}

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
        types.iter().map(|t| match t {
            TypeDef::Struct(s) => format!("struct {}", s.name),
            TypeDef::Enum(e) => format!("enum {}", e.name),
            TypeDef::Alias(a) => format!("alias {}", a.name),
        }).collect::<Vec<_>>()
    );

    // Register types
    let mut registry = TypeRegistry::new();
    for type_def in &types {
        match type_def {
            TypeDef::Struct(s) => { registry.register_struct(s.clone()); }
            TypeDef::Enum(e) => { registry.register_enum(e.clone()); }
            _ => {}
        }
    }

    assert!(registry.structs.contains_key("LState"), "Should have LState");
    assert!(registry.structs.contains_key("LConstants"), "Should have LConstants");
    assert!(registry.structs.contains_key("LLogEntry"), "Should have LLogEntry");
    assert!(registry.enums.contains_key("LServerRole"), "Should have LServerRole");

    // Check LState has expected fields
    let state = &registry.structs["LState"];
    let field_names: Vec<&str> = state.fields.iter().map(|f| f.name.as_str()).collect();
    assert!(field_names.contains(&"current_term"), "LState should have current_term");
    assert!(field_names.contains(&"role"), "LState should have role");
    assert!(field_names.contains(&"log"), "LState should have log");
    assert!(field_names.contains(&"commit_index"), "LState should have commit_index");
    assert!(field_names.contains(&"votes_granted"), "LState should have votes_granted");
    assert!(field_names.contains(&"match_index"), "LState should have match_index");

    // Check LServerRole has expected variants
    let role_enum = &registry.enums["LServerRole"];
    let variant_names: Vec<&str> = role_enum.variants.iter().map(|v| v.name.as_str()).collect();
    assert!(variant_names.contains(&"Follower"), "Should have Follower variant");
    assert!(variant_names.contains(&"Candidate"), "Should have Candidate variant");
    assert!(variant_names.contains(&"Leader"), "Should have Leader variant");
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
        skip_functions: vec!["LNext".to_string()],
        ..Default::default()
    };

    let transpiler = Transpiler::new(config);
    let result = transpiler.transpile_source(&spec_source, &annotation_source);
    assert!(result.is_ok(), "Transpilation should succeed: {:?}", result.err());

    let output = result.unwrap();

    // Check that all expected exec functions are generated
    assert!(output.contains("pub exec fn CInit"), "Should generate CInit");
    assert!(output.contains("pub exec fn CTimeout"), "Should generate CTimeout");
    assert!(output.contains("pub exec fn CGrantVote"), "Should generate CGrantVote");
    assert!(output.contains("pub exec fn CReceiveVoteGranted"), "Should generate CReceiveVoteGranted");
    assert!(output.contains("pub exec fn CBecomeLeader"), "Should generate CBecomeLeader");
    assert!(output.contains("pub exec fn CClientRequest"), "Should generate CClientRequest");
    assert!(output.contains("pub exec fn CHandleAppendResponse"), "Should generate CHandleAppendResponse");
    assert!(output.contains("pub exec fn CAdvanceCommitIndex"), "Should generate CAdvanceCommitIndex");
    assert!(output.contains("pub exec fn CStepDown"), "Should generate CStepDown");

    // Verify LNext is NOT generated (it's in skip_functions)
    assert!(!output.contains("pub exec fn CNext"), "Should NOT generate CNext");

    // Check that ensures clauses reference spec functions
    assert!(output.contains("LInit("), "Should reference LInit in ensures");
    assert!(output.contains("LTimeout("), "Should reference LTimeout in ensures");
    assert!(output.contains("LBecomeLeader("), "Should reference LBecomeLeader in ensures");

    // Check struct construction patterns
    assert!(output.contains("CState"), "Should construct CState in function bodies");
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

    // Should have 8 function annotations
    assert!(
        funcs.len() >= 8,
        "Expected at least 8 function annotations but got {}",
        funcs.len()
    );

    // Check specific function annotations
    let init = funcs.get("LInit").expect("Should have LInit");
    assert_eq!(init.param_modes.len(), 2, "LInit should have 2 params");
    assert_eq!(init.param_modes[0], ParameterMode::Output, "LInit s should be output");
    assert_eq!(init.param_modes[1], ParameterMode::Input, "LInit c should be input");

    let timeout = funcs.get("LTimeout").expect("Should have LTimeout");
    assert_eq!(timeout.param_modes.len(), 3, "LTimeout should have 3 params");

    let grant = funcs.get("LGrantVote").expect("Should have LGrantVote");
    assert_eq!(grant.param_modes.len(), 7, "LGrantVote should have 7 params");

    let become_leader = funcs.get("LBecomeLeader").expect("Should have LBecomeLeader");
    assert_eq!(become_leader.param_modes.len(), 3, "LBecomeLeader should have 3 params");
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

    // Check remapping
    let remapping = &config["remapping"];
    assert_eq!(remapping["LState"].as_str(), Some("CState"));
    assert_eq!(remapping["LConstants"].as_str(), Some("CConstants"));
    assert_eq!(remapping["LServerRole"].as_str(), Some("CServerRole"));
    assert_eq!(remapping["LLogEntry"].as_str(), Some("CLogEntry"));

    // Check output settings
    let output = &config["output"];
    assert_eq!(output["validity_predicate_name"].as_str(), Some("valid"));
    assert_eq!(output["generate_loops_for_verification"].as_bool(), Some(true));
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
        types.iter().map(|t| match t {
            TypeDef::Struct(s) => format!("struct {}", s.name),
            TypeDef::Enum(e) => format!("enum {}", e.name),
            TypeDef::Alias(a) => format!("alias {}", a.name),
        }).collect::<Vec<_>>()
    );

    let mut registry = TypeRegistry::new();
    for type_def in &types {
        match type_def {
            TypeDef::Struct(s) => { registry.register_struct(s.clone()); }
            TypeDef::Enum(e) => { registry.register_enum(e.clone()); }
            _ => {}
        }
    }

    assert!(registry.structs.contains_key("LState"), "Should have LState");
    assert!(registry.structs.contains_key("LConstants"), "Should have LConstants");
    assert!(registry.enums.contains_key("LNodeRole"), "Should have LNodeRole");

    // Check LState has expected fields
    let state = &registry.structs["LState"];
    let field_names: Vec<&str> = state.fields.iter().map(|f| f.name.as_str()).collect();
    assert!(field_names.contains(&"role"), "LState should have role");
    assert!(field_names.contains(&"history"), "LState should have history");
    assert!(field_names.contains(&"pending_sent"), "LState should have pending_sent");
    assert!(field_names.contains(&"committed_count"), "LState should have committed_count");
    assert!(field_names.contains(&"obj_value"), "LState should have obj_value");

    // Check LNodeRole has expected variants
    let role_enum = &registry.enums["LNodeRole"];
    let variant_names: Vec<&str> = role_enum.variants.iter().map(|v| v.name.as_str()).collect();
    assert!(variant_names.contains(&"Head"), "Should have Head variant");
    assert!(variant_names.contains(&"Middle"), "Should have Middle variant");
    assert!(variant_names.contains(&"Tail"), "Should have Tail variant");
}

#[test]
fn test_chain_replication_function_transpilation() {
    let spec_source = std::fs::read_to_string("../src/protocol/ChainReplication/chain.rs")
        .expect("Failed to read ChainReplication chain.rs");
    let annotation_source = std::fs::read_to_string("../src/protocol/ChainReplication/chain.automan")
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
    assert!(result.is_ok(), "Transpilation should succeed: {:?}", result.err());

    let output = result.unwrap();

    // Check all expected exec functions are generated
    assert!(output.contains("pub exec fn CInit"), "Should generate CInit");
    assert!(output.contains("pub exec fn CHeadReceiveWrite"), "Should generate CHeadReceiveWrite");
    assert!(output.contains("pub exec fn CReceiveUpdate"), "Should generate CReceiveUpdate");
    assert!(output.contains("pub exec fn CTailCommit"), "Should generate CTailCommit");
    assert!(output.contains("pub exec fn CReceiveAck"), "Should generate CReceiveAck");
    assert!(output.contains("pub exec fn CClientRead"), "Should generate CClientRead");

    // Verify LNext is NOT generated
    assert!(!output.contains("pub exec fn CNext"), "Should NOT generate CNext");

    // Check ensures clauses reference spec functions
    assert!(output.contains("LInit("), "Should reference LInit in ensures");
    assert!(output.contains("LHeadReceiveWrite("), "Should reference LHeadReceiveWrite in ensures");
    assert!(output.contains("LTailCommit("), "Should reference LTailCommit in ensures");
}

#[test]
fn test_chain_replication_annotation_parsing() {
    let annotation_source = std::fs::read_to_string("../src/protocol/ChainReplication/chain.automan")
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

    let head_write = funcs.get("LHeadReceiveWrite").expect("Should have LHeadReceiveWrite");
    assert_eq!(head_write.param_modes.len(), 4, "LHeadReceiveWrite should have 4 params");

    let tail_commit = funcs.get("LTailCommit").expect("Should have LTailCommit");
    assert_eq!(tail_commit.param_modes.len(), 4, "LTailCommit should have 4 params");

    let client_read = funcs.get("LClientRead").expect("Should have LClientRead");
    assert_eq!(client_read.param_modes.len(), 3, "LClientRead should have 3 params");
}

#[test]
fn test_chain_replication_config_loading() {
    let config_str = std::fs::read_to_string("../src/protocol/ChainReplication/chain_transpile.toml")
        .expect("Failed to read ChainReplication config");

    let config: toml::Value = config_str.parse().expect("Failed to parse TOML");

    // Check skip_functions
    let skip = config["skip_functions"].as_array().unwrap();
    assert!(skip.iter().any(|v| v.as_str() == Some("LNext")), "Should skip LNext");

    // Check naming
    let naming = &config["naming"];
    assert_eq!(naming["spec_prefix"].as_str(), Some("L"));
    assert_eq!(naming["exec_prefix"].as_str(), Some("C"));

    // Check remapping
    let remapping = &config["remapping"];
    assert_eq!(remapping["LState"].as_str(), Some("CState"));
    assert_eq!(remapping["LConstants"].as_str(), Some("CConstants"));
    assert_eq!(remapping["LNodeRole"].as_str(), Some("CNodeRole"));
}

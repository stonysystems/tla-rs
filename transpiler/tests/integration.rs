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

    registry.structs.insert("LAcceptor".to_string(), struct_def);

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
        field_substitutions: HashMap::new(),
        temp_var_counter: std::cell::RefCell::new(0),
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
            registry.structs.insert(s.name.clone(), s);
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
            registry.enums.insert(e.name.clone(), e);
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
                registry.structs.insert(s.name.clone(), s);
            }
            TypeDef::Enum(e) => {
                registry.enums.insert(e.name.clone(), e);
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

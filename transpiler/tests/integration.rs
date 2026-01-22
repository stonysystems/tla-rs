//! Integration tests for the Verus transpiler.

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

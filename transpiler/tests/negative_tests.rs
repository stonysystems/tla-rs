//! Negative tests for error reporting.
//!
//! These tests verify that the transpiler correctly reports errors
//! for invalid inputs, missing annotations, and unsupported patterns.

use std::collections::HashSet;
use verus_transpiler::*;

// ============================================================================
// Missing Mode Annotation Tests
// ============================================================================

#[test]
fn test_missing_annotation_for_function() {
    let spec_source = r#"
    verus! {
        spec fn LUnknownFunction(s: LState, s_: LState) -> bool {
            s_ == s
        }
    }
    "#;

    // Empty annotation - function is not annotated
    let annotation_source = r#"
    # Mode annotations
    "#;

    let transpiler = Transpiler::default();
    let result = transpiler.transpile_source(spec_source, annotation_source);

    // Should succeed but produce empty output (no annotated functions)
    assert!(result.is_ok());
    let output = result.unwrap();
    // Output should be empty (no functions to transpile without annotations)
    assert!(output.is_empty() || !output.contains("exec fn"));
}

#[test]
fn test_annotation_wrong_parameter_count() {
    let parser = AnnotationParser::new(String::new());

    // Try to match a function with 2 params but annotation has 3
    let result = parser.parse_function_line("LTestFunction(+, -, +);");
    assert!(result.is_ok());
    let annotation = result.unwrap();
    assert_eq!(annotation.param_modes.len(), 3);

    // When mode analyzer tries to apply this to a 2-param function,
    // it should detect the mismatch
    let spec_fn = SpecFunction {
        name: "LTestFunction".to_string(),
        generics: ast::Generics::default(),
        params: vec![
            Parameter {
                name: "s".to_string(),
                ty: ast::Type::Named(ast::Path::single("LState".to_string())),
                mode: None,
                variable_mode: ast::VariableMode::default(),
                span: None,
            },
            Parameter {
                name: "s_".to_string(),
                ty: ast::Type::Named(ast::Path::single("LState".to_string())),
                mode: None,
                variable_mode: ast::VariableMode::default(),
                span: None,
            },
        ],
        return_type: ast::Type::Bool,
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        body: ast::Expr::Literal(ast::Literal::Bool(true)),
        span: None,
    };

    let mut analyzer = ModeAnalyzer::new();
    let result = analyzer.annotate(spec_fn, &annotation);

    // This should fail due to parameter count mismatch
    assert!(result.is_err());
    let err = result.unwrap_err();
    let err_str = format!("{}", err);
    assert!(
        err_str.contains("parameter") || err_str.contains("mismatch"),
        "Expected error about parameter count mismatch, got: {}",
        err_str
    );
}

#[test]
fn test_invalid_annotation_syntax() {
    let parser = AnnotationParser::new("fn InvalidSyntax without parens".to_string());
    let result = parser.parse();

    // Parser should handle invalid syntax gracefully
    assert!(result.is_ok());
    // But no functions should be parsed from invalid syntax
    let modules = result.unwrap();
    let total_functions: usize = modules.iter().map(|m| m.functions.len()).sum();
    assert_eq!(total_functions, 0);
}

// ============================================================================
// Saturation Failure Tests
// ============================================================================

#[test]
fn test_saturation_missing_field_assignment() {
    use verus_transpiler::moder::{AssignmentTracker, MemberPath};

    // Only assign one field out of two needed
    let mut tracker = AssignmentTracker::new();
    tracker.record_assignment("s_", MemberPath::root().field("field1".to_string()));

    // When we check saturation, field2 should be missing
    let is_root_assigned = tracker.is_assigned("s_", &MemberPath::Root);
    let is_field1_assigned = tracker.is_assigned("s_", &MemberPath::root().field("field1".to_string()));
    let is_field2_assigned = tracker.is_assigned("s_", &MemberPath::root().field("field2".to_string()));

    // Root should not be considered assigned when only a field is assigned
    assert!(!is_root_assigned);
    assert!(is_field1_assigned);
    assert!(!is_field2_assigned);
}

#[test]
fn test_saturation_no_assignments() {
    use verus_transpiler::moder::{AssignmentTracker, MemberPath};

    let tracker = AssignmentTracker::new(); // No assignments at all

    // Nothing should be assigned
    let is_assigned = tracker.is_assigned("s_", &MemberPath::Root);
    assert!(!is_assigned);
}

// ============================================================================
// Unsupported Pattern Tests
// ============================================================================

#[test]
fn test_unsupported_quantifier_multiple_vars() {
    use verus_transpiler::checker::TemplateMatcher;
    use verus_transpiler::ast::{Binding, Expr, VariableMode};

    // Create forall with multiple bound variables - not supported by our templates
    let expr = Expr::Forall {
        vars: vec![
            Binding {
                name: "i".to_string(),
                ty: Some(ast::Type::Int),
                variable_mode: VariableMode::default(),
            },
            Binding {
                name: "j".to_string(),
                ty: Some(ast::Type::Int),
                variable_mode: VariableMode::default(),
            },
        ],
        triggers: vec![],
        body: Box::new(Expr::Literal(ast::Literal::Bool(true))),
    };

    // Template matcher should not match this
    let result = TemplateMatcher::match_template(&expr);
    assert!(result.is_none());
}

#[test]
fn test_unsupported_quantifier_complex_body() {
    use verus_transpiler::templates::match_expression;
    use verus_transpiler::ast::{Binding, Expr, VariableMode};

    // Create forall that doesn't match any known template
    let expr = Expr::Forall {
        vars: vec![Binding {
            name: "x".to_string(),
            ty: Some(ast::Type::Int),
            variable_mode: VariableMode::default(),
        }],
        triggers: vec![],
        // Body that doesn't match seq/map/set comprehension patterns
        body: Box::new(Expr::Disjunction(vec![
            Expr::Literal(ast::Literal::Bool(true)),
            Expr::Literal(ast::Literal::Bool(false)),
        ])),
    };

    let result = match_expression(&expr, &["result".to_string()]);

    // Should return Unrecognized template
    match result.template {
        templates::QuantifierTemplate::Unrecognized { .. } => {
            // Expected - pattern not recognized
        }
        _ => panic!("Expected Unrecognized template for complex body"),
    }
}

// ============================================================================
// Mode Conflict Tests
// ============================================================================

#[test]
fn test_input_assignment_conflict() {
    use verus_transpiler::moder::ModeAnalyzer;

    let mut analyzer = ModeAnalyzer::new();

    let input_params: HashSet<String> = ["s".to_string()].into_iter().collect();
    let output_params: HashSet<String> = ["s_".to_string()].into_iter().collect();

    // Expr: s == new_value (assigning to input s)
    let expr = ast::Expr::Eq(
        Box::new(ast::Expr::Ident("s".to_string())),
        Box::new(ast::Expr::Literal(ast::Literal::Int(42))),
    );

    let result = analyzer.detect_conflicts(&expr, &input_params, &output_params);

    // Should detect that 's' is being assigned but is marked as input
    assert!(!result.is_empty());
    assert!(result.iter().any(|c| matches!(c, moder::ModeConflict::InputAssignment { .. })));
}

#[test]
fn test_use_before_assignment_conflict() {
    use verus_transpiler::moder::ModeAnalyzer;

    let mut analyzer = ModeAnalyzer::new();
    let input_params: HashSet<String> = ["s".to_string()].into_iter().collect();
    let output_params: HashSet<String> = ["s_".to_string()].into_iter().collect();

    // Expr that uses s_ before assignment: some_func(s_) &&& s_ == value
    // The first conjunct uses s_, second assigns it
    let expr = ast::Expr::Conjunction(vec![
        // Use s_ before it's assigned
        ast::Expr::Call {
            func: ast::Path::single("some_func".to_string()),
            args: vec![ast::Expr::Ident("s_".to_string())],
        },
        // Then try to assign it
        ast::Expr::Eq(
            Box::new(ast::Expr::Ident("s_".to_string())),
            Box::new(ast::Expr::Literal(ast::Literal::Int(42))),
        ),
    ]);

    let result = analyzer.detect_conflicts(&expr, &input_params, &output_params);

    // Should detect use before assignment
    assert!(!result.is_empty());
    assert!(result.iter().any(|c| matches!(c, moder::ModeConflict::UseBeforeAssignment { .. })));
}

// ============================================================================
// Error Message Quality Tests
// ============================================================================

#[test]
fn test_error_messages_contain_context() {
    // Create a parse error
    let error = TranspileError::Parse {
        message: "Unexpected token".to_string(),
        span: None,
    };

    let display = format!("{}", error);
    assert!(display.contains("Unexpected token"));
    assert!(display.contains("parse") || display.contains("Parse"));
}

#[test]
fn test_error_messages_have_suggestions() {
    let error = TranspileError::UnsupportedPattern {
        message: "Quantifier not recognized".to_string(),
        span: None,
        help: Some("Try restructuring as: forall |i| 0 <= i < n ==> ...".to_string()),
    };

    let display = format!("{}", error);
    assert!(display.contains("not recognized"));
}

#[test]
fn test_diagnostic_accumulator_collects_all_errors() {
    let mut acc = DiagnosticAccumulator::new();

    acc.add_error(TranspileError::Parse {
        message: "Error 1".to_string(),
        span: None,
    });
    acc.add_error(TranspileError::Config {
        message: "Error 2".to_string(),
    });
    acc.add_warning(TranspileWarning {
        message: "Warning 1".to_string(),
        span: None,
        suggestion: None,
    });

    assert_eq!(acc.errors.len(), 2);
    assert_eq!(acc.warnings.len(), 1);
    assert!(acc.has_errors());
}

// ============================================================================
// Translator Error Tests
// ============================================================================

#[test]
fn test_translator_forall_without_template() {
    use verus_transpiler::translator::{Translator, TransformContext, TranslatorConfig};

    let translator = Translator::default();
    static CONFIG: std::sync::OnceLock<TranslatorConfig> = std::sync::OnceLock::new();
    let ctx = TransformContext {
        config: CONFIG.get_or_init(TranslatorConfig::default),
        output_params: vec!["s_".to_string()],
        input_params: vec!["s".to_string()],
    };

    // A forall that can't be translated directly
    let expr = ast::Expr::Forall {
        vars: vec![ast::Binding {
            name: "x".to_string(),
            ty: Some(ast::Type::Int),
            variable_mode: ast::VariableMode::default(),
        }],
        triggers: vec![],
        body: Box::new(ast::Expr::Literal(ast::Literal::Bool(true))),
    };

    let result = translator.transform_expr_public(&expr, &ctx);

    // Should return an error about needing template matching
    assert!(result.is_err());
    let err_str = format!("{}", result.unwrap_err());
    assert!(err_str.contains("template") || err_str.contains("Forall") || err_str.contains("quantifier"));
}

#[test]
fn test_translator_exists_not_supported() {
    use verus_transpiler::translator::{Translator, TransformContext, TranslatorConfig};

    let translator = Translator::default();
    static CONFIG: std::sync::OnceLock<TranslatorConfig> = std::sync::OnceLock::new();
    let ctx = TransformContext {
        config: CONFIG.get_or_init(TranslatorConfig::default),
        output_params: vec![],
        input_params: vec![],
    };

    // Exists quantifier - not directly translatable
    let expr = ast::Expr::Exists {
        vars: vec![ast::Binding {
            name: "x".to_string(),
            ty: Some(ast::Type::Int),
            variable_mode: ast::VariableMode::default(),
        }],
        body: Box::new(ast::Expr::Literal(ast::Literal::Bool(true))),
    };

    let result = translator.transform_expr_public(&expr, &ctx);

    // Should return an error
    assert!(result.is_err());
    let err_str = format!("{}", result.unwrap_err());
    assert!(err_str.contains("Exists") || err_str.contains("cannot") || err_str.contains("quantifier"));
}

//! Mode analysis for spec functions.
//!
//! This module performs mode analysis on annotated spec functions to:
//! - Propagate modes through expressions
//! - Track output variable assignments
//! - Detect mode conflicts
//! - Classify predicates for translation

use crate::ast::{Expr, Parameter, ParameterMode, SpecFunction};
use crate::annotation::FunctionAnnotation;
use crate::error::{DiagnosticAccumulator, TranspileError, TranspileResult};
use std::collections::{HashMap, HashSet};

/// Annotated function with mode information
#[derive(Debug, Clone)]
pub struct AnnotatedFunction {
    /// Original spec function
    pub spec_fn: SpecFunction,
    /// Parameter modes (from annotation)
    pub param_modes: Vec<ParameterMode>,
    /// Whether this can be functionalized
    pub is_functionalizable: bool,
    /// Reason if not functionalizable
    pub non_functionalizable_reason: Option<String>,
}

/// Member path for tracking field assignments
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum MemberPath {
    /// The variable itself
    Root,
    /// Field access (.field)
    Field(Box<MemberPath>, String),
    /// Index access ([idx])
    Index(Box<MemberPath>),
}

impl MemberPath {
    /// Create a root path
    pub fn root() -> Self {
        Self::Root
    }

    /// Add a field access to this path
    pub fn field(self, name: String) -> Self {
        Self::Field(Box::new(self), name)
    }

    /// Add an index access to this path
    pub fn index(self) -> Self {
        Self::Index(Box::new(self))
    }
}

/// Tracks assignments to output variables
#[derive(Debug, Default)]
pub struct AssignmentTracker {
    /// Maps output variable name to set of assigned member paths
    pub assignments: HashMap<String, HashSet<MemberPath>>,
}

impl AssignmentTracker {
    /// Create a new assignment tracker
    pub fn new() -> Self {
        Self::default()
    }

    /// Record an assignment to a member path
    pub fn record_assignment(&mut self, var_name: &str, path: MemberPath) {
        self.assignments
            .entry(var_name.to_string())
            .or_default()
            .insert(path);
    }

    /// Check if a member path has been assigned
    pub fn is_assigned(&self, var_name: &str, path: &MemberPath) -> bool {
        self.assignments
            .get(var_name)
            .map(|paths| paths.contains(path))
            .unwrap_or(false)
    }
}

/// Classification of predicates for translation
#[derive(Debug, Clone)]
pub enum PredicateKind {
    /// Can be fully functionalized (converted to exec)
    Functional {
        inputs: Vec<Parameter>,
        outputs: Vec<Parameter>,
    },
    /// Cannot functionalize, generate stub
    Stub { reason: String },
    /// Pure predicate, no functionalization needed
    Pure,
}

/// Mode analyzer
pub struct ModeAnalyzer {
    diagnostics: DiagnosticAccumulator,
}

impl ModeAnalyzer {
    /// Create a new mode analyzer
    pub fn new() -> Self {
        Self {
            diagnostics: DiagnosticAccumulator::new(),
        }
    }

    /// Annotate a spec function with mode information
    pub fn annotate(
        &mut self,
        spec_fn: SpecFunction,
        annotation: &FunctionAnnotation,
    ) -> TranspileResult<AnnotatedFunction> {
        // Validate annotation matches function
        if spec_fn.params.len() != annotation.param_modes.len() {
            return Err(TranspileError::Annotation {
                message: format!(
                    "Parameter count mismatch: function has {} params, annotation has {}",
                    spec_fn.params.len(),
                    annotation.param_modes.len()
                ),
                span: None, // TODO: Convert proc_macro2::Span to miette::SourceSpan
            });
        }

        let param_modes = annotation.param_modes.clone();

        // Check if function can be functionalized
        let (is_functionalizable, reason) = self.check_functionalizable(&spec_fn, &param_modes);

        Ok(AnnotatedFunction {
            spec_fn,
            param_modes,
            is_functionalizable,
            non_functionalizable_reason: reason,
        })
    }

    /// Check if a function can be functionalized
    fn check_functionalizable(
        &self,
        _spec_fn: &SpecFunction,
        param_modes: &[ParameterMode],
    ) -> (bool, Option<String>) {
        // Must have at least one output
        let has_output = param_modes.contains(&ParameterMode::Output);
        if !has_output {
            return (false, Some("No output parameters".to_string()));
        }

        // TODO: Add more checks (unsupported patterns, etc.)
        (true, None)
    }

    /// Classify a predicate based on its structure
    pub fn classify_predicate(&self, func: &AnnotatedFunction) -> PredicateKind {
        if !func.is_functionalizable {
            return PredicateKind::Stub {
                reason: func
                    .non_functionalizable_reason
                    .clone()
                    .unwrap_or_else(|| "Unknown reason".to_string()),
            };
        }

        let inputs: Vec<_> = func
            .spec_fn
            .params
            .iter()
            .zip(&func.param_modes)
            .filter(|(_, mode)| **mode == ParameterMode::Input)
            .map(|(p, _)| p.clone())
            .collect();

        let outputs: Vec<_> = func
            .spec_fn
            .params
            .iter()
            .zip(&func.param_modes)
            .filter(|(_, mode)| **mode == ParameterMode::Output)
            .map(|(p, _)| p.clone())
            .collect();

        if outputs.is_empty() {
            PredicateKind::Pure
        } else {
            PredicateKind::Functional { inputs, outputs }
        }
    }

    /// Analyze mode propagation within an expression
    ///
    /// This traverses the expression tree and:
    /// - Identifies assignments to output variables
    /// - Records them in the tracker
    #[allow(clippy::only_used_in_recursion)] // Will use self for diagnostics accumulation
    pub fn analyze_expression(
        &mut self,
        expr: &Expr,
        tracker: &mut AssignmentTracker,
        output_params: &HashSet<String>,
    ) {
        match expr {
            // Conjunction chains - analyze each clause
            Expr::Conjunction(clauses) => {
                for clause in clauses {
                    self.analyze_expression(clause, tracker, output_params);
                }
            }

            // Disjunction chains - analyze each clause
            Expr::Disjunction(clauses) => {
                for clause in clauses {
                    self.analyze_expression(clause, tracker, output_params);
                }
            }

            // Equality - this is where assignments happen in specs
            Expr::Eq(left, right) => {
                Self::analyze_equality(left, right, tracker, output_params);
            }

            // Binary operators - recurse into operands
            Expr::Binary(left, _, right) => {
                self.analyze_expression(left, tracker, output_params);
                self.analyze_expression(right, tracker, output_params);
            }

            // Implications - analyze both sides
            Expr::Implies(premise, conclusion) => {
                self.analyze_expression(premise, tracker, output_params);
                self.analyze_expression(conclusion, tracker, output_params);
            }

            // Conditionals - analyze both branches
            Expr::If { cond, then_branch, else_branch } => {
                self.analyze_expression(cond, tracker, output_params);
                self.analyze_expression(then_branch, tracker, output_params);
                if let Some(else_expr) = else_branch {
                    self.analyze_expression(else_expr, tracker, output_params);
                }
            }

            // Let bindings - analyze value and body
            Expr::Let { value, body, .. } => {
                self.analyze_expression(value, tracker, output_params);
                self.analyze_expression(body, tracker, output_params);
            }

            // Match expressions - analyze arms
            Expr::Match { scrutinee, arms } => {
                self.analyze_expression(scrutinee, tracker, output_params);
                for arm in arms {
                    self.analyze_expression(&arm.body, tracker, output_params);
                }
            }

            // Forall/Exists - analyze body
            Expr::Forall { body, .. } | Expr::Exists { body, .. } => {
                self.analyze_expression(body, tracker, output_params);
            }

            // Other expression types don't contain assignments
            _ => {}
        }
    }

    /// Analyze an equality expression for output assignments
    fn analyze_equality(
        left: &Expr,
        right: &Expr,
        tracker: &mut AssignmentTracker,
        output_params: &HashSet<String>,
    ) {
        // Check if left side is an output path
        if let Some((var, path)) = Self::extract_output_path(left, output_params) {
            tracker.record_assignment(&var, path);
        }
        // Also check right side (less common but valid in specs)
        else if let Some((var, path)) = Self::extract_output_path(right, output_params) {
            tracker.record_assignment(&var, path);
        }
    }

    /// Extract an output variable path from an expression
    ///
    /// Returns Some((var_name, path)) if the expression is an output parameter
    /// or a field access on an output parameter.
    fn extract_output_path(
        expr: &Expr,
        output_params: &HashSet<String>,
    ) -> Option<(String, MemberPath)> {
        match expr {
            // Direct identifier reference
            Expr::Ident(name) if output_params.contains(name) => {
                Some((name.clone(), MemberPath::Root))
            }

            // Field access: base.field
            Expr::Field(base, field) => {
                if let Some((var, path)) = Self::extract_output_path(base, output_params) {
                    Some((var, path.field(field.clone())))
                } else {
                    None
                }
            }

            // Index access: base[idx]
            Expr::Index(base, _) => {
                if let Some((var, path)) = Self::extract_output_path(base, output_params) {
                    Some((var, path.index()))
                } else {
                    None
                }
            }

            _ => None,
        }
    }

    /// Get accumulated diagnostics
    pub fn diagnostics(&self) -> &DiagnosticAccumulator {
        &self.diagnostics
    }
}

impl Default for ModeAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Expr, Path, Type};

    #[test]
    fn test_member_path() {
        let path = MemberPath::root().field("max_bal".to_string());
        assert!(matches!(path, MemberPath::Field(_, _)));
    }

    #[test]
    fn test_assignment_tracker() {
        let mut tracker = AssignmentTracker::new();
        let path = MemberPath::root().field("max_bal".to_string());

        tracker.record_assignment("s_", path.clone());
        assert!(tracker.is_assigned("s_", &path));
        assert!(!tracker.is_assigned("s_", &MemberPath::root()));
    }

    #[test]
    fn test_annotate_function() {
        use crate::ast::VariableMode;
        let spec_fn = SpecFunction {
            name: "TestFn".to_string(),
            generics: Default::default(),
            params: vec![
                Parameter {
                    name: "s".to_string(),
                    ty: Type::Named(Path::single("State".to_string())),
                    mode: None,
                    variable_mode: VariableMode::Exec,
                    span: None,
                },
                Parameter {
                    name: "s_".to_string(),
                    ty: Type::Named(Path::single("State".to_string())),
                    mode: None,
                    variable_mode: VariableMode::Exec,
                    span: None,
                },
            ],
            return_type: Type::Bool,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body: Expr::Literal(crate::ast::Literal::Bool(true)),
            span: None,
        };

        let annotation = FunctionAnnotation {
            name: "TestFn".to_string(),
            param_modes: vec![ParameterMode::Input, ParameterMode::Output],
        };

        let mut analyzer = ModeAnalyzer::new();
        let result = analyzer.annotate(spec_fn, &annotation);
        assert!(result.is_ok());

        let annotated = result.unwrap();
        assert!(annotated.is_functionalizable);
        assert_eq!(annotated.param_modes.len(), 2);
    }

    #[test]
    fn test_analyze_simple_equality() {
        let mut analyzer = ModeAnalyzer::new();
        let mut tracker = AssignmentTracker::new();
        let output_params: HashSet<String> = ["s_".to_string()].into_iter().collect();

        // Expression: s_ == s
        let expr = Expr::Eq(
            Box::new(Expr::Ident("s_".to_string())),
            Box::new(Expr::Ident("s".to_string())),
        );

        analyzer.analyze_expression(&expr, &mut tracker, &output_params);

        assert!(tracker.is_assigned("s_", &MemberPath::Root));
    }

    #[test]
    fn test_analyze_field_assignment() {
        let mut analyzer = ModeAnalyzer::new();
        let mut tracker = AssignmentTracker::new();
        let output_params: HashSet<String> = ["s_".to_string()].into_iter().collect();

        // Expression: s_.max_bal == bal
        let expr = Expr::Eq(
            Box::new(Expr::Field(
                Box::new(Expr::Ident("s_".to_string())),
                "max_bal".to_string(),
            )),
            Box::new(Expr::Ident("bal".to_string())),
        );

        analyzer.analyze_expression(&expr, &mut tracker, &output_params);

        let expected_path = MemberPath::root().field("max_bal".to_string());
        assert!(tracker.is_assigned("s_", &expected_path));
    }

    #[test]
    fn test_analyze_conjunction() {
        let mut analyzer = ModeAnalyzer::new();
        let mut tracker = AssignmentTracker::new();
        let output_params: HashSet<String> =
            ["s_".to_string(), "packets".to_string()].into_iter().collect();

        // Expression: &&& s_.max_bal == bal &&& packets == seq![]
        let expr = Expr::Conjunction(vec![
            Expr::Eq(
                Box::new(Expr::Field(
                    Box::new(Expr::Ident("s_".to_string())),
                    "max_bal".to_string(),
                )),
                Box::new(Expr::Ident("bal".to_string())),
            ),
            Expr::Eq(
                Box::new(Expr::Ident("packets".to_string())),
                Box::new(Expr::SeqLit(vec![])),
            ),
        ]);

        analyzer.analyze_expression(&expr, &mut tracker, &output_params);

        let max_bal_path = MemberPath::root().field("max_bal".to_string());
        assert!(tracker.is_assigned("s_", &max_bal_path));
        assert!(tracker.is_assigned("packets", &MemberPath::Root));
    }

    #[test]
    fn test_analyze_conditional() {
        let mut analyzer = ModeAnalyzer::new();
        let mut tracker = AssignmentTracker::new();
        let output_params: HashSet<String> = ["s_".to_string()].into_iter().collect();

        // Expression: if cond { s_ == new_state } else { s_ == s }
        let expr = Expr::If {
            cond: Box::new(Expr::Ident("cond".to_string())),
            then_branch: Box::new(Expr::Eq(
                Box::new(Expr::Ident("s_".to_string())),
                Box::new(Expr::Ident("new_state".to_string())),
            )),
            else_branch: Some(Box::new(Expr::Eq(
                Box::new(Expr::Ident("s_".to_string())),
                Box::new(Expr::Ident("s".to_string())),
            ))),
        };

        analyzer.analyze_expression(&expr, &mut tracker, &output_params);

        // Both branches should have recorded the assignment
        // (tracker doesn't track which branch, just that it was assigned)
        assert!(tracker.is_assigned("s_", &MemberPath::Root));
    }
}

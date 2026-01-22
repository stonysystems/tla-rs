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
    pub fn analyze_expression(&mut self, _expr: &Expr, _tracker: &mut AssignmentTracker) {
        // TODO: Implement expression analysis
        // This will traverse the expression and:
        // - Track assignments to output variables
        // - Detect mode conflicts
        // - Build dependency graph
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
        let spec_fn = SpecFunction {
            name: "TestFn".to_string(),
            generics: Default::default(),
            params: vec![
                Parameter {
                    name: "s".to_string(),
                    ty: Type::Named(Path::single("State".to_string())),
                    mode: None,
                    span: None,
                },
                Parameter {
                    name: "s_".to_string(),
                    ty: Type::Named(Path::single("State".to_string())),
                    mode: None,
                    span: None,
                },
            ],
            return_type: Type::Bool,
            recommends: vec![],
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
}

//! Mode analysis for spec functions.
//!
//! This module performs mode analysis on annotated spec functions to:
//! - Propagate modes through expressions
//! - Track output variable assignments
//! - Detect mode conflicts
//! - Classify predicates for translation

use crate::annotation::FunctionAnnotation;
use crate::ast::{Expr, Parameter, ParameterMode, SpecFunction};
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

/// Mode conflict types detected during analysis
#[derive(Debug, Clone)]
pub enum ModeConflict {
    /// Output variable used before it was assigned
    UseBeforeAssignment { var: String, context: String },
    /// Input variable appears on left side of assignment
    InputAssignment { var: String },
    /// Different branches assign different output variables
    BranchMismatch {
        branch1_assigns: HashSet<String>,
        branch2_assigns: HashSet<String>,
    },
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
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
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

    /// Detect mode conflicts during expression analysis
    ///
    /// This performs a more thorough analysis that:
    /// - Tracks which outputs have been assigned
    /// - Detects input variables being assigned
    /// - Checks branch consistency
    pub fn detect_conflicts(
        &mut self,
        expr: &Expr,
        input_params: &HashSet<String>,
        output_params: &HashSet<String>,
    ) -> Vec<ModeConflict> {
        let mut conflicts = Vec::new();
        self.detect_conflicts_inner(
            expr,
            input_params,
            output_params,
            &HashSet::new(),
            &mut conflicts,
        );
        conflicts
    }

    fn detect_conflicts_inner(
        &self,
        expr: &Expr,
        input_params: &HashSet<String>,
        output_params: &HashSet<String>,
        already_assigned: &HashSet<String>,
        conflicts: &mut Vec<ModeConflict>,
    ) -> HashSet<String> {
        let mut newly_assigned = already_assigned.clone();

        match expr {
            Expr::Conjunction(clauses) => {
                for clause in clauses {
                    let assigned_here = self.detect_conflicts_inner(
                        clause,
                        input_params,
                        output_params,
                        &newly_assigned,
                        conflicts,
                    );
                    newly_assigned.extend(assigned_here);
                }
            }

            Expr::Eq(left, right) => {
                // Determine which side is the assignment target
                // In spec predicates, the output variable side is the target
                let left_is_output = Self::extract_output_path(left, output_params).is_some();
                let right_is_output = Self::extract_output_path(right, output_params).is_some();
                let left_is_input = Self::extract_any_param_path(left, input_params).is_some();
                let right_is_input = Self::extract_any_param_path(right, input_params).is_some();

                // Check if we're assigning to an input (input on the "target" side)
                // Only flag as conflict if an input is the root being assigned (not just used)
                if left_is_input && !right_is_output {
                    // Left is input and right is not an output - this means left is being "assigned"
                    if let Some((var, _)) = Self::extract_any_param_path(left, input_params) {
                        conflicts.push(ModeConflict::InputAssignment { var: var.clone() });
                    }
                } else if right_is_input && !left_is_output {
                    // Right is input and left is not an output - unusual, flag it
                    if let Some((var, _)) = Self::extract_any_param_path(right, input_params) {
                        conflicts.push(ModeConflict::InputAssignment { var: var.clone() });
                    }
                }

                // Check for assignment to output
                if let Some((var, _)) = Self::extract_output_path(left, output_params) {
                    newly_assigned.insert(var);
                } else if let Some((var, _)) = Self::extract_output_path(right, output_params) {
                    newly_assigned.insert(var);
                }

                // Check if we're using unassigned outputs
                self.check_use_before_assignment(left, output_params, &newly_assigned, conflicts);
                self.check_use_before_assignment(right, output_params, &newly_assigned, conflicts);
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                // Check condition for conflicts
                self.detect_conflicts_inner(
                    cond,
                    input_params,
                    output_params,
                    &newly_assigned,
                    conflicts,
                );

                // Analyze both branches
                let then_assigned = self.detect_conflicts_inner(
                    then_branch,
                    input_params,
                    output_params,
                    &newly_assigned,
                    conflicts,
                );

                if let Some(else_expr) = else_branch {
                    let else_assigned = self.detect_conflicts_inner(
                        else_expr,
                        input_params,
                        output_params,
                        &newly_assigned,
                        conflicts,
                    );

                    // Check for branch mismatch
                    if then_assigned != else_assigned {
                        conflicts.push(ModeConflict::BranchMismatch {
                            branch1_assigns: then_assigned
                                .difference(&newly_assigned)
                                .cloned()
                                .collect(),
                            branch2_assigns: else_assigned
                                .difference(&newly_assigned)
                                .cloned()
                                .collect(),
                        });
                    }

                    // Both branches must assign the same outputs
                    newly_assigned.extend(then_assigned.intersection(&else_assigned).cloned());
                } else {
                    // No else branch - then branch outputs are assigned
                    newly_assigned.extend(then_assigned);
                }
            }

            // For other expressions, recursively check
            Expr::Binary(left, _, right) => {
                self.check_use_before_assignment(left, output_params, &newly_assigned, conflicts);
                self.check_use_before_assignment(right, output_params, &newly_assigned, conflicts);
            }

            Expr::Implies(premise, conclusion) => {
                self.detect_conflicts_inner(
                    premise,
                    input_params,
                    output_params,
                    &newly_assigned,
                    conflicts,
                );
                self.detect_conflicts_inner(
                    conclusion,
                    input_params,
                    output_params,
                    &newly_assigned,
                    conflicts,
                );
            }

            Expr::Call { args, .. } | Expr::MethodCall { args, .. } => {
                // Check for use of unassigned outputs in function arguments
                for arg in args {
                    self.check_use_before_assignment(
                        arg,
                        output_params,
                        &newly_assigned,
                        conflicts,
                    );
                }
            }

            _ => {}
        }

        newly_assigned
    }

    /// Check if an expression uses an output variable that hasn't been assigned yet
    #[allow(clippy::only_used_in_recursion)] // Method for future extension with diagnostics
    fn check_use_before_assignment(
        &self,
        expr: &Expr,
        output_params: &HashSet<String>,
        already_assigned: &HashSet<String>,
        conflicts: &mut Vec<ModeConflict>,
    ) {
        match expr {
            Expr::Ident(name)
                if output_params.contains(name) && !already_assigned.contains(name) =>
            {
                conflicts.push(ModeConflict::UseBeforeAssignment {
                    var: name.clone(),
                    context: "expression".to_string(),
                });
            }
            Expr::Field(base, _) | Expr::Index(base, _) => {
                self.check_use_before_assignment(base, output_params, already_assigned, conflicts);
            }
            Expr::Binary(left, _, right) => {
                self.check_use_before_assignment(left, output_params, already_assigned, conflicts);
                self.check_use_before_assignment(right, output_params, already_assigned, conflicts);
            }
            Expr::Call { args, .. } | Expr::MethodCall { args, .. } => {
                for arg in args {
                    self.check_use_before_assignment(
                        arg,
                        output_params,
                        already_assigned,
                        conflicts,
                    );
                }
            }
            _ => {}
        }
    }

    /// Extract a parameter path regardless of whether it's input or output
    fn extract_any_param_path(
        expr: &Expr,
        params: &HashSet<String>,
    ) -> Option<(String, MemberPath)> {
        match expr {
            Expr::Ident(name) if params.contains(name) => Some((name.clone(), MemberPath::Root)),
            Expr::Field(base, field) => {
                if let Some((var, path)) = Self::extract_any_param_path(base, params) {
                    Some((var, path.field(field.clone())))
                } else {
                    None
                }
            }
            Expr::Index(base, _) => {
                if let Some((var, path)) = Self::extract_any_param_path(base, params) {
                    Some((var, path.index()))
                } else {
                    None
                }
            }
            _ => None,
        }
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
            kind: crate::ast::FunctionKind::Predicate,
            param_modes: vec![ParameterMode::Input, ParameterMode::Output],
            return_type: None,
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
        let output_params: HashSet<String> = ["s_".to_string(), "packets".to_string()]
            .into_iter()
            .collect();

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

    #[test]
    fn test_detect_input_assignment_conflict() {
        let mut analyzer = ModeAnalyzer::new();
        let input_params: HashSet<String> = ["s".to_string()].into_iter().collect();
        let output_params: HashSet<String> = ["s_".to_string()].into_iter().collect();

        // Expression: s.field == value (assigning to input is invalid)
        let expr = Expr::Eq(
            Box::new(Expr::Field(
                Box::new(Expr::Ident("s".to_string())),
                "field".to_string(),
            )),
            Box::new(Expr::Ident("value".to_string())),
        );

        let conflicts = analyzer.detect_conflicts(&expr, &input_params, &output_params);
        assert!(!conflicts.is_empty());
        assert!(matches!(conflicts[0], ModeConflict::InputAssignment { .. }));
    }

    #[test]
    fn test_detect_branch_mismatch_conflict() {
        let mut analyzer = ModeAnalyzer::new();
        let input_params: HashSet<String> = HashSet::new();
        let output_params: HashSet<String> = ["s_".to_string(), "packets".to_string()]
            .into_iter()
            .collect();

        // Expression: if cond { s_ == new } else { packets == empty }
        // This is a branch mismatch - different outputs in each branch
        let expr = Expr::If {
            cond: Box::new(Expr::Ident("cond".to_string())),
            then_branch: Box::new(Expr::Eq(
                Box::new(Expr::Ident("s_".to_string())),
                Box::new(Expr::Ident("new".to_string())),
            )),
            else_branch: Some(Box::new(Expr::Eq(
                Box::new(Expr::Ident("packets".to_string())),
                Box::new(Expr::SeqEmpty),
            ))),
        };

        let conflicts = analyzer.detect_conflicts(&expr, &input_params, &output_params);
        assert!(!conflicts.is_empty());
        assert!(matches!(conflicts[0], ModeConflict::BranchMismatch { .. }));
    }

    #[test]
    fn test_no_conflict_valid_expression() {
        let mut analyzer = ModeAnalyzer::new();
        let input_params: HashSet<String> = ["s".to_string()].into_iter().collect();
        let output_params: HashSet<String> = ["s_".to_string()].into_iter().collect();

        // Expression: s_ == compute(s) - valid, assigning to output using input
        let expr = Expr::Eq(
            Box::new(Expr::Ident("s_".to_string())),
            Box::new(Expr::Ident("s".to_string())),
        );

        let conflicts = analyzer.detect_conflicts(&expr, &input_params, &output_params);
        assert!(conflicts.is_empty());
    }
}

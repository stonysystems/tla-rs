//! Mode analysis for spec functions.
//!
//! This module performs mode analysis on annotated spec functions to:
//! - Propagate modes through expressions
//! - Track output variable assignments
//! - Detect mode conflicts
//! - Classify predicates for translation

use crate::annotation::FunctionAnnotation;
use crate::ast::{Expr, FunctionKind, Parameter, ParameterMode, SpecFunction};
use crate::error::{DiagnosticAccumulator, TranspileError, TranspileResult};
use std::collections::{HashMap, HashSet};

/// Annotated function with mode information
#[derive(Debug, Clone)]
pub struct AnnotatedFunction {
    /// Original spec function
    pub spec_fn: SpecFunction,
    /// Function kind (predicate or helper)
    pub kind: FunctionKind,
    /// Parameter modes (from annotation)
    pub param_modes: Vec<ParameterMode>,
    /// Return type for helper functions (e.g., "Ballot", "Seq<Request>")
    pub return_type: Option<String>,
    /// Whether this function is recursive (calls itself)
    pub is_recursive: bool,
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

impl std::fmt::Display for MemberPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MemberPath::Root => write!(f, "<root>"),
            MemberPath::Field(base, name) => write!(f, "{}.{}", base, name),
            MemberPath::Index(base) => write!(f, "{}[_]", base),
        }
    }
}

/// Tracks assignments to output variables
#[derive(Debug, Default)]
pub struct AssignmentTracker {
    /// Maps output variable name to set of assigned member paths
    pub assignments: HashMap<String, HashSet<MemberPath>>,
    /// Counts how many times each (variable, path) pair has been assigned
    assignment_counts: HashMap<(String, MemberPath), usize>,
}

impl AssignmentTracker {
    /// Create a new assignment tracker
    pub fn new() -> Self {
        Self::default()
    }

    /// Record an assignment to a member path
    pub fn record_assignment(&mut self, var_name: &str, path: MemberPath) {
        *self
            .assignment_counts
            .entry((var_name.to_string(), path.clone()))
            .or_insert(0) += 1;
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

    /// Get the number of times a (variable, path) pair was assigned
    pub fn get_count(&self, var_name: &str, path: &MemberPath) -> usize {
        self.assignment_counts
            .get(&(var_name.to_string(), path.clone()))
            .copied()
            .unwrap_or(0)
    }

    /// Iterate over all (variable, path) pairs with their assignment counts
    pub fn assignment_counts(&self) -> impl Iterator<Item = (&(String, MemberPath), &usize)> {
        self.assignment_counts.iter()
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
        let kind = annotation.kind;
        let return_type = annotation.return_type.clone();

        // Check if function is recursive
        let is_recursive = Self::is_recursive(&spec_fn);

        // Check if function can be functionalized (different logic for helpers vs predicates)
        let (is_functionalizable, reason) =
            self.check_functionalizable(&spec_fn, &param_modes, kind);

        Ok(AnnotatedFunction {
            spec_fn,
            kind,
            param_modes,
            return_type,
            is_recursive,
            is_functionalizable,
            non_functionalizable_reason: reason,
        })
    }

    /// Check if a function can be functionalized
    fn check_functionalizable(
        &self,
        spec_fn: &SpecFunction,
        param_modes: &[ParameterMode],
        kind: FunctionKind,
    ) -> (bool, Option<String>) {
        match kind {
            FunctionKind::Predicate => {
                // Predicates must have at least one output
                let has_output = param_modes.contains(&ParameterMode::Output);
                if !has_output {
                    return (false, Some("No output parameters".to_string()));
                }

                // Collect output parameter names for body analysis
                let output_names: HashSet<String> = spec_fn
                    .params
                    .iter()
                    .zip(param_modes)
                    .filter(|(_, mode)| **mode == ParameterMode::Output)
                    .map(|(p, _)| p.name.clone())
                    .collect();

                // Check for output parameters assigned inside quantifier bodies
                if let Some(reason) =
                    Self::check_output_in_quantifier(&spec_fn.body, &output_names, false)
                {
                    return (false, Some(reason));
                }

                // Check for multi-variable exists quantifiers
                if let Some(reason) = Self::check_multi_var_exists(&spec_fn.body) {
                    return (false, Some(reason));
                }

                (true, None)
            }
            FunctionKind::Helper => {
                // Helper functions have no output parameters (all inputs)
                // They are always functionalizable (body is the return value)
                let has_output = param_modes.contains(&ParameterMode::Output);
                if has_output {
                    return (
                        false,
                        Some("Helper functions should not have output parameters".to_string()),
                    );
                }
                (true, None)
            }
        }
    }

    /// Check if output parameters are assigned (via equality) inside quantifier bodies.
    ///
    /// An output parameter appearing on the LHS of an equality inside a forall/exists
    /// body means the spec constrains the output through a quantified formula, which
    /// cannot be directly converted to executable assignment code.
    ///
    /// Note: output parameters appearing in quantifier bodies on the RHS (as values
    /// being read, not assigned) are fine — this is the common "forall invariant" pattern.
    fn check_output_in_quantifier(
        expr: &Expr,
        output_names: &HashSet<String>,
        inside_quantifier: bool,
    ) -> Option<String> {
        match expr {
            // Equality: check if LHS is an output assignment inside a quantifier
            Expr::Eq(left, right) => {
                if inside_quantifier {
                    if let Some(name) = Self::extract_root_ident(left) {
                        if output_names.contains(&name) {
                            return Some(format!(
                                "Output parameter '{}' is assigned inside a quantifier body \
                                 (cannot convert quantified assignment to executable code)",
                                name
                            ));
                        }
                    }
                }
                // Recurse into both sides for nested quantifiers
                Self::check_output_in_quantifier(left, output_names, inside_quantifier).or_else(
                    || Self::check_output_in_quantifier(right, output_names, inside_quantifier),
                )
            }

            // Quantifiers: recurse with inside_quantifier = true
            // But first check for the Seq comprehension pattern which IS convertible:
            //   forall |idx| bounds ==> output[idx] == element_expr
            // This pattern is handled by the translator's WhileLoop generator.
            Expr::Forall { vars, body, .. } => {
                if vars.len() == 1 {
                    if let Expr::Implies(_, assign_expr) = body.as_ref() {
                        if Self::is_seq_comprehension_assignment(
                            assign_expr,
                            output_names,
                            &vars[0].name_string(),
                        ) {
                            // This is a convertible Seq comprehension — allow it
                            return None;
                        }
                    }
                }
                Self::check_output_in_quantifier(body, output_names, true)
            }
            Expr::Exists { body, .. } => Self::check_output_in_quantifier(body, output_names, true),

            // Conjunction/disjunction: recurse into clauses
            Expr::Conjunction(clauses) | Expr::Disjunction(clauses) => clauses
                .iter()
                .find_map(|c| Self::check_output_in_quantifier(c, output_names, inside_quantifier)),

            // Implication: recurse into both sides
            Expr::Implies(left, right) | Expr::Iff(left, right) => {
                Self::check_output_in_quantifier(left, output_names, inside_quantifier).or_else(
                    || Self::check_output_in_quantifier(right, output_names, inside_quantifier),
                )
            }

            // Conditional: recurse into all branches
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => Self::check_output_in_quantifier(cond, output_names, inside_quantifier)
                .or_else(|| {
                    Self::check_output_in_quantifier(then_branch, output_names, inside_quantifier)
                })
                .or_else(|| {
                    else_branch.as_ref().and_then(|e| {
                        Self::check_output_in_quantifier(e, output_names, inside_quantifier)
                    })
                }),

            // Let binding: recurse into value and body
            Expr::Let { value, body, .. } => {
                Self::check_output_in_quantifier(value, output_names, inside_quantifier).or_else(
                    || Self::check_output_in_quantifier(body, output_names, inside_quantifier),
                )
            }

            // Binary: recurse
            Expr::Binary(left, _, right)
            | Expr::Ne(left, right)
            | Expr::Lt(left, right)
            | Expr::Le(left, right)
            | Expr::Gt(left, right)
            | Expr::Ge(left, right) => {
                Self::check_output_in_quantifier(left, output_names, inside_quantifier).or_else(
                    || Self::check_output_in_quantifier(right, output_names, inside_quantifier),
                )
            }

            // Match: recurse into scrutinee and arms
            Expr::Match { scrutinee, arms } => {
                Self::check_output_in_quantifier(scrutinee, output_names, inside_quantifier)
                    .or_else(|| {
                        arms.iter().find_map(|arm| {
                            Self::check_output_in_quantifier(
                                &arm.body,
                                output_names,
                                inside_quantifier,
                            )
                        })
                    })
            }

            // Terminals and other expressions: no quantifier issues
            _ => None,
        }
    }

    /// Check if an expression is a Seq comprehension assignment pattern:
    ///   output[idx] == element_expr  (or output[idx] =~= element_expr)
    /// where `output` is an output parameter and `idx` is the forall variable.
    /// This pattern is convertible to a WhileLoop by the translator.
    fn is_seq_comprehension_assignment(
        expr: &Expr,
        output_names: &HashSet<String>,
        forall_var: &str,
    ) -> bool {
        match expr {
            Expr::Eq(left, _right) => {
                // Check: left is output[idx] where output is DIRECTLY an output param
                // (not output.field[idx]) and idx is the forall var.
                if let Expr::Index(base, index) = left.as_ref() {
                    if let Expr::Ident(name) = base.as_ref() {
                        if output_names.contains(name) {
                            if let Expr::Ident(idx_name) = index.as_ref() {
                                return idx_name == forall_var;
                            }
                        }
                    }
                }
                false
            }
            _ => false,
        }
    }

    /// Extract the root identifier from an expression (through field/index chains).
    ///
    /// For `s_.field.subfield`, returns `"s_"`.
    /// For `s_[i]`, returns `"s_"`.
    /// For `s_`, returns `"s_"`.
    fn extract_root_ident(expr: &Expr) -> Option<String> {
        match expr {
            Expr::Ident(name) => Some(name.clone()),
            Expr::Field(base, _) | Expr::Arrow(base, _) => Self::extract_root_ident(base),
            Expr::Index(base, _) => Self::extract_root_ident(base),
            _ => None,
        }
    }

    /// Check for multi-variable exists quantifiers, which cannot be functionalized.
    ///
    /// The translator only supports single-variable exists (converted to `.any()`).
    /// Multi-variable exists would require nested iteration or solver support.
    fn check_multi_var_exists(expr: &Expr) -> Option<String> {
        match expr {
            Expr::Exists { vars, body } => {
                if vars.len() > 1 {
                    let var_names: Vec<_> = vars.iter().map(|v| v.name_string()).collect();
                    return Some(format!(
                        "Exists quantifier with {} variables ({}) not supported \
                         (only single-variable exists can be converted to executable code)",
                        vars.len(),
                        var_names.join(", ")
                    ));
                }
                Self::check_multi_var_exists(body)
            }

            Expr::Forall { body, .. } => Self::check_multi_var_exists(body),

            Expr::Conjunction(clauses) | Expr::Disjunction(clauses) => {
                clauses.iter().find_map(Self::check_multi_var_exists)
            }

            Expr::Implies(left, right) | Expr::Iff(left, right) => {
                Self::check_multi_var_exists(left).or_else(|| Self::check_multi_var_exists(right))
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => Self::check_multi_var_exists(cond)
                .or_else(|| Self::check_multi_var_exists(then_branch))
                .or_else(|| {
                    else_branch
                        .as_deref()
                        .and_then(Self::check_multi_var_exists)
                }),

            Expr::Let { value, body, .. } => {
                Self::check_multi_var_exists(value).or_else(|| Self::check_multi_var_exists(body))
            }

            Expr::Binary(left, _, right)
            | Expr::Eq(left, right)
            | Expr::Ne(left, right)
            | Expr::Lt(left, right)
            | Expr::Le(left, right)
            | Expr::Gt(left, right)
            | Expr::Ge(left, right) => {
                Self::check_multi_var_exists(left).or_else(|| Self::check_multi_var_exists(right))
            }

            Expr::Match { scrutinee, arms } => {
                Self::check_multi_var_exists(scrutinee).or_else(|| {
                    arms.iter()
                        .find_map(|arm| Self::check_multi_var_exists(&arm.body))
                })
            }

            _ => None,
        }
    }

    /// Detect if a function is recursive (contains calls to itself)
    fn is_recursive(spec_fn: &SpecFunction) -> bool {
        Self::contains_self_call(&spec_fn.body, &spec_fn.name)
    }

    /// Check if an expression contains a call to the given function name
    fn contains_self_call(expr: &Expr, func_name: &str) -> bool {
        match expr {
            // Check function calls - primary way recursion occurs
            Expr::Call { func, args } => {
                // Check if this is a call to the same function
                if func.segments.last().map(|s| s.as_str()) == Some(func_name) {
                    return true;
                }
                // Check arguments recursively
                args.iter()
                    .any(|arg| Self::contains_self_call(arg, func_name))
            }

            // Check method calls (receiver.method(args))
            Expr::MethodCall {
                receiver,
                method: _,
                args,
            } => {
                Self::contains_self_call(receiver, func_name)
                    || args
                        .iter()
                        .any(|arg| Self::contains_self_call(arg, func_name))
            }

            // Binary expressions (arithmetic, logical, comparison)
            Expr::Binary(left, _, right)
            | Expr::Eq(left, right)
            | Expr::Ne(left, right)
            | Expr::Lt(left, right)
            | Expr::Le(left, right)
            | Expr::Gt(left, right)
            | Expr::Ge(left, right)
            | Expr::Implies(left, right)
            | Expr::Iff(left, right) => {
                Self::contains_self_call(left, func_name)
                    || Self::contains_self_call(right, func_name)
            }

            // Unary expressions
            Expr::Not(inner) | Expr::View(inner) | Expr::Unary(_, inner) => {
                Self::contains_self_call(inner, func_name)
            }

            // Field/arrow access
            Expr::Field(base, _) | Expr::Arrow(base, _) => {
                Self::contains_self_call(base, func_name)
            }

            // Index access
            Expr::Index(base, idx) => {
                Self::contains_self_call(base, func_name)
                    || Self::contains_self_call(idx, func_name)
            }

            // Conditional
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                Self::contains_self_call(cond, func_name)
                    || Self::contains_self_call(then_branch, func_name)
                    || else_branch
                        .as_ref()
                        .is_some_and(|e| Self::contains_self_call(e, func_name))
            }

            // Match expression
            Expr::Match { scrutinee, arms } => {
                Self::contains_self_call(scrutinee, func_name)
                    || arms
                        .iter()
                        .any(|arm| Self::contains_self_call(&arm.body, func_name))
            }

            // Struct construction
            Expr::Struct { name: _, fields } => fields
                .iter()
                .any(|(_, value)| Self::contains_self_call(value, func_name)),

            // Struct update
            Expr::StructUpdate { base, fields, .. } => {
                Self::contains_self_call(base, func_name)
                    || fields
                        .iter()
                        .any(|(_, value)| Self::contains_self_call(value, func_name))
            }

            // Collection literals
            Expr::SeqLit(elements) | Expr::SetLit(elements) => elements
                .iter()
                .any(|e| Self::contains_self_call(e, func_name)),

            // Map literal
            Expr::MapLit(pairs) => pairs.iter().any(|(k, v)| {
                Self::contains_self_call(k, func_name) || Self::contains_self_call(v, func_name)
            }),

            // Conjunction/disjunction
            Expr::Conjunction(clauses) | Expr::Disjunction(clauses) => clauses
                .iter()
                .any(|c| Self::contains_self_call(c, func_name)),

            // Quantifiers
            Expr::Forall {
                vars: _,
                triggers: _,
                body,
            } => Self::contains_self_call(body, func_name),

            Expr::Exists { vars: _, body }
            | Expr::Closure { params: _, body }
            | Expr::Choose { vars: _, body } => Self::contains_self_call(body, func_name),

            // Is/Cast
            Expr::Is(base, _) | Expr::Cast(base, _) => Self::contains_self_call(base, func_name),

            // Let binding
            Expr::Let { value, body, .. } => {
                Self::contains_self_call(value, func_name)
                    || Self::contains_self_call(body, func_name)
            }

            // Terminals - no recursion possible
            Expr::Ident(_)
            | Expr::Literal(_)
            | Expr::SeqEmpty
            | Expr::SetEmpty
            | Expr::MapEmpty
            | Expr::ConstantValue(_) => false,
        }
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
    use crate::ast::{BinOp, Expr, Literal, Path, Type};

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
    fn test_member_path_display() {
        assert_eq!(format!("{}", MemberPath::Root), "<root>");
        assert_eq!(
            format!("{}", MemberPath::root().field("max_bal".to_string())),
            "<root>.max_bal"
        );
        assert_eq!(
            format!("{}", MemberPath::root().field("votes".to_string()).index()),
            "<root>.votes[_]"
        );
    }

    #[test]
    fn test_assignment_tracker_get_count() {
        let mut tracker = AssignmentTracker::new();
        assert_eq!(tracker.get_count("s_", &MemberPath::Root), 0);

        tracker.record_assignment("s_", MemberPath::Root);
        assert_eq!(tracker.get_count("s_", &MemberPath::Root), 1);

        tracker.record_assignment("s_", MemberPath::Root);
        assert_eq!(tracker.get_count("s_", &MemberPath::Root), 2);

        // Different path is independent
        let field_path = MemberPath::root().field("x".to_string());
        assert_eq!(tracker.get_count("s_", &field_path), 0);
    }

    #[test]
    fn test_assignment_tracker_counts_different_vars() {
        let mut tracker = AssignmentTracker::new();
        tracker.record_assignment("s_", MemberPath::Root);
        tracker.record_assignment("t_", MemberPath::Root);

        assert_eq!(tracker.get_count("s_", &MemberPath::Root), 1);
        assert_eq!(tracker.get_count("t_", &MemberPath::Root), 1);
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

    #[test]
    fn test_detect_recursive_function() {
        // Create a recursive function: F(x) = if x == 0 then 1 else F(x-1)
        let spec_fn = SpecFunction {
            name: "Factorial".to_string(),
            generics: Default::default(),
            params: vec![],
            return_type: Type::Int,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body: Expr::If {
                cond: Box::new(Expr::Eq(
                    Box::new(Expr::Ident("x".to_string())),
                    Box::new(Expr::Literal(Literal::Int(0))),
                )),
                then_branch: Box::new(Expr::Literal(Literal::Int(1))),
                else_branch: Some(Box::new(Expr::Call {
                    func: Path::single("Factorial".to_string()),
                    args: vec![Expr::Binary(
                        Box::new(Expr::Ident("x".to_string())),
                        BinOp::Sub,
                        Box::new(Expr::Literal(Literal::Int(1))),
                    )],
                })),
            },
            span: None,
        };

        assert!(ModeAnalyzer::is_recursive(&spec_fn));
    }

    #[test]
    fn test_detect_non_recursive_function() {
        // Create a non-recursive function: F(x) = x + 1
        let spec_fn = SpecFunction {
            name: "Increment".to_string(),
            generics: Default::default(),
            params: vec![],
            return_type: Type::Int,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body: Expr::Binary(
                Box::new(Expr::Ident("x".to_string())),
                BinOp::Add,
                Box::new(Expr::Literal(Literal::Int(1))),
            ),
            span: None,
        };

        assert!(!ModeAnalyzer::is_recursive(&spec_fn));
    }

    #[test]
    fn test_detect_recursive_in_nested_if() {
        // Create a function with recursion in nested branch
        let spec_fn = SpecFunction {
            name: "NestedRecursive".to_string(),
            generics: Default::default(),
            params: vec![],
            return_type: Type::Int,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body: Expr::If {
                cond: Box::new(Expr::Literal(Literal::Bool(true))),
                then_branch: Box::new(Expr::If {
                    cond: Box::new(Expr::Literal(Literal::Bool(false))),
                    then_branch: Box::new(Expr::Literal(Literal::Int(1))),
                    else_branch: Some(Box::new(Expr::Call {
                        func: Path::single("NestedRecursive".to_string()),
                        args: vec![],
                    })),
                }),
                else_branch: None,
            },
            span: None,
        };

        assert!(ModeAnalyzer::is_recursive(&spec_fn));
    }

    #[test]
    fn test_detect_recursive_calls_different_function() {
        // Calling a different function should not count as recursive
        let spec_fn = SpecFunction {
            name: "MyFunction".to_string(),
            generics: Default::default(),
            params: vec![],
            return_type: Type::Int,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body: Expr::Call {
                func: Path::single("OtherFunction".to_string()),
                args: vec![Expr::Ident("x".to_string())],
            },
            span: None,
        };

        assert!(!ModeAnalyzer::is_recursive(&spec_fn));
    }

    // ============ Functionalizable Check Tests ============

    use crate::annotation::FunctionAnnotation;
    use crate::ast::{Binding, FunctionKind, Pattern, VariableMode};

    /// Helper to create a simple annotated function for testing
    fn make_annotated(
        body: Expr,
        param_modes: Vec<ParameterMode>,
    ) -> (AnnotatedFunction, bool, Option<String>) {
        let params: Vec<_> = param_modes
            .iter()
            .enumerate()
            .map(|(i, mode)| crate::ast::Parameter {
                name: if *mode == ParameterMode::Output {
                    format!("s{}_", i)
                } else {
                    format!("s{}", i)
                },
                ty: Type::Named(Path::single("State".to_string())),
                mode: Some(*mode),
                variable_mode: VariableMode::Exec,
                span: None,
            })
            .collect();

        let spec_fn = SpecFunction {
            name: "TestPredicate".to_string(),
            generics: Default::default(),
            params,
            return_type: Type::Bool,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body,
            span: None,
        };

        let annotation = FunctionAnnotation {
            name: "TestPredicate".to_string(),
            param_modes: param_modes.clone(),
            kind: FunctionKind::Predicate,
            return_type: None,
        };

        let mut analyzer = ModeAnalyzer::new();
        let result = analyzer.annotate(spec_fn, &annotation).unwrap();
        let is_func = result.is_functionalizable;
        let reason = result.non_functionalizable_reason.clone();
        (result, is_func, reason)
    }

    fn make_binding(name: &str) -> Binding {
        Binding {
            pattern: Pattern::Ident(name.to_string()),
            ty: Some(Type::Int),
            variable_mode: VariableMode::default(),
        }
    }

    #[test]
    fn test_functionalizable_simple_predicate() {
        // s1_ == s0 (simple equality, output assigned at top level)
        let body = Expr::Eq(
            Box::new(Expr::Ident("s1_".to_string())),
            Box::new(Expr::Ident("s0".to_string())),
        );
        let (_, is_func, reason) =
            make_annotated(body, vec![ParameterMode::Input, ParameterMode::Output]);
        assert!(
            is_func,
            "Simple equality should be functionalizable, reason: {:?}",
            reason
        );
    }

    #[test]
    fn test_functionalizable_no_output() {
        // No output parameters → not functionalizable
        let body = Expr::Literal(Literal::Bool(true));
        let (_, is_func, reason) = make_annotated(body, vec![ParameterMode::Input]);
        assert!(!is_func);
        assert_eq!(reason.unwrap(), "No output parameters");
    }

    #[test]
    fn test_functionalizable_output_in_forall() {
        // forall |i| s1_.field[i] == s0.field[i]
        // Output s1_ is assigned inside a forall body → not functionalizable
        let body = Expr::Forall {
            vars: vec![make_binding("i")],
            triggers: vec![],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Index(
                    Box::new(Expr::Field(
                        Box::new(Expr::Ident("s1_".to_string())),
                        "field".to_string(),
                    )),
                    Box::new(Expr::Ident("i".to_string())),
                )),
                Box::new(Expr::Index(
                    Box::new(Expr::Field(
                        Box::new(Expr::Ident("s0".to_string())),
                        "field".to_string(),
                    )),
                    Box::new(Expr::Ident("i".to_string())),
                )),
            )),
        };
        let (_, is_func, reason) =
            make_annotated(body, vec![ParameterMode::Input, ParameterMode::Output]);
        assert!(
            !is_func,
            "Output inside forall should not be functionalizable"
        );
        assert!(
            reason.as_ref().unwrap().contains("inside a quantifier"),
            "Expected quantifier message, got: {:?}",
            reason
        );
    }

    #[test]
    fn test_functionalizable_output_in_exists() {
        // exists |x| s1_.field == x (output assigned inside exists)
        let body = Expr::Exists {
            vars: vec![make_binding("x")],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Field(
                    Box::new(Expr::Ident("s1_".to_string())),
                    "field".to_string(),
                )),
                Box::new(Expr::Ident("x".to_string())),
            )),
        };
        let (_, is_func, reason) =
            make_annotated(body, vec![ParameterMode::Input, ParameterMode::Output]);
        assert!(
            !is_func,
            "Output inside exists should not be functionalizable"
        );
        assert!(
            reason.as_ref().unwrap().contains("inside a quantifier"),
            "Expected quantifier message, got: {:?}",
            reason
        );
    }

    #[test]
    fn test_functionalizable_forall_over_input_only() {
        // forall |i| s0.votes[i].value > 0 (only input in quantifier body — OK)
        let body = Expr::Conjunction(vec![
            Expr::Eq(
                Box::new(Expr::Ident("s1_".to_string())),
                Box::new(Expr::Ident("s0".to_string())),
            ),
            Expr::Forall {
                vars: vec![make_binding("i")],
                triggers: vec![],
                body: Box::new(Expr::Gt(
                    Box::new(Expr::Field(
                        Box::new(Expr::Index(
                            Box::new(Expr::Field(
                                Box::new(Expr::Ident("s0".to_string())),
                                "votes".to_string(),
                            )),
                            Box::new(Expr::Ident("i".to_string())),
                        )),
                        "value".to_string(),
                    )),
                    Box::new(Expr::Literal(Literal::Int(0))),
                )),
            },
        ]);
        let (_, is_func, reason) =
            make_annotated(body, vec![ParameterMode::Input, ParameterMode::Output]);
        assert!(
            is_func,
            "Forall over input should be functionalizable, reason: {:?}",
            reason
        );
    }

    #[test]
    fn test_functionalizable_multi_var_exists() {
        // exists |x, y| x + y == s0.value (multi-variable exists → not functionalizable)
        let body = Expr::Conjunction(vec![
            Expr::Eq(
                Box::new(Expr::Ident("s1_".to_string())),
                Box::new(Expr::Ident("s0".to_string())),
            ),
            Expr::Exists {
                vars: vec![make_binding("x"), make_binding("y")],
                body: Box::new(Expr::Eq(
                    Box::new(Expr::Binary(
                        Box::new(Expr::Ident("x".to_string())),
                        BinOp::Add,
                        Box::new(Expr::Ident("y".to_string())),
                    )),
                    Box::new(Expr::Field(
                        Box::new(Expr::Ident("s0".to_string())),
                        "value".to_string(),
                    )),
                )),
            },
        ]);
        let (_, is_func, reason) =
            make_annotated(body, vec![ParameterMode::Input, ParameterMode::Output]);
        assert!(
            !is_func,
            "Multi-variable exists should not be functionalizable"
        );
        assert!(
            reason.as_ref().unwrap().contains("2 variables"),
            "Expected multi-var message, got: {:?}",
            reason
        );
    }

    #[test]
    fn test_functionalizable_single_var_exists_ok() {
        // exists |x| container.contains(x) && ... (single var exists — OK)
        let body = Expr::Conjunction(vec![
            Expr::Eq(
                Box::new(Expr::Ident("s1_".to_string())),
                Box::new(Expr::Ident("s0".to_string())),
            ),
            Expr::Exists {
                vars: vec![make_binding("x")],
                body: Box::new(Expr::Binary(
                    Box::new(Expr::MethodCall {
                        receiver: Box::new(Expr::Ident("container".to_string())),
                        method: "contains".to_string(),
                        args: vec![Expr::Ident("x".to_string())],
                    }),
                    BinOp::And,
                    Box::new(Expr::Gt(
                        Box::new(Expr::Ident("x".to_string())),
                        Box::new(Expr::Literal(Literal::Int(0))),
                    )),
                )),
            },
        ]);
        let (_, is_func, reason) =
            make_annotated(body, vec![ParameterMode::Input, ParameterMode::Output]);
        assert!(
            is_func,
            "Single-var exists should be functionalizable, reason: {:?}",
            reason
        );
    }

    #[test]
    fn test_functionalizable_output_in_nested_if_forall() {
        // if cond { forall |i| s1_.field[i] == val } else { s1_ == s0 }
        // Output inside forall in one branch → not functionalizable
        let body = Expr::If {
            cond: Box::new(Expr::Literal(Literal::Bool(true))),
            then_branch: Box::new(Expr::Forall {
                vars: vec![make_binding("i")],
                triggers: vec![],
                body: Box::new(Expr::Eq(
                    Box::new(Expr::Index(
                        Box::new(Expr::Field(
                            Box::new(Expr::Ident("s1_".to_string())),
                            "field".to_string(),
                        )),
                        Box::new(Expr::Ident("i".to_string())),
                    )),
                    Box::new(Expr::Literal(Literal::Int(0))),
                )),
            }),
            else_branch: Some(Box::new(Expr::Eq(
                Box::new(Expr::Ident("s1_".to_string())),
                Box::new(Expr::Ident("s0".to_string())),
            ))),
        };
        let (_, is_func, reason) =
            make_annotated(body, vec![ParameterMode::Input, ParameterMode::Output]);
        assert!(
            !is_func,
            "Output inside forall in if-branch should not be functionalizable"
        );
        assert!(
            reason.as_ref().unwrap().contains("inside a quantifier"),
            "Expected quantifier message, got: {:?}",
            reason
        );
    }

    #[test]
    fn test_extract_root_ident() {
        assert_eq!(
            ModeAnalyzer::extract_root_ident(&Expr::Ident("s_".to_string())),
            Some("s_".to_string())
        );
        assert_eq!(
            ModeAnalyzer::extract_root_ident(&Expr::Field(
                Box::new(Expr::Ident("s_".to_string())),
                "field".to_string(),
            )),
            Some("s_".to_string())
        );
        assert_eq!(
            ModeAnalyzer::extract_root_ident(&Expr::Index(
                Box::new(Expr::Field(
                    Box::new(Expr::Ident("s_".to_string())),
                    "votes".to_string(),
                )),
                Box::new(Expr::Ident("i".to_string())),
            )),
            Some("s_".to_string())
        );
        assert_eq!(
            ModeAnalyzer::extract_root_ident(&Expr::Literal(Literal::Int(42))),
            None
        );
    }

    #[test]
    fn test_functionalizable_seq_comprehension_allowed() {
        // Seq comprehension pattern SHOULD be allowed:
        // forall |idx| 0 <= idx < sent_packets.len() ==> sent_packets[idx] == expr
        // This is convertible to a WhileLoop by the translator.
        let body = Expr::Conjunction(vec![
            // sent_packets.len() == c.replica_ids.len()
            Expr::Eq(
                Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::Ident("sent_packets".to_string())),
                    method: "len".to_string(),
                    args: vec![],
                }),
                Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::Field(
                        Box::new(Expr::Ident("c".to_string())),
                        "ids".to_string(),
                    )),
                    method: "len".to_string(),
                    args: vec![],
                }),
            ),
            // forall |idx| 0 <= idx < sent_packets.len() ==> sent_packets[idx] == SomeExpr
            Expr::Forall {
                vars: vec![make_binding("idx")],
                triggers: vec![],
                body: Box::new(Expr::Implies(
                    // bounds
                    Box::new(Expr::Conjunction(vec![Expr::Le(
                        Box::new(Expr::Literal(Literal::Int(0))),
                        Box::new(Expr::Ident("idx".to_string())),
                    )])),
                    // sent_packets[idx] == some_expr
                    Box::new(Expr::Eq(
                        Box::new(Expr::Index(
                            Box::new(Expr::Ident("sent_packets".to_string())),
                            Box::new(Expr::Ident("idx".to_string())),
                        )),
                        Box::new(Expr::Ident("some_value".to_string())),
                    )),
                )),
            },
        ]);
        let (_, is_func, reason) =
            make_annotated(body, vec![ParameterMode::Input, ParameterMode::Output]);
        assert!(
            is_func,
            "Seq comprehension pattern should be functionalizable, got: {:?}",
            reason
        );
    }

    #[test]
    fn test_functionalizable_output_in_forall_not_seq_comprehension() {
        // Output inside forall but NOT a seq comprehension pattern:
        // forall |i| s1_.field[i] == s0.field[i]
        // Here the index is on s1_.field (a field access), not s1_[i] directly
        // This should still be rejected.
        let body = Expr::Forall {
            vars: vec![make_binding("i")],
            triggers: vec![],
            body: Box::new(Expr::Implies(
                Box::new(Expr::Le(
                    Box::new(Expr::Literal(Literal::Int(0))),
                    Box::new(Expr::Ident("i".to_string())),
                )),
                Box::new(Expr::Eq(
                    Box::new(Expr::Index(
                        Box::new(Expr::Field(
                            Box::new(Expr::Ident("s1_".to_string())),
                            "field".to_string(),
                        )),
                        Box::new(Expr::Ident("i".to_string())),
                    )),
                    Box::new(Expr::Ident("value".to_string())),
                )),
            )),
        };
        let (_, is_func, reason) =
            make_annotated(body, vec![ParameterMode::Input, ParameterMode::Output]);
        assert!(
            !is_func,
            "Output.field[i] pattern should not be a seq comprehension"
        );
        assert!(
            reason.as_ref().unwrap().contains("inside a quantifier"),
            "Expected quantifier message, got: {:?}",
            reason
        );
    }

    #[test]
    fn test_functionalizable_helper_with_output_rejected() {
        // Helper function with output parameter → not functionalizable
        let spec_fn = SpecFunction {
            name: "Helper".to_string(),
            generics: Default::default(),
            params: vec![crate::ast::Parameter {
                name: "x_".to_string(),
                ty: Type::Int,
                mode: Some(ParameterMode::Output),
                variable_mode: VariableMode::Exec,
                span: None,
            }],
            return_type: Type::Int,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body: Expr::Literal(Literal::Int(42)),
            span: None,
        };

        let annotation = FunctionAnnotation {
            name: "Helper".to_string(),
            param_modes: vec![ParameterMode::Output],
            kind: FunctionKind::Helper,
            return_type: Some("int".to_string()),
        };

        let mut analyzer = ModeAnalyzer::new();
        let result = analyzer.annotate(spec_fn, &annotation).unwrap();
        assert!(!result.is_functionalizable);
        assert!(result
            .non_functionalizable_reason
            .as_ref()
            .unwrap()
            .contains("Helper functions should not have output parameters"));
    }
}

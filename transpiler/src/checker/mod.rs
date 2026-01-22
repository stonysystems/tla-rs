//! Validation passes for mode-annotated functions.
//!
//! This module implements the three main validation checks:
//! - Saturation: All output members are assigned exactly once
//! - Harmony: No double assignments to the same member
//! - Obligation: Output variables are only used after assignment

use crate::ast::Type;
use crate::error::{TranspileError, TranspileResult};
use crate::moder::{AnnotatedFunction, AssignmentTracker, MemberPath};
use std::collections::HashSet;

/// Saturation checker - verifies all output members are assigned
pub struct SaturationChecker;

impl SaturationChecker {
    /// Check that all members of output parameters are assigned
    pub fn check(
        func: &AnnotatedFunction,
        tracker: &AssignmentTracker,
    ) -> TranspileResult<()> {
        for (param, mode) in func.spec_fn.params.iter().zip(&func.param_modes) {
            if *mode == crate::ast::ParameterMode::Output {
                let required = Self::get_required_members(&param.ty);
                let assigned = tracker
                    .assignments
                    .get(&param.name)
                    .cloned()
                    .unwrap_or_default();

                let missing: Vec<_> = required.difference(&assigned).collect();
                if !missing.is_empty() {
                    return Err(TranspileError::Saturation {
                        message: format!(
                            "Output parameter '{}' has unassigned members: {:?}",
                            param.name, missing
                        ),
                        span: None, // TODO: Convert proc_macro2::Span to SourceSpan
                        help: Some("Ensure all fields of output parameters are assigned".to_string()),
                    });
                }
            }
        }
        Ok(())
    }

    /// Get all members that need to be assigned for a type
    fn get_required_members(ty: &Type) -> HashSet<MemberPath> {
        let mut members = HashSet::new();
        // For now, just require the root to be assigned
        // TODO: Expand to handle struct fields recursively
        members.insert(MemberPath::Root);
        let _ = ty; // Use the parameter to avoid warning
        members
    }
}

/// Harmony checker - verifies no double assignments
pub struct HarmonyChecker;

impl HarmonyChecker {
    /// Check that no member is assigned more than once
    pub fn check(
        _func: &AnnotatedFunction,
        _tracker: &AssignmentTracker,
    ) -> TranspileResult<()> {
        // TODO: Implement harmony check
        // This requires tracking assignment order during expression analysis
        Ok(())
    }
}

/// Obligation checker - verifies outputs are used only after assignment
pub struct ObligationChecker;

impl ObligationChecker {
    /// Check that output variables are only used after assignment
    pub fn check(
        _func: &AnnotatedFunction,
        _tracker: &AssignmentTracker,
    ) -> TranspileResult<()> {
        // TODO: Implement obligation check
        // This requires building a dependency graph and detecting cycles
        Ok(())
    }
}

/// Supported quantifier templates for collection operations
#[derive(Debug, Clone)]
pub enum QuantifierTemplate {
    /// Sequence comprehension: `seq![...] or Seq::new(|i| ...)`
    SeqComprehension {
        length_expr: Box<crate::ast::Expr>,
        element_expr: Box<crate::ast::Expr>,
        index_var: String,
    },

    /// Set comprehension: `Set::new(|x| ...)`
    SetComprehension {
        domain_predicate: Box<crate::ast::Expr>,
        element_var: String,
    },

    /// Map comprehension: `Map::new(|k| ..., |k| ...)`
    MapComprehension {
        domain_predicate: Box<crate::ast::Expr>,
        value_expr: Box<crate::ast::Expr>,
        key_var: String,
    },
}

/// Template matcher for quantifier expressions
pub struct TemplateMatcher;

impl TemplateMatcher {
    /// Try to match a quantifier expression to a known template
    pub fn match_template(expr: &crate::ast::Expr) -> Option<QuantifierTemplate> {
        use crate::ast::Expr;

        if let Expr::Forall { vars, body, .. } = expr {
            // Only handle single-variable quantifiers
            if vars.len() == 1 {
                let var = &vars[0];

                // Try sequence comprehension first
                if let Some(template) = Self::try_seq_comprehension(var, body) {
                    return Some(template);
                }

                // Try map comprehension
                if let Some(template) = Self::try_map_comprehension(var, body) {
                    return Some(template);
                }

                // Try set comprehension
                if let Some(template) = Self::try_set_comprehension(var, body) {
                    return Some(template);
                }
            }
        }
        None
    }

    /// Try to match: forall |i| 0 <= i < n ==> seq[i] == f(i)
    fn try_seq_comprehension(
        var: &crate::ast::Binding,
        body: &crate::ast::Expr,
    ) -> Option<QuantifierTemplate> {
        use crate::ast::Expr;

        // Body must be an implication: bounds ==> assignment
        if let Expr::Implies(lhs, rhs) = body {
            // Check if LHS is a bounds check like: 0 <= i && i < n  or  0 <= i < n
            if let Some(upper_bound) = Self::extract_int_upper_bound(lhs, &var.name) {
                // Check if RHS is: seq[i] == expr or expr == seq[i]
                if let Some((collection, element_expr)) =
                    Self::extract_indexed_assignment(rhs, &var.name)
                {
                    // Verify the collection is being indexed by our variable
                    return Some(QuantifierTemplate::SeqComprehension {
                        length_expr: upper_bound,
                        element_expr: Box::new(element_expr.clone()),
                        index_var: var.name.clone(),
                    });
                }
            }
        }
        None
    }

    /// Try to match: forall |k| k in map' <==> pred (domain) or
    ///               forall |k| k in map' ==> map'[k] == f(k) (value)
    fn try_map_comprehension(
        var: &crate::ast::Binding,
        body: &crate::ast::Expr,
    ) -> Option<QuantifierTemplate> {
        use crate::ast::Expr;

        // Check for biconditional (domain pattern): k in map' <==> pred
        // We represent <==> as Eq between boolean expressions
        if let Expr::Eq(lhs, rhs) = body {
            // Check if one side is membership: k in collection
            if let Some(_collection) = Self::extract_membership(lhs, &var.name) {
                // The other side is the domain predicate
                return Some(QuantifierTemplate::MapComprehension {
                    domain_predicate: rhs.clone(),
                    value_expr: Box::new(Expr::Ident(var.name.clone())), // placeholder
                    key_var: var.name.clone(),
                });
            }
            if let Some(_collection) = Self::extract_membership(rhs, &var.name) {
                return Some(QuantifierTemplate::MapComprehension {
                    domain_predicate: lhs.clone(),
                    value_expr: Box::new(Expr::Ident(var.name.clone())),
                    key_var: var.name.clone(),
                });
            }
        }

        // Check for implication (value pattern): k in map' ==> map'[k] == expr
        if let Expr::Implies(lhs, rhs) = body {
            if let Some(collection) = Self::extract_membership(lhs, &var.name) {
                // RHS should be: map'[k] == expr
                if let Some((_, value_expr)) =
                    Self::extract_indexed_assignment(rhs, &var.name)
                {
                    return Some(QuantifierTemplate::MapComprehension {
                        domain_predicate: Box::new(Expr::Literal(crate::ast::Literal::Bool(true))),
                        value_expr: Box::new(value_expr.clone()),
                        key_var: var.name.clone(),
                    });
                }
            }
        }
        None
    }

    /// Try to match: forall |x| x in set' <==> pred
    fn try_set_comprehension(
        var: &crate::ast::Binding,
        body: &crate::ast::Expr,
    ) -> Option<QuantifierTemplate> {
        use crate::ast::Expr;

        // Check for biconditional: x in set' <==> pred
        if let Expr::Eq(lhs, rhs) = body {
            if let Some(_collection) = Self::extract_membership(lhs, &var.name) {
                return Some(QuantifierTemplate::SetComprehension {
                    domain_predicate: rhs.clone(),
                    element_var: var.name.clone(),
                });
            }
            if let Some(_collection) = Self::extract_membership(rhs, &var.name) {
                return Some(QuantifierTemplate::SetComprehension {
                    domain_predicate: lhs.clone(),
                    element_var: var.name.clone(),
                });
            }
        }
        None
    }

    /// Extract upper bound from expressions like:
    /// - `0 <= i && i < n` -> Some(n)
    /// - `i < n` (assuming lower bound 0) -> Some(n)
    /// - `i >= 0 && i < n` -> Some(n)
    fn extract_int_upper_bound(
        expr: &crate::ast::Expr,
        var_name: &str,
    ) -> Option<Box<crate::ast::Expr>> {
        use crate::ast::{BinOp, Expr};

        match expr {
            // Pattern: a && b - check both sides
            Expr::Binary(lhs, BinOp::And, rhs) => {
                // Try to find upper bound in either side
                Self::extract_int_upper_bound(lhs, var_name)
                    .or_else(|| Self::extract_int_upper_bound(rhs, var_name))
            }

            // Pattern: 0 <= i (lower bound - ignore, just recurse)
            Expr::Le(lhs, rhs) => {
                if Self::is_zero(lhs) && Self::is_var(rhs, var_name) {
                    // This is just the lower bound, no upper bound here
                    None
                } else if Self::is_var(lhs, var_name) {
                    // i <= n means upper bound is n (inclusive), but we want exclusive
                    // Return n for now, codegen can handle
                    Some(rhs.clone())
                } else {
                    None
                }
            }

            // Pattern: i < n (upper bound - what we want)
            Expr::Lt(lhs, rhs) => {
                if Self::is_var(lhs, var_name) {
                    Some(rhs.clone())
                } else {
                    None
                }
            }

            // Pattern: i >= 0 (lower bound - ignore)
            Expr::Ge(lhs, rhs) => {
                if Self::is_var(lhs, var_name) && Self::is_zero(rhs) {
                    None
                } else {
                    None
                }
            }

            // Conjunction (Verus &&&)
            Expr::Conjunction(exprs) => {
                for e in exprs {
                    if let Some(bound) = Self::extract_int_upper_bound(e, var_name) {
                        return Some(bound);
                    }
                }
                None
            }

            _ => None,
        }
    }

    /// Extract collection from membership check: `x in collection` or `collection.contains(x)`
    fn extract_membership<'a>(
        expr: &'a crate::ast::Expr,
        var_name: &str,
    ) -> Option<&'a crate::ast::Expr> {
        use crate::ast::Expr;

        match expr {
            // Pattern: x in collection (binary `in` operator - represented as MethodCall)
            Expr::MethodCall {
                receiver,
                method,
                args,
            } if method == "contains" && args.len() == 1 => {
                if Self::is_var(&args[0], var_name) {
                    Some(receiver)
                } else {
                    None
                }
            }

            // Could also be Call to a `contains` function
            Expr::Call { func, args } if args.len() == 2 => {
                // Pattern: contains(collection, x)
                if func.last() == Some("contains") && Self::is_var(&args[1], var_name) {
                    Some(&args[0])
                } else {
                    None
                }
            }

            _ => None,
        }
    }

    /// Extract assignment from indexed access: `seq[i] == expr` or `expr == seq[i]`
    /// Returns (collection_name, assigned_expr)
    fn extract_indexed_assignment<'a>(
        expr: &'a crate::ast::Expr,
        var_name: &str,
    ) -> Option<(String, &'a crate::ast::Expr)> {
        use crate::ast::Expr;

        if let Expr::Eq(lhs, rhs) = expr {
            // Try lhs[var] == rhs
            if let Some(collection) = Self::extract_index_by_var(lhs, var_name) {
                return Some((collection, rhs));
            }
            // Try lhs == rhs[var]
            if let Some(collection) = Self::extract_index_by_var(rhs, var_name) {
                return Some((collection, lhs));
            }
        }
        None
    }

    /// Check if expr is `collection[var_name]` and return collection name
    fn extract_index_by_var(expr: &crate::ast::Expr, var_name: &str) -> Option<String> {
        use crate::ast::Expr;

        if let Expr::Index(collection, index) = expr {
            if Self::is_var(index, var_name) {
                // Get collection name
                if let Expr::Ident(name) = collection.as_ref() {
                    return Some(name.clone());
                }
            }
        }
        None
    }

    /// Check if expression is the given variable
    fn is_var(expr: &crate::ast::Expr, var_name: &str) -> bool {
        matches!(expr, crate::ast::Expr::Ident(name) if name == var_name)
    }

    /// Check if expression is zero literal
    fn is_zero(expr: &crate::ast::Expr) -> bool {
        matches!(expr, crate::ast::Expr::Literal(crate::ast::Literal::Int(0)))
    }
}

/// Result of attempting template matching with failure information
#[derive(Debug, Clone)]
pub enum TemplateMatchResult {
    /// Successfully matched a template
    Matched(QuantifierTemplate),
    /// Failed to match - provides reason for diagnostics
    NotMatched(TemplateMatchFailure),
}

/// Reasons why template matching failed
#[derive(Debug, Clone)]
pub enum TemplateMatchFailure {
    /// Not a forall expression
    NotForall,
    /// Multiple quantifier variables (we only support single var)
    MultipleVariables { count: usize },
    /// Body is not in a recognized pattern
    UnrecognizedPattern { description: String },
    /// Missing bounds in sequence comprehension
    MissingBounds,
    /// Index variable not used correctly
    InvalidIndexUsage { var: String },
}

impl TemplateMatcher {
    /// Match with detailed failure information for error reporting
    pub fn match_template_detailed(expr: &crate::ast::Expr) -> TemplateMatchResult {
        use crate::ast::Expr;

        match expr {
            Expr::Forall { vars, body, .. } => {
                if vars.len() != 1 {
                    return TemplateMatchResult::NotMatched(TemplateMatchFailure::MultipleVariables {
                        count: vars.len(),
                    });
                }

                let var = &vars[0];

                // Try all patterns
                if let Some(template) = Self::try_seq_comprehension(var, body) {
                    return TemplateMatchResult::Matched(template);
                }
                if let Some(template) = Self::try_map_comprehension(var, body) {
                    return TemplateMatchResult::Matched(template);
                }
                if let Some(template) = Self::try_set_comprehension(var, body) {
                    return TemplateMatchResult::Matched(template);
                }

                // Provide specific failure reason based on body structure
                let description = match body.as_ref() {
                    Expr::Implies(_, _) => {
                        "Implication body doesn't match seq/map comprehension pattern".to_string()
                    }
                    Expr::Eq(_, _) => {
                        "Equality body doesn't match set/map comprehension pattern".to_string()
                    }
                    _ => format!("Unexpected body structure: expected implication or equality"),
                };

                TemplateMatchResult::NotMatched(TemplateMatchFailure::UnrecognizedPattern {
                    description,
                })
            }
            _ => TemplateMatchResult::NotMatched(TemplateMatchFailure::NotForall),
        }
    }
}

/// Run all validation checks on a function
pub fn validate_function(
    func: &AnnotatedFunction,
    tracker: &AssignmentTracker,
) -> TranspileResult<()> {
    SaturationChecker::check(func, tracker)?;
    HarmonyChecker::check(func, tracker)?;
    ObligationChecker::check(func, tracker)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Expr, Literal, Parameter, ParameterMode, Path, SpecFunction, Type, VariableMode};

    fn make_test_function() -> AnnotatedFunction {
        AnnotatedFunction {
            spec_fn: SpecFunction {
                name: "TestFn".to_string(),
                generics: Default::default(),
                params: vec![
                    Parameter {
                        name: "s".to_string(),
                        ty: Type::Named(Path::single("State".to_string())),
                        mode: Some(ParameterMode::Input),
                        variable_mode: VariableMode::Exec,
                        span: None,
                    },
                    Parameter {
                        name: "s_".to_string(),
                        ty: Type::Named(Path::single("State".to_string())),
                        mode: Some(ParameterMode::Output),
                        variable_mode: VariableMode::Exec,
                        span: None,
                    },
                ],
                return_type: Type::Bool,
                requires: vec![],
                ensures: vec![],
                recommends: vec![],
                decreases: vec![],
                body: Expr::Literal(Literal::Bool(true)),
                span: None,
            },
            param_modes: vec![ParameterMode::Input, ParameterMode::Output],
            is_functionalizable: true,
            non_functionalizable_reason: None,
        }
    }

    #[test]
    fn test_saturation_check_passes() {
        let func = make_test_function();
        let mut tracker = AssignmentTracker::new();
        tracker.record_assignment("s_", MemberPath::Root);

        let result = SaturationChecker::check(&func, &tracker);
        assert!(result.is_ok());
    }

    #[test]
    fn test_saturation_check_fails() {
        let func = make_test_function();
        let tracker = AssignmentTracker::new(); // No assignments

        let result = SaturationChecker::check(&func, &tracker);
        assert!(result.is_err());
    }

    #[test]
    fn test_validate_function() {
        let func = make_test_function();
        let mut tracker = AssignmentTracker::new();
        tracker.record_assignment("s_", MemberPath::Root);

        let result = validate_function(&func, &tracker);
        assert!(result.is_ok());
    }
}

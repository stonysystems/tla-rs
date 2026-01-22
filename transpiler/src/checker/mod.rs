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
    pub fn match_template(_expr: &crate::ast::Expr) -> Option<QuantifierTemplate> {
        // TODO: Implement template matching
        // Patterns to match:
        // - forall |i| 0 <= i < n ==> seq[i] == f(i)  -> SeqComprehension
        // - forall |k| k in map' <==> pred            -> MapComprehension domain
        // - forall |k| k in map' ==> map'[k] == f(k)  -> MapComprehension value
        None
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

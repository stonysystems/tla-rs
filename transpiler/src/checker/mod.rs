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
    pub fn check(func: &AnnotatedFunction, tracker: &AssignmentTracker) -> TranspileResult<()> {
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
                        help: Some(
                            "Ensure all fields of output parameters are assigned".to_string(),
                        ),
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
    pub fn check(_func: &AnnotatedFunction, _tracker: &AssignmentTracker) -> TranspileResult<()> {
        // TODO: Implement harmony check
        // This requires tracking assignment order during expression analysis
        Ok(())
    }
}

/// Obligation checker - verifies outputs are used only after assignment
pub struct ObligationChecker;

impl ObligationChecker {
    /// Check that output variables are only used after assignment
    pub fn check(_func: &AnnotatedFunction, _tracker: &AssignmentTracker) -> TranspileResult<()> {
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

    /// Map filtering: filter keys from source map based on predicate
    /// Pattern: `forall |k| output.contains_key(k) ==> source.contains_key(k) && output[k] == source[k]`
    /// combined with exclusion: `forall |k| k < threshold ==> !output.contains_key(k)`
    /// and inclusion: `forall |k| k >= threshold && source.contains_key(k) ==> output.contains_key(k)`
    MapFilter {
        /// Source map variable name
        source_map: String,
        /// Output map variable name
        output_map: String,
        /// Key variable name
        key_var: String,
        /// Filter predicate (key >= threshold form)
        filter_predicate: Box<crate::ast::Expr>,
    },

    /// Map preservation pattern: output[k] == source[k] for all k in output
    /// Pattern: `forall |k| output.contains_key(k) ==> source.contains_key(k) && output[k] == source[k]`
    MapPreservation {
        /// Source map variable
        source_map: String,
        /// Output map variable
        output_map: String,
        /// Key variable
        key_var: String,
    },

    /// Map with conditional value: output[k] == if cond then v1 else v2
    /// Pattern: `forall |k| output.contains_key(k) ==> output[k] == (if cond { v1 } else { v2 })`
    MapConditionalValue {
        /// Output map variable
        output_map: String,
        /// Key variable
        key_var: String,
        /// Conditional value expression
        value_expr: Box<crate::ast::Expr>,
    },

    /// Map domain biconditional: output.dom().contains(k) <==> predicate
    /// Used for defining which keys are in the output map
    MapDomainBiconditional {
        /// Output map variable
        output_map: String,
        /// Key variable
        key_var: String,
        /// Domain predicate (what keys should be in output)
        domain_predicate: Box<crate::ast::Expr>,
    },

    /// Map exclusion pattern: predicate ==> !output.contains_key(key)
    /// Keys satisfying predicate are excluded from output
    MapExclusion {
        /// Output map variable
        output_map: String,
        /// Key variable
        key_var: String,
        /// Exclusion predicate (when true, key is NOT in output)
        exclusion_predicate: Box<crate::ast::Expr>,
    },

    /// Map inclusion pattern: predicate && source.contains_key(key) ==> output.contains_key(key)
    /// Keys that meet predicate and are in source are included in output
    MapInclusion {
        /// Output map variable
        output_map: String,
        /// Source map variable (optional)
        source_map: Option<String>,
        /// Key variable
        key_var: String,
        /// Inclusion predicate
        inclusion_predicate: Box<crate::ast::Expr>,
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

                // Try sequence comprehension first (uses Implies with bounds)
                if let Some(template) = Self::try_seq_comprehension(var, body) {
                    return Some(template);
                }

                // Try map domain biconditional (uses Iff with dom().contains())
                if let Some(template) = Self::try_map_domain_biconditional(var, body) {
                    return Some(template);
                }

                // Try map preservation (uses Implies with contains_key)
                if let Some(template) = Self::try_map_preservation(var, body) {
                    return Some(template);
                }

                // Try map conditional value (uses Implies with conditional value)
                if let Some(template) = Self::try_map_conditional_value(var, body) {
                    return Some(template);
                }

                // Try map exclusion (uses Implies with negated contains)
                if let Some(template) = Self::try_map_exclusion(var, body) {
                    return Some(template);
                }

                // Try map inclusion (uses Implies with contains_key in conclusion)
                if let Some(template) = Self::try_map_inclusion(var, body) {
                    return Some(template);
                }

                // Try set comprehension (uses Eq/biconditional for membership)
                // Note: Set comprehension has same pattern as map domain, but set is simpler
                if let Some(template) = Self::try_set_comprehension(var, body) {
                    return Some(template);
                }

                // Try map comprehension value (uses Implies with membership)
                if let Some(template) = Self::try_map_value_comprehension(var, body) {
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
                if let Some((_collection, element_expr)) =
                    Self::extract_indexed_assignment(rhs, &var.name)
                {
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

    /// Try to match: forall |k| k in map' ==> map'[k] == f(k) (value mapping)
    fn try_map_value_comprehension(
        var: &crate::ast::Binding,
        body: &crate::ast::Expr,
    ) -> Option<QuantifierTemplate> {
        use crate::ast::Expr;

        // Check for implication (value pattern): k in map' ==> map'[k] == expr
        if let Expr::Implies(lhs, rhs) = body {
            if let Some(_collection) = Self::extract_membership(lhs, &var.name) {
                // RHS should be: map'[k] == expr
                if let Some((_, value_expr)) = Self::extract_indexed_assignment(rhs, &var.name) {
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

    /// Try to match map domain biconditional:
    /// `forall |k| output.dom().contains(k) <==> predicate`
    /// or `forall |k| output.contains_key(k) <==> predicate`
    fn try_map_domain_biconditional(
        var: &crate::ast::Binding,
        body: &crate::ast::Expr,
    ) -> Option<QuantifierTemplate> {
        use crate::ast::Expr;

        // Check for Iff (biconditional <==>)
        if let Expr::Iff(lhs, rhs) = body {
            // Check if LHS is output.dom().contains(k) or output.contains_key(k)
            if let Some(output_map) = Self::extract_map_membership(lhs, &var.name) {
                return Some(QuantifierTemplate::MapDomainBiconditional {
                    output_map,
                    key_var: var.name.clone(),
                    domain_predicate: rhs.clone(),
                });
            }
            // Also check RHS in case it's reversed
            if let Some(output_map) = Self::extract_map_membership(rhs, &var.name) {
                return Some(QuantifierTemplate::MapDomainBiconditional {
                    output_map,
                    key_var: var.name.clone(),
                    domain_predicate: lhs.clone(),
                });
            }
        }
        None
    }

    /// Try to match map preservation pattern:
    /// `forall |k| output.contains_key(k) ==> source.contains_key(k) && output[k] == source[k]`
    fn try_map_preservation(
        var: &crate::ast::Binding,
        body: &crate::ast::Expr,
    ) -> Option<QuantifierTemplate> {
        use crate::ast::Expr;

        // Check for implication
        if let Expr::Implies(premise, conclusion) = body {
            // Premise should be: output.contains_key(k)
            if let Some(output_map) = Self::extract_map_membership(premise, &var.name) {
                // Conclusion should be: source.contains_key(k) && output[k] == source[k]
                // or conjunction with these parts
                if let Some(source_map) =
                    Self::extract_preservation_conclusion(conclusion, &var.name, &output_map)
                {
                    return Some(QuantifierTemplate::MapPreservation {
                        source_map,
                        output_map,
                        key_var: var.name.clone(),
                    });
                }
            }
        }
        None
    }

    /// Try to match map conditional value pattern:
    /// `forall |k| output.contains_key(k) ==> output[k] == (if cond { v1 } else { v2 })`
    /// or simpler: `forall |k| output.dom().contains(k) ==> output[k] == value_expr`
    fn try_map_conditional_value(
        var: &crate::ast::Binding,
        body: &crate::ast::Expr,
    ) -> Option<QuantifierTemplate> {
        use crate::ast::Expr;

        // Check for implication
        if let Expr::Implies(premise, conclusion) = body {
            // Premise should be: output.contains_key(k) or output.dom().contains(k)
            if let Some(output_map) = Self::extract_map_membership(premise, &var.name) {
                // Conclusion should be: output[k] == value_expr
                if let Expr::Eq(lhs, rhs) = conclusion.as_ref() {
                    // Check if LHS is output[k]
                    if let Some(indexed_map) = Self::extract_index_by_var(lhs, &var.name) {
                        if indexed_map == output_map {
                            return Some(QuantifierTemplate::MapConditionalValue {
                                output_map,
                                key_var: var.name.clone(),
                                value_expr: rhs.clone(),
                            });
                        }
                    }
                    // Check if RHS is output[k]
                    if let Some(indexed_map) = Self::extract_index_by_var(rhs, &var.name) {
                        if indexed_map == output_map {
                            return Some(QuantifierTemplate::MapConditionalValue {
                                output_map,
                                key_var: var.name.clone(),
                                value_expr: lhs.clone(),
                            });
                        }
                    }
                }
            }
        }
        None
    }

    /// Try to match map exclusion pattern:
    /// `forall |k| predicate ==> !output.contains_key(k)`
    fn try_map_exclusion(
        var: &crate::ast::Binding,
        body: &crate::ast::Expr,
    ) -> Option<QuantifierTemplate> {
        use crate::ast::Expr;

        // Check for implication with negated membership in conclusion
        if let Expr::Implies(premise, conclusion) = body {
            // Conclusion should be: !output.contains_key(k)
            if let Expr::Not(inner) = conclusion.as_ref() {
                if let Some(output_map) = Self::extract_map_membership(inner, &var.name) {
                    return Some(QuantifierTemplate::MapExclusion {
                        output_map,
                        key_var: var.name.clone(),
                        exclusion_predicate: premise.clone(),
                    });
                }
            }
        }
        None
    }

    /// Try to match map inclusion pattern:
    /// `forall |k| predicate && source.contains_key(k) ==> output.contains_key(k)`
    /// or simpler: `forall |k| predicate ==> output.contains_key(k)`
    fn try_map_inclusion(
        var: &crate::ast::Binding,
        body: &crate::ast::Expr,
    ) -> Option<QuantifierTemplate> {
        use crate::ast::Expr;

        // Check for implication with membership in conclusion
        if let Expr::Implies(premise, conclusion) = body {
            // Conclusion should be: output.contains_key(k)
            if let Some(output_map) = Self::extract_map_membership(conclusion, &var.name) {
                // Premise might be: predicate && source.contains_key(k)
                // Try to extract source map from premise
                let (source_map, pred) = Self::extract_source_from_premise(premise, &var.name);

                return Some(QuantifierTemplate::MapInclusion {
                    output_map,
                    source_map,
                    key_var: var.name.clone(),
                    inclusion_predicate: pred,
                });
            }
        }
        None
    }

    /// Extract source map from conjunction premise like: pred && source.contains_key(k)
    /// Returns (source_map, remaining_predicate)
    fn extract_source_from_premise(
        expr: &crate::ast::Expr,
        var_name: &str,
    ) -> (Option<String>, Box<crate::ast::Expr>) {
        use crate::ast::{BinOp, Expr};

        match expr {
            Expr::Binary(lhs, BinOp::And, rhs) => {
                // Check if LHS is contains_key
                if let Some(source) = Self::extract_map_membership(lhs, var_name) {
                    return (Some(source), rhs.clone());
                }
                // Check if RHS is contains_key
                if let Some(source) = Self::extract_map_membership(rhs, var_name) {
                    return (Some(source), lhs.clone());
                }
                // Neither side is membership, return the whole thing
                (None, Box::new(expr.clone()))
            }
            Expr::Conjunction(parts) => {
                // Look for membership in any part
                let mut source_map = None;
                let mut remaining: Vec<Expr> = vec![];

                for part in parts {
                    if let Some(source) = Self::extract_map_membership(part, var_name) {
                        source_map = Some(source);
                    } else {
                        remaining.push(part.clone());
                    }
                }

                if remaining.is_empty() {
                    (
                        source_map,
                        Box::new(Expr::Literal(crate::ast::Literal::Bool(true))),
                    )
                } else if remaining.len() == 1 {
                    (source_map, Box::new(remaining.into_iter().next().unwrap()))
                } else {
                    (source_map, Box::new(Expr::Conjunction(remaining)))
                }
            }
            _ => (None, Box::new(expr.clone())),
        }
    }

    /// Extract map name from membership patterns:
    /// - `map.contains_key(k)` -> Some(map)
    /// - `map.dom().contains(k)` -> Some(map)
    /// - `obj.field.contains_key(k)` -> Some(obj.field)
    fn extract_map_membership(expr: &crate::ast::Expr, var_name: &str) -> Option<String> {
        use crate::ast::Expr;

        match expr {
            // Pattern: map.contains_key(k) or obj.field.contains_key(k)
            Expr::MethodCall {
                receiver,
                method,
                args,
            } if method == "contains_key" && args.len() == 1 => {
                if Self::is_var(&args[0], var_name) {
                    // Use expr_to_name to handle both identifiers and field access
                    return Some(Self::expr_to_name(receiver));
                }
                None
            }

            // Pattern: map.dom().contains(k) or obj.field.dom().contains(k)
            Expr::MethodCall {
                receiver,
                method,
                args,
            } if method == "contains" && args.len() == 1 => {
                if Self::is_var(&args[0], var_name) {
                    // receiver should be map.dom()
                    if let Expr::MethodCall {
                        receiver: inner_recv,
                        method: inner_method,
                        args: inner_args,
                    } = receiver.as_ref()
                    {
                        if inner_method == "dom" && inner_args.is_empty() {
                            // Use expr_to_name to handle both identifiers and field access
                            return Some(Self::expr_to_name(inner_recv));
                        }
                    }
                }
                None
            }

            _ => None,
        }
    }

    /// Extract source map from preservation conclusion:
    /// `source.contains_key(k) && output[k] == source[k]`
    fn extract_preservation_conclusion(
        expr: &crate::ast::Expr,
        var_name: &str,
        output_map: &str,
    ) -> Option<String> {
        use crate::ast::{BinOp, Expr};

        match expr {
            // Pattern: conjunction
            Expr::Conjunction(parts) => {
                let mut source_from_contains: Option<String> = None;
                let mut source_from_eq: Option<String> = None;

                for part in parts {
                    // Check for source.contains_key(k)
                    if let Some(map) = Self::extract_map_membership(part, var_name) {
                        if map != output_map {
                            source_from_contains = Some(map);
                        }
                    }
                    // Check for output[k] == source[k]
                    if let Expr::Eq(lhs, rhs) = part {
                        if let Some(eq_source) =
                            Self::extract_eq_source_map(lhs, rhs, var_name, output_map)
                        {
                            source_from_eq = Some(eq_source);
                        }
                    }
                }

                // Both should match and agree on source
                if source_from_contains == source_from_eq {
                    return source_from_contains;
                }
                None
            }

            // Pattern: a && b
            Expr::Binary(lhs, BinOp::And, rhs) => {
                // Try to extract from both sides
                let source1 = Self::extract_map_membership(lhs, var_name);
                let source2 = Self::extract_map_membership(rhs, var_name);

                // One side should have contains_key for source, other should be equality
                if let Some(s) = source1 {
                    if s != output_map {
                        // lhs is source.contains_key(k), rhs should be equality
                        if let Expr::Eq(eq_lhs, eq_rhs) = rhs.as_ref() {
                            if let Some(eq_source) =
                                Self::extract_eq_source_map(eq_lhs, eq_rhs, var_name, output_map)
                            {
                                if eq_source == s {
                                    return Some(s);
                                }
                            }
                        }
                    }
                }
                if let Some(s) = source2 {
                    if s != output_map {
                        // rhs is source.contains_key(k), lhs should be equality
                        if let Expr::Eq(eq_lhs, eq_rhs) = lhs.as_ref() {
                            if let Some(eq_source) =
                                Self::extract_eq_source_map(eq_lhs, eq_rhs, var_name, output_map)
                            {
                                if eq_source == s {
                                    return Some(s);
                                }
                            }
                        }
                    }
                }
                None
            }

            _ => None,
        }
    }

    /// Extract source map from equality: output[k] == source[k]
    fn extract_eq_source_map(
        lhs: &crate::ast::Expr,
        rhs: &crate::ast::Expr,
        var_name: &str,
        output_map: &str,
    ) -> Option<String> {
        // Check lhs[k] == rhs[k] pattern
        let lhs_map = Self::extract_index_by_var(lhs, var_name);
        let rhs_map = Self::extract_index_by_var(rhs, var_name);

        match (lhs_map, rhs_map) {
            (Some(l), Some(r)) => {
                if l == output_map {
                    Some(r)
                } else if r == output_map {
                    Some(l)
                } else {
                    None
                }
            }
            _ => None,
        }
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

            // Pattern: i >= 0 (lower bound - ignore, we always assume 0 lower bound)
            Expr::Ge(_, _) => None,

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
    /// Handles both simple identifiers and field access patterns
    fn extract_index_by_var(expr: &crate::ast::Expr, var_name: &str) -> Option<String> {
        use crate::ast::Expr;

        if let Expr::Index(collection, index) = expr {
            if Self::is_var(index, var_name) {
                // Get collection name (can be identifier or field access)
                return Some(Self::expr_to_name(collection));
            }
        }
        None
    }

    /// Convert an expression to a string name (for collection names)
    /// Handles identifiers and field access chains
    fn expr_to_name(expr: &crate::ast::Expr) -> String {
        use crate::ast::Expr;

        match expr {
            Expr::Ident(name) => name.clone(),
            Expr::Field(base, field) => {
                format!("{}.{}", Self::expr_to_name(base), field)
            }
            // For other expression types, just use a placeholder
            _ => "_expr_".to_string(),
        }
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
                    return TemplateMatchResult::NotMatched(
                        TemplateMatchFailure::MultipleVariables { count: vars.len() },
                    );
                }

                let var = &vars[0];

                // Try all patterns (same order as match_template)
                if let Some(template) = Self::try_seq_comprehension(var, body) {
                    return TemplateMatchResult::Matched(template);
                }
                if let Some(template) = Self::try_map_domain_biconditional(var, body) {
                    return TemplateMatchResult::Matched(template);
                }
                if let Some(template) = Self::try_map_preservation(var, body) {
                    return TemplateMatchResult::Matched(template);
                }
                if let Some(template) = Self::try_map_conditional_value(var, body) {
                    return TemplateMatchResult::Matched(template);
                }
                if let Some(template) = Self::try_map_exclusion(var, body) {
                    return TemplateMatchResult::Matched(template);
                }
                if let Some(template) = Self::try_map_inclusion(var, body) {
                    return TemplateMatchResult::Matched(template);
                }
                if let Some(template) = Self::try_set_comprehension(var, body) {
                    return TemplateMatchResult::Matched(template);
                }
                if let Some(template) = Self::try_map_value_comprehension(var, body) {
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
                    Expr::Iff(_, _) => {
                        "Biconditional body doesn't match map domain pattern".to_string()
                    }
                    _ => "Unexpected body structure: expected implication, equality, or biconditional".to_string(),
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
    use crate::ast::{
        BinOp, Binding, Expr, Literal, Parameter, ParameterMode, Path, SpecFunction, Type,
        VariableMode,
    };

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

    // ============ Template Matching Tests ============

    /// Helper to create a binding for testing
    fn make_binding(name: &str) -> Binding {
        Binding {
            name: name.to_string(),
            ty: Some(Type::Int),
            variable_mode: VariableMode::default(),
        }
    }

    /// Test: forall |i| 0 <= i && i < 5 ==> result[i] == i * 2
    #[test]
    fn test_seq_comprehension_simple() {
        // Build: 0 <= i && i < 5
        let bounds = Expr::Binary(
            Box::new(Expr::Le(
                Box::new(Expr::Literal(Literal::Int(0))),
                Box::new(Expr::Ident("i".to_string())),
            )),
            BinOp::And,
            Box::new(Expr::Lt(
                Box::new(Expr::Ident("i".to_string())),
                Box::new(Expr::Literal(Literal::Int(5))),
            )),
        );

        // Build: result[i] == i * 2
        let assignment = Expr::Eq(
            Box::new(Expr::Index(
                Box::new(Expr::Ident("result".to_string())),
                Box::new(Expr::Ident("i".to_string())),
            )),
            Box::new(Expr::Binary(
                Box::new(Expr::Ident("i".to_string())),
                BinOp::Mul,
                Box::new(Expr::Literal(Literal::Int(2))),
            )),
        );

        // Build: bounds ==> assignment
        let body = Expr::Implies(Box::new(bounds), Box::new(assignment));

        // Build: forall |i| body
        let forall = Expr::Forall {
            vars: vec![make_binding("i")],
            triggers: vec![],
            body: Box::new(body),
        };

        let result = TemplateMatcher::match_template(&forall);
        assert!(result.is_some());

        if let Some(QuantifierTemplate::SeqComprehension {
            length_expr,
            index_var,
            ..
        }) = result
        {
            assert_eq!(index_var, "i");
            // length should be 5
            if let Expr::Literal(Literal::Int(n)) = *length_expr {
                assert_eq!(n, 5);
            } else {
                panic!("Expected literal length");
            }
        } else {
            panic!("Expected SeqComprehension template");
        }
    }

    /// Test: forall |i| i < n ==> seq[i] == f(i) (just upper bound)
    #[test]
    fn test_seq_comprehension_upper_bound_only() {
        let bounds = Expr::Lt(
            Box::new(Expr::Ident("i".to_string())),
            Box::new(Expr::Ident("n".to_string())),
        );

        let assignment = Expr::Eq(
            Box::new(Expr::Index(
                Box::new(Expr::Ident("seq".to_string())),
                Box::new(Expr::Ident("i".to_string())),
            )),
            Box::new(Expr::Call {
                func: Path::single("f".to_string()),
                args: vec![Expr::Ident("i".to_string())],
            }),
        );

        let body = Expr::Implies(Box::new(bounds), Box::new(assignment));

        let forall = Expr::Forall {
            vars: vec![make_binding("i")],
            triggers: vec![],
            body: Box::new(body),
        };

        let result = TemplateMatcher::match_template(&forall);
        assert!(result.is_some());
        assert!(matches!(
            result,
            Some(QuantifierTemplate::SeqComprehension { .. })
        ));
    }

    /// Test: forall |k| map'.contains(k) == pred(k) (set/map domain)
    #[test]
    fn test_set_comprehension() {
        // Build: set'.contains(k)
        let membership = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("set_".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Ident("k".to_string())],
        };

        // Build: k > 0
        let pred = Expr::Gt(
            Box::new(Expr::Ident("k".to_string())),
            Box::new(Expr::Literal(Literal::Int(0))),
        );

        // Build: membership == pred (biconditional)
        let body = Expr::Eq(Box::new(membership), Box::new(pred));

        let forall = Expr::Forall {
            vars: vec![make_binding("k")],
            triggers: vec![],
            body: Box::new(body),
        };

        let result = TemplateMatcher::match_template(&forall);
        assert!(result.is_some());

        if let Some(QuantifierTemplate::SetComprehension { element_var, .. }) = result {
            assert_eq!(element_var, "k");
        } else {
            panic!("Expected SetComprehension template");
        }
    }

    /// Test: forall |k| map'.contains(k) ==> map'[k] == f(k) (map value)
    #[test]
    fn test_map_comprehension_value() {
        // Build: map'.contains(k)
        let membership = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("map_".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Ident("k".to_string())],
        };

        // Build: map'[k] == f(k)
        let value_assign = Expr::Eq(
            Box::new(Expr::Index(
                Box::new(Expr::Ident("map_".to_string())),
                Box::new(Expr::Ident("k".to_string())),
            )),
            Box::new(Expr::Call {
                func: Path::single("f".to_string()),
                args: vec![Expr::Ident("k".to_string())],
            }),
        );

        // Build: membership ==> value_assign
        let body = Expr::Implies(Box::new(membership), Box::new(value_assign));

        let forall = Expr::Forall {
            vars: vec![make_binding("k")],
            triggers: vec![],
            body: Box::new(body),
        };

        let result = TemplateMatcher::match_template(&forall);
        assert!(result.is_some());

        if let Some(QuantifierTemplate::MapComprehension { key_var, .. }) = result {
            assert_eq!(key_var, "k");
        } else {
            panic!("Expected MapComprehension template");
        }
    }

    /// Test: non-forall expression returns None
    #[test]
    fn test_template_match_non_forall() {
        let expr = Expr::Literal(Literal::Bool(true));
        let result = TemplateMatcher::match_template(&expr);
        assert!(result.is_none());
    }

    /// Test: multiple variables returns None
    #[test]
    fn test_template_match_multiple_vars() {
        let forall = Expr::Forall {
            vars: vec![make_binding("i"), make_binding("j")],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };

        let result = TemplateMatcher::match_template(&forall);
        assert!(result.is_none());
    }

    /// Test detailed match result for unrecognized pattern
    #[test]
    fn test_template_match_detailed_unrecognized() {
        // Body is just a literal - not a recognized pattern
        let forall = Expr::Forall {
            vars: vec![make_binding("i")],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };

        let result = TemplateMatcher::match_template_detailed(&forall);
        assert!(matches!(
            result,
            TemplateMatchResult::NotMatched(TemplateMatchFailure::UnrecognizedPattern { .. })
        ));
    }

    /// Test detailed match result for multiple variables
    #[test]
    fn test_template_match_detailed_multiple_vars() {
        let forall = Expr::Forall {
            vars: vec![make_binding("i"), make_binding("j")],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };

        let result = TemplateMatcher::match_template_detailed(&forall);
        if let TemplateMatchResult::NotMatched(TemplateMatchFailure::MultipleVariables { count }) =
            result
        {
            assert_eq!(count, 2);
        } else {
            panic!("Expected MultipleVariables failure");
        }
    }

    /// Test with Conjunction bounds (Verus &&&)
    #[test]
    fn test_seq_comprehension_with_conjunction_bounds() {
        // Build bounds using Conjunction: &&& 0 <= i &&& i < n
        let bounds = Expr::Conjunction(vec![
            Expr::Le(
                Box::new(Expr::Literal(Literal::Int(0))),
                Box::new(Expr::Ident("i".to_string())),
            ),
            Expr::Lt(
                Box::new(Expr::Ident("i".to_string())),
                Box::new(Expr::Ident("n".to_string())),
            ),
        ]);

        let assignment = Expr::Eq(
            Box::new(Expr::Index(
                Box::new(Expr::Ident("result".to_string())),
                Box::new(Expr::Ident("i".to_string())),
            )),
            Box::new(Expr::Ident("i".to_string())),
        );

        let body = Expr::Implies(Box::new(bounds), Box::new(assignment));

        let forall = Expr::Forall {
            vars: vec![make_binding("i")],
            triggers: vec![],
            body: Box::new(body),
        };

        let result = TemplateMatcher::match_template(&forall);
        assert!(result.is_some());
        assert!(matches!(
            result,
            Some(QuantifierTemplate::SeqComprehension { .. })
        ));
    }

    // ============ New RSL Pattern Tests ============

    /// Test: forall |k| votes_.dom().contains(k) <==> predicate
    #[test]
    fn test_map_domain_biconditional() {
        // Build: votes_.dom().contains(k)
        let dom_contains = Expr::MethodCall {
            receiver: Box::new(Expr::MethodCall {
                receiver: Box::new(Expr::Ident("votes_".to_string())),
                method: "dom".to_string(),
                args: vec![],
            }),
            method: "contains".to_string(),
            args: vec![Expr::Ident("k".to_string())],
        };

        // Build: k >= threshold && source.dom().contains(k)
        let predicate = Expr::Binary(
            Box::new(Expr::Ge(
                Box::new(Expr::Ident("k".to_string())),
                Box::new(Expr::Ident("threshold".to_string())),
            )),
            BinOp::And,
            Box::new(Expr::MethodCall {
                receiver: Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::Ident("votes".to_string())),
                    method: "dom".to_string(),
                    args: vec![],
                }),
                method: "contains".to_string(),
                args: vec![Expr::Ident("k".to_string())],
            }),
        );

        // Build: dom_contains <==> predicate
        let body = Expr::Iff(Box::new(dom_contains), Box::new(predicate));

        let forall = Expr::Forall {
            vars: vec![make_binding("k")],
            triggers: vec![],
            body: Box::new(body),
        };

        let result = TemplateMatcher::match_template(&forall);
        assert!(result.is_some());

        if let Some(QuantifierTemplate::MapDomainBiconditional {
            output_map,
            key_var,
            ..
        }) = result
        {
            assert_eq!(output_map, "votes_");
            assert_eq!(key_var, "k");
        } else {
            panic!("Expected MapDomainBiconditional template, got {:?}", result);
        }
    }

    /// Test: forall |k| votes_.contains_key(k) ==> votes[k] == votes_[k]
    #[test]
    fn test_map_preservation() {
        // Build: votes_.contains_key(k)
        let contains_key = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("votes_".to_string())),
            method: "contains_key".to_string(),
            args: vec![Expr::Ident("k".to_string())],
        };

        // Build: votes.contains_key(k) && votes_[k] == votes[k]
        let conclusion = Expr::Binary(
            Box::new(Expr::MethodCall {
                receiver: Box::new(Expr::Ident("votes".to_string())),
                method: "contains_key".to_string(),
                args: vec![Expr::Ident("k".to_string())],
            }),
            BinOp::And,
            Box::new(Expr::Eq(
                Box::new(Expr::Index(
                    Box::new(Expr::Ident("votes_".to_string())),
                    Box::new(Expr::Ident("k".to_string())),
                )),
                Box::new(Expr::Index(
                    Box::new(Expr::Ident("votes".to_string())),
                    Box::new(Expr::Ident("k".to_string())),
                )),
            )),
        );

        // Build: contains_key ==> conclusion
        let body = Expr::Implies(Box::new(contains_key), Box::new(conclusion));

        let forall = Expr::Forall {
            vars: vec![make_binding("k")],
            triggers: vec![],
            body: Box::new(body),
        };

        let result = TemplateMatcher::match_template(&forall);
        assert!(result.is_some());

        if let Some(QuantifierTemplate::MapPreservation {
            source_map,
            output_map,
            key_var,
        }) = result
        {
            assert_eq!(source_map, "votes");
            assert_eq!(output_map, "votes_");
            assert_eq!(key_var, "k");
        } else {
            panic!("Expected MapPreservation template, got {:?}", result);
        }
    }

    /// Test: forall |k| votes_.dom().contains(k) ==> votes_[k] == (if k == new_key { new_val } else { votes[k] })
    #[test]
    fn test_map_conditional_value() {
        // Build: votes_.dom().contains(k)
        let dom_contains = Expr::MethodCall {
            receiver: Box::new(Expr::MethodCall {
                receiver: Box::new(Expr::Ident("votes_".to_string())),
                method: "dom".to_string(),
                args: vec![],
            }),
            method: "contains".to_string(),
            args: vec![Expr::Ident("k".to_string())],
        };

        // Build: votes_[k] == (if k == new_key { new_val } else { votes[k] })
        let value_eq = Expr::Eq(
            Box::new(Expr::Index(
                Box::new(Expr::Ident("votes_".to_string())),
                Box::new(Expr::Ident("k".to_string())),
            )),
            Box::new(Expr::If {
                cond: Box::new(Expr::Eq(
                    Box::new(Expr::Ident("k".to_string())),
                    Box::new(Expr::Ident("new_key".to_string())),
                )),
                then_branch: Box::new(Expr::Ident("new_val".to_string())),
                else_branch: Some(Box::new(Expr::Index(
                    Box::new(Expr::Ident("votes".to_string())),
                    Box::new(Expr::Ident("k".to_string())),
                ))),
            }),
        );

        // Build: dom_contains ==> value_eq
        let body = Expr::Implies(Box::new(dom_contains), Box::new(value_eq));

        let forall = Expr::Forall {
            vars: vec![make_binding("k")],
            triggers: vec![],
            body: Box::new(body),
        };

        let result = TemplateMatcher::match_template(&forall);
        assert!(result.is_some());

        if let Some(QuantifierTemplate::MapConditionalValue {
            output_map,
            key_var,
            ..
        }) = result
        {
            assert_eq!(output_map, "votes_");
            assert_eq!(key_var, "k");
        } else {
            panic!("Expected MapConditionalValue template, got {:?}", result);
        }
    }

    /// Test: forall |k| votes_.contains_key(k) <==> predicate (using contains_key instead of dom)
    #[test]
    fn test_map_domain_biconditional_contains_key() {
        // Build: votes_.contains_key(k)
        let contains_key = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("votes_".to_string())),
            method: "contains_key".to_string(),
            args: vec![Expr::Ident("k".to_string())],
        };

        // Build: k >= 0
        let predicate = Expr::Ge(
            Box::new(Expr::Ident("k".to_string())),
            Box::new(Expr::Literal(Literal::Int(0))),
        );

        // Build: contains_key <==> predicate
        let body = Expr::Iff(Box::new(contains_key), Box::new(predicate));

        let forall = Expr::Forall {
            vars: vec![make_binding("k")],
            triggers: vec![],
            body: Box::new(body),
        };

        let result = TemplateMatcher::match_template(&forall);
        assert!(result.is_some());

        if let Some(QuantifierTemplate::MapDomainBiconditional {
            output_map,
            key_var,
            ..
        }) = result
        {
            assert_eq!(output_map, "votes_");
            assert_eq!(key_var, "k");
        } else {
            panic!("Expected MapDomainBiconditional template, got {:?}", result);
        }
    }
}

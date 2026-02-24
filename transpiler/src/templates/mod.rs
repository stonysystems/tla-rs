//! Quantifier template matching for code generation.
//!
//! This module provides template matching to recognize common quantifier patterns
//! in spec predicates and transform them into executable code.
//!
//! Supported patterns:
//! - Sequence comprehensions: `forall |i| 0 <= i < len ==> seq[i] == expr`
//! - Set comprehensions: `forall |x| x in set <==> pred(x)`
//! - Map comprehensions: `forall |k| k in map <==> pred(k) && map[k] == expr`

use crate::ast::{BinOp, Expr};

/// Recognized quantifier templates for code generation.
///
/// This is the single canonical enum for all template patterns, used by both
/// the `templates::TemplateMatcher` (stateful, handles all patterns including
/// non-quantifier assignments) and the `checker::QuantifierMatcher` (stateless,
/// handles forall-quantifier patterns only).
#[derive(Debug, Clone)]
pub enum QuantifierTemplate {
    // ── Shared variants (used by both matchers) ──────────────────────
    /// Sequence comprehension pattern
    /// Pattern: `forall |i| 0 <= i < len ==> seq[i] == element_expr(i)`
    /// Generates: `Vec::from_fn(len, |i| element_expr(i))`
    SeqComprehension {
        /// Expression for the sequence length
        length_expr: Box<Expr>,
        /// Expression for each element (as function of index)
        element_expr: Box<Expr>,
        /// Variable name for the index
        index_var: String,
        /// The sequence variable being defined (set by TemplateMatcher, None from QuantifierMatcher)
        seq_var: Option<String>,
    },

    /// Set comprehension pattern
    /// Pattern: `forall |x| x in set <==> domain_pred(x)`
    /// Generates: domain iteration with predicate filter
    SetComprehension {
        /// Domain predicate that defines membership
        domain_predicate: Box<Expr>,
        /// Variable name for set elements
        element_var: String,
        /// The set variable being defined (set by TemplateMatcher, None from QuantifierMatcher)
        set_var: Option<String>,
    },

    /// Full map comprehension (domain + value combined)
    MapComprehension {
        /// Domain predicate
        domain_predicate: Box<Expr>,
        /// Value expression
        value_expr: Box<Expr>,
        /// Variable name for keys
        key_var: String,
        /// The map variable being defined (set by TemplateMatcher, None from QuantifierMatcher)
        map_var: Option<String>,
    },

    // ── TemplateMatcher-only variants ────────────────────────────────
    /// Map comprehension pattern - domain
    /// Pattern: `forall |k| k in map <==> domain_pred(k)`
    /// Combined with value pattern to generate full map
    MapDomain {
        /// Variable name for keys
        key_var: String,
        /// Domain predicate
        domain_predicate: Box<Expr>,
        /// The map variable being defined
        map_var: String,
    },

    /// Map comprehension pattern - value
    /// Pattern: `forall |k| k in map ==> map[k] == value_expr(k)`
    /// Generates: HashMap with computed values
    MapValue {
        /// Variable name for keys
        key_var: String,
        /// Value expression (as function of key)
        value_expr: Box<Expr>,
        /// The map variable being defined
        map_var: String,
    },

    /// Simple equality - not a comprehension but common
    /// Pattern: `output == expr`
    SimpleAssignment {
        /// Output variable name
        output_var: String,
        /// Expression to assign
        value_expr: Box<Expr>,
    },

    /// Copy/clone pattern
    /// Pattern: `output == input` where both are same type
    Copy {
        /// Output variable
        output_var: String,
        /// Input variable to copy
        input_var: String,
    },

    /// Field-wise assignment pattern
    /// Pattern: `output.field1 == e1 &&& output.field2 == e2 &&& ...`
    StructConstruction {
        /// Output variable name
        output_var: String,
        /// Field assignments
        fields: Vec<(String, Expr)>,
    },

    /// Unrecognized pattern that needs manual handling
    Unrecognized {
        /// Original expression
        expr: Box<Expr>,
        /// Reason why it couldn't be matched
        reason: String,
        /// Suggested manual implementation hint
        hint: Option<String>,
    },

    // ── QuantifierMatcher-only variants ──────────────────────────────
    /// Map filtering: filter keys from source map based on predicate
    /// Pattern: `forall |k| output.contains_key(k) ==> source.contains_key(k) && output[k] == source[k]`
    MapFilter {
        /// Source map variable name
        source_map: String,
        /// Output map variable name
        output_map: String,
        /// Key variable name
        key_var: String,
        /// Filter predicate (key >= threshold form)
        filter_predicate: Box<Expr>,
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
        value_expr: Box<Expr>,
    },

    /// Map domain biconditional: output.dom().contains(k) <==> predicate
    /// Used for defining which keys are in the output map
    MapDomainBiconditional {
        /// Output map variable
        output_map: String,
        /// Key variable
        key_var: String,
        /// Domain predicate (what keys should be in output)
        domain_predicate: Box<Expr>,
    },

    /// Map exclusion pattern: predicate ==> !output.contains_key(key)
    /// Keys satisfying predicate are excluded from output
    MapExclusion {
        /// Output map variable
        output_map: String,
        /// Key variable
        key_var: String,
        /// Exclusion predicate (when true, key is NOT in output)
        exclusion_predicate: Box<Expr>,
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
        inclusion_predicate: Box<Expr>,
    },

    /// Collection check pattern: forall |x| container.contains(x) ==> pred(x)
    /// Used to verify all elements in a collection satisfy a predicate
    /// Translates to: container.iter().all(|x| pred(x))
    CollectionCheck {
        /// Container expression (can be a set, vec, etc.)
        container: Box<Expr>,
        /// Element variable
        element_var: String,
        /// Predicate to check for each element
        predicate: Box<Expr>,
    },
}

/// Template matcher for quantified expressions
pub struct TemplateMatcher {
    /// Output variables to look for in assignments
    output_vars: Vec<String>,
}

impl TemplateMatcher {
    /// Create a new template matcher
    pub fn new(output_vars: Vec<String>) -> Self {
        Self { output_vars }
    }

    /// Try to match an expression to a known template
    pub fn match_template(&self, expr: &Expr) -> QuantifierTemplate {
        // Try matching in order of specificity
        if let Some(template) = self.try_match_seq_comprehension(expr) {
            return template;
        }

        if let Some(template) = self.try_match_map_comprehension(expr) {
            return template;
        }

        if let Some(template) = self.try_match_set_comprehension(expr) {
            return template;
        }

        if let Some(template) = self.try_match_struct_construction(expr) {
            return template;
        }

        if let Some(template) = self.try_match_simple_assignment(expr) {
            return template;
        }

        // Couldn't match any known pattern
        QuantifierTemplate::Unrecognized {
            expr: Box::new(expr.clone()),
            reason: "Expression doesn't match any known template".to_string(),
            hint: Some(self.generate_hint(expr)),
        }
    }

    /// Try to match sequence comprehension pattern
    /// `forall |i| 0 <= i < len ==> seq[i] == element_expr`
    fn try_match_seq_comprehension(&self, expr: &Expr) -> Option<QuantifierTemplate> {
        let Expr::Forall { vars, body, .. } = expr else {
            return None;
        };

        // Must have exactly one bound variable
        if vars.len() != 1 {
            return None;
        }
        let index_var = vars[0].name_string();

        // Body should be an implication
        let Expr::Implies(premise, conclusion) = body.as_ref() else {
            return None;
        };

        // Try to extract range bounds from premise: 0 <= i < len
        let length_expr = self.extract_range_bound(premise, &index_var)?;

        // Conclusion should be seq[i] == element_expr
        let (seq_var, element_expr) = self.extract_indexed_equality(conclusion, &index_var)?;

        // Check if seq_var is an output variable
        if !self.output_vars.contains(&seq_var) {
            return None;
        }

        Some(QuantifierTemplate::SeqComprehension {
            index_var,
            length_expr: Box::new(length_expr),
            element_expr: Box::new(element_expr),
            seq_var: Some(seq_var),
        })
    }

    /// Try to match map comprehension pattern
    fn try_match_map_comprehension(&self, expr: &Expr) -> Option<QuantifierTemplate> {
        let Expr::Forall { vars, body, .. } = expr else {
            return None;
        };

        if vars.len() != 1 {
            return None;
        }
        let key_var = vars[0].name_string();

        // Check for domain pattern: k in map <==> pred
        if let Expr::Eq(lhs, rhs) = body.as_ref() {
            // Could be bidirectional (iff)
            if let Some((map_var, domain_pred)) = self.extract_membership_equiv(lhs, rhs, &key_var)
            {
                if self.output_vars.contains(&map_var) {
                    return Some(QuantifierTemplate::MapDomain {
                        key_var,
                        domain_predicate: Box::new(domain_pred),
                        map_var,
                    });
                }
            }
        }

        // Check for value pattern: k in map ==> map[k] == expr
        if let Expr::Implies(premise, conclusion) = body.as_ref() {
            if let Some((map_var, value_expr)) =
                self.extract_map_value_pattern(premise, conclusion, &key_var)
            {
                if self.output_vars.contains(&map_var) {
                    return Some(QuantifierTemplate::MapValue {
                        key_var,
                        value_expr: Box::new(value_expr),
                        map_var,
                    });
                }
            }
        }

        None
    }

    /// Try to match set comprehension pattern
    fn try_match_set_comprehension(&self, expr: &Expr) -> Option<QuantifierTemplate> {
        let Expr::Forall { vars, body, .. } = expr else {
            return None;
        };

        if vars.len() != 1 {
            return None;
        }
        let element_var = vars[0].name_string();

        // Check for: x in set <==> pred(x)
        if let Expr::Eq(lhs, rhs) = body.as_ref() {
            if let Some((set_var, domain_pred)) =
                self.extract_set_membership_equiv(lhs, rhs, &element_var)
            {
                if self.output_vars.contains(&set_var) {
                    return Some(QuantifierTemplate::SetComprehension {
                        element_var,
                        domain_predicate: Box::new(domain_pred),
                        set_var: Some(set_var),
                    });
                }
            }
        }

        None
    }

    /// Try to match struct construction pattern (conjunction of field assignments)
    fn try_match_struct_construction(&self, expr: &Expr) -> Option<QuantifierTemplate> {
        let Expr::Conjunction(clauses) = expr else {
            return None;
        };

        let mut output_var: Option<String> = None;
        let mut fields = Vec::new();

        for clause in clauses {
            let Expr::Eq(lhs, rhs) = clause else {
                continue;
            };

            // Check for output.field == expr pattern
            if let Expr::Field(base, field_name) = lhs.as_ref() {
                if let Expr::Ident(var_name) = base.as_ref() {
                    if self.output_vars.contains(var_name) {
                        // Initialize or verify output var consistency
                        if let Some(ref existing) = output_var {
                            if existing != var_name {
                                return None; // Mixed output vars
                            }
                        } else {
                            output_var = Some(var_name.clone());
                        }

                        fields.push((field_name.clone(), *rhs.clone()));
                    }
                }
            }
        }

        if fields.is_empty() {
            return None;
        }

        Some(QuantifierTemplate::StructConstruction {
            output_var: output_var?,
            fields,
        })
    }

    /// Try to match simple assignment: output == expr
    fn try_match_simple_assignment(&self, expr: &Expr) -> Option<QuantifierTemplate> {
        let Expr::Eq(lhs, rhs) = expr else {
            return None;
        };

        // Check if left side is an output variable
        if let Expr::Ident(var_name) = lhs.as_ref() {
            if self.output_vars.contains(var_name) {
                // Check for copy pattern: output == input
                if let Expr::Ident(input_name) = rhs.as_ref() {
                    if !self.output_vars.contains(input_name) {
                        return Some(QuantifierTemplate::Copy {
                            output_var: var_name.clone(),
                            input_var: input_name.clone(),
                        });
                    }
                }

                return Some(QuantifierTemplate::SimpleAssignment {
                    output_var: var_name.clone(),
                    value_expr: rhs.clone(),
                });
            }
        }

        // Also check right side (output on right)
        if let Expr::Ident(var_name) = rhs.as_ref() {
            if self.output_vars.contains(var_name) {
                if let Expr::Ident(input_name) = lhs.as_ref() {
                    if !self.output_vars.contains(input_name) {
                        return Some(QuantifierTemplate::Copy {
                            output_var: var_name.clone(),
                            input_var: input_name.clone(),
                        });
                    }
                }

                return Some(QuantifierTemplate::SimpleAssignment {
                    output_var: var_name.clone(),
                    value_expr: lhs.clone(),
                });
            }
        }

        None
    }

    // Helper methods for pattern extraction

    /// Extract upper bound from range pattern: 0 <= i < len or i < len && i >= 0
    fn extract_range_bound(&self, expr: &Expr, index_var: &str) -> Option<Expr> {
        match expr {
            // Pattern: 0 <= i < len (chained comparison)
            // This might be represented as conjunction
            Expr::Conjunction(parts) => {
                // Look for i < len or len > i
                for part in parts {
                    if let Some(bound) = self.extract_upper_bound(part, index_var) {
                        return Some(bound);
                    }
                }
                None
            }

            // Direct less-than
            Expr::Lt(lhs, rhs) => {
                if let Expr::Ident(name) = lhs.as_ref() {
                    if name == index_var {
                        return Some(*rhs.clone());
                    }
                }
                None
            }

            // Binary and
            Expr::Binary(lhs, BinOp::And, rhs) => self
                .extract_upper_bound(lhs, index_var)
                .or_else(|| self.extract_upper_bound(rhs, index_var)),

            _ => None,
        }
    }

    /// Extract just the upper bound from a comparison
    fn extract_upper_bound(&self, expr: &Expr, index_var: &str) -> Option<Expr> {
        match expr {
            Expr::Lt(lhs, rhs) | Expr::Le(lhs, rhs) => {
                if let Expr::Ident(name) = lhs.as_ref() {
                    if name == index_var {
                        return Some(*rhs.clone());
                    }
                }
                None
            }
            Expr::Gt(lhs, rhs) | Expr::Ge(lhs, rhs) => {
                if let Expr::Ident(name) = rhs.as_ref() {
                    if name == index_var {
                        return Some(*lhs.clone());
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Extract (seq_var, element_expr) from seq[i] == expr pattern
    fn extract_indexed_equality(&self, expr: &Expr, index_var: &str) -> Option<(String, Expr)> {
        let Expr::Eq(lhs, rhs) = expr else {
            return None;
        };

        // Check lhs = seq[i]
        if let Expr::Index(base, idx) = lhs.as_ref() {
            if let Expr::Ident(seq_name) = base.as_ref() {
                if let Expr::Ident(idx_name) = idx.as_ref() {
                    if idx_name == index_var {
                        return Some((seq_name.clone(), *rhs.clone()));
                    }
                }
            }
        }

        // Check rhs = seq[i]
        if let Expr::Index(base, idx) = rhs.as_ref() {
            if let Expr::Ident(seq_name) = base.as_ref() {
                if let Expr::Ident(idx_name) = idx.as_ref() {
                    if idx_name == index_var {
                        return Some((seq_name.clone(), *lhs.clone()));
                    }
                }
            }
        }

        None
    }

    /// Extract membership equivalence: (map_var, domain_pred) from k in map <==> pred
    fn extract_membership_equiv(
        &self,
        lhs: &Expr,
        rhs: &Expr,
        key_var: &str,
    ) -> Option<(String, Expr)> {
        // Check lhs = k in map
        if let Some(map_var) = self.extract_contains_pattern(lhs, key_var) {
            return Some((map_var, rhs.clone()));
        }

        // Check rhs = k in map
        if let Some(map_var) = self.extract_contains_pattern(rhs, key_var) {
            return Some((map_var, lhs.clone()));
        }

        None
    }

    /// Extract set membership equivalence
    fn extract_set_membership_equiv(
        &self,
        lhs: &Expr,
        rhs: &Expr,
        elem_var: &str,
    ) -> Option<(String, Expr)> {
        // Same logic as map membership
        self.extract_membership_equiv(lhs, rhs, elem_var)
    }

    /// Extract map value pattern: k in map ==> map[k] == value
    fn extract_map_value_pattern(
        &self,
        premise: &Expr,
        conclusion: &Expr,
        key_var: &str,
    ) -> Option<(String, Expr)> {
        // Premise should be: k in map
        let map_var = self.extract_contains_pattern(premise, key_var)?;

        // Conclusion should be: map[k] == value
        let Expr::Eq(lhs, rhs) = conclusion else {
            return None;
        };

        // Check lhs = map[k]
        if let Expr::Index(base, idx) = lhs.as_ref() {
            if let Expr::Ident(base_name) = base.as_ref() {
                if base_name == &map_var {
                    if let Expr::Ident(idx_name) = idx.as_ref() {
                        if idx_name == key_var {
                            return Some((map_var, *rhs.clone()));
                        }
                    }
                }
            }
        }

        // Check rhs = map[k]
        if let Expr::Index(base, idx) = rhs.as_ref() {
            if let Expr::Ident(base_name) = base.as_ref() {
                if base_name == &map_var {
                    if let Expr::Ident(idx_name) = idx.as_ref() {
                        if idx_name == key_var {
                            return Some((map_var, *lhs.clone()));
                        }
                    }
                }
            }
        }

        None
    }

    /// Extract container name from "var in container" pattern
    fn extract_contains_pattern(&self, expr: &Expr, var_name: &str) -> Option<String> {
        // Pattern: var.contains(container) or container.contains(var)
        // or method call: set.contains(var)
        if let Expr::MethodCall {
            receiver,
            method,
            args,
        } = expr
        {
            if method == "contains" && args.len() == 1 {
                // container.contains(var)
                if let Expr::Ident(arg_name) = &args[0] {
                    if arg_name == var_name {
                        if let Expr::Ident(container_name) = receiver.as_ref() {
                            return Some(container_name.clone());
                        }
                    }
                }
            }
        }

        // Pattern: Binary operation (var in set might be represented differently)
        // This depends on how the parser represents membership

        None
    }

    /// Generate a hint for unrecognized patterns
    fn generate_hint(&self, expr: &Expr) -> String {
        match expr {
            Expr::Forall { .. } => "Consider restructuring the forall to match a known pattern:\n\
                 - Sequence: forall |i| 0 <= i < len ==> seq[i] == expr\n\
                 - Map domain: forall |k| k in map <==> pred\n\
                 - Map value: forall |k| k in map ==> map[k] == expr"
                .to_string(),
            Expr::Exists { .. } => {
                "Exists patterns typically need manual implementation. Consider:\n\
                 - Using choose! macro for witnessing\n\
                 - Restructuring as a find/filter operation"
                    .to_string()
            }
            _ => "This pattern may need manual implementation".to_string(),
        }
    }
}

/// Match results for reporting
#[derive(Debug)]
pub struct MatchResult {
    /// The matched template (or Unrecognized)
    pub template: QuantifierTemplate,
    /// Confidence level (0.0 - 1.0)
    pub confidence: f64,
    /// Any warnings about the match
    pub warnings: Vec<String>,
}

/// Match an expression against all known templates
pub fn match_expression(expr: &Expr, output_vars: &[String]) -> MatchResult {
    let matcher = TemplateMatcher::new(output_vars.to_vec());
    let template = matcher.match_template(expr);

    let confidence = match &template {
        QuantifierTemplate::SeqComprehension { .. } => 0.95,
        QuantifierTemplate::MapComprehension { .. } => 0.90,
        QuantifierTemplate::MapDomain { .. } => 0.85,
        QuantifierTemplate::MapValue { .. } => 0.85,
        QuantifierTemplate::SetComprehension { .. } => 0.85,
        QuantifierTemplate::StructConstruction { .. } => 0.90,
        QuantifierTemplate::SimpleAssignment { .. } => 0.95,
        QuantifierTemplate::Copy { .. } => 1.0,
        QuantifierTemplate::Unrecognized { .. } => 0.0,
        // QuantifierMatcher-only variants (not produced by TemplateMatcher)
        QuantifierTemplate::MapFilter { .. }
        | QuantifierTemplate::MapPreservation { .. }
        | QuantifierTemplate::MapConditionalValue { .. }
        | QuantifierTemplate::MapDomainBiconditional { .. }
        | QuantifierTemplate::MapExclusion { .. }
        | QuantifierTemplate::MapInclusion { .. }
        | QuantifierTemplate::CollectionCheck { .. } => 0.90,
    };

    MatchResult {
        template,
        confidence,
        warnings: vec![],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Binding, Literal, Path, Pattern};

    #[test]
    fn test_simple_assignment_match() {
        let matcher = TemplateMatcher::new(vec!["output".to_string()]);

        // output == input
        let expr = Expr::Eq(
            Box::new(Expr::Ident("output".to_string())),
            Box::new(Expr::Ident("input".to_string())),
        );

        let template = matcher.match_template(&expr);
        assert!(matches!(template, QuantifierTemplate::Copy { .. }));
    }

    #[test]
    fn test_struct_construction_match() {
        let matcher = TemplateMatcher::new(vec!["s_".to_string()]);

        // s_.field1 == val1 &&& s_.field2 == val2
        let expr = Expr::Conjunction(vec![
            Expr::Eq(
                Box::new(Expr::Field(
                    Box::new(Expr::Ident("s_".to_string())),
                    "field1".to_string(),
                )),
                Box::new(Expr::Ident("val1".to_string())),
            ),
            Expr::Eq(
                Box::new(Expr::Field(
                    Box::new(Expr::Ident("s_".to_string())),
                    "field2".to_string(),
                )),
                Box::new(Expr::Ident("val2".to_string())),
            ),
        ]);

        let template = matcher.match_template(&expr);
        match template {
            QuantifierTemplate::StructConstruction { output_var, fields } => {
                assert_eq!(output_var, "s_");
                assert_eq!(fields.len(), 2);
            }
            _ => panic!("Expected StructConstruction"),
        }
    }

    #[test]
    fn test_seq_comprehension_match() {
        let matcher = TemplateMatcher::new(vec!["seq".to_string()]);

        // forall |i| 0 <= i < len ==> seq[i] == f(i)
        let expr = Expr::Forall {
            vars: vec![Binding {
                pattern: Pattern::Ident("i".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            }],
            triggers: vec![],
            body: Box::new(Expr::Implies(
                Box::new(Expr::Lt(
                    Box::new(Expr::Ident("i".to_string())),
                    Box::new(Expr::Ident("len".to_string())),
                )),
                Box::new(Expr::Eq(
                    Box::new(Expr::Index(
                        Box::new(Expr::Ident("seq".to_string())),
                        Box::new(Expr::Ident("i".to_string())),
                    )),
                    Box::new(Expr::Call {
                        func: Path::single("f".to_string()),
                        args: vec![Expr::Ident("i".to_string())],
                    }),
                )),
            )),
        };

        let template = matcher.match_template(&expr);
        match template {
            QuantifierTemplate::SeqComprehension {
                index_var, seq_var, ..
            } => {
                assert_eq!(index_var, "i");
                assert_eq!(seq_var, Some("seq".to_string()));
            }
            _ => panic!("Expected SeqComprehension, got {:?}", template),
        }
    }

    #[test]
    fn test_unrecognized_pattern() {
        let matcher = TemplateMatcher::new(vec!["output".to_string()]);

        // Some complex expression that doesn't match
        let expr = Expr::Exists {
            vars: vec![Binding {
                pattern: Pattern::Ident("x".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            }],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };

        let template = matcher.match_template(&expr);
        assert!(matches!(template, QuantifierTemplate::Unrecognized { .. }));
    }

    #[test]
    fn test_match_expression_confidence() {
        let result = match_expression(
            &Expr::Eq(
                Box::new(Expr::Ident("out".to_string())),
                Box::new(Expr::Ident("in".to_string())),
            ),
            &["out".to_string()],
        );

        assert!(result.confidence >= 0.9);
    }

    // --- Copy / SimpleAssignment distinction ---

    #[test]
    fn test_copy_template_fields() {
        let matcher = TemplateMatcher::new(vec!["result".to_string()]);
        let expr = Expr::Eq(
            Box::new(Expr::Ident("result".to_string())),
            Box::new(Expr::Ident("src".to_string())),
        );
        match matcher.match_template(&expr) {
            QuantifierTemplate::Copy {
                output_var,
                input_var,
            } => {
                assert_eq!(output_var, "result");
                assert_eq!(input_var, "src");
            }
            other => panic!("Expected Copy, got {:?}", other),
        }
    }

    #[test]
    fn test_simple_assignment_non_ident() {
        let matcher = TemplateMatcher::new(vec!["output".to_string()]);
        // output == 42 — value is a literal, not an ident, so it's SimpleAssignment
        let expr = Expr::Eq(
            Box::new(Expr::Ident("output".to_string())),
            Box::new(Expr::Literal(Literal::Int(42))),
        );
        match matcher.match_template(&expr) {
            QuantifierTemplate::SimpleAssignment { output_var, .. } => {
                assert_eq!(output_var, "output");
            }
            other => panic!("Expected SimpleAssignment, got {:?}", other),
        }
    }

    #[test]
    fn test_copy_reversed() {
        // input == output (reversed order)
        let matcher = TemplateMatcher::new(vec!["output".to_string()]);
        let expr = Expr::Eq(
            Box::new(Expr::Ident("input".to_string())),
            Box::new(Expr::Ident("output".to_string())),
        );
        match matcher.match_template(&expr) {
            QuantifierTemplate::Copy {
                output_var,
                input_var,
            } => {
                assert_eq!(output_var, "output");
                assert_eq!(input_var, "input");
            }
            other => panic!("Expected Copy (reversed), got {:?}", other),
        }
    }

    // --- StructConstruction tests ---

    #[test]
    fn test_struct_construction_three_fields() {
        let matcher = TemplateMatcher::new(vec!["s_".to_string()]);
        let expr = Expr::Conjunction(vec![
            Expr::Eq(
                Box::new(Expr::Field(Box::new(Expr::Ident("s_".into())), "a".into())),
                Box::new(Expr::Literal(Literal::Int(1))),
            ),
            Expr::Eq(
                Box::new(Expr::Field(Box::new(Expr::Ident("s_".into())), "b".into())),
                Box::new(Expr::Literal(Literal::Int(2))),
            ),
            Expr::Eq(
                Box::new(Expr::Field(Box::new(Expr::Ident("s_".into())), "c".into())),
                Box::new(Expr::Literal(Literal::Int(3))),
            ),
        ]);
        match matcher.match_template(&expr) {
            QuantifierTemplate::StructConstruction { output_var, fields } => {
                assert_eq!(output_var, "s_");
                assert_eq!(fields.len(), 3);
                assert_eq!(fields[0].0, "a");
                assert_eq!(fields[1].0, "b");
                assert_eq!(fields[2].0, "c");
            }
            other => panic!("Expected StructConstruction, got {:?}", other),
        }
    }

    #[test]
    fn test_struct_construction_mixed_outputs_returns_none() {
        // s_.a == 1 &&& t_.b == 2 — different output vars → None
        let matcher = TemplateMatcher::new(vec!["s_".to_string(), "t_".to_string()]);
        let expr = Expr::Conjunction(vec![
            Expr::Eq(
                Box::new(Expr::Field(Box::new(Expr::Ident("s_".into())), "a".into())),
                Box::new(Expr::Literal(Literal::Int(1))),
            ),
            Expr::Eq(
                Box::new(Expr::Field(Box::new(Expr::Ident("t_".into())), "b".into())),
                Box::new(Expr::Literal(Literal::Int(2))),
            ),
        ]);
        // This should return Unrecognized because mixed output vars
        match matcher.match_template(&expr) {
            QuantifierTemplate::Unrecognized { .. } => {}
            other => panic!("Expected Unrecognized for mixed outputs, got {:?}", other),
        }
    }

    // --- SeqComprehension with conjunction range ---

    #[test]
    fn test_seq_comprehension_conjunction_range() {
        let matcher = TemplateMatcher::new(vec!["seq".to_string()]);
        // forall |i| (0 <= i &&& i < n) ==> seq[i] == i
        let expr = Expr::Forall {
            vars: vec![Binding {
                pattern: Pattern::Ident("i".into()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            }],
            triggers: vec![],
            body: Box::new(Expr::Implies(
                Box::new(Expr::Conjunction(vec![
                    Expr::Le(
                        Box::new(Expr::Literal(Literal::Int(0))),
                        Box::new(Expr::Ident("i".into())),
                    ),
                    Expr::Lt(
                        Box::new(Expr::Ident("i".into())),
                        Box::new(Expr::Ident("n".into())),
                    ),
                ])),
                Box::new(Expr::Eq(
                    Box::new(Expr::Index(
                        Box::new(Expr::Ident("seq".into())),
                        Box::new(Expr::Ident("i".into())),
                    )),
                    Box::new(Expr::Ident("i".into())),
                )),
            )),
        };
        match matcher.match_template(&expr) {
            QuantifierTemplate::SeqComprehension {
                index_var, seq_var, ..
            } => {
                assert_eq!(index_var, "i");
                assert_eq!(seq_var, Some("seq".to_string()));
            }
            other => panic!("Expected SeqComprehension, got {:?}", other),
        }
    }

    // --- MapDomain / MapValue / SetComprehension ---

    #[test]
    fn test_map_domain_match() {
        let matcher = TemplateMatcher::new(vec!["m".to_string()]);
        // forall |k| m.contains(k) == pred(k)
        let expr = Expr::Forall {
            vars: vec![Binding {
                pattern: Pattern::Ident("k".into()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            }],
            triggers: vec![],
            body: Box::new(Expr::Eq(
                Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::Ident("m".into())),
                    method: "contains".into(),
                    args: vec![Expr::Ident("k".into())],
                }),
                Box::new(Expr::Call {
                    func: Path::single("pred".into()),
                    args: vec![Expr::Ident("k".into())],
                }),
            )),
        };
        match matcher.match_template(&expr) {
            QuantifierTemplate::MapDomain {
                key_var, map_var, ..
            } => {
                assert_eq!(key_var, "k");
                assert_eq!(map_var, "m");
            }
            other => panic!("Expected MapDomain, got {:?}", other),
        }
    }

    #[test]
    fn test_map_value_match() {
        let matcher = TemplateMatcher::new(vec!["m".to_string()]);
        // forall |k| m.contains(k) ==> m[k] == f(k)
        let expr = Expr::Forall {
            vars: vec![Binding {
                pattern: Pattern::Ident("k".into()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            }],
            triggers: vec![],
            body: Box::new(Expr::Implies(
                Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::Ident("m".into())),
                    method: "contains".into(),
                    args: vec![Expr::Ident("k".into())],
                }),
                Box::new(Expr::Eq(
                    Box::new(Expr::Index(
                        Box::new(Expr::Ident("m".into())),
                        Box::new(Expr::Ident("k".into())),
                    )),
                    Box::new(Expr::Call {
                        func: Path::single("f".into()),
                        args: vec![Expr::Ident("k".into())],
                    }),
                )),
            )),
        };
        match matcher.match_template(&expr) {
            QuantifierTemplate::MapValue {
                key_var, map_var, ..
            } => {
                assert_eq!(key_var, "k");
                assert_eq!(map_var, "m");
            }
            other => panic!("Expected MapValue, got {:?}", other),
        }
    }

    #[test]
    fn test_set_comprehension_matched_as_map_domain() {
        // MapDomain and SetComprehension patterns are structurally identical
        // (both use extract_membership_equiv). Since try_match_map_comprehension
        // runs first in match_template(), this pattern matches as MapDomain.
        let matcher = TemplateMatcher::new(vec!["s".to_string()]);
        // forall |x| s.contains(x) == true
        let expr = Expr::Forall {
            vars: vec![Binding {
                pattern: Pattern::Ident("x".into()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            }],
            triggers: vec![],
            body: Box::new(Expr::Eq(
                Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::Ident("s".into())),
                    method: "contains".into(),
                    args: vec![Expr::Ident("x".into())],
                }),
                Box::new(Expr::Literal(Literal::Bool(true))),
            )),
        };
        match matcher.match_template(&expr) {
            QuantifierTemplate::MapDomain {
                key_var, map_var, ..
            } => {
                assert_eq!(key_var, "x");
                assert_eq!(map_var, "s");
            }
            other => panic!(
                "Expected MapDomain (higher priority than SetComprehension), got {:?}",
                other
            ),
        }
    }

    // --- Confidence levels ---

    #[test]
    fn test_confidence_copy_is_1() {
        let result = match_expression(
            &Expr::Eq(
                Box::new(Expr::Ident("out".into())),
                Box::new(Expr::Ident("inp".into())),
            ),
            &["out".to_string()],
        );
        assert_eq!(result.confidence, 1.0);
    }

    #[test]
    fn test_confidence_unrecognized_is_0() {
        let result = match_expression(
            &Expr::Exists {
                vars: vec![Binding {
                    pattern: Pattern::Ident("x".into()),
                    ty: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                }],
                body: Box::new(Expr::Literal(Literal::Bool(true))),
            },
            &["out".to_string()],
        );
        assert_eq!(result.confidence, 0.0);
    }

    // --- Hint generation ---

    #[test]
    fn test_hint_for_forall() {
        let matcher = TemplateMatcher::new(vec!["out".to_string()]);
        let expr = Expr::Forall {
            vars: vec![
                Binding {
                    pattern: Pattern::Ident("a".into()),
                    ty: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                },
                Binding {
                    pattern: Pattern::Ident("b".into()),
                    ty: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                },
            ],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        let hint = matcher.generate_hint(&expr);
        assert!(
            hint.contains("forall"),
            "Hint should mention forall: {}",
            hint
        );
    }

    #[test]
    fn test_hint_for_exists() {
        let matcher = TemplateMatcher::new(vec![]);
        let expr = Expr::Exists {
            vars: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        let hint = matcher.generate_hint(&expr);
        assert!(
            hint.contains("Exists"),
            "Hint should mention Exists: {}",
            hint
        );
    }

    #[test]
    fn test_hint_for_other() {
        let matcher = TemplateMatcher::new(vec![]);
        let hint = matcher.generate_hint(&Expr::Literal(Literal::Int(42)));
        assert!(
            hint.contains("manual"),
            "Hint should suggest manual impl: {}",
            hint
        );
    }
}

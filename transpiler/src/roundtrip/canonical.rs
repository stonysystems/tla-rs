//! Canonical form conversion for TLA+ AST.
//!
//! Converts TLA+ AST elements to canonical forms for comparison.
//! This handles normalization of:
//! - Identifier prefixes (L/C prefix stripping)
//! - Binary operator forms (a != b → ~(a = b))
//! - Record field ordering (alphabetical)
//! - Commutative operator ordering

use crate::tla::ast::{
    TlaBinOp, TlaConstantDecl, TlaExpr, TlaModule, TlaOperator, TlaParam, TlaQuantBound, TlaUnaryOp,
};

#[cfg(test)]
use crate::tla::ast::TlaNumber;

/// Configuration for canonical form conversion.
#[derive(Debug, Clone)]
pub struct CanonicalConfig {
    /// Prefixes to strip from identifiers (e.g., "L", "C")
    pub strip_prefixes: Vec<String>,
    /// Whether to normalize != to ~(= )
    pub normalize_neq: bool,
    /// Whether to sort record fields
    pub sort_record_fields: bool,
    /// Whether to sort commutative binary operators
    pub sort_commutative: bool,
}

impl Default for CanonicalConfig {
    fn default() -> Self {
        Self {
            strip_prefixes: vec!["L".to_string(), "C".to_string()],
            normalize_neq: true,
            sort_record_fields: true,
            sort_commutative: false, // Can change semantics for non-associative ops
        }
    }
}

/// Canonicalize a TLA+ expression.
pub fn canonicalize_tla_expr(expr: &TlaExpr, config: &CanonicalConfig) -> TlaExpr {
    let canonicalizer = Canonicalizer::new(config.clone());
    canonicalizer.canonicalize_expr(expr)
}

/// Canonicalize a TLA+ module.
pub fn canonicalize_tla_module(module: &TlaModule, config: &CanonicalConfig) -> TlaModule {
    let canonicalizer = Canonicalizer::new(config.clone());
    canonicalizer.canonicalize_module(module)
}

/// Internal canonicalizer implementation.
struct Canonicalizer {
    config: CanonicalConfig,
}

impl Canonicalizer {
    fn new(config: CanonicalConfig) -> Self {
        Self { config }
    }

    /// Canonicalize an entire module.
    fn canonicalize_module(&self, module: &TlaModule) -> TlaModule {
        TlaModule {
            name: self.strip_prefix(&module.name),
            extends: module.extends.clone(),
            constants: module
                .constants
                .iter()
                .map(|c| TlaConstantDecl {
                    name: self.strip_prefix(&c.name),
                    type_constraint: c
                        .type_constraint
                        .as_ref()
                        .map(|tc| self.canonicalize_expr(tc)),
                })
                .collect(),
            variables: module
                .variables
                .iter()
                .map(|v| self.strip_prefix(v))
                .collect(),
            operators: module
                .operators
                .iter()
                .map(|op| self.canonicalize_operator(op))
                .collect(),
            assumptions: module
                .assumptions
                .iter()
                .map(|a| self.canonicalize_expr(a))
                .collect(),
            theorems: module.theorems.clone(),
            instances: module.instances.clone(),
            span: None,
        }
    }

    /// Canonicalize an operator definition.
    fn canonicalize_operator(&self, op: &TlaOperator) -> TlaOperator {
        TlaOperator {
            name: self.strip_prefix(&op.name),
            params: op
                .params
                .iter()
                .map(|p| TlaParam {
                    name: p.name.clone(), // Don't strip params, they're local
                    arity: p.arity,
                })
                .collect(),
            body: self.canonicalize_expr(&op.body),
            is_local: op.is_local,
            is_recursive: op.is_recursive,
            span: None,
        }
    }

    /// Canonicalize an expression.
    fn canonicalize_expr(&self, expr: &TlaExpr) -> TlaExpr {
        match expr {
            // Identifiers: strip prefixes
            TlaExpr::Ident(name) => TlaExpr::Ident(self.strip_prefix(name)),

            // Prime: canonicalize inner
            TlaExpr::Prime(inner) => TlaExpr::Prime(Box::new(self.canonicalize_expr(inner))),

            // Literals: unchanged
            TlaExpr::Number(n) => TlaExpr::Number(n.clone()),
            TlaExpr::String(s) => TlaExpr::String(s.clone()),
            TlaExpr::Bool(b) => TlaExpr::Bool(*b),

            // Binary operators: handle special cases
            TlaExpr::BinOp { op, left, right } => self.canonicalize_binop(*op, left, right),

            // Unary operators: canonicalize operand
            TlaExpr::UnaryOp { op, operand } => TlaExpr::UnaryOp {
                op: *op,
                operand: Box::new(self.canonicalize_expr(operand)),
            },

            // Operator application
            TlaExpr::OpApply { op, args } => TlaExpr::OpApply {
                op: Box::new(self.canonicalize_expr(op)),
                args: args.iter().map(|a| self.canonicalize_expr(a)).collect(),
            },

            // Function application
            TlaExpr::FnApply { func, arg } => TlaExpr::FnApply {
                func: Box::new(self.canonicalize_expr(func)),
                arg: Box::new(self.canonicalize_expr(arg)),
            },

            // Sets
            TlaExpr::SetEnum(elements) => {
                TlaExpr::SetEnum(elements.iter().map(|e| self.canonicalize_expr(e)).collect())
            }
            TlaExpr::SetFilter { var, set, filter } => TlaExpr::SetFilter {
                var: var.clone(),
                set: Box::new(self.canonicalize_expr(set)),
                filter: Box::new(self.canonicalize_expr(filter)),
            },
            TlaExpr::SetMap { expr, var, set } => TlaExpr::SetMap {
                expr: Box::new(self.canonicalize_expr(expr)),
                var: var.clone(),
                set: Box::new(self.canonicalize_expr(set)),
            },
            TlaExpr::Lambda { params, body } => TlaExpr::Lambda {
                params: params.clone(),
                body: Box::new(self.canonicalize_expr(body)),
            },
            TlaExpr::SetMapMulti { expr, bindings } => TlaExpr::SetMapMulti {
                expr: Box::new(self.canonicalize_expr(expr)),
                bindings: bindings
                    .iter()
                    .map(|b| TlaQuantBound {
                        var: b.var.clone(),
                        set: b.set.as_ref().map(|s| self.canonicalize_expr(s)),
                    })
                    .collect(),
            },

            // Functions
            TlaExpr::FnConstruct { var, domain, body } => TlaExpr::FnConstruct {
                var: var.clone(),
                domain: Box::new(self.canonicalize_expr(domain)),
                body: Box::new(self.canonicalize_expr(body)),
            },
            TlaExpr::FnExcept { func, updates } => TlaExpr::FnExcept {
                func: Box::new(self.canonicalize_expr(func)),
                updates: updates
                    .iter()
                    .map(|u| crate::tla::ast::TlaExceptUpdate {
                        path: u.path.clone(),
                        value: self.canonicalize_expr(&u.value),
                    })
                    .collect(),
            },
            TlaExpr::FnSet { domain, range } => TlaExpr::FnSet {
                domain: Box::new(self.canonicalize_expr(domain)),
                range: Box::new(self.canonicalize_expr(range)),
            },

            // Records: optionally sort fields
            TlaExpr::RecordSet(fields) => {
                let mut canonical_fields: Vec<(String, TlaExpr)> = fields
                    .iter()
                    .map(|(name, value)| (name.clone(), self.canonicalize_expr(value)))
                    .collect();
                if self.config.sort_record_fields {
                    canonical_fields.sort_by(|a, b| a.0.cmp(&b.0));
                }
                TlaExpr::RecordSet(canonical_fields)
            }

            TlaExpr::Record(fields) => {
                let mut canonical_fields: Vec<(String, TlaExpr)> = fields
                    .iter()
                    .map(|(name, value)| (name.clone(), self.canonicalize_expr(value)))
                    .collect();
                if self.config.sort_record_fields {
                    canonical_fields.sort_by(|a, b| a.0.cmp(&b.0));
                }
                TlaExpr::Record(canonical_fields)
            }
            TlaExpr::RecordAccess { record, field } => TlaExpr::RecordAccess {
                record: Box::new(self.canonicalize_expr(record)),
                field: field.clone(),
            },

            // Tuples
            TlaExpr::Tuple(elements) => {
                TlaExpr::Tuple(elements.iter().map(|e| self.canonicalize_expr(e)).collect())
            }

            // Quantifiers
            TlaExpr::Forall { vars, body } => TlaExpr::Forall {
                vars: vars
                    .iter()
                    .map(|v| self.canonicalize_quant_bound(v))
                    .collect(),
                body: Box::new(self.canonicalize_expr(body)),
            },
            TlaExpr::Exists { vars, body } => TlaExpr::Exists {
                vars: vars
                    .iter()
                    .map(|v| self.canonicalize_quant_bound(v))
                    .collect(),
                body: Box::new(self.canonicalize_expr(body)),
            },
            TlaExpr::Choose { var, set, body } => TlaExpr::Choose {
                var: var.clone(),
                set: set.as_ref().map(|s| Box::new(self.canonicalize_expr(s))),
                body: Box::new(self.canonicalize_expr(body)),
            },

            // Control flow
            TlaExpr::IfThenElse {
                cond,
                then_expr,
                else_expr,
            } => TlaExpr::IfThenElse {
                cond: Box::new(self.canonicalize_expr(cond)),
                then_expr: Box::new(self.canonicalize_expr(then_expr)),
                else_expr: Box::new(self.canonicalize_expr(else_expr)),
            },
            TlaExpr::Case { arms, other } => TlaExpr::Case {
                arms: arms
                    .iter()
                    .map(|(c, e)| (self.canonicalize_expr(c), self.canonicalize_expr(e)))
                    .collect(),
                other: other.as_ref().map(|o| Box::new(self.canonicalize_expr(o))),
            },
            TlaExpr::LetIn { defs, body } => TlaExpr::LetIn {
                defs: defs.iter().map(|d| self.canonicalize_operator(d)).collect(),
                body: Box::new(self.canonicalize_expr(body)),
            },

            // Action operators
            TlaExpr::Unchanged(vars) => {
                TlaExpr::Unchanged(vars.iter().map(|v| self.canonicalize_expr(v)).collect())
            }
            TlaExpr::Enabled(action) => TlaExpr::Enabled(Box::new(self.canonicalize_expr(action))),

            // Temporal operators
            TlaExpr::Always(inner) => TlaExpr::Always(Box::new(self.canonicalize_expr(inner))),
            TlaExpr::Eventually(inner) => {
                TlaExpr::Eventually(Box::new(self.canonicalize_expr(inner)))
            }
            TlaExpr::LeadsTo { left, right } => TlaExpr::LeadsTo {
                left: Box::new(self.canonicalize_expr(left)),
                right: Box::new(self.canonicalize_expr(right)),
            },
            TlaExpr::WeakFairness { vars, action } => TlaExpr::WeakFairness {
                vars: Box::new(self.canonicalize_expr(vars)),
                action: Box::new(self.canonicalize_expr(action)),
            },
            TlaExpr::StrongFairness { vars, action } => TlaExpr::StrongFairness {
                vars: Box::new(self.canonicalize_expr(vars)),
                action: Box::new(self.canonicalize_expr(action)),
            },
        }
    }

    /// Canonicalize a binary operation.
    fn canonicalize_binop(&self, op: TlaBinOp, left: &TlaExpr, right: &TlaExpr) -> TlaExpr {
        let left_canon = self.canonicalize_expr(left);
        let right_canon = self.canonicalize_expr(right);

        // Normalize != to ~(=)
        if self.config.normalize_neq && op == TlaBinOp::Neq {
            return TlaExpr::UnaryOp {
                op: TlaUnaryOp::Not,
                operand: Box::new(TlaExpr::BinOp {
                    op: TlaBinOp::Eq,
                    left: Box::new(left_canon),
                    right: Box::new(right_canon),
                }),
            };
        }

        TlaExpr::BinOp {
            op,
            left: Box::new(left_canon),
            right: Box::new(right_canon),
        }
    }

    /// Canonicalize a quantifier bound.
    fn canonicalize_quant_bound(&self, bound: &TlaQuantBound) -> TlaQuantBound {
        TlaQuantBound {
            var: bound.var.clone(),
            set: bound.set.as_ref().map(|s| self.canonicalize_expr(s)),
        }
    }

    /// Strip known prefixes from an identifier.
    fn strip_prefix(&self, name: &str) -> String {
        for prefix in &self.config.strip_prefixes {
            if name.starts_with(prefix) {
                let rest = &name[prefix.len()..];
                // Only strip if followed by uppercase (to avoid stripping from words like "Length")
                if rest.chars().next().is_some_and(|c| c.is_uppercase()) {
                    return rest.to_string();
                }
            }
        }
        name.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strip_prefix() {
        let config = CanonicalConfig::default();
        let canon = Canonicalizer::new(config);

        assert_eq!(canon.strip_prefix("LReplica"), "Replica");
        assert_eq!(canon.strip_prefix("CState"), "State");
        assert_eq!(canon.strip_prefix("Length"), "Length"); // Not stripped
        assert_eq!(canon.strip_prefix("lowercase"), "lowercase"); // Not stripped
        assert_eq!(canon.strip_prefix("LearnerTuple"), "LearnerTuple"); // Not stripped (earner...)
    }

    #[test]
    fn test_canonicalize_ident() {
        let config = CanonicalConfig::default();
        let expr = TlaExpr::Ident("LInit".to_string());
        let result = canonicalize_tla_expr(&expr, &config);
        assert_eq!(result, TlaExpr::Ident("Init".to_string()));
    }

    #[test]
    fn test_canonicalize_neq() {
        let config = CanonicalConfig::default();
        let expr = TlaExpr::BinOp {
            op: TlaBinOp::Neq,
            left: Box::new(TlaExpr::Ident("x".to_string())),
            right: Box::new(TlaExpr::Ident("y".to_string())),
        };
        let result = canonicalize_tla_expr(&expr, &config);

        // Should become ~(x = y)
        match result {
            TlaExpr::UnaryOp {
                op: TlaUnaryOp::Not,
                operand,
            } => match *operand {
                TlaExpr::BinOp {
                    op: TlaBinOp::Eq, ..
                } => {}
                _ => panic!("Expected BinOp Eq"),
            },
            _ => panic!("Expected UnaryOp Not"),
        }
    }

    #[test]
    fn test_canonicalize_record_sorting() {
        let config = CanonicalConfig::default();
        let expr = TlaExpr::Record(vec![
            (
                "z".to_string(),
                TlaExpr::Number(TlaNumber::Decimal("3".to_string())),
            ),
            (
                "a".to_string(),
                TlaExpr::Number(TlaNumber::Decimal("1".to_string())),
            ),
            (
                "m".to_string(),
                TlaExpr::Number(TlaNumber::Decimal("2".to_string())),
            ),
        ]);
        let result = canonicalize_tla_expr(&expr, &config);

        match result {
            TlaExpr::Record(fields) => {
                assert_eq!(fields[0].0, "a");
                assert_eq!(fields[1].0, "m");
                assert_eq!(fields[2].0, "z");
            }
            _ => panic!("Expected Record"),
        }
    }

    #[test]
    fn test_canonicalize_module() {
        let module = TlaModule {
            name: "LTest".to_string(),
            extends: vec!["Integers".to_string()],
            constants: vec![TlaConstantDecl {
                name: "LN".to_string(),
                type_constraint: None,
            }],
            variables: vec!["LState".to_string()],
            operators: vec![TlaOperator {
                name: "LInit".to_string(),
                params: vec![],
                body: TlaExpr::Bool(true),
                is_local: false,
                is_recursive: false,
                span: None,
            }],
            assumptions: vec![],
            theorems: vec![],
            instances: vec![],
            span: None,
        };

        let config = CanonicalConfig::default();
        let result = canonicalize_tla_module(&module, &config);

        assert_eq!(result.name, "Test");
        assert_eq!(result.constants[0].name, "N");
        assert_eq!(result.variables[0], "State");
        assert_eq!(result.operators[0].name, "Init");
    }
}

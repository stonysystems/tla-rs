//! AST comparison utilities for round-trip testing.
//!
//! Provides structural comparison of TLA+ AST elements with meaningful
//! difference reporting.

use crate::tla::ast::{TlaExpr, TlaModule, TlaNumber, TlaOperator, TlaQuantBound};

/// Result of comparing two AST elements.
#[derive(Debug, Clone)]
pub struct CompareResult {
    /// Whether the elements are equivalent
    pub equivalent: bool,
    /// List of differences found
    pub differences: Vec<Difference>,
}

impl CompareResult {
    /// Create a successful comparison result (no differences).
    pub fn equal() -> Self {
        Self {
            equivalent: true,
            differences: vec![],
        }
    }

    /// Create a failed comparison result with a single difference.
    pub fn diff(difference: Difference) -> Self {
        Self {
            equivalent: false,
            differences: vec![difference],
        }
    }

    /// Merge two comparison results.
    pub fn merge(mut self, other: CompareResult) -> Self {
        if !other.equivalent {
            self.equivalent = false;
        }
        self.differences.extend(other.differences);
        self
    }

    /// Add a path prefix to all differences.
    pub fn with_path(mut self, prefix: &str) -> Self {
        for diff in &mut self.differences {
            diff.path = format!("{}.{}", prefix, diff.path);
        }
        self
    }
}

/// A single difference between two AST elements.
#[derive(Debug, Clone)]
pub struct Difference {
    /// Path to the differing element (e.g., "body.left.operand")
    pub path: String,
    /// Description of the difference
    pub description: String,
    /// Expected value (from first AST)
    pub expected: String,
    /// Actual value (from second AST)
    pub actual: String,
}

impl Difference {
    /// Create a new difference.
    pub fn new(
        path: impl Into<String>,
        description: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self {
            path: path.into(),
            description: description.into(),
            expected: expected.into(),
            actual: actual.into(),
        }
    }
}

impl std::fmt::Display for Difference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "at {}: {} (expected: {}, actual: {})",
            self.path, self.description, self.expected, self.actual
        )
    }
}

/// Compare two TLA+ expressions for structural equivalence.
pub fn compare_tla_expr(a: &TlaExpr, b: &TlaExpr) -> CompareResult {
    ExprComparer::new().compare(a, b)
}

/// Compare two TLA+ modules for structural equivalence.
pub fn compare_tla_modules(a: &TlaModule, b: &TlaModule) -> CompareResult {
    ModuleComparer::new().compare(a, b)
}

/// Expression comparer.
struct ExprComparer;

impl ExprComparer {
    fn new() -> Self {
        Self
    }

    fn compare(&self, a: &TlaExpr, b: &TlaExpr) -> CompareResult {
        match (a, b) {
            (TlaExpr::Ident(name_a), TlaExpr::Ident(name_b)) => {
                if name_a == name_b {
                    CompareResult::equal()
                } else {
                    CompareResult::diff(Difference::new(
                        "ident",
                        "identifier mismatch",
                        name_a,
                        name_b,
                    ))
                }
            }

            (TlaExpr::Prime(inner_a), TlaExpr::Prime(inner_b)) => {
                self.compare(inner_a, inner_b).with_path("prime")
            }

            (TlaExpr::Number(num_a), TlaExpr::Number(num_b)) => self.compare_numbers(num_a, num_b),

            (TlaExpr::String(s_a), TlaExpr::String(s_b)) => {
                if s_a == s_b {
                    CompareResult::equal()
                } else {
                    CompareResult::diff(Difference::new("string", "string mismatch", s_a, s_b))
                }
            }

            (TlaExpr::Bool(b_a), TlaExpr::Bool(b_b)) => {
                if b_a == b_b {
                    CompareResult::equal()
                } else {
                    CompareResult::diff(Difference::new(
                        "bool",
                        "boolean mismatch",
                        b_a.to_string(),
                        b_b.to_string(),
                    ))
                }
            }

            (
                TlaExpr::BinOp {
                    op: op_a,
                    left: left_a,
                    right: right_a,
                },
                TlaExpr::BinOp {
                    op: op_b,
                    left: left_b,
                    right: right_b,
                },
            ) => {
                if op_a != op_b {
                    return CompareResult::diff(Difference::new(
                        "binop",
                        "operator mismatch",
                        format!("{:?}", op_a),
                        format!("{:?}", op_b),
                    ));
                }
                self.compare(left_a, left_b)
                    .with_path("left")
                    .merge(self.compare(right_a, right_b).with_path("right"))
            }

            (
                TlaExpr::UnaryOp {
                    op: op_a,
                    operand: operand_a,
                },
                TlaExpr::UnaryOp {
                    op: op_b,
                    operand: operand_b,
                },
            ) => {
                if op_a != op_b {
                    return CompareResult::diff(Difference::new(
                        "unaryop",
                        "operator mismatch",
                        format!("{:?}", op_a),
                        format!("{:?}", op_b),
                    ));
                }
                self.compare(operand_a, operand_b).with_path("operand")
            }

            (
                TlaExpr::OpApply {
                    op: op_a,
                    args: args_a,
                },
                TlaExpr::OpApply {
                    op: op_b,
                    args: args_b,
                },
            ) => {
                let mut result = self.compare(op_a, op_b).with_path("op");
                result = result.merge(self.compare_lists(args_a, args_b, "args"));
                result
            }

            (
                TlaExpr::FnApply {
                    func: func_a,
                    arg: arg_a,
                },
                TlaExpr::FnApply {
                    func: func_b,
                    arg: arg_b,
                },
            ) => self
                .compare(func_a, func_b)
                .with_path("func")
                .merge(self.compare(arg_a, arg_b).with_path("arg")),

            (TlaExpr::SetEnum(elems_a), TlaExpr::SetEnum(elems_b)) => {
                self.compare_lists(elems_a, elems_b, "elements")
            }

            (
                TlaExpr::SetFilter {
                    var: var_a,
                    set: set_a,
                    filter: filter_a,
                },
                TlaExpr::SetFilter {
                    var: var_b,
                    set: set_b,
                    filter: filter_b,
                },
            ) => {
                if var_a != var_b {
                    return CompareResult::diff(Difference::new(
                        "var",
                        "variable mismatch",
                        var_a,
                        var_b,
                    ));
                }
                self.compare(set_a, set_b)
                    .with_path("set")
                    .merge(self.compare(filter_a, filter_b).with_path("filter"))
            }

            (
                TlaExpr::SetMap {
                    expr: expr_a,
                    var: var_a,
                    set: set_a,
                },
                TlaExpr::SetMap {
                    expr: expr_b,
                    var: var_b,
                    set: set_b,
                },
            ) => {
                if var_a != var_b {
                    return CompareResult::diff(Difference::new(
                        "var",
                        "variable mismatch",
                        var_a,
                        var_b,
                    ));
                }
                self.compare(expr_a, expr_b)
                    .with_path("expr")
                    .merge(self.compare(set_a, set_b).with_path("set"))
            }

            (
                TlaExpr::FnConstruct {
                    var: var_a,
                    domain: domain_a,
                    body: body_a,
                },
                TlaExpr::FnConstruct {
                    var: var_b,
                    domain: domain_b,
                    body: body_b,
                },
            ) => {
                if var_a != var_b {
                    return CompareResult::diff(Difference::new(
                        "var",
                        "variable mismatch",
                        var_a,
                        var_b,
                    ));
                }
                self.compare(domain_a, domain_b)
                    .with_path("domain")
                    .merge(self.compare(body_a, body_b).with_path("body"))
            }

            (TlaExpr::Record(fields_a), TlaExpr::Record(fields_b)) => {
                self.compare_record_fields(fields_a, fields_b)
            }

            (
                TlaExpr::RecordAccess {
                    record: record_a,
                    field: field_a,
                },
                TlaExpr::RecordAccess {
                    record: record_b,
                    field: field_b,
                },
            ) => {
                if field_a != field_b {
                    return CompareResult::diff(Difference::new(
                        "field",
                        "field mismatch",
                        field_a,
                        field_b,
                    ));
                }
                self.compare(record_a, record_b).with_path("record")
            }

            (TlaExpr::Tuple(elems_a), TlaExpr::Tuple(elems_b)) => {
                self.compare_lists(elems_a, elems_b, "elements")
            }

            (
                TlaExpr::Forall {
                    vars: vars_a,
                    body: body_a,
                },
                TlaExpr::Forall {
                    vars: vars_b,
                    body: body_b,
                },
            ) => self
                .compare_quant_bounds(vars_a, vars_b)
                .merge(self.compare(body_a, body_b).with_path("body")),

            (
                TlaExpr::Exists {
                    vars: vars_a,
                    body: body_a,
                },
                TlaExpr::Exists {
                    vars: vars_b,
                    body: body_b,
                },
            ) => self
                .compare_quant_bounds(vars_a, vars_b)
                .merge(self.compare(body_a, body_b).with_path("body")),

            (
                TlaExpr::Choose {
                    var: var_a,
                    set: set_a,
                    body: body_a,
                },
                TlaExpr::Choose {
                    var: var_b,
                    set: set_b,
                    body: body_b,
                },
            ) => {
                if var_a != var_b {
                    return CompareResult::diff(Difference::new(
                        "var",
                        "variable mismatch",
                        var_a,
                        var_b,
                    ));
                }
                let mut result = CompareResult::equal();
                match (set_a, set_b) {
                    (Some(s_a), Some(s_b)) => {
                        result = result.merge(self.compare(s_a, s_b).with_path("set"));
                    }
                    (None, None) => {}
                    _ => {
                        return CompareResult::diff(Difference::new(
                            "set",
                            "set presence mismatch",
                            set_a.is_some().to_string(),
                            set_b.is_some().to_string(),
                        ));
                    }
                }
                result.merge(self.compare(body_a, body_b).with_path("body"))
            }

            (
                TlaExpr::IfThenElse {
                    cond: cond_a,
                    then_expr: then_a,
                    else_expr: else_a,
                },
                TlaExpr::IfThenElse {
                    cond: cond_b,
                    then_expr: then_b,
                    else_expr: else_b,
                },
            ) => self
                .compare(cond_a, cond_b)
                .with_path("cond")
                .merge(self.compare(then_a, then_b).with_path("then"))
                .merge(self.compare(else_a, else_b).with_path("else")),

            (TlaExpr::Unchanged(vars_a), TlaExpr::Unchanged(vars_b)) => {
                self.compare_lists(vars_a, vars_b, "vars")
            }

            (TlaExpr::Always(inner_a), TlaExpr::Always(inner_b)) => {
                self.compare(inner_a, inner_b).with_path("always")
            }

            (TlaExpr::Eventually(inner_a), TlaExpr::Eventually(inner_b)) => {
                self.compare(inner_a, inner_b).with_path("eventually")
            }

            // Type mismatch
            _ => CompareResult::diff(Difference::new(
                "type",
                "expression type mismatch",
                format!("{:?}", std::mem::discriminant(a)),
                format!("{:?}", std::mem::discriminant(b)),
            )),
        }
    }

    fn compare_numbers(&self, a: &TlaNumber, b: &TlaNumber) -> CompareResult {
        // Compare numeric value, not representation
        let val_a = match a {
            TlaNumber::Decimal(s) => s.clone(),
            TlaNumber::Binary(s) => s.clone(),
            TlaNumber::Octal(s) => s.clone(),
            TlaNumber::Hex(s) => s.clone(),
        };
        let val_b = match b {
            TlaNumber::Decimal(s) => s.clone(),
            TlaNumber::Binary(s) => s.clone(),
            TlaNumber::Octal(s) => s.clone(),
            TlaNumber::Hex(s) => s.clone(),
        };

        if val_a == val_b {
            CompareResult::equal()
        } else {
            CompareResult::diff(Difference::new("number", "number mismatch", val_a, val_b))
        }
    }

    fn compare_lists(&self, a: &[TlaExpr], b: &[TlaExpr], name: &str) -> CompareResult {
        if a.len() != b.len() {
            return CompareResult::diff(Difference::new(
                name,
                "list length mismatch",
                a.len().to_string(),
                b.len().to_string(),
            ));
        }

        let mut result = CompareResult::equal();
        for (i, (elem_a, elem_b)) in a.iter().zip(b.iter()).enumerate() {
            result = result.merge(
                self.compare(elem_a, elem_b)
                    .with_path(&format!("{}[{}]", name, i)),
            );
        }
        result
    }

    fn compare_record_fields(
        &self,
        a: &[(String, TlaExpr)],
        b: &[(String, TlaExpr)],
    ) -> CompareResult {
        if a.len() != b.len() {
            return CompareResult::diff(Difference::new(
                "fields",
                "field count mismatch",
                a.len().to_string(),
                b.len().to_string(),
            ));
        }

        let mut result = CompareResult::equal();
        for (i, ((name_a, val_a), (name_b, val_b))) in a.iter().zip(b.iter()).enumerate() {
            if name_a != name_b {
                result = result.merge(CompareResult::diff(Difference::new(
                    format!("field[{}]", i),
                    "field name mismatch",
                    name_a,
                    name_b,
                )));
            }
            result = result.merge(
                self.compare(val_a, val_b)
                    .with_path(&format!("field[{}].value", i)),
            );
        }
        result
    }

    fn compare_quant_bounds(&self, a: &[TlaQuantBound], b: &[TlaQuantBound]) -> CompareResult {
        if a.len() != b.len() {
            return CompareResult::diff(Difference::new(
                "bounds",
                "bound count mismatch",
                a.len().to_string(),
                b.len().to_string(),
            ));
        }

        let mut result = CompareResult::equal();
        for (i, (bound_a, bound_b)) in a.iter().zip(b.iter()).enumerate() {
            if bound_a.var != bound_b.var {
                result = result.merge(CompareResult::diff(Difference::new(
                    format!("bound[{}].var", i),
                    "variable mismatch",
                    &bound_a.var,
                    &bound_b.var,
                )));
            }
            match (&bound_a.set, &bound_b.set) {
                (Some(s_a), Some(s_b)) => {
                    result = result.merge(
                        self.compare(s_a, s_b)
                            .with_path(&format!("bound[{}].set", i)),
                    );
                }
                (None, None) => {}
                _ => {
                    result = result.merge(CompareResult::diff(Difference::new(
                        format!("bound[{}].set", i),
                        "set presence mismatch",
                        bound_a.set.is_some().to_string(),
                        bound_b.set.is_some().to_string(),
                    )));
                }
            }
        }
        result
    }
}

/// Module comparer.
struct ModuleComparer;

impl ModuleComparer {
    fn new() -> Self {
        Self
    }

    fn compare(&self, a: &TlaModule, b: &TlaModule) -> CompareResult {
        let mut result = CompareResult::equal();

        // Compare names
        if a.name != b.name {
            result = result.merge(CompareResult::diff(Difference::new(
                "name",
                "module name mismatch",
                &a.name,
                &b.name,
            )));
        }

        // Compare extends
        if a.extends != b.extends {
            result = result.merge(CompareResult::diff(Difference::new(
                "extends",
                "extends mismatch",
                format!("{:?}", a.extends),
                format!("{:?}", b.extends),
            )));
        }

        // Compare constants
        if a.constants.len() != b.constants.len() {
            result = result.merge(CompareResult::diff(Difference::new(
                "constants",
                "constant count mismatch",
                a.constants.len().to_string(),
                b.constants.len().to_string(),
            )));
        } else {
            for (i, (const_a, const_b)) in a.constants.iter().zip(b.constants.iter()).enumerate() {
                if const_a.name != const_b.name {
                    result = result.merge(CompareResult::diff(Difference::new(
                        format!("constant[{}]", i),
                        "constant name mismatch",
                        &const_a.name,
                        &const_b.name,
                    )));
                }
            }
        }

        // Compare variables
        if a.variables != b.variables {
            result = result.merge(CompareResult::diff(Difference::new(
                "variables",
                "variables mismatch",
                format!("{:?}", a.variables),
                format!("{:?}", b.variables),
            )));
        }

        // Compare operators
        if a.operators.len() != b.operators.len() {
            result = result.merge(CompareResult::diff(Difference::new(
                "operators",
                "operator count mismatch",
                a.operators.len().to_string(),
                b.operators.len().to_string(),
            )));
        } else {
            for (i, (op_a, op_b)) in a.operators.iter().zip(b.operators.iter()).enumerate() {
                result = result.merge(
                    self.compare_operators(op_a, op_b)
                        .with_path(&format!("operator[{}]", i)),
                );
            }
        }

        result
    }

    fn compare_operators(&self, a: &TlaOperator, b: &TlaOperator) -> CompareResult {
        let mut result = CompareResult::equal();

        if a.name != b.name {
            result = result.merge(CompareResult::diff(Difference::new(
                "name",
                "operator name mismatch",
                &a.name,
                &b.name,
            )));
        }

        if a.params.len() != b.params.len() {
            result = result.merge(CompareResult::diff(Difference::new(
                "params",
                "parameter count mismatch",
                a.params.len().to_string(),
                b.params.len().to_string(),
            )));
        }

        // Compare body
        let expr_comparer = ExprComparer::new();
        result = result.merge(expr_comparer.compare(&a.body, &b.body).with_path("body"));

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tla::ast::TlaBinOp;

    #[test]
    fn test_compare_identical_idents() {
        let a = TlaExpr::Ident("x".to_string());
        let b = TlaExpr::Ident("x".to_string());
        let result = compare_tla_expr(&a, &b);
        assert!(result.equivalent);
        assert!(result.differences.is_empty());
    }

    #[test]
    fn test_compare_different_idents() {
        let a = TlaExpr::Ident("x".to_string());
        let b = TlaExpr::Ident("y".to_string());
        let result = compare_tla_expr(&a, &b);
        assert!(!result.equivalent);
        assert_eq!(result.differences.len(), 1);
    }

    #[test]
    fn test_compare_binop() {
        let a = TlaExpr::BinOp {
            op: TlaBinOp::Plus,
            left: Box::new(TlaExpr::Ident("x".to_string())),
            right: Box::new(TlaExpr::Number(TlaNumber::Decimal("1".to_string()))),
        };
        let b = TlaExpr::BinOp {
            op: TlaBinOp::Plus,
            left: Box::new(TlaExpr::Ident("x".to_string())),
            right: Box::new(TlaExpr::Number(TlaNumber::Decimal("1".to_string()))),
        };
        let result = compare_tla_expr(&a, &b);
        assert!(result.equivalent);
    }

    #[test]
    fn test_compare_binop_mismatch() {
        let a = TlaExpr::BinOp {
            op: TlaBinOp::Plus,
            left: Box::new(TlaExpr::Ident("x".to_string())),
            right: Box::new(TlaExpr::Number(TlaNumber::Decimal("1".to_string()))),
        };
        let b = TlaExpr::BinOp {
            op: TlaBinOp::Minus,
            left: Box::new(TlaExpr::Ident("x".to_string())),
            right: Box::new(TlaExpr::Number(TlaNumber::Decimal("1".to_string()))),
        };
        let result = compare_tla_expr(&a, &b);
        assert!(!result.equivalent);
    }

    #[test]
    fn test_compare_type_mismatch() {
        let a = TlaExpr::Ident("x".to_string());
        let b = TlaExpr::Number(TlaNumber::Decimal("1".to_string()));
        let result = compare_tla_expr(&a, &b);
        assert!(!result.equivalent);
        assert!(result.differences[0].description.contains("type mismatch"));
    }

    #[test]
    fn test_difference_display() {
        let diff = Difference::new("path.to.element", "value mismatch", "expected", "actual");
        let s = format!("{}", diff);
        assert!(s.contains("path.to.element"));
        assert!(s.contains("value mismatch"));
        assert!(s.contains("expected"));
        assert!(s.contains("actual"));
    }
}

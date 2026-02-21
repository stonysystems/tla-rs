use crate::ast::{Binding, Expr, SpecFunction, Type};
use crate::error::{TranspileError, TranspileResult};

/// Normalized transition IR extracted from `LNext`.
#[derive(Debug, Clone)]
pub struct TransitionIr {
    /// The current-state parameter name (typically `s`).
    pub current_state_param: String,
    /// The next-state parameter name (typically `s_`).
    pub next_state_param: String,
    /// Optional constants parameter name (typically `c`).
    pub constants_param: Option<String>,
    /// Disjunctive transition branches.
    pub branches: Vec<TransitionBranchIr>,
}

/// A single normalized `LNext` branch.
#[derive(Debug, Clone)]
pub struct TransitionBranchIr {
    /// Stable branch label in source order.
    pub label: String,
    /// Existential variables scoped to this branch.
    pub existential_vars: Vec<ExistentialVarIr>,
    /// Normalized branch constraints.
    pub constraints: Vec<BranchConstraintIr>,
}

/// Existential variable metadata.
#[derive(Debug, Clone)]
pub struct ExistentialVarIr {
    pub name: String,
    pub ty: Option<Type>,
}

/// A branch-level constraint.
#[derive(Debug, Clone)]
pub enum BranchConstraintIr {
    /// Equality where one side is a recognized target path.
    Eq {
        target: ConstraintTarget,
        value: Expr,
    },
    /// Any non-normalized predicate or side condition.
    Predicate { expr: Expr },
}

/// Target path in normalized constraints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstraintTarget {
    pub root: ConstraintRoot,
    pub path: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintRoot {
    CurrentState,
    NextState,
    Constants,
    Other(String),
}

/// Build normalized transition IR from an `LNext` spec function.
pub fn build_transition_ir(next_fn: &SpecFunction) -> TranspileResult<TransitionIr> {
    if next_fn.params.len() < 2 {
        return Err(TranspileError::Config {
            message: format!(
                "Cannot build transition IR from `{}`: expected at least 2 parameters (s, s_), got {}.",
                next_fn.name,
                next_fn.params.len()
            ),
        });
    }

    let current_state_param = next_fn.params[0].name.clone();
    let next_state_param = next_fn.params[1].name.clone();
    let constants_param = next_fn.params.get(2).map(|p| p.name.clone());

    let mut branches = Vec::new();
    for (idx, disjunct) in split_disjunction(&next_fn.body).into_iter().enumerate() {
        let (existential_bindings, body_without_exists) = peel_exists(&disjunct);
        let existential_vars = existential_bindings
            .into_iter()
            .map(|binding| ExistentialVarIr {
                name: binding.name().unwrap_or("_").to_string(),
                ty: binding.ty,
            })
            .collect();

        let constraints = split_conjunction(&body_without_exists)
            .into_iter()
            .map(|expr| {
                normalize_constraint(
                    expr,
                    &current_state_param,
                    &next_state_param,
                    constants_param.as_deref(),
                )
            })
            .collect();

        branches.push(TransitionBranchIr {
            label: format!("branch_{}", idx),
            existential_vars,
            constraints,
        });
    }

    Ok(TransitionIr {
        current_state_param,
        next_state_param,
        constants_param,
        branches,
    })
}

fn normalize_constraint(
    expr: Expr,
    current_state_param: &str,
    next_state_param: &str,
    constants_param: Option<&str>,
) -> BranchConstraintIr {
    if let Expr::Eq(lhs, rhs) = expr {
        if let Some(target) =
            extract_target(&lhs, current_state_param, next_state_param, constants_param)
        {
            return BranchConstraintIr::Eq {
                target,
                value: *rhs,
            };
        }
        if let Some(target) =
            extract_target(&rhs, current_state_param, next_state_param, constants_param)
        {
            return BranchConstraintIr::Eq {
                target,
                value: *lhs,
            };
        }
        return BranchConstraintIr::Predicate {
            expr: Expr::Eq(lhs, rhs),
        };
    }
    BranchConstraintIr::Predicate { expr }
}

fn split_disjunction(expr: &Expr) -> Vec<Expr> {
    match expr {
        Expr::Disjunction(items) => {
            let mut out = Vec::new();
            for item in items {
                out.extend(split_disjunction(item));
            }
            out
        }
        _ => vec![expr.clone()],
    }
}

fn split_conjunction(expr: &Expr) -> Vec<Expr> {
    match expr {
        Expr::Conjunction(items) => {
            let mut out = Vec::new();
            for item in items {
                out.extend(split_conjunction(item));
            }
            out
        }
        _ => vec![expr.clone()],
    }
}

fn peel_exists(expr: &Expr) -> (Vec<Binding>, Expr) {
    let mut vars = Vec::new();
    let mut cursor = expr.clone();
    while let Expr::Exists {
        vars: branch_vars,
        body,
    } = cursor
    {
        vars.extend(branch_vars);
        cursor = *body;
    }
    (vars, cursor)
}

fn extract_target(
    expr: &Expr,
    current_state_param: &str,
    next_state_param: &str,
    constants_param: Option<&str>,
) -> Option<ConstraintTarget> {
    let mut segments = extract_segments(expr)?;
    if segments.is_empty() {
        return None;
    }
    let head = segments.remove(0);

    let root = if head == current_state_param {
        ConstraintRoot::CurrentState
    } else if head == next_state_param {
        ConstraintRoot::NextState
    } else if constants_param == Some(head.as_str()) {
        ConstraintRoot::Constants
    } else {
        ConstraintRoot::Other(head)
    };

    Some(ConstraintTarget {
        root,
        path: segments,
    })
}

fn extract_segments(expr: &Expr) -> Option<Vec<String>> {
    match expr {
        Expr::Ident(name) => Some(vec![name.clone()]),
        Expr::Field(base, field) | Expr::Arrow(base, field) => {
            let mut segments = extract_segments(base)?;
            segments.push(field.clone());
            Some(segments)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Expr, Literal, Parameter, Path, Type, VariableMode};

    fn mk_param(name: &str) -> Parameter {
        Parameter {
            name: name.to_string(),
            ty: Type::Named(Path::single("Dummy".to_string())),
            mode: None,
            variable_mode: VariableMode::Exec,
            span: None,
        }
    }

    fn mk_lnext(body: Expr) -> SpecFunction {
        SpecFunction {
            name: "LNext".to_string(),
            generics: Default::default(),
            params: vec![mk_param("s"), mk_param("s_"), mk_param("c")],
            return_type: Type::Bool,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body,
            span: None,
        }
    }

    fn s_field(name: &str) -> Expr {
        Expr::Field(Box::new(Expr::Ident("s".to_string())), name.to_string())
    }

    fn s_next_field(name: &str) -> Expr {
        Expr::Field(Box::new(Expr::Ident("s_".to_string())), name.to_string())
    }

    fn c_field(name: &str) -> Expr {
        Expr::Field(Box::new(Expr::Ident("c".to_string())), name.to_string())
    }

    #[test]
    fn test_build_transition_ir_rejects_missing_state_params() {
        let spec = SpecFunction {
            name: "LNext".to_string(),
            generics: Default::default(),
            params: vec![mk_param("s")],
            return_type: Type::Bool,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body: Expr::Literal(Literal::Bool(true)),
            span: None,
        };
        let err = build_transition_ir(&spec).unwrap_err();
        assert!(err.to_string().contains("expected at least 2 parameters"));
    }

    #[test]
    fn test_build_transition_ir_normalizes_disjunction_and_exists() {
        let body = Expr::Disjunction(vec![
            Expr::Conjunction(vec![
                Expr::Eq(
                    Box::new(s_next_field("x")),
                    Box::new(Expr::Literal(Literal::Int(1))),
                ),
                Expr::Eq(
                    Box::new(c_field("limit")),
                    Box::new(Expr::Literal(Literal::Int(3))),
                ),
            ]),
            Expr::Exists {
                vars: vec![Binding {
                    pattern: crate::ast::Pattern::Ident("i".to_string()),
                    ty: Some(Type::Int),
                    variable_mode: VariableMode::Exec,
                }],
                body: Box::new(Expr::Conjunction(vec![
                    Expr::Eq(
                        Box::new(s_next_field("x")),
                        Box::new(Expr::Ident("i".to_string())),
                    ),
                    Expr::Gt(
                        Box::new(Expr::Ident("i".to_string())),
                        Box::new(Expr::Literal(Literal::Int(0))),
                    ),
                ])),
            },
        ]);

        let ir = build_transition_ir(&mk_lnext(body)).unwrap();
        assert_eq!(ir.current_state_param, "s");
        assert_eq!(ir.next_state_param, "s_");
        assert_eq!(ir.constants_param.as_deref(), Some("c"));
        assert_eq!(ir.branches.len(), 2);

        assert_eq!(ir.branches[0].label, "branch_0");
        assert_eq!(ir.branches[0].existential_vars.len(), 0);
        assert_eq!(ir.branches[0].constraints.len(), 2);

        match &ir.branches[1].constraints[0] {
            BranchConstraintIr::Eq { target, value } => {
                assert_eq!(target.root, ConstraintRoot::NextState);
                assert_eq!(target.path, vec!["x".to_string()]);
                assert!(matches!(value, Expr::Ident(name) if name == "i"));
            }
            other => panic!("expected Eq constraint, got {:?}", other),
        }
        match &ir.branches[1].constraints[1] {
            BranchConstraintIr::Predicate { expr } => {
                assert!(matches!(expr, Expr::Gt(_, _)));
            }
            other => panic!("expected Predicate constraint, got {:?}", other),
        }
        assert_eq!(ir.branches[1].existential_vars.len(), 1);
        assert_eq!(ir.branches[1].existential_vars[0].name, "i");
    }

    #[test]
    fn test_build_transition_ir_classifies_state_roots() {
        let body = Expr::Conjunction(vec![
            Expr::Eq(
                Box::new(s_field("x")),
                Box::new(Expr::Literal(Literal::Int(0))),
            ),
            Expr::Eq(
                Box::new(Expr::Literal(Literal::Int(1))),
                Box::new(s_next_field("x")),
            ),
            Expr::Eq(
                Box::new(c_field("k")),
                Box::new(Expr::Literal(Literal::Int(2))),
            ),
            Expr::Eq(
                Box::new(Expr::Field(
                    Box::new(Expr::Ident("other".to_string())),
                    "y".to_string(),
                )),
                Box::new(Expr::Literal(Literal::Int(7))),
            ),
        ]);

        let ir = build_transition_ir(&mk_lnext(body)).unwrap();
        let constraints = &ir.branches[0].constraints;
        assert_eq!(constraints.len(), 4);

        let roots: Vec<ConstraintRoot> = constraints
            .iter()
            .map(|c| match c {
                BranchConstraintIr::Eq { target, .. } => target.root.clone(),
                BranchConstraintIr::Predicate { .. } => {
                    panic!("all constraints should normalize to Eq in this test")
                }
            })
            .collect();
        assert!(roots.contains(&ConstraintRoot::CurrentState));
        assert!(roots.contains(&ConstraintRoot::NextState));
        assert!(roots.contains(&ConstraintRoot::Constants));
        assert!(roots.contains(&ConstraintRoot::Other("other".to_string())));
    }
}

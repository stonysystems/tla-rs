use crate::ast::{BinOp, Binding, Expr, SpecFunction, Type};
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
    /// Extra parameters beyond state/state_/constants (e.g., `c: int` in generated protocol specs).
    /// These are treated as existential variables enumerated during solving.
    pub extra_params: Vec<ExistentialVarIr>,
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

#[derive(Debug, Clone)]
struct DiscoveredBranch {
    existential_bindings: Vec<Binding>,
    expr: Expr,
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

    // Capture extra params beyond state/state_/constants as existential variables
    let extra_start = if constants_param.is_some() { 3 } else { 2 };
    let extra_params: Vec<ExistentialVarIr> = next_fn.params[extra_start..]
        .iter()
        .map(|p| ExistentialVarIr {
            name: p.name.clone(),
            ty: Some(p.ty.clone()),
        })
        .collect();

    let branches = discover_lnext_branches(next_fn)?;

    Ok(TransitionIr {
        current_state_param,
        next_state_param,
        constants_param,
        extra_params,
        branches,
    })
}

/// Discover normalized disjunctive branches from an `LNext` body.
///
/// This routine flattens disjunctions, carries branch-scoped existential
/// variables, and normalizes conjunctions into branch constraints.
pub fn discover_lnext_branches(next_fn: &SpecFunction) -> TranspileResult<Vec<TransitionBranchIr>> {
    if next_fn.params.len() < 2 {
        return Err(TranspileError::Config {
            message: format!(
                "Cannot discover transition branches from `{}`: expected at least 2 parameters (s, s_), got {}.",
                next_fn.name,
                next_fn.params.len()
            ),
        });
    }

    let current_state_param = next_fn.params[0].name.as_str();
    let next_state_param = next_fn.params[1].name.as_str();
    let constants_param = next_fn.params.get(2).map(|p| p.name.as_str());

    let mut branches = Vec::new();
    for (idx, branch_expr) in discover_disjunctive_branches(&next_fn.body)
        .into_iter()
        .enumerate()
    {
        let (extra_existentials, constraint_exprs) = flatten_branch_body(branch_expr.expr);
        let existential_bindings = branch_expr
            .existential_bindings
            .into_iter()
            .chain(extra_existentials.into_iter())
            .collect::<Vec<_>>();
        // Deduplicate existential variables by name: nested existentials produce
        // duplicate names when inner scopes shadow outer ones (e.g., `exists |node|
        // (A || exists |node| B)` produces [outer_node, inner_node] for branch B).
        // Keep only the LAST occurrence of each name (the innermost/shadowing one).
        let mut seen = std::collections::HashSet::new();
        let existential_vars: Vec<ExistentialVarIr> = existential_bindings
            .into_iter()
            .rev() // reverse to prefer inner (later) bindings
            .filter_map(|binding| {
                let name = binding.name().unwrap_or("_").to_string();
                if seen.insert(name.clone()) {
                    Some(ExistentialVarIr { name, ty: binding.ty })
                } else {
                    None // duplicate name — skip outer binding
                }
            })
            .collect::<Vec<_>>()
            .into_iter()
            .rev() // restore original order
            .collect();

        let constraints: Vec<BranchConstraintIr> = constraint_exprs
            .into_iter()
            .map(|expr| {
                normalize_constraint(expr, current_state_param, next_state_param, constants_param)
            })
            .collect();
        // Existentials are gathered by syntactic scope while flattening disjunctions.
        // In generated-D1 shapes this can over-approximate branch-local variables
        // (outer existentials remain in scope for right-hand disjuncts even when the
        // branch body does not reference them). Prune truly-unused vars here so
        // branch assignment expansion does not explode on irrelevant domains.
        let existential_vars: Vec<ExistentialVarIr> = existential_vars
            .into_iter()
            .filter(|var| {
                constraints
                    .iter()
                    .any(|constraint| constraint_mentions_identifier(constraint, &var.name))
            })
            .collect();

        branches.push(TransitionBranchIr {
            label: format!("branch_{}", idx),
            existential_vars,
            constraints,
        });
    }

    Ok(branches)
}

/// Public wrapper for `normalize_constraint` (Phase 38.17.2).
pub fn normalize_constraint_pub(
    expr: Expr,
    current_state_param: &str,
    next_state_param: &str,
    constants_param: Option<&str>,
) -> BranchConstraintIr {
    normalize_constraint(expr, current_state_param, next_state_param, constants_param)
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

fn constraint_mentions_identifier(constraint: &BranchConstraintIr, ident: &str) -> bool {
    match constraint {
        BranchConstraintIr::Eq { target, value } => {
            matches!(&target.root, ConstraintRoot::Other(root) if root == ident)
                || expr_mentions_identifier(value, ident)
        }
        BranchConstraintIr::Predicate { expr } => expr_mentions_identifier(expr, ident),
    }
}

fn expr_mentions_identifier(expr: &Expr, ident: &str) -> bool {
    match expr {
        Expr::Ident(name) => name == ident,
        Expr::Conjunction(items) | Expr::Disjunction(items) => items
            .iter()
            .any(|item| expr_mentions_identifier(item, ident)),
        Expr::Implies(lhs, rhs)
        | Expr::Iff(lhs, rhs)
        | Expr::Eq(lhs, rhs)
        | Expr::Ne(lhs, rhs)
        | Expr::Lt(lhs, rhs)
        | Expr::Le(lhs, rhs)
        | Expr::Gt(lhs, rhs)
        | Expr::Ge(lhs, rhs)
        | Expr::Binary(lhs, _, rhs)
        | Expr::Index(lhs, rhs) => {
            expr_mentions_identifier(lhs, ident) || expr_mentions_identifier(rhs, ident)
        }
        Expr::Not(inner)
        | Expr::View(inner)
        | Expr::Cast(inner, _)
        | Expr::Unary(_, inner)
        | Expr::Field(inner, _)
        | Expr::Arrow(inner, _)
        | Expr::Is(inner, _) => expr_mentions_identifier(inner, ident),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            expr_mentions_identifier(cond, ident)
                || expr_mentions_identifier(then_branch, ident)
                || else_branch
                    .as_deref()
                    .is_some_and(|branch| expr_mentions_identifier(branch, ident))
        }
        Expr::Match { scrutinee, arms } => {
            expr_mentions_identifier(scrutinee, ident)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| expr_mentions_identifier(guard, ident))
                        || expr_mentions_identifier(&arm.body, ident)
                })
        }
        Expr::Let {
            binding,
            value,
            body,
        } => {
            expr_mentions_identifier(value, ident)
                || (binding.name() != Some(ident) && expr_mentions_identifier(body, ident))
        }
        Expr::Forall {
            vars,
            triggers,
            body,
        } => {
            let shadowed = vars.iter().any(|var| var.name() == Some(ident));
            triggers.iter().any(|trigger| {
                trigger
                    .exprs
                    .iter()
                    .any(|expr| expr_mentions_identifier(expr, ident))
            }) || (!shadowed && expr_mentions_identifier(body, ident))
        }
        Expr::Exists { vars, body } | Expr::Choose { vars, body } => {
            let shadowed = vars.iter().any(|var| var.name() == Some(ident));
            !shadowed && expr_mentions_identifier(body, ident)
        }
        Expr::Closure { params, body } => {
            let shadowed = params.iter().any(|param| param.name() == Some(ident));
            !shadowed && expr_mentions_identifier(body, ident)
        }
        Expr::Struct { fields, .. } => fields
            .iter()
            .any(|(_, value)| expr_mentions_identifier(value, ident)),
        Expr::StructUpdate { base, fields, .. } => {
            expr_mentions_identifier(base, ident)
                || fields
                    .iter()
                    .any(|(_, value)| expr_mentions_identifier(value, ident))
        }
        Expr::SeqLit(items) | Expr::SetLit(items) => items
            .iter()
            .any(|item| expr_mentions_identifier(item, ident)),
        Expr::MapLit(entries) => entries.iter().any(|(key, value)| {
            expr_mentions_identifier(key, ident) || expr_mentions_identifier(value, ident)
        }),
        Expr::Call { args, .. } => args.iter().any(|arg| expr_mentions_identifier(arg, ident)),
        Expr::MethodCall { receiver, args, .. } => {
            expr_mentions_identifier(receiver, ident)
                || args.iter().any(|arg| expr_mentions_identifier(arg, ident))
        }
        Expr::Literal(_) | Expr::SeqEmpty | Expr::SetEmpty | Expr::MapEmpty => false,
    }
}

fn discover_disjunctive_branches(expr: &Expr) -> Vec<DiscoveredBranch> {
    match expr {
        Expr::Disjunction(items) => {
            let mut out = Vec::new();
            for item in items {
                out.extend(discover_disjunctive_branches(item));
            }
            out
        }
        Expr::Binary(lhs, BinOp::Or, rhs) => {
            let mut out = Vec::new();
            out.extend(discover_disjunctive_branches(lhs));
            out.extend(discover_disjunctive_branches(rhs));
            out
        }
        Expr::Exists { vars, body } => discover_disjunctive_branches(body)
            .into_iter()
            .map(|branch| {
                let mut existential_bindings = vars.clone();
                existential_bindings.extend(branch.existential_bindings);
                DiscoveredBranch {
                    existential_bindings,
                    expr: branch.expr,
                }
            })
            .collect(),
        _ => vec![DiscoveredBranch {
            existential_bindings: Vec::new(),
            expr: expr.clone(),
        }],
    }
}

/// Public wrapper for `flatten_branch_body` (Phase 38.17.2).
pub fn flatten_branch_body_pub(expr: Expr) -> (Vec<Binding>, Vec<Expr>) {
    flatten_branch_body(expr)
}

/// Phase 38.17.4: Inline action predicate calls in branch constraints.
/// When LNext decomposes into branches like `LSend1a(s, s_, 1)`, the IR
/// creates a single Predicate { Call("LSend1a", ...) } constraint. The
/// solver can't extract s_.field assignments from this opaque call,
/// forcing the 500x-slower candidate-enumeration fallback.
///
/// This function looks up the called function in `spec_functions`,
/// substitutes formal parameters with actual arguments, and expands the
/// conjunction into individual normalized constraints. If the inlined
/// result has no NextState Eq constraints, the original Predicate call
/// is kept (for the predicate_only_solver to handle).
///
/// Returns the number of branches that were inlined.
pub fn inline_action_calls(
    transition: &mut TransitionIr,
    spec_functions: &[SpecFunction],
) -> usize {
    let current_state_param = transition.current_state_param.clone();
    let next_state_param = transition.next_state_param.clone();
    let constants_param = transition.constants_param.clone();
    let mut inlined_count = 0;

    for branch in &mut transition.branches {
        let mut new_constraints = Vec::new();
        let mut any_inlined = false;
        for constraint in &branch.constraints {
            if let BranchConstraintIr::Predicate { expr } = constraint {
                if let Expr::Call { func, args } = expr {
                    let func_name = func.segments.last().map(|s| s.as_str()).unwrap_or("");
                    if let Some(spec_fn) = spec_functions.iter().find(|f| f.name == func_name) {
                        let body = substitute_call_args(&spec_fn.body, &spec_fn.params, args);
                        let (_, conjuncts) = flatten_branch_body(body);
                        let inlined_constraints: Vec<BranchConstraintIr> = conjuncts
                            .into_iter()
                            .map(|c| {
                                normalize_constraint(
                                    c,
                                    &current_state_param,
                                    &next_state_param,
                                    constants_param.as_deref(),
                                )
                            })
                            .collect();
                        let has_next_state_eq = inlined_constraints.iter().any(|c| {
                            matches!(
                                c,
                                BranchConstraintIr::Eq {
                                    target: ConstraintTarget {
                                        root: ConstraintRoot::NextState,
                                        ..
                                    },
                                    ..
                                }
                            )
                        });
                        if has_next_state_eq {
                            new_constraints.extend(inlined_constraints);
                            any_inlined = true;
                            continue;
                        }
                    }
                }
            }
            new_constraints.push(constraint.clone());
        }
        if any_inlined {
            branch.constraints = new_constraints;
            inlined_count += 1;
        }
    }

    inlined_count
}

/// Substitute formal parameters with actual argument expressions.
fn substitute_call_args(
    body: &Expr,
    params: &[crate::ast::Parameter],
    args: &[Expr],
) -> Expr {
    let subst: std::collections::BTreeMap<String, &Expr> = params
        .iter()
        .zip(args.iter())
        .map(|(p, a)| (p.name.clone(), a))
        .collect();
    substitute_expr(body, &subst)
}

fn substitute_expr(
    expr: &Expr,
    subst: &std::collections::BTreeMap<String, &Expr>,
) -> Expr {
    match expr {
        Expr::Ident(name) => {
            if let Some(replacement) = subst.get(name.as_str()) {
                (*replacement).clone()
            } else {
                expr.clone()
            }
        }
        Expr::Eq(lhs, rhs) => Expr::Eq(
            Box::new(substitute_expr(lhs, subst)),
            Box::new(substitute_expr(rhs, subst)),
        ),
        Expr::Ne(lhs, rhs) => Expr::Ne(
            Box::new(substitute_expr(lhs, subst)),
            Box::new(substitute_expr(rhs, subst)),
        ),
        Expr::Lt(lhs, rhs) => Expr::Lt(
            Box::new(substitute_expr(lhs, subst)),
            Box::new(substitute_expr(rhs, subst)),
        ),
        Expr::Le(lhs, rhs) => Expr::Le(
            Box::new(substitute_expr(lhs, subst)),
            Box::new(substitute_expr(rhs, subst)),
        ),
        Expr::Gt(lhs, rhs) => Expr::Gt(
            Box::new(substitute_expr(lhs, subst)),
            Box::new(substitute_expr(rhs, subst)),
        ),
        Expr::Ge(lhs, rhs) => Expr::Ge(
            Box::new(substitute_expr(lhs, subst)),
            Box::new(substitute_expr(rhs, subst)),
        ),
        Expr::Conjunction(exprs) => Expr::Conjunction(
            exprs.iter().map(|e| substitute_expr(e, subst)).collect(),
        ),
        Expr::Disjunction(exprs) => Expr::Disjunction(
            exprs.iter().map(|e| substitute_expr(e, subst)).collect(),
        ),
        Expr::Not(inner) => Expr::Not(Box::new(substitute_expr(inner, subst))),
        Expr::Binary(lhs, op, rhs) => Expr::Binary(
            Box::new(substitute_expr(lhs, subst)),
            op.clone(),
            Box::new(substitute_expr(rhs, subst)),
        ),
        Expr::Field(base, field) => Expr::Field(
            Box::new(substitute_expr(base, subst)),
            field.clone(),
        ),
        Expr::Arrow(base, field) => Expr::Arrow(
            Box::new(substitute_expr(base, subst)),
            field.clone(),
        ),
        Expr::Call { func, args } => Expr::Call {
            func: func.clone(),
            args: args.iter().map(|a| substitute_expr(a, subst)).collect(),
        },
        Expr::MethodCall { receiver, method, args } => Expr::MethodCall {
            receiver: Box::new(substitute_expr(receiver, subst)),
            method: method.clone(),
            args: args.iter().map(|a| substitute_expr(a, subst)).collect(),
        },
        Expr::If { cond, then_branch, else_branch } => Expr::If {
            cond: Box::new(substitute_expr(cond, subst)),
            then_branch: Box::new(substitute_expr(then_branch, subst)),
            else_branch: else_branch.as_ref().map(|e| Box::new(substitute_expr(e, subst))),
        },
        Expr::Implies(lhs, rhs) => Expr::Implies(
            Box::new(substitute_expr(lhs, subst)),
            Box::new(substitute_expr(rhs, subst)),
        ),
        Expr::SetLit(exprs) => Expr::SetLit(
            exprs.iter().map(|e| substitute_expr(e, subst)).collect(),
        ),
        Expr::SeqLit(exprs) => Expr::SeqLit(
            exprs.iter().map(|e| substitute_expr(e, subst)).collect(),
        ),
        Expr::View(inner) => Expr::View(Box::new(substitute_expr(inner, subst))),
        _ => expr.clone(),
    }
}

fn flatten_branch_body(expr: Expr) -> (Vec<Binding>, Vec<Expr>) {
    let mut existential_bindings = Vec::new();
    let mut constraints = Vec::new();
    flatten_branch_body_into(expr, &mut existential_bindings, &mut constraints);
    (existential_bindings, constraints)
}

fn flatten_branch_body_into(
    expr: Expr,
    existential_bindings: &mut Vec<Binding>,
    constraints: &mut Vec<Expr>,
) {
    match expr {
        Expr::Conjunction(items) => {
            for item in items {
                flatten_branch_body_into(item, existential_bindings, constraints);
            }
        }
        Expr::Binary(lhs, BinOp::And, rhs) => {
            flatten_branch_body_into(*lhs, existential_bindings, constraints);
            flatten_branch_body_into(*rhs, existential_bindings, constraints);
        }
        Expr::Exists { vars, body } => {
            existential_bindings.extend(vars);
            flatten_branch_body_into(*body, existential_bindings, constraints);
        }
        other => constraints.push(other),
    }
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
    use crate::ast::{BinOp, Expr, Literal, Parameter, Path, Type, VariableMode};

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

    #[test]
    fn test_discover_lnext_branches_splits_exists_wrapped_disjunction() {
        let body = Expr::Exists {
            vars: vec![Binding {
                pattern: crate::ast::Pattern::Ident("i".to_string()),
                ty: Some(Type::Int),
                variable_mode: VariableMode::Exec,
            }],
            body: Box::new(Expr::Disjunction(vec![
                Expr::Eq(
                    Box::new(s_next_field("x")),
                    Box::new(Expr::Ident("i".to_string())),
                ),
                Expr::Eq(
                    Box::new(s_next_field("x")),
                    Box::new(Expr::Literal(Literal::Int(5))),
                ),
            ])),
        };

        let branches = discover_lnext_branches(&mk_lnext(body)).unwrap();
        assert_eq!(branches.len(), 2);

        assert_eq!(branches[0].existential_vars.len(), 1);
        assert_eq!(branches[0].existential_vars[0].name, "i");
        assert_eq!(branches[1].existential_vars.len(), 0);

        for branch in &branches {
            assert_eq!(branch.constraints.len(), 1);
            match &branch.constraints[0] {
                BranchConstraintIr::Eq { target, .. } => {
                    assert_eq!(target.root, ConstraintRoot::NextState);
                    assert_eq!(target.path, vec!["x".to_string()]);
                }
                other => panic!("expected Eq constraint, got {:?}", other),
            }
        }
    }

    #[test]
    fn test_build_transition_ir_hoists_exists_inside_conjunction() {
        let body = Expr::Conjunction(vec![
            Expr::Exists {
                vars: vec![Binding {
                    pattern: crate::ast::Pattern::Ident("i".to_string()),
                    ty: Some(Type::Int),
                    variable_mode: VariableMode::Exec,
                }],
                body: Box::new(Expr::Eq(
                    Box::new(s_next_field("x")),
                    Box::new(Expr::Ident("i".to_string())),
                )),
            },
            Expr::Eq(
                Box::new(s_field("x")),
                Box::new(Expr::Literal(Literal::Int(0))),
            ),
        ]);

        let ir = build_transition_ir(&mk_lnext(body)).unwrap();
        assert_eq!(ir.branches.len(), 1);
        assert_eq!(ir.branches[0].existential_vars.len(), 1);
        assert_eq!(ir.branches[0].existential_vars[0].name, "i");
        assert_eq!(ir.branches[0].constraints.len(), 2);

        let roots: Vec<ConstraintRoot> = ir.branches[0]
            .constraints
            .iter()
            .filter_map(|constraint| match constraint {
                BranchConstraintIr::Eq { target, .. } => Some(target.root.clone()),
                BranchConstraintIr::Predicate { .. } => None,
            })
            .collect();
        assert!(roots.contains(&ConstraintRoot::NextState));
        assert!(roots.contains(&ConstraintRoot::CurrentState));
    }

    #[test]
    fn test_discover_lnext_branches_supports_binary_or_and_and() {
        let body = Expr::Binary(
            Box::new(Expr::Binary(
                Box::new(Expr::Eq(
                    Box::new(s_next_field("x")),
                    Box::new(Expr::Literal(Literal::Int(1))),
                )),
                BinOp::And,
                Box::new(Expr::Eq(
                    Box::new(s_field("x")),
                    Box::new(Expr::Literal(Literal::Int(0))),
                )),
            )),
            BinOp::Or,
            Box::new(Expr::Eq(
                Box::new(s_next_field("x")),
                Box::new(Expr::Literal(Literal::Int(2))),
            )),
        );

        let branches = discover_lnext_branches(&mk_lnext(body)).unwrap();
        assert_eq!(branches.len(), 2);
        assert_eq!(branches[0].constraints.len(), 2);
        assert_eq!(branches[1].constraints.len(), 1);
    }
}

use crate::ast::Expr;
use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::domain::ExistentialAssignment;
use crate::modelcheck::evaluator::{eval_expr, CallEvaluator, EvalContext, MethodEvaluator};
use crate::modelcheck::ir::{
    BranchConstraintIr, ConstraintRoot, ConstraintTarget, TransitionBranchIr, TransitionIr,
};
use crate::modelcheck::value::{RuntimeCollectionBounds, RuntimeValue};
use std::collections::{BTreeMap, BTreeSet};

/// Optional evaluator hooks used while solving branch constraints.
#[derive(Clone, Copy, Default)]
pub struct SolverHooks<'a> {
    pub call_evaluator: Option<&'a CallEvaluator>,
    pub method_evaluator: Option<&'a MethodEvaluator>,
}

/// Solve one normalized `LNext` branch into concrete successor states.
///
/// For each existential assignment:
/// - apply all `s_.* == expr` assignments against a candidate next state,
/// - validate non-next-state equalities and predicates,
/// - emit concrete `s_` when all constraints hold.
pub fn solve_branch_successors(
    transition: &TransitionIr,
    branch: &TransitionBranchIr,
    current_state: &RuntimeValue,
    constants: Option<&RuntimeValue>,
    existential_assignments: &[ExistentialAssignment],
    bounds: RuntimeCollectionBounds,
    hooks: SolverHooks<'_>,
) -> TranspileResult<Vec<RuntimeValue>> {
    if !branch_has_next_state_assignment(branch) {
        return Err(unsupported_solver(
            format!(
                "branch `{}` has no direct next-state equality constraints (`s_.field == ...`)",
                branch.label
            )
            .as_str(),
            Some(
                "Inline called action predicates into equality constraints before solving."
                    .to_string(),
            ),
        ));
    }

    let assignments: Vec<ExistentialAssignment> = if existential_assignments.is_empty() {
        vec![BTreeMap::new()]
    } else {
        existential_assignments.to_vec()
    };

    let mut successors = Vec::new();
    for assignment in assignments {
        if !assignment_compatible_with_branch(branch, &assignment)? {
            return Err(TranspileError::Config {
                message: format!(
                    "Branch `{}` received existential assignment missing required variables.",
                    branch.label
                ),
            });
        }
        if let Some(next_state) = solve_one_assignment(
            transition,
            branch,
            current_state,
            constants,
            &assignment,
            bounds,
            hooks,
        )? {
            successors.push(next_state);
        }
    }

    Ok(deduplicate_successors(successors))
}

/// Solve all `LNext` branches for one current state and return deduplicated successors.
///
/// `existential_assignments_by_branch` maps branch labels (`branch_0`, `branch_1`, ...)
/// to concrete existential assignments. If omitted or missing a label, the branch
/// is solved with an empty assignment set.
pub fn solve_transition_successors(
    transition: &TransitionIr,
    current_state: &RuntimeValue,
    constants: Option<&RuntimeValue>,
    existential_assignments_by_branch: Option<&BTreeMap<String, Vec<ExistentialAssignment>>>,
    bounds: RuntimeCollectionBounds,
    hooks: SolverHooks<'_>,
) -> TranspileResult<Vec<RuntimeValue>> {
    let mut successors = Vec::new();
    for branch in &transition.branches {
        let branch_assignments: &[ExistentialAssignment] = existential_assignments_by_branch
            .and_then(|map| map.get(&branch.label))
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        successors.extend(solve_branch_successors(
            transition,
            branch,
            current_state,
            constants,
            branch_assignments,
            bounds,
            hooks,
        )?);
    }

    Ok(deduplicate_successors(successors))
}

/// Deduplicate successor states by canonical runtime-value key while preserving order.
pub fn deduplicate_successors(successors: Vec<RuntimeValue>) -> Vec<RuntimeValue> {
    let mut seen = BTreeSet::new();
    let mut unique = Vec::new();
    for successor in successors {
        let key = successor.canonical_key();
        if seen.insert(key) {
            unique.push(successor);
        }
    }
    unique
}

fn solve_one_assignment(
    transition: &TransitionIr,
    branch: &TransitionBranchIr,
    current_state: &RuntimeValue,
    constants: Option<&RuntimeValue>,
    existential_assignment: &ExistentialAssignment,
    bounds: RuntimeCollectionBounds,
    hooks: SolverHooks<'_>,
) -> TranspileResult<Option<RuntimeValue>> {
    let mut next_state = current_state.clone();
    let mut deferred_constraints = Vec::new();
    let mut next_state_targets: BTreeMap<Vec<String>, RuntimeValue> = BTreeMap::new();

    for constraint in &branch.constraints {
        match constraint {
            BranchConstraintIr::Eq {
                target:
                    ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path,
                    },
                value,
            } => {
                let env = build_environment(
                    transition,
                    current_state,
                    Some(&next_state),
                    constants,
                    existential_assignment,
                );
                let evaluated =
                    eval_with_environment(value, &env, bounds, hooks).map_err(|err| {
                        TranspileError::Config {
                            message: format!(
                                "Failed to evaluate next-state assignment in branch `{}` at `s_.{}`: {}",
                                branch.label,
                                join_path(path),
                                err
                            ),
                        }
                    })?;

                if let Some(existing) = next_state_targets.get(path) {
                    if existing != &evaluated {
                        return Ok(None);
                    }
                } else {
                    write_value_at_path(&mut next_state, path, evaluated.clone())?;
                    next_state_targets.insert(path.clone(), evaluated);
                }
            }
            other => deferred_constraints.push(other),
        }
    }

    for constraint in deferred_constraints {
        let env = build_environment(
            transition,
            current_state,
            Some(&next_state),
            constants,
            existential_assignment,
        );
        let satisfied = evaluate_constraint(constraint, &env, bounds, hooks)?;
        if !satisfied {
            return Ok(None);
        }
    }

    Ok(Some(next_state))
}

fn evaluate_constraint(
    constraint: &BranchConstraintIr,
    env: &BTreeMap<String, RuntimeValue>,
    bounds: RuntimeCollectionBounds,
    hooks: SolverHooks<'_>,
) -> TranspileResult<bool> {
    match constraint {
        BranchConstraintIr::Eq { target, value } => {
            let actual = read_constraint_target(env, target)?;
            let expected = eval_with_environment(value, env, bounds, hooks)?;
            Ok(actual == expected)
        }
        BranchConstraintIr::Predicate { expr } => {
            let evaluated = eval_with_environment(expr, env, bounds, hooks)?;
            match evaluated {
                RuntimeValue::Bool(v) => Ok(v),
                other => Err(TranspileError::Config {
                    message: format!(
                        "Predicate constraint did not evaluate to bool (got `{}`).",
                        other.canonical_key()
                    ),
                }),
            }
        }
    }
}

fn eval_with_environment(
    expr: &Expr,
    env: &BTreeMap<String, RuntimeValue>,
    bounds: RuntimeCollectionBounds,
    hooks: SolverHooks<'_>,
) -> TranspileResult<RuntimeValue> {
    let mut ctx = EvalContext::new(bounds);
    for (name, value) in env {
        ctx = ctx.with_binding(name.clone(), value.clone());
    }
    if let Some(call_evaluator) = hooks.call_evaluator {
        ctx = ctx.with_call_evaluator(call_evaluator);
    }
    if let Some(method_evaluator) = hooks.method_evaluator {
        ctx = ctx.with_method_evaluator(method_evaluator);
    }
    eval_expr(expr, &ctx)
}

fn build_environment(
    transition: &TransitionIr,
    current_state: &RuntimeValue,
    next_state: Option<&RuntimeValue>,
    constants: Option<&RuntimeValue>,
    existential_assignment: &ExistentialAssignment,
) -> BTreeMap<String, RuntimeValue> {
    let mut env = BTreeMap::new();
    env.insert(
        transition.current_state_param.clone(),
        current_state.clone(),
    );
    if let Some(next_state) = next_state {
        env.insert(transition.next_state_param.clone(), next_state.clone());
    }
    if let (Some(name), Some(value)) = (&transition.constants_param, constants) {
        env.insert(name.clone(), value.clone());
    }
    for (name, value) in existential_assignment {
        env.insert(name.clone(), value.clone());
    }
    env
}

fn read_constraint_target(
    env: &BTreeMap<String, RuntimeValue>,
    target: &ConstraintTarget,
) -> TranspileResult<RuntimeValue> {
    let root_name = match &target.root {
        ConstraintRoot::CurrentState => "s",
        ConstraintRoot::NextState => "s_",
        ConstraintRoot::Constants => "c",
        ConstraintRoot::Other(name) => name.as_str(),
    };

    let root_value = env.get(root_name).ok_or_else(|| TranspileError::Config {
        message: format!(
            "Constraint target root `{}` is not bound in solver environment.",
            root_name
        ),
    })?;

    read_value_at_path(root_value, &target.path)
}

fn read_value_at_path(value: &RuntimeValue, path: &[String]) -> TranspileResult<RuntimeValue> {
    if path.is_empty() {
        return Ok(value.clone());
    }
    let head = &path[0];
    let tail = &path[1..];

    match value {
        RuntimeValue::Struct { fields, .. } | RuntimeValue::Enum { fields, .. } => {
            let next = fields.get(head).ok_or_else(|| TranspileError::Config {
                message: format!(
                    "Constraint path `.{}.` is invalid: field `{}` not found.",
                    join_path(path),
                    head
                ),
            })?;
            read_value_at_path(next, tail)
        }
        other => Err(TranspileError::Config {
            message: format!(
                "Constraint path `.{}.` cannot be read from non-record value `{}`.",
                join_path(path),
                other.canonical_key()
            ),
        }),
    }
}

fn write_value_at_path(
    value: &mut RuntimeValue,
    path: &[String],
    replacement: RuntimeValue,
) -> TranspileResult<()> {
    if path.is_empty() {
        *value = replacement;
        return Ok(());
    }

    let head = &path[0];
    let tail = &path[1..];
    match value {
        RuntimeValue::Struct { fields, .. } | RuntimeValue::Enum { fields, .. } => {
            let next = fields.get_mut(head).ok_or_else(|| TranspileError::Config {
                message: format!(
                    "Cannot assign to `.{}`: field `{}` does not exist.",
                    join_path(path),
                    head
                ),
            })?;
            write_value_at_path(next, tail, replacement)
        }
        other => Err(TranspileError::Config {
            message: format!(
                "Cannot assign to `.{}` on non-record value `{}`.",
                join_path(path),
                other.canonical_key()
            ),
        }),
    }
}

fn assignment_compatible_with_branch(
    branch: &TransitionBranchIr,
    assignment: &ExistentialAssignment,
) -> TranspileResult<bool> {
    for existential in &branch.existential_vars {
        if !assignment.contains_key(&existential.name) {
            return Ok(false);
        }
    }
    Ok(true)
}

fn branch_has_next_state_assignment(branch: &TransitionBranchIr) -> bool {
    branch.constraints.iter().any(|constraint| {
        matches!(
            constraint,
            BranchConstraintIr::Eq {
                target: ConstraintTarget {
                    root: ConstraintRoot::NextState,
                    ..
                },
                ..
            }
        )
    })
}

fn join_path(path: &[String]) -> String {
    path.join(".")
}

fn unsupported_solver(message: &str, help: Option<String>) -> TranspileError {
    TranspileError::UnsupportedPattern {
        message: message.to_string(),
        span: None,
        help,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinOp, Expr};
    use crate::modelcheck::ir::{ConstraintRoot, ConstraintTarget, TransitionIr};

    fn bounds() -> RuntimeCollectionBounds {
        RuntimeCollectionBounds {
            max_seq_len: 4,
            max_set_len: 4,
            max_map_len: 4,
        }
    }

    fn transition() -> TransitionIr {
        TransitionIr {
            current_state_param: "s".to_string(),
            next_state_param: "s_".to_string(),
            constants_param: Some("c".to_string()),
            branches: vec![],
        }
    }

    fn state(x: i128, y: i128) -> RuntimeValue {
        RuntimeValue::struct_value(
            "LState",
            vec![
                ("x".to_string(), RuntimeValue::Int(x)),
                ("y".to_string(), RuntimeValue::Int(y)),
            ],
        )
        .unwrap()
    }

    fn constants(limit: i128) -> RuntimeValue {
        RuntimeValue::struct_value(
            "LConstants",
            vec![("limit".to_string(), RuntimeValue::Int(limit))],
        )
        .unwrap()
    }

    #[test]
    fn test_solve_branch_successors_applies_next_state_equalities() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![
                BranchConstraintIr::Eq {
                    target: ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path: vec!["x".to_string()],
                    },
                    value: Expr::Literal(crate::ast::Literal::Int(7)),
                },
                BranchConstraintIr::Eq {
                    target: ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path: vec!["y".to_string()],
                    },
                    value: Expr::Binary(
                        Box::new(Expr::Field(
                            Box::new(Expr::Ident("s".to_string())),
                            "x".to_string(),
                        )),
                        BinOp::Add,
                        Box::new(Expr::Literal(crate::ast::Literal::Int(1))),
                    ),
                },
                BranchConstraintIr::Predicate {
                    expr: Expr::Gt(
                        Box::new(Expr::Field(
                            Box::new(Expr::Ident("s_".to_string())),
                            "y".to_string(),
                        )),
                        Box::new(Expr::Literal(crate::ast::Literal::Int(0))),
                    ),
                },
            ],
        };

        let successors = solve_branch_successors(
            &transition(),
            &branch,
            &state(2, 0),
            Some(&constants(10)),
            &[],
            bounds(),
            SolverHooks::default(),
        )
        .unwrap();
        assert_eq!(successors.len(), 1);
        let succ = &successors[0];
        assert_eq!(
            read_value_at_path(succ, &[String::from("x")]).unwrap(),
            RuntimeValue::Int(7)
        );
        assert_eq!(
            read_value_at_path(succ, &[String::from("y")]).unwrap(),
            RuntimeValue::Int(3)
        );
    }

    #[test]
    fn test_solve_branch_successors_rejects_inconsistent_assignments() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![
                BranchConstraintIr::Eq {
                    target: ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path: vec!["x".to_string()],
                    },
                    value: Expr::Literal(crate::ast::Literal::Int(1)),
                },
                BranchConstraintIr::Eq {
                    target: ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path: vec!["x".to_string()],
                    },
                    value: Expr::Literal(crate::ast::Literal::Int(2)),
                },
            ],
        };

        let successors = solve_branch_successors(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[],
            bounds(),
            SolverHooks::default(),
        )
        .unwrap();
        assert!(successors.is_empty());
    }

    #[test]
    fn test_solve_branch_successors_rejects_failed_predicates() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![
                BranchConstraintIr::Eq {
                    target: ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path: vec!["x".to_string()],
                    },
                    value: Expr::Literal(crate::ast::Literal::Int(3)),
                },
                BranchConstraintIr::Predicate {
                    expr: Expr::Eq(
                        Box::new(Expr::Field(
                            Box::new(Expr::Ident("c".to_string())),
                            "limit".to_string(),
                        )),
                        Box::new(Expr::Literal(crate::ast::Literal::Int(1))),
                    ),
                },
            ],
        };

        let successors = solve_branch_successors(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[],
            bounds(),
            SolverHooks::default(),
        )
        .unwrap();
        assert!(successors.is_empty());
    }

    #[test]
    fn test_solve_branch_successors_supports_existential_assignments() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![crate::modelcheck::ir::ExistentialVarIr {
                name: "i".to_string(),
                ty: Some(crate::ast::Type::Int),
            }],
            constraints: vec![BranchConstraintIr::Eq {
                target: ConstraintTarget {
                    root: ConstraintRoot::NextState,
                    path: vec!["x".to_string()],
                },
                value: Expr::Ident("i".to_string()),
            }],
        };

        let a1 = BTreeMap::from([("i".to_string(), RuntimeValue::Int(1))]);
        let a2 = BTreeMap::from([("i".to_string(), RuntimeValue::Int(2))]);
        let successors = solve_branch_successors(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[a1, a2],
            bounds(),
            SolverHooks::default(),
        )
        .unwrap();
        assert_eq!(successors.len(), 2);
    }

    #[test]
    fn test_solve_branch_successors_deduplicates_equivalent_states() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![crate::modelcheck::ir::ExistentialVarIr {
                name: "i".to_string(),
                ty: Some(crate::ast::Type::Int),
            }],
            constraints: vec![BranchConstraintIr::Eq {
                target: ConstraintTarget {
                    root: ConstraintRoot::NextState,
                    path: vec!["x".to_string()],
                },
                value: Expr::Literal(crate::ast::Literal::Int(9)),
            }],
        };

        let a1 = BTreeMap::from([("i".to_string(), RuntimeValue::Int(1))]);
        let a2 = BTreeMap::from([("i".to_string(), RuntimeValue::Int(2))]);
        let successors = solve_branch_successors(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[a1, a2],
            bounds(),
            SolverHooks::default(),
        )
        .unwrap();
        assert_eq!(successors.len(), 1);
        assert_eq!(
            read_value_at_path(&successors[0], &[String::from("x")]).unwrap(),
            RuntimeValue::Int(9)
        );
    }

    #[test]
    fn test_solve_transition_successors_deduplicates_across_branches() {
        let mut transition = transition();
        transition.branches = vec![
            TransitionBranchIr {
                label: "branch_0".to_string(),
                existential_vars: vec![],
                constraints: vec![
                    BranchConstraintIr::Eq {
                        target: ConstraintTarget {
                            root: ConstraintRoot::NextState,
                            path: vec!["x".to_string()],
                        },
                        value: Expr::Literal(crate::ast::Literal::Int(1)),
                    },
                    BranchConstraintIr::Eq {
                        target: ConstraintTarget {
                            root: ConstraintRoot::NextState,
                            path: vec!["y".to_string()],
                        },
                        value: Expr::Literal(crate::ast::Literal::Int(2)),
                    },
                ],
            },
            TransitionBranchIr {
                label: "branch_1".to_string(),
                existential_vars: vec![],
                constraints: vec![
                    BranchConstraintIr::Eq {
                        target: ConstraintTarget {
                            root: ConstraintRoot::NextState,
                            path: vec!["x".to_string()],
                        },
                        value: Expr::Literal(crate::ast::Literal::Int(1)),
                    },
                    BranchConstraintIr::Eq {
                        target: ConstraintTarget {
                            root: ConstraintRoot::NextState,
                            path: vec!["y".to_string()],
                        },
                        value: Expr::Literal(crate::ast::Literal::Int(2)),
                    },
                ],
            },
        ];

        let successors = solve_transition_successors(
            &transition,
            &state(0, 0),
            Some(&constants(10)),
            None,
            bounds(),
            SolverHooks::default(),
        )
        .unwrap();
        assert_eq!(successors.len(), 1);
        assert_eq!(successors[0], state(1, 2));
    }

    #[test]
    fn test_solve_branch_successors_errors_when_no_next_state_equalities() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![BranchConstraintIr::Predicate {
                expr: Expr::Literal(crate::ast::Literal::Bool(true)),
            }],
        };
        let err = solve_branch_successors(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[],
            bounds(),
            SolverHooks::default(),
        )
        .unwrap_err();
        assert!(err
            .to_string()
            .contains("no direct next-state equality constraints"));
    }

    #[test]
    fn test_write_value_at_path_nested() {
        let mut root = RuntimeValue::struct_value(
            "Outer",
            vec![(
                "inner".to_string(),
                RuntimeValue::struct_value(
                    "Inner",
                    vec![("count".to_string(), RuntimeValue::Int(0))],
                )
                .unwrap(),
            )],
        )
        .unwrap();
        write_value_at_path(
            &mut root,
            &[String::from("inner"), String::from("count")],
            RuntimeValue::Int(5),
        )
        .unwrap();
        let got =
            read_value_at_path(&root, &[String::from("inner"), String::from("count")]).unwrap();
        assert_eq!(got, RuntimeValue::Int(5));
    }
}

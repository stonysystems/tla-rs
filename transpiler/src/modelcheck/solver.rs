use crate::ast::Expr;
use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::domain::ExistentialAssignment;
use crate::modelcheck::evaluator::{
    eval_expr, CallEvaluator, EvalContext, MethodEvaluator, QuantifierDomainEvaluator,
};
use crate::modelcheck::ir::{
    BranchConstraintIr, ConstraintRoot, ConstraintTarget, TransitionBranchIr, TransitionIr,
};
use crate::modelcheck::value::{RuntimeCollectionBounds, RuntimeValue};
use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

pub type PredicateOnlyBranchSolver<'a> = dyn Fn(
        &TransitionIr,
        &TransitionBranchIr,
        &RuntimeValue,
        Option<&RuntimeValue>,
        &[ExistentialAssignment],
        RuntimeCollectionBounds,
    ) -> TranspileResult<Option<Vec<RuntimeValue>>>
    + 'a;

/// Optional evaluator hooks used while solving branch constraints.
#[derive(Clone, Copy, Default)]
pub struct SolverHooks<'a> {
    pub call_evaluator: Option<&'a CallEvaluator<'a>>,
    pub method_evaluator: Option<&'a MethodEvaluator<'a>>,
    pub quantifier_domain_evaluator: Option<&'a QuantifierDomainEvaluator<'a>>,
    pub predicate_only_branch_solver: Option<&'a PredicateOnlyBranchSolver<'a>>,
}

/// Semantics to apply when `LNext` yields no enabled successors.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum EmptySuccessorSemantics {
    /// No implicit transition (deadlock semantics).
    #[default]
    Deadlock,
    /// Add one stutter successor where `s_ == s`.
    Stuttering,
}

/// Telemetry emitted for one branch-solve attempt.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct BranchSolveTelemetry {
    /// Count of branch solves using direct `s_.field == ...` assignments.
    pub direct_assignment_branch_solves: usize,
    /// Count of branch solves using candidate-enumeration fallback.
    pub enumeration_fallback_branch_solves: usize,
    /// Number of candidate next-state evaluations performed by fallback.
    pub enumeration_candidate_evaluations: usize,
    /// Number of candidate next-state evaluations skipped by static guard pruning.
    pub guard_pruned_candidate_evaluations: usize,
    /// Wall-clock time spent in candidate-evaluation fallback for this branch solve.
    pub enumeration_candidate_evaluation_elapsed_ms: u128,
    /// Number of next-state fields derived directly from `s_.field == expr` equalities
    /// (Phase 36.3.2 finer-grained telemetry).
    pub direct_assigned_fields: usize,
    /// Number of deferred constraint evaluations (non-next-state equalities/predicates).
    pub deferred_constraint_evaluations: usize,
    /// Total evaluator calls across all assignments for this branch solve.
    pub evaluator_calls: usize,
    /// Number of existential assignments pruned by guard-first evaluation
    /// (Phase 36.3.7.c: constraints checked before cloning next state).
    pub guard_pruned_assignments: usize,
}

/// Result payload for one branch-solve attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchSolveResult {
    pub successors: Vec<RuntimeValue>,
    pub telemetry: BranchSolveTelemetry,
}

/// Outcome of solving one existential assignment within a branch.
enum AssignmentOutcome {
    /// Assignment produced a valid successor state.
    Successor(RuntimeValue),
    /// Assignment failed a guard constraint (no s_ dependency) before
    /// cloning/constructing the next state.
    GuardPruned,
    /// Assignment failed a deferred or next-state constraint.
    ConstraintFailed,
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
    Ok(solve_branch_successors_with_candidates_and_telemetry(
        transition,
        branch,
        current_state,
        constants,
        existential_assignments,
        None,
        None,
        bounds,
        hooks,
        None,
    )?
    .successors)
}

/// Solve one normalized `LNext` branch with optional next-state candidates.
///
/// If a branch has direct `s_.* == expr` constraints, solving uses assignment-style
/// mutation from `current_state`. If not, and `next_state_candidates` is provided,
/// the solver evaluates the full branch predicate against each candidate `s_` value.
#[allow(clippy::too_many_arguments)]
pub fn solve_branch_successors_with_candidates(
    transition: &TransitionIr,
    branch: &TransitionBranchIr,
    current_state: &RuntimeValue,
    constants: Option<&RuntimeValue>,
    existential_assignments: &[ExistentialAssignment],
    next_state_candidates: Option<&[RuntimeValue]>,
    bounds: RuntimeCollectionBounds,
    hooks: SolverHooks<'_>,
) -> TranspileResult<Vec<RuntimeValue>> {
    Ok(solve_branch_successors_with_candidates_and_telemetry(
        transition,
        branch,
        current_state,
        constants,
        existential_assignments,
        next_state_candidates,
        None,
        bounds,
        hooks,
        None,
    )?
    .successors)
}

/// Same as `solve_branch_successors_with_candidates`, but returns per-branch telemetry
/// and optionally enforces a candidate-enumeration guardrail.
#[allow(clippy::too_many_arguments)]
pub fn solve_branch_successors_with_candidates_and_telemetry(
    transition: &TransitionIr,
    branch: &TransitionBranchIr,
    current_state: &RuntimeValue,
    constants: Option<&RuntimeValue>,
    existential_assignments: &[ExistentialAssignment],
    next_state_candidates: Option<&[RuntimeValue]>,
    max_candidate_evaluations_per_state_branch: Option<usize>,
    bounds: RuntimeCollectionBounds,
    hooks: SolverHooks<'_>,
    should_stop: Option<&dyn Fn() -> bool>,
) -> TranspileResult<BranchSolveResult> {
    // Candidate key set for filtering direct-assignment successors.
    // OPTIMIZATION: Defer computation until needed. For large candidate pools
    // (e.g., 1.7M for Paxos), computing canonical_key() for every candidate
    // was the dominant cost (~40s). When the predicate-only solver handles
    // the branch, this set is never needed.
    let mut candidate_state_keys: Option<BTreeSet<String>> = None;

    let assignments: Vec<ExistentialAssignment> = if existential_assignments.is_empty() {
        vec![BTreeMap::new()]
    } else {
        existential_assignments.to_vec()
    };
    for assignment in &assignments {
        if !assignment_compatible_with_branch(branch, assignment)? {
            return Err(TranspileError::Config {
                message: format!(
                    "Branch `{}` received existential assignment missing required variables.",
                    branch.label
                ),
            });
        }
    }

    let has_next_state_assignments =
        branch_has_next_state_assignment(branch, &transition.next_state_param);
    let can_use_direct_assignments = if next_state_candidates.is_some() {
        has_next_state_assignments
            && branch_assigns_all_next_state_root_fields(
                branch,
                current_state,
                &transition.next_state_param,
            )
    } else {
        // Keep standalone solver behavior (used by unit tests and non-candidate paths):
        // partial next-state assignments overlay onto the current state.
        has_next_state_assignments
    };

    if !can_use_direct_assignments {
        if let Some(predicate_only_solver) = hooks.predicate_only_branch_solver {
            if let Some(successors) = predicate_only_solver(
                transition,
                branch,
                current_state,
                constants,
                &assignments,
                bounds,
            )? {
                // OPTIMIZATION (Phase 36.3.4): Skip candidate-key filtering
                // for predicate-only solver results. The predicate-only solver
                // already produces domain-bounded successors internally
                // (existentials expanded from configured domains). Skipping
                // the filter avoids computing canonical_key() for all
                // candidates (e.g., 1.7M for Paxos, which was ~40s).
                let successors = deduplicate_successors(successors);
                let (direct_fields, deferred_evals) = count_branch_constraint_telemetry(branch);
                let assignment_count = assignments.len().max(1);
                return Ok(BranchSolveResult {
                    successors,
                    telemetry: BranchSolveTelemetry {
                        direct_assignment_branch_solves: 1,
                        direct_assigned_fields: direct_fields,
                        deferred_constraint_evaluations: deferred_evals,
                        evaluator_calls: (direct_fields + deferred_evals) * assignment_count,
                        ..Default::default()
                    },
                });
            }
        }
        if let Some(candidates) = next_state_candidates {
            let (
                successors,
                candidate_evaluations,
                guard_pruned_candidate_evaluations,
                enumeration_candidate_evaluation_elapsed_ms,
            ) = solve_branch_by_candidate_enumeration(
                transition,
                branch,
                current_state,
                constants,
                &assignments,
                candidates,
                max_candidate_evaluations_per_state_branch,
                bounds,
                hooks,
                should_stop,
            )?;
            return Ok(BranchSolveResult {
                successors,
                telemetry: BranchSolveTelemetry {
                    enumeration_fallback_branch_solves: 1,
                    enumeration_candidate_evaluations: candidate_evaluations,
                    guard_pruned_candidate_evaluations,
                    enumeration_candidate_evaluation_elapsed_ms,
                    ..Default::default()
                },
            });
        }
        return Err(unsupported_solver(
            format!(
                "branch `{}` has no direct next-state equality constraints (`s_.field == ...`)",
                branch.label
            )
            .as_str(),
            Some(
                "Inline called action predicates into equality constraints before solving, or provide candidate next-state values."
                    .to_string(),
            ),
        ));
    }

    let mut successors = Vec::new();
    let mut guard_pruned_assignments = 0usize;
    for assignment in assignments {
        if should_stop.map(|check| check()).unwrap_or(false) {
            // Lazily compute candidate keys only when needed for filtering
            if candidate_state_keys.is_none() {
                if let Some(candidates) = next_state_candidates {
                    candidate_state_keys =
                        Some(candidates.iter().map(RuntimeValue::canonical_key).collect());
                }
            }
            let successors = filter_successors_to_candidate_keys(
                deduplicate_successors(successors),
                candidate_state_keys.as_ref(),
            );
            return Ok(BranchSolveResult {
                successors,
                telemetry: BranchSolveTelemetry {
                    direct_assignment_branch_solves: 1,
                    guard_pruned_assignments,
                    ..Default::default()
                },
            });
        }
        match solve_one_assignment(
            transition,
            branch,
            current_state,
            constants,
            &assignment,
            bounds,
            hooks,
        )? {
            AssignmentOutcome::Successor(next_state) => successors.push(next_state),
            AssignmentOutcome::GuardPruned => guard_pruned_assignments += 1,
            AssignmentOutcome::ConstraintFailed => {}
        }
    }

    // Lazily compute candidate keys only when needed for filtering
    if candidate_state_keys.is_none() {
        if let Some(candidates) = next_state_candidates {
            candidate_state_keys =
                Some(candidates.iter().map(RuntimeValue::canonical_key).collect());
        }
    }
    let successors = filter_successors_to_candidate_keys(
        deduplicate_successors(successors),
        candidate_state_keys.as_ref(),
    );

    let (direct_fields, deferred_evals) = count_branch_constraint_telemetry(branch);
    let assignment_count = existential_assignments.len().max(1);
    Ok(BranchSolveResult {
        successors,
        telemetry: BranchSolveTelemetry {
            direct_assignment_branch_solves: 1,
            direct_assigned_fields: direct_fields,
            deferred_constraint_evaluations: deferred_evals,
            evaluator_calls: (direct_fields + deferred_evals) * assignment_count,
            guard_pruned_assignments,
            ..Default::default()
        },
    })
}

#[allow(clippy::too_many_arguments)]
fn solve_branch_by_candidate_enumeration(
    transition: &TransitionIr,
    branch: &TransitionBranchIr,
    current_state: &RuntimeValue,
    constants: Option<&RuntimeValue>,
    existential_assignments: &[ExistentialAssignment],
    next_state_candidates: &[RuntimeValue],
    max_candidate_evaluations_per_state_branch: Option<usize>,
    bounds: RuntimeCollectionBounds,
    hooks: SolverHooks<'_>,
    should_stop: Option<&dyn Fn() -> bool>,
) -> TranspileResult<(Vec<RuntimeValue>, usize, usize, u128)> {
    let started = Instant::now();
    let assignments: Vec<ExistentialAssignment> = if existential_assignments.is_empty() {
        vec![BTreeMap::new()]
    } else {
        existential_assignments.to_vec()
    };
    let (candidate_independent_constraints, candidate_dependent_constraints): (
        Vec<&BranchConstraintIr>,
        Vec<&BranchConstraintIr>,
    ) = branch
        .constraints
        .iter()
        .partition(|constraint| !constraint_depends_on_next_state(constraint, transition));

    let mut successors = Vec::new();
    let mut candidate_evaluations = 0usize;
    let mut guard_pruned_candidate_evaluations = 0usize;
    for assignment in assignments {
        if should_stop.map(|check| check()).unwrap_or(false) {
            return Ok((
                deduplicate_successors(successors),
                candidate_evaluations,
                guard_pruned_candidate_evaluations,
                started.elapsed().as_millis(),
            ));
        }
        if !assignment_compatible_with_branch(branch, &assignment)? {
            return Err(TranspileError::Config {
                message: format!(
                    "Branch `{}` received existential assignment missing required variables.",
                    branch.label
                ),
            });
        }

        let env_without_next =
            build_environment(transition, current_state, None, constants, &assignment);
        let mut static_guard_enabled = true;
        for constraint in &candidate_independent_constraints {
            if !evaluate_constraint(constraint, &env_without_next, bounds, hooks)? {
                static_guard_enabled = false;
                break;
            }
        }
        if !static_guard_enabled {
            guard_pruned_candidate_evaluations =
                guard_pruned_candidate_evaluations.saturating_add(next_state_candidates.len());
            continue;
        }

        if candidate_dependent_constraints.is_empty() {
            candidate_evaluations =
                candidate_evaluations.saturating_add(next_state_candidates.len());
            if let Some(limit) = max_candidate_evaluations_per_state_branch {
                if candidate_evaluations > limit {
                    return Err(TranspileError::Config {
                        message: format!(
                            "Model-check candidate-enumeration guardrail exceeded for branch `{}`: \
                             evaluated {} candidate next-states for a single explored state/branch \
                             (limit = {}). Reduce candidate-state domains, inline direct `s_.field == ...` \
                             constraints, or simplify predicate-only helper branches.",
                            branch.label, candidate_evaluations, limit
                        ),
                    });
                }
            }
            successors.extend(next_state_candidates.iter().cloned());
            continue;
        }

        for candidate_next_state in next_state_candidates {
            if should_stop.map(|check| check()).unwrap_or(false) {
                return Ok((
                    deduplicate_successors(successors),
                    candidate_evaluations,
                    guard_pruned_candidate_evaluations,
                    started.elapsed().as_millis(),
                ));
            }
            candidate_evaluations += 1;
            if let Some(limit) = max_candidate_evaluations_per_state_branch {
                if candidate_evaluations > limit {
                    return Err(TranspileError::Config {
                        message: format!(
                            "Model-check candidate-enumeration guardrail exceeded for branch `{}`: \
                             evaluated {} candidate next-states for a single explored state/branch \
                             (limit = {}). Reduce candidate-state domains, inline direct `s_.field == ...` \
                             constraints, or simplify predicate-only helper branches.",
                            branch.label, candidate_evaluations, limit
                        ),
                    });
                }
            }
            let env = build_environment(
                transition,
                current_state,
                Some(candidate_next_state),
                constants,
                &assignment,
            );

            let mut enabled = true;
            for constraint in &candidate_dependent_constraints {
                if !evaluate_constraint(constraint, &env, bounds, hooks)? {
                    enabled = false;
                    break;
                }
            }
            if enabled {
                successors.push(candidate_next_state.clone());
            }
        }
    }

    Ok((
        deduplicate_successors(successors),
        candidate_evaluations,
        guard_pruned_candidate_evaluations,
        started.elapsed().as_millis(),
    ))
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
    solve_transition_successors_with_semantics(
        transition,
        current_state,
        constants,
        existential_assignments_by_branch,
        bounds,
        hooks,
        EmptySuccessorSemantics::Deadlock,
    )
}

/// Solve all `LNext` branches with explicit empty-successor semantics.
pub fn solve_transition_successors_with_semantics(
    transition: &TransitionIr,
    current_state: &RuntimeValue,
    constants: Option<&RuntimeValue>,
    existential_assignments_by_branch: Option<&BTreeMap<String, Vec<ExistentialAssignment>>>,
    bounds: RuntimeCollectionBounds,
    hooks: SolverHooks<'_>,
    empty_successor_semantics: EmptySuccessorSemantics,
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

    let mut deduplicated = deduplicate_successors(successors);
    if deduplicated.is_empty()
        && matches!(
            empty_successor_semantics,
            EmptySuccessorSemantics::Stuttering
        )
    {
        deduplicated.push(current_state.clone());
    }
    Ok(deduplicated)
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

/// Count structural telemetry from a branch's constraint set.
fn count_branch_constraint_telemetry(branch: &TransitionBranchIr) -> (usize, usize) {
    let mut direct_assigned = 0usize;
    let mut deferred = 0usize;
    for constraint in &branch.constraints {
        match constraint {
            BranchConstraintIr::Eq {
                target:
                    ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        ..
                    },
                ..
            } => {
                direct_assigned += 1;
            }
            BranchConstraintIr::Predicate { expr } => {
                if next_state_variant_assignment(expr, "s_").is_some() {
                    direct_assigned += 1;
                } else {
                    deferred += 1;
                }
            }
            _ => {
                deferred += 1;
            }
        }
    }
    (direct_assigned, deferred)
}

/// Detect if a constraint is a frame condition: `s_.path == s.path`.
///
/// A frame condition assigns the next-state field to the same field of the
/// current state. Since `next_state` starts as `current_state.clone()`, these
/// are tautological and can be skipped to avoid unnecessary evaluator calls.
///
/// Returns true if the constraint is `Eq { target: NextState(path), value }`
/// where `value` is a simple field access `current_state_param.path`.
fn is_frame_condition(target_path: &[String], value: &Expr, current_state_param: &str) -> bool {
    // Extract segments from the value expression (e.g., `s.field` → ["s", "field"])
    fn extract_expr_segments(expr: &Expr) -> Option<Vec<String>> {
        match expr {
            Expr::Ident(name) => Some(vec![name.clone()]),
            Expr::Field(base, field) | Expr::Arrow(base, field) => {
                let mut segments = extract_expr_segments(base)?;
                segments.push(field.clone());
                Some(segments)
            }
            _ => None,
        }
    }

    let Some(segments) = extract_expr_segments(value) else {
        return false;
    };
    if segments.is_empty() {
        return false;
    }
    // First segment must be the current state parameter
    if segments[0] != current_state_param {
        return false;
    }
    // Remaining segments must match the target path exactly
    segments[1..] == *target_path
}

fn filter_successors_to_candidate_keys(
    successors: Vec<RuntimeValue>,
    candidate_state_keys: Option<&BTreeSet<String>>,
) -> Vec<RuntimeValue> {
    let Some(candidate_state_keys) = candidate_state_keys else {
        return successors;
    };
    successors
        .into_iter()
        .filter(|state| candidate_state_keys.contains(&state.canonical_key()))
        .collect()
}

fn solve_one_assignment(
    transition: &TransitionIr,
    branch: &TransitionBranchIr,
    current_state: &RuntimeValue,
    constants: Option<&RuntimeValue>,
    existential_assignment: &ExistentialAssignment,
    bounds: RuntimeCollectionBounds,
    hooks: SolverHooks<'_>,
) -> TranspileResult<AssignmentOutcome> {
    // Phase 36.3.7.c: Guard-first evaluation — check constraints that depend
    // only on the current state + existential params (not s_) BEFORE cloning
    // current_state and processing assignments. For branches where most
    // existential assignments fail the guard, this avoids the expensive
    // clone + evaluate cycle entirely.
    let (guard_constraints, non_guard_constraints): (Vec<_>, Vec<_>) = branch
        .constraints
        .iter()
        .partition(|c| !constraint_depends_on_next_state(c, transition));

    if !guard_constraints.is_empty() {
        let guard_env = build_environment(
            transition,
            current_state,
            None, // no s_ needed for guard constraints
            constants,
            existential_assignment,
        );
        for constraint in &guard_constraints {
            let satisfied = evaluate_constraint(constraint, &guard_env, bounds, hooks)?;
            if !satisfied {
                return Ok(AssignmentOutcome::GuardPruned);
            }
        }
    }

    // Guards passed — now proceed with next-state construction.
    let mut next_state = current_state.clone();
    let mut deferred_constraints = Vec::new();
    let mut next_state_targets: BTreeMap<Vec<String>, RuntimeValue> = BTreeMap::new();

    for constraint in &non_guard_constraints {
        match constraint {
            BranchConstraintIr::Eq {
                target:
                    ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path,
                    },
                value,
            } => {
                // Frame-condition optimization (Phase 36.3.5): skip `s_.f == s.f`
                // since next_state starts as current_state.clone(), making these
                // tautological. This avoids building the environment, evaluating
                // the expression, and writing the value.
                if is_frame_condition(path, value, &transition.current_state_param) {
                    continue;
                }

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
                        return Ok(AssignmentOutcome::ConstraintFailed);
                    }
                } else {
                    write_value_at_path(&mut next_state, path, evaluated.clone())?;
                    next_state_targets.insert(path.clone(), evaluated);
                }
            }
            BranchConstraintIr::Predicate { expr } => {
                if let Some((path, variant)) =
                    next_state_variant_assignment(expr, &transition.next_state_param)
                {
                    let assigned =
                        enum_variant_assignment_value(&next_state, &path, &variant, &branch.label)?;
                    if let Some(existing) = next_state_targets.get(&path) {
                        if existing != &assigned {
                            return Ok(AssignmentOutcome::ConstraintFailed);
                        }
                    } else {
                        write_value_at_path(&mut next_state, &path, assigned.clone())?;
                        next_state_targets.insert(path, assigned);
                    }
                } else {
                    deferred_constraints.push(constraint);
                }
            }
            BranchConstraintIr::Eq { .. } => deferred_constraints.push(constraint),
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
            return Ok(AssignmentOutcome::ConstraintFailed);
        }
    }

    Ok(AssignmentOutcome::Successor(next_state))
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
    if let Some(quantifier_domain_evaluator) = hooks.quantifier_domain_evaluator {
        ctx = ctx.with_quantifier_domain_evaluator(quantifier_domain_evaluator);
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

fn branch_has_next_state_assignment(branch: &TransitionBranchIr, next_state_param: &str) -> bool {
    branch
        .constraints
        .iter()
        .any(|constraint| match constraint {
            BranchConstraintIr::Eq {
                target:
                    ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        ..
                    },
                ..
            } => true,
            BranchConstraintIr::Predicate { expr } => {
                next_state_variant_assignment(expr, next_state_param).is_some()
            }
            _ => false,
        })
}

fn branch_assigns_all_next_state_root_fields(
    branch: &TransitionBranchIr,
    current_state: &RuntimeValue,
    next_state_param: &str,
) -> bool {
    let required_fields = match current_state {
        RuntimeValue::Struct { fields, .. } | RuntimeValue::Enum { fields, .. } => {
            fields.keys().cloned().collect::<BTreeSet<String>>()
        }
        _ => return true,
    };
    if required_fields.is_empty() {
        return true;
    }

    let mut assigned_fields = BTreeSet::<String>::new();
    for constraint in &branch.constraints {
        match constraint {
            BranchConstraintIr::Eq {
                target:
                    ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path,
                    },
                ..
            } => {
                if path.is_empty() {
                    return true;
                }
                assigned_fields.insert(path[0].clone());
            }
            BranchConstraintIr::Predicate { expr } => {
                let Some((path, _variant)) = next_state_variant_assignment(expr, next_state_param)
                else {
                    continue;
                };
                if path.is_empty() {
                    return true;
                }
                assigned_fields.insert(path[0].clone());
            }
            _ => {}
        }
    }

    required_fields.is_subset(&assigned_fields)
}

fn enum_variant_assignment_value(
    next_state: &RuntimeValue,
    path: &[String],
    variant: &str,
    branch_label: &str,
) -> TranspileResult<RuntimeValue> {
    let current = read_value_at_path(next_state, path)?;
    match current {
        RuntimeValue::Enum { ty, fields, .. } => Ok(RuntimeValue::Enum {
            ty,
            variant: variant.to_string(),
            fields,
        }),
        other => Err(TranspileError::Config {
            message: format!(
                "Failed to evaluate enum-variant next-state assignment in branch `{}` at `s_.{}`: \
                 `is` target is not an enum value (`{}`).",
                branch_label,
                join_path(path),
                other.canonical_key()
            ),
        }),
    }
}

fn next_state_variant_assignment(
    expr: &Expr,
    next_state_param: &str,
) -> Option<(Vec<String>, String)> {
    let Expr::Is(base, variant) = expr else {
        return None;
    };
    let (root, path) = extract_identifier_path(base)?;
    if root != next_state_param {
        return None;
    }
    Some((path, variant.clone()))
}

fn extract_identifier_path(expr: &Expr) -> Option<(String, Vec<String>)> {
    match expr {
        Expr::Ident(name) => Some((name.clone(), Vec::new())),
        Expr::Field(base, field) | Expr::Arrow(base, field) => {
            let (root, mut path) = extract_identifier_path(base)?;
            path.push(field.clone());
            Some((root, path))
        }
        _ => None,
    }
}

fn constraint_depends_on_next_state(
    constraint: &BranchConstraintIr,
    transition: &TransitionIr,
) -> bool {
    match constraint {
        BranchConstraintIr::Eq { target, value } => {
            if matches!(target.root, ConstraintRoot::NextState) {
                return true;
            }
            expr_mentions_identifier(value, &transition.next_state_param)
        }
        BranchConstraintIr::Predicate { expr } => {
            expr_mentions_identifier(expr, &transition.next_state_param)
        }
    }
}

fn expr_mentions_identifier(expr: &Expr, ident: &str) -> bool {
    match expr {
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
        | Expr::Index(lhs, rhs)
        | Expr::Binary(lhs, _, rhs) => {
            expr_mentions_identifier(lhs, ident) || expr_mentions_identifier(rhs, ident)
        }
        Expr::Not(inner) | Expr::View(inner) | Expr::Cast(inner, _) | Expr::Unary(_, inner) => {
            expr_mentions_identifier(inner, ident)
        }
        Expr::Forall { body, triggers, .. } => {
            expr_mentions_identifier(body, ident)
                || triggers
                    .iter()
                    .flat_map(|trigger| trigger.exprs.iter())
                    .any(|trigger_expr| expr_mentions_identifier(trigger_expr, ident))
        }
        Expr::Exists { body, .. } | Expr::Closure { body, .. } => {
            expr_mentions_identifier(body, ident)
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            expr_mentions_identifier(cond, ident)
                || expr_mentions_identifier(then_branch, ident)
                || else_branch
                    .as_ref()
                    .map(|branch| expr_mentions_identifier(branch, ident))
                    .unwrap_or(false)
        }
        Expr::Match { scrutinee, arms } => {
            expr_mentions_identifier(scrutinee, ident)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .map(|guard| expr_mentions_identifier(guard, ident))
                        .unwrap_or(false)
                        || expr_mentions_identifier(&arm.body, ident)
                })
        }
        Expr::Let { value, body, .. } => {
            expr_mentions_identifier(value, ident) || expr_mentions_identifier(body, ident)
        }
        Expr::Is(base, _) | Expr::Field(base, _) | Expr::Arrow(base, _) => {
            expr_mentions_identifier(base, ident)
        }
        Expr::Struct { fields, .. } => fields
            .iter()
            .any(|(_, field_expr)| expr_mentions_identifier(field_expr, ident)),
        Expr::StructUpdate { base, fields, .. } => {
            expr_mentions_identifier(base, ident)
                || fields
                    .iter()
                    .any(|(_, field_expr)| expr_mentions_identifier(field_expr, ident))
        }
        Expr::SeqLit(items) | Expr::SetLit(items) => items
            .iter()
            .any(|item| expr_mentions_identifier(item, ident)),
        Expr::MapLit(items) => items.iter().any(|(key, value)| {
            expr_mentions_identifier(key, ident) || expr_mentions_identifier(value, ident)
        }),
        Expr::Call { args, .. } => args.iter().any(|arg| expr_mentions_identifier(arg, ident)),
        Expr::MethodCall { receiver, args, .. } => {
            expr_mentions_identifier(receiver, ident)
                || args.iter().any(|arg| expr_mentions_identifier(arg, ident))
        }
        Expr::Ident(name) => name == ident,
        Expr::SeqEmpty | Expr::SetEmpty | Expr::MapEmpty | Expr::Literal(_) => false,
    }
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
    use crate::ast::{BinOp, Expr, Path};
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

    fn phase_state(phase_variant: &str, value: i128) -> RuntimeValue {
        RuntimeValue::struct_value(
            "LState",
            vec![
                (
                    "phase".to_string(),
                    RuntimeValue::enum_value(
                        "LPhase",
                        phase_variant.to_string(),
                        Vec::<(String, RuntimeValue)>::new(),
                    )
                    .unwrap(),
                ),
                ("value".to_string(), RuntimeValue::Int(value)),
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
    fn test_solve_branch_successors_applies_next_state_enum_variant_constraint() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![
                BranchConstraintIr::Eq {
                    target: ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path: vec!["value".to_string()],
                    },
                    value: Expr::Literal(crate::ast::Literal::Int(1)),
                },
                BranchConstraintIr::Predicate {
                    expr: Expr::Is(
                        Box::new(Expr::Field(
                            Box::new(Expr::Ident("s_".to_string())),
                            "phase".to_string(),
                        )),
                        "Phase1".to_string(),
                    ),
                },
            ],
        };

        let successors = solve_branch_successors(
            &transition(),
            &branch,
            &phase_state("Idle", 0),
            Some(&constants(10)),
            &[],
            bounds(),
            SolverHooks::default(),
        )
        .unwrap();
        assert_eq!(successors.len(), 1);
        assert_eq!(
            read_value_at_path(&successors[0], &[String::from("phase")]).unwrap(),
            RuntimeValue::enum_value(
                "LPhase",
                "Phase1".to_string(),
                Vec::<(String, RuntimeValue)>::new()
            )
            .unwrap()
        );
        assert_eq!(
            read_value_at_path(&successors[0], &[String::from("value")]).unwrap(),
            RuntimeValue::Int(1)
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
    fn test_solve_transition_successors_deadlock_semantics_keeps_empty() {
        let mut transition = transition();
        transition.branches = vec![TransitionBranchIr {
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
                BranchConstraintIr::Predicate {
                    expr: Expr::Literal(crate::ast::Literal::Bool(false)),
                },
            ],
        }];

        let successors = solve_transition_successors_with_semantics(
            &transition,
            &state(0, 0),
            Some(&constants(10)),
            None,
            bounds(),
            SolverHooks::default(),
            EmptySuccessorSemantics::Deadlock,
        )
        .unwrap();
        assert!(successors.is_empty());
    }

    #[test]
    fn test_solve_transition_successors_stuttering_semantics_adds_self_loop() {
        let mut transition = transition();
        transition.branches = vec![TransitionBranchIr {
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
                BranchConstraintIr::Predicate {
                    expr: Expr::Literal(crate::ast::Literal::Bool(false)),
                },
            ],
        }];

        let current = state(4, 7);
        let successors = solve_transition_successors_with_semantics(
            &transition,
            &current,
            Some(&constants(10)),
            None,
            bounds(),
            SolverHooks::default(),
            EmptySuccessorSemantics::Stuttering,
        )
        .unwrap();
        assert_eq!(successors, vec![current]);
    }

    #[test]
    fn test_solve_branch_successors_with_candidates_supports_predicate_only_branch() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![BranchConstraintIr::Predicate {
                expr: Expr::Call {
                    func: Path::single("LHelper".to_string()),
                    args: vec![Expr::Ident("s".to_string()), Expr::Ident("s_".to_string())],
                },
            }],
        };
        let candidate_next_states = vec![state(0, 0), state(1, 0)];
        let call_hook = |func: &Path, args: &[RuntimeValue]| -> TranspileResult<RuntimeValue> {
            if func.last() == Some("LHelper") {
                let candidate_x = read_value_at_path(&args[1], &[String::from("x")])?;
                return Ok(RuntimeValue::Bool(candidate_x == RuntimeValue::Int(1)));
            }
            Err(unsupported_solver(
                "Unexpected helper call in solver test",
                None,
            ))
        };
        let hooks = SolverHooks {
            call_evaluator: Some(&call_hook),
            method_evaluator: None,
            quantifier_domain_evaluator: None,
            predicate_only_branch_solver: None,
        };

        let successors = solve_branch_successors_with_candidates(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[],
            Some(&candidate_next_states),
            bounds(),
            hooks,
        )
        .unwrap();
        assert_eq!(successors, vec![state(1, 0)]);
    }

    #[test]
    fn test_solve_branch_successors_with_candidates_reports_enumeration_telemetry() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![BranchConstraintIr::Predicate {
                expr: Expr::Call {
                    func: Path::single("LHelper".to_string()),
                    args: vec![Expr::Ident("s".to_string()), Expr::Ident("s_".to_string())],
                },
            }],
        };
        let candidate_next_states = vec![state(0, 0), state(1, 0)];
        let call_hook = |func: &Path, args: &[RuntimeValue]| -> TranspileResult<RuntimeValue> {
            if func.last() == Some("LHelper") {
                let candidate_x = read_value_at_path(&args[1], &[String::from("x")])?;
                return Ok(RuntimeValue::Bool(candidate_x == RuntimeValue::Int(1)));
            }
            Err(unsupported_solver(
                "Unexpected helper call in solver test",
                None,
            ))
        };
        let hooks = SolverHooks {
            call_evaluator: Some(&call_hook),
            method_evaluator: None,
            quantifier_domain_evaluator: None,
            predicate_only_branch_solver: None,
        };

        let result = solve_branch_successors_with_candidates_and_telemetry(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[],
            Some(&candidate_next_states),
            None,
            bounds(),
            hooks,
            None,
        )
        .unwrap();

        assert_eq!(result.successors, vec![state(1, 0)]);
        assert_eq!(result.telemetry.direct_assignment_branch_solves, 0);
        assert_eq!(result.telemetry.enumeration_fallback_branch_solves, 1);
        assert_eq!(result.telemetry.enumeration_candidate_evaluations, 2);
        assert_eq!(result.telemetry.guard_pruned_candidate_evaluations, 0);
    }

    #[test]
    fn test_solve_branch_successors_with_candidates_enforces_enumeration_guardrail() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![BranchConstraintIr::Predicate {
                expr: Expr::Literal(crate::ast::Literal::Bool(true)),
            }],
        };
        let candidate_next_states = vec![state(0, 0), state(1, 0)];

        let err = solve_branch_successors_with_candidates_and_telemetry(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[],
            Some(&candidate_next_states),
            Some(1),
            bounds(),
            SolverHooks::default(),
            None,
        )
        .unwrap_err();

        assert!(err
            .to_string()
            .contains("candidate-enumeration guardrail exceeded"));
        assert!(err.to_string().contains("branch_0"));
        assert!(err.to_string().contains("limit = 1"));
    }

    #[test]
    fn test_solve_branch_successors_with_candidates_prunes_static_guard() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![
                BranchConstraintIr::Predicate {
                    expr: Expr::Eq(
                        Box::new(Expr::Field(
                            Box::new(Expr::Ident("s".to_string())),
                            "x".to_string(),
                        )),
                        Box::new(Expr::Literal(crate::ast::Literal::Int(1))),
                    ),
                },
                BranchConstraintIr::Predicate {
                    expr: Expr::Call {
                        func: Path::single("LHelper".to_string()),
                        args: vec![Expr::Ident("s".to_string()), Expr::Ident("s_".to_string())],
                    },
                },
            ],
        };
        let candidate_next_states = vec![state(0, 0), state(1, 0)];
        let helper_call_count = AtomicUsize::new(0);
        let call_hook = |func: &Path, _args: &[RuntimeValue]| -> TranspileResult<RuntimeValue> {
            if func.last() == Some("LHelper") {
                helper_call_count.fetch_add(1, Ordering::Relaxed);
                return Ok(RuntimeValue::Bool(true));
            }
            Err(unsupported_solver(
                "Unexpected helper call in solver test",
                None,
            ))
        };
        let hooks = SolverHooks {
            call_evaluator: Some(&call_hook),
            method_evaluator: None,
            quantifier_domain_evaluator: None,
            predicate_only_branch_solver: None,
        };

        let result = solve_branch_successors_with_candidates_and_telemetry(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[],
            Some(&candidate_next_states),
            None,
            bounds(),
            hooks,
            None,
        )
        .unwrap();

        assert!(result.successors.is_empty());
        assert_eq!(result.telemetry.direct_assignment_branch_solves, 0);
        assert_eq!(result.telemetry.enumeration_fallback_branch_solves, 1);
        assert_eq!(result.telemetry.enumeration_candidate_evaluations, 0);
        assert_eq!(result.telemetry.guard_pruned_candidate_evaluations, 2);
        assert_eq!(helper_call_count.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn test_solve_branch_successors_with_candidates_honors_stop_callback_mid_enumeration() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![BranchConstraintIr::Predicate {
                expr: Expr::Call {
                    func: Path::single("LHelper".to_string()),
                    args: vec![Expr::Ident("s".to_string()), Expr::Ident("s_".to_string())],
                },
            }],
        };
        let candidate_next_states = vec![state(0, 0), state(1, 0), state(2, 0)];
        let call_hook = |func: &Path, _args: &[RuntimeValue]| -> TranspileResult<RuntimeValue> {
            if func.last() == Some("LHelper") {
                return Ok(RuntimeValue::Bool(true));
            }
            Err(unsupported_solver(
                "Unexpected helper call in solver test",
                None,
            ))
        };
        let hooks = SolverHooks {
            call_evaluator: Some(&call_hook),
            method_evaluator: None,
            quantifier_domain_evaluator: None,
            predicate_only_branch_solver: None,
        };
        let stop_checks = AtomicUsize::new(0);
        let stop_after_first_candidate = || stop_checks.fetch_add(1, Ordering::Relaxed) >= 2;

        let result = solve_branch_successors_with_candidates_and_telemetry(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[],
            Some(&candidate_next_states),
            None,
            bounds(),
            hooks,
            Some(&stop_after_first_candidate),
        )
        .unwrap();

        assert_eq!(result.successors, vec![state(0, 0)]);
        assert_eq!(result.telemetry.direct_assignment_branch_solves, 0);
        assert_eq!(result.telemetry.enumeration_fallback_branch_solves, 1);
        assert_eq!(result.telemetry.enumeration_candidate_evaluations, 1);
        assert_eq!(result.telemetry.guard_pruned_candidate_evaluations, 0);
    }

    #[test]
    fn test_solve_branch_successors_with_direct_predicate_only_solver_hook() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![BranchConstraintIr::Predicate {
                expr: Expr::Call {
                    func: Path::single("LHelper".to_string()),
                    args: vec![Expr::Ident("s".to_string()), Expr::Ident("s_".to_string())],
                },
            }],
        };

        let predicate_only_solver = |_transition: &TransitionIr,
                                     _branch: &TransitionBranchIr,
                                     _current_state: &RuntimeValue,
                                     _constants: Option<&RuntimeValue>,
                                     _existentials: &[ExistentialAssignment],
                                     _bounds: RuntimeCollectionBounds|
         -> TranspileResult<Option<Vec<RuntimeValue>>> {
            Ok(Some(vec![state(9, 9)]))
        };
        let hooks = SolverHooks {
            call_evaluator: None,
            method_evaluator: None,
            quantifier_domain_evaluator: None,
            predicate_only_branch_solver: Some(&predicate_only_solver),
        };

        let result = solve_branch_successors_with_candidates_and_telemetry(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[],
            None,
            None,
            bounds(),
            hooks,
            None,
        )
        .unwrap();

        assert_eq!(result.successors, vec![state(9, 9)]);
        assert_eq!(result.telemetry.direct_assignment_branch_solves, 1);
        assert_eq!(result.telemetry.enumeration_fallback_branch_solves, 0);
        assert_eq!(result.telemetry.enumeration_candidate_evaluations, 0);
        assert_eq!(result.telemetry.guard_pruned_candidate_evaluations, 0);
    }

    #[test]
    fn test_direct_assignment_solver_respects_candidate_state_filter() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![
                BranchConstraintIr::Eq {
                    target: ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path: vec!["x".to_string()],
                    },
                    value: Expr::Literal(crate::ast::Literal::Int(9)),
                },
                BranchConstraintIr::Eq {
                    target: ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path: vec!["y".to_string()],
                    },
                    value: Expr::Literal(crate::ast::Literal::Int(9)),
                },
            ],
        };
        let candidates = vec![state(0, 0), state(1, 0)];

        let result = solve_branch_successors_with_candidates_and_telemetry(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[],
            Some(&candidates),
            None,
            bounds(),
            SolverHooks::default(),
            None,
        )
        .unwrap();

        assert!(result.successors.is_empty());
        assert_eq!(result.telemetry.direct_assignment_branch_solves, 1);
    }

    #[test]
    fn test_direct_assignment_solver_treats_next_state_is_as_assignment_with_candidates() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![
                BranchConstraintIr::Eq {
                    target: ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path: vec!["value".to_string()],
                    },
                    value: Expr::Literal(crate::ast::Literal::Int(1)),
                },
                BranchConstraintIr::Predicate {
                    expr: Expr::Is(
                        Box::new(Expr::Field(
                            Box::new(Expr::Ident("s_".to_string())),
                            "phase".to_string(),
                        )),
                        "Phase1".to_string(),
                    ),
                },
            ],
        };
        let candidates = vec![phase_state("Phase1", 1), phase_state("Idle", 1)];

        let result = solve_branch_successors_with_candidates_and_telemetry(
            &transition(),
            &branch,
            &phase_state("Idle", 0),
            Some(&constants(10)),
            &[],
            Some(&candidates),
            None,
            bounds(),
            SolverHooks::default(),
            None,
        )
        .unwrap();

        assert_eq!(result.successors, vec![phase_state("Phase1", 1)]);
        assert_eq!(result.telemetry.direct_assignment_branch_solves, 1);
        assert_eq!(result.telemetry.enumeration_fallback_branch_solves, 0);
        assert_eq!(result.telemetry.enumeration_candidate_evaluations, 0);
    }

    #[test]
    fn test_predicate_only_solver_hook_skips_candidate_filter() {
        // OPTIMIZATION (Phase 36.3.4): The predicate-only solver path
        // skips candidate-key filtering. Successors are returned as-is
        // (after deduplication) to avoid computing canonical_key() for
        // all candidates (which was the dominant cost for large pools).
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![BranchConstraintIr::Predicate {
                expr: Expr::Call {
                    func: Path::single("LHelper".to_string()),
                    args: vec![Expr::Ident("s".to_string()), Expr::Ident("s_".to_string())],
                },
            }],
        };
        let candidates = vec![state(1, 0)];
        let predicate_only_solver = |_transition: &TransitionIr,
                                     _branch: &TransitionBranchIr,
                                     _current_state: &RuntimeValue,
                                     _constants: Option<&RuntimeValue>,
                                     _existentials: &[ExistentialAssignment],
                                     _bounds: RuntimeCollectionBounds|
         -> TranspileResult<Option<Vec<RuntimeValue>>> {
            Ok(Some(vec![state(9, 9), state(1, 0)]))
        };
        let hooks = SolverHooks {
            call_evaluator: None,
            method_evaluator: None,
            quantifier_domain_evaluator: None,
            predicate_only_branch_solver: Some(&predicate_only_solver),
        };

        let result = solve_branch_successors_with_candidates_and_telemetry(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[],
            Some(&candidates),
            None,
            bounds(),
            hooks,
            None,
        )
        .unwrap();

        // Both successors returned — predicate-only solver skips candidate filter
        assert_eq!(result.successors.len(), 2);
        assert!(result.successors.contains(&state(1, 0)));
        assert!(result.successors.contains(&state(9, 9)));
        assert_eq!(result.telemetry.direct_assignment_branch_solves, 1);
    }

    #[test]
    fn test_partial_next_state_assignments_fall_back_to_candidate_enumeration() {
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![BranchConstraintIr::Eq {
                target: ConstraintTarget {
                    root: ConstraintRoot::NextState,
                    path: vec!["x".to_string()],
                },
                value: Expr::Literal(crate::ast::Literal::Int(1)),
            }],
        };
        let candidates = vec![state(1, 0), state(1, 1), state(0, 0)];

        let result = solve_branch_successors_with_candidates_and_telemetry(
            &transition(),
            &branch,
            &state(0, 0),
            Some(&constants(10)),
            &[],
            Some(&candidates),
            None,
            bounds(),
            SolverHooks::default(),
            None,
        )
        .unwrap();

        assert_eq!(result.successors, vec![state(1, 0), state(1, 1)]);
        assert_eq!(result.telemetry.direct_assignment_branch_solves, 0);
        assert_eq!(result.telemetry.enumeration_fallback_branch_solves, 1);
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

    #[test]
    fn test_is_frame_condition_simple_field() {
        // s_.x == s.x → frame condition
        let path = vec!["x".to_string()];
        let value = Expr::Field(Box::new(Expr::Ident("s".to_string())), "x".to_string());
        assert!(is_frame_condition(&path, &value, "s"));
    }

    #[test]
    fn test_is_frame_condition_nested_field() {
        // s_.inner.count == s.inner.count → frame condition
        let path = vec!["inner".to_string(), "count".to_string()];
        let value = Expr::Field(
            Box::new(Expr::Field(
                Box::new(Expr::Ident("s".to_string())),
                "inner".to_string(),
            )),
            "count".to_string(),
        );
        assert!(is_frame_condition(&path, &value, "s"));
    }

    #[test]
    fn test_is_frame_condition_not_frame_different_field() {
        // s_.x == s.y → NOT a frame condition
        let path = vec!["x".to_string()];
        let value = Expr::Field(Box::new(Expr::Ident("s".to_string())), "y".to_string());
        assert!(!is_frame_condition(&path, &value, "s"));
    }

    #[test]
    fn test_is_frame_condition_not_frame_complex_expr() {
        // s_.x == s.x + 1 → NOT a frame condition (complex expression)
        let path = vec!["x".to_string()];
        let value = Expr::Binary(
            Box::new(Expr::Field(
                Box::new(Expr::Ident("s".to_string())),
                "x".to_string(),
            )),
            BinOp::Add,
            Box::new(Expr::Literal(crate::ast::Literal::Int(1))),
        );
        assert!(!is_frame_condition(&path, &value, "s"));
    }

    #[test]
    fn test_is_frame_condition_wrong_root() {
        // s_.x == c.x → NOT a frame condition (constants, not current state)
        let path = vec!["x".to_string()];
        let value = Expr::Field(Box::new(Expr::Ident("c".to_string())), "x".to_string());
        assert!(!is_frame_condition(&path, &value, "s"));
    }

    #[test]
    fn test_guard_first_prunes_assignments_before_cloning() {
        // Branch with: s_.x == 99, s_.y == s.y (frame), AND a guard `s.x > c.limit`
        // The guard only references s and c, not s_. When the guard fails
        // (s.x=4, c.limit=10 → 4 > 10 is false), the assignment should be
        // guard-pruned without cloning current_state.
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![],
            constraints: vec![
                // Guard: s.x > c.limit (no s_ dependency)
                BranchConstraintIr::Predicate {
                    expr: Expr::Gt(
                        Box::new(Expr::Field(
                            Box::new(Expr::Ident("s".to_string())),
                            "x".to_string(),
                        )),
                        Box::new(Expr::Field(
                            Box::new(Expr::Ident("c".to_string())),
                            "limit".to_string(),
                        )),
                    ),
                },
                // Assignment: s_.x == 99
                BranchConstraintIr::Eq {
                    target: ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path: vec!["x".to_string()],
                    },
                    value: Expr::Literal(crate::ast::Literal::Int(99)),
                },
                // Frame: s_.y == s.y
                BranchConstraintIr::Eq {
                    target: ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path: vec!["y".to_string()],
                    },
                    value: Expr::Field(Box::new(Expr::Ident("s".to_string())), "y".to_string()),
                },
            ],
        };

        let transition_ir = TransitionIr {
            current_state_param: "s".to_string(),
            next_state_param: "s_".to_string(),
            constants_param: Some("c".to_string()),
            branches: vec![branch.clone()],
        };

        // s.x=4, c.limit=10 → guard fails (4 > 10 is false)
        let current = state(4, 7);
        let result = solve_one_assignment(
            &transition_ir,
            &branch,
            &current,
            Some(&constants(10)),
            &BTreeMap::new(),
            bounds(),
            SolverHooks::default(),
        )
        .unwrap();
        assert!(
            matches!(result, AssignmentOutcome::GuardPruned),
            "Expected GuardPruned when s.x < c.limit"
        );

        // s.x=20, c.limit=10 → guard passes (20 > 10), produces successor
        let current_pass = state(20, 7);
        let result = solve_one_assignment(
            &transition_ir,
            &branch,
            &current_pass,
            Some(&constants(10)),
            &BTreeMap::new(),
            bounds(),
            SolverHooks::default(),
        )
        .unwrap();
        assert!(
            matches!(result, AssignmentOutcome::Successor(_)),
            "Expected Successor when s.x > c.limit"
        );
        if let AssignmentOutcome::Successor(next) = result {
            assert_eq!(
                read_value_at_path(&next, &["x".to_string()]).unwrap(),
                RuntimeValue::Int(99)
            );
            assert_eq!(
                read_value_at_path(&next, &["y".to_string()]).unwrap(),
                RuntimeValue::Int(7)
            );
        }
    }

    #[test]
    fn test_guard_first_telemetry_in_branch_solve() {
        // Branch with a guard that always fails: 3 existential assignments should
        // all be guard-pruned, producing 0 successors and guard_pruned_assignments=3.
        let branch = TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vec![crate::modelcheck::ir::ExistentialVarIr {
                name: "v".to_string(),
                ty: None,
            }],
            constraints: vec![
                // Guard: s.x > 100 (always fails for s.x=4)
                BranchConstraintIr::Predicate {
                    expr: Expr::Gt(
                        Box::new(Expr::Field(
                            Box::new(Expr::Ident("s".to_string())),
                            "x".to_string(),
                        )),
                        Box::new(Expr::Literal(crate::ast::Literal::Int(100))),
                    ),
                },
                // Assignment: s_.x == v
                BranchConstraintIr::Eq {
                    target: ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path: vec!["x".to_string()],
                    },
                    value: Expr::Ident("v".to_string()),
                },
                // Frame: s_.y == s.y
                BranchConstraintIr::Eq {
                    target: ConstraintTarget {
                        root: ConstraintRoot::NextState,
                        path: vec!["y".to_string()],
                    },
                    value: Expr::Field(Box::new(Expr::Ident("s".to_string())), "y".to_string()),
                },
            ],
        };

        let transition_ir = TransitionIr {
            current_state_param: "s".to_string(),
            next_state_param: "s_".to_string(),
            constants_param: Some("c".to_string()),
            branches: vec![branch],
        };

        // 3 existential assignments for v: {0, 1, 2}
        let assignments: Vec<ExistentialAssignment> = (0..3)
            .map(|i| {
                let mut a = BTreeMap::new();
                a.insert("v".to_string(), RuntimeValue::Int(i));
                a
            })
            .collect();

        let current = state(4, 7);
        let result = solve_branch_successors_with_candidates_and_telemetry(
            &transition_ir,
            &transition_ir.branches[0],
            &current,
            Some(&constants(10)),
            &assignments,
            None,
            None,
            bounds(),
            SolverHooks::default(),
            None,
        )
        .unwrap();

        assert_eq!(result.successors.len(), 0);
        assert_eq!(result.telemetry.guard_pruned_assignments, 3);
    }
}

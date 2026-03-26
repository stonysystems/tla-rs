use crate::ast::{Expr, SpecFunction};
use crate::modelcheck::ir::{BranchConstraintIr, ConstraintRoot, TransitionBranchIr, TransitionIr};
use std::collections::BTreeSet;

/// Read/write footprint for a transition branch.
/// Used for POR invisible-branch pruning and DPOR independence checking.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Footprint {
    /// State fields read by this branch.
    pub read_fields: BTreeSet<String>,
    /// State fields written by this branch.
    pub write_fields: BTreeSet<String>,
    /// Whether the branch reads the entire state (conservative).
    pub reads_whole_state: bool,
    /// Whether the branch writes the entire state (conservative).
    pub writes_whole_state: bool,
}

impl Footprint {
    /// Two footprints are independent if their read/write sets don't conflict.
    /// Returns true only if neither reads/writes a field the other writes.
    pub fn independent_of(&self, other: &Footprint) -> bool {
        if self.writes_whole_state
            || other.writes_whole_state
            || self.reads_whole_state
            || other.reads_whole_state
        {
            return false;
        }
        self.write_fields.is_disjoint(&other.read_fields)
            && self.write_fields.is_disjoint(&other.write_fields)
            && self.read_fields.is_disjoint(&other.write_fields)
    }
}

pub fn infer_invisible_branch_pruning(
    transition: &TransitionIr,
    selected_invariants: &[SpecFunction],
) -> BTreeSet<String> {
    let branch_footprints = transition
        .branches
        .iter()
        .map(|branch| branch_footprint(transition, branch))
        .collect::<Vec<_>>();
    let invariant_footprint = invariant_footprint(selected_invariants);

    let mut prunable = BTreeSet::new();
    for (idx, branch) in transition.branches.iter().enumerate() {
        let candidate = &branch_footprints[idx];
        if candidate.writes_whole_state || candidate.write_fields.is_empty() {
            continue;
        }
        if invariant_footprint.reads_whole_state {
            continue;
        }

        let mut other_reads = BTreeSet::new();
        let mut other_writes = BTreeSet::new();
        let mut other_reads_whole = false;
        let mut other_writes_whole = false;
        for (other_idx, other) in branch_footprints.iter().enumerate() {
            if other_idx == idx {
                continue;
            }
            other_reads.extend(other.read_fields.iter().cloned());
            other_writes.extend(other.write_fields.iter().cloned());
            other_reads_whole |= other.reads_whole_state;
            other_writes_whole |= other.writes_whole_state;
        }
        if other_reads_whole || other_writes_whole {
            continue;
        }

        let all_writes_invisible = candidate.write_fields.iter().all(|field| {
            !other_reads.contains(field)
                && !other_writes.contains(field)
                && !invariant_footprint.read_fields.contains(field)
        });
        if all_writes_invisible {
            prunable.insert(branch.label.clone());
        }
    }

    prunable
}

/// Extract the read/write footprint for a single branch.
/// Used by DPOR for independence-based backtrack pruning.
pub fn branch_footprint(transition: &TransitionIr, branch: &TransitionBranchIr) -> Footprint {
    let mut footprint = Footprint::default();
    for constraint in &branch.constraints {
        match constraint {
            BranchConstraintIr::Eq { target, value } => {
                collect_expr_state_reads(
                    value,
                    transition.current_state_param.as_str(),
                    transition.next_state_param.as_str(),
                    &mut footprint.read_fields,
                    &mut footprint.reads_whole_state,
                );
                match &target.root {
                    ConstraintRoot::NextState => {
                        if let Some(field) = target.path.first() {
                            footprint.write_fields.insert(field.clone());
                        } else {
                            footprint.writes_whole_state = true;
                        }
                    }
                    ConstraintRoot::CurrentState => {
                        if let Some(field) = target.path.first() {
                            footprint.read_fields.insert(field.clone());
                        } else {
                            footprint.reads_whole_state = true;
                        }
                    }
                    ConstraintRoot::Constants | ConstraintRoot::Other(_) => {}
                }
            }
            BranchConstraintIr::Predicate { expr } => {
                collect_expr_state_reads(
                    expr,
                    transition.current_state_param.as_str(),
                    transition.next_state_param.as_str(),
                    &mut footprint.read_fields,
                    &mut footprint.reads_whole_state,
                );
            }
        }
    }
    footprint
}

fn invariant_footprint(selected_invariants: &[SpecFunction]) -> Footprint {
    let mut footprint = Footprint::default();
    for invariant in selected_invariants {
        let Some(state_param) = invariant.params.first().map(|p| p.name.as_str()) else {
            continue;
        };
        collect_expr_state_reads(
            &invariant.body,
            state_param,
            "__modelcheck_por_no_next__",
            &mut footprint.read_fields,
            &mut footprint.reads_whole_state,
        );
    }
    footprint
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct StateAccessPath {
    top_field: Option<String>,
}

fn extract_state_access_path(
    expr: &Expr,
    current_state_param: &str,
    next_state_param: &str,
) -> Option<StateAccessPath> {
    match expr {
        Expr::Ident(name) if name == current_state_param || name == next_state_param => {
            Some(StateAccessPath { top_field: None })
        }
        Expr::Field(base, field) | Expr::Arrow(base, field) => {
            let mut access =
                extract_state_access_path(base, current_state_param, next_state_param)?;
            if access.top_field.is_none() {
                access.top_field = Some(field.clone());
            }
            Some(access)
        }
        Expr::Index(base, _) => {
            extract_state_access_path(base, current_state_param, next_state_param)
        }
        Expr::View(inner) | Expr::Cast(inner, _) => {
            extract_state_access_path(inner, current_state_param, next_state_param)
        }
        _ => None,
    }
}

fn collect_expr_state_reads(
    expr: &Expr,
    current_state_param: &str,
    next_state_param: &str,
    out_fields: &mut BTreeSet<String>,
    out_reads_whole_state: &mut bool,
) {
    if let Some(access) = extract_state_access_path(expr, current_state_param, next_state_param) {
        if let Some(field) = access.top_field {
            out_fields.insert(field);
        } else {
            *out_reads_whole_state = true;
        }
    }

    match expr {
        Expr::Conjunction(items)
        | Expr::Disjunction(items)
        | Expr::SeqLit(items)
        | Expr::SetLit(items) => {
            for item in items {
                collect_expr_state_reads(
                    item,
                    current_state_param,
                    next_state_param,
                    out_fields,
                    out_reads_whole_state,
                );
            }
        }
        Expr::MapLit(entries) => {
            for (key, value) in entries {
                collect_expr_state_reads(
                    key,
                    current_state_param,
                    next_state_param,
                    out_fields,
                    out_reads_whole_state,
                );
                collect_expr_state_reads(
                    value,
                    current_state_param,
                    next_state_param,
                    out_fields,
                    out_reads_whole_state,
                );
            }
        }
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
            collect_expr_state_reads(
                lhs,
                current_state_param,
                next_state_param,
                out_fields,
                out_reads_whole_state,
            );
            collect_expr_state_reads(
                rhs,
                current_state_param,
                next_state_param,
                out_fields,
                out_reads_whole_state,
            );
        }
        Expr::Not(inner) | Expr::Unary(_, inner) | Expr::Is(inner, _) => {
            collect_expr_state_reads(
                inner,
                current_state_param,
                next_state_param,
                out_fields,
                out_reads_whole_state,
            );
        }
        Expr::Forall { triggers, body, .. } => {
            for trigger in triggers {
                for trigger_expr in &trigger.exprs {
                    collect_expr_state_reads(
                        trigger_expr,
                        current_state_param,
                        next_state_param,
                        out_fields,
                        out_reads_whole_state,
                    );
                }
            }
            collect_expr_state_reads(
                body,
                current_state_param,
                next_state_param,
                out_fields,
                out_reads_whole_state,
            );
        }
        Expr::Exists { body, .. } | Expr::Closure { body, .. } | Expr::Choose { body, .. } => {
            collect_expr_state_reads(
                body,
                current_state_param,
                next_state_param,
                out_fields,
                out_reads_whole_state,
            );
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_expr_state_reads(
                cond,
                current_state_param,
                next_state_param,
                out_fields,
                out_reads_whole_state,
            );
            collect_expr_state_reads(
                then_branch,
                current_state_param,
                next_state_param,
                out_fields,
                out_reads_whole_state,
            );
            if let Some(else_expr) = else_branch {
                collect_expr_state_reads(
                    else_expr,
                    current_state_param,
                    next_state_param,
                    out_fields,
                    out_reads_whole_state,
                );
            }
        }
        Expr::Match { scrutinee, arms } => {
            collect_expr_state_reads(
                scrutinee,
                current_state_param,
                next_state_param,
                out_fields,
                out_reads_whole_state,
            );
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_state_reads(
                        guard,
                        current_state_param,
                        next_state_param,
                        out_fields,
                        out_reads_whole_state,
                    );
                }
                collect_expr_state_reads(
                    &arm.body,
                    current_state_param,
                    next_state_param,
                    out_fields,
                    out_reads_whole_state,
                );
            }
        }
        Expr::Let { value, body, .. } => {
            collect_expr_state_reads(
                value,
                current_state_param,
                next_state_param,
                out_fields,
                out_reads_whole_state,
            );
            collect_expr_state_reads(
                body,
                current_state_param,
                next_state_param,
                out_fields,
                out_reads_whole_state,
            );
        }
        Expr::Struct { fields, .. } => {
            for (_, value) in fields {
                collect_expr_state_reads(
                    value,
                    current_state_param,
                    next_state_param,
                    out_fields,
                    out_reads_whole_state,
                );
            }
        }
        Expr::StructUpdate { base, fields, .. } => {
            collect_expr_state_reads(
                base,
                current_state_param,
                next_state_param,
                out_fields,
                out_reads_whole_state,
            );
            for (_, value) in fields {
                collect_expr_state_reads(
                    value,
                    current_state_param,
                    next_state_param,
                    out_fields,
                    out_reads_whole_state,
                );
            }
        }
        Expr::Call { args, .. } => {
            for arg in args {
                collect_expr_state_reads(
                    arg,
                    current_state_param,
                    next_state_param,
                    out_fields,
                    out_reads_whole_state,
                );
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            collect_expr_state_reads(
                receiver,
                current_state_param,
                next_state_param,
                out_fields,
                out_reads_whole_state,
            );
            for arg in args {
                collect_expr_state_reads(
                    arg,
                    current_state_param,
                    next_state_param,
                    out_fields,
                    out_reads_whole_state,
                );
            }
        }
        Expr::Field(base, _) | Expr::Arrow(base, _) | Expr::View(base) | Expr::Cast(base, _) => {
            if extract_state_access_path(expr, current_state_param, next_state_param).is_none() {
                collect_expr_state_reads(
                    base,
                    current_state_param,
                    next_state_param,
                    out_fields,
                    out_reads_whole_state,
                );
            }
        }
        Expr::Ident(_) | Expr::Literal(_) | Expr::SeqEmpty | Expr::SetEmpty | Expr::MapEmpty => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        BinOp, Expr, Generics, Literal, Parameter, Path, SpecFunction, Type, VariableMode,
    };
    use crate::modelcheck::ir::{ConstraintTarget, TransitionBranchIr};

    fn s_field(name: &str) -> Expr {
        Expr::Field(Box::new(Expr::Ident("s".to_string())), name.to_string())
    }

    fn add_one(expr: Expr) -> Expr {
        Expr::Binary(
            Box::new(expr),
            BinOp::Add,
            Box::new(Expr::Literal(Literal::Int(1))),
        )
    }

    fn next_assign(field: &str, value: Expr) -> BranchConstraintIr {
        BranchConstraintIr::Eq {
            target: ConstraintTarget {
                root: ConstraintRoot::NextState,
                path: vec![field.to_string()],
            },
            value,
        }
    }

    fn branch(label: &str, constraints: Vec<BranchConstraintIr>) -> TransitionBranchIr {
        TransitionBranchIr {
            label: label.to_string(),
            existential_vars: vec![],
            constraints,
        }
    }

    fn transition(branches: Vec<TransitionBranchIr>) -> TransitionIr {
        TransitionIr {
            current_state_param: "s".to_string(),
            next_state_param: "s_".to_string(),
            constants_param: Some("c".to_string()),
            extra_params: vec![],
            branches,
        }
    }

    fn invariant_reads(field: &str) -> SpecFunction {
        SpecFunction {
            name: "LInv".to_string(),
            generics: Generics::default(),
            params: vec![Parameter {
                name: "s".to_string(),
                ty: Type::Named(Path::single("LState".to_string())),
                mode: None,
                variable_mode: VariableMode::Exec,
                span: None,
            }],
            return_type: Type::Bool,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body: Expr::Ge(
                Box::new(s_field(field)),
                Box::new(Expr::Literal(Literal::Int(0))),
            ),
            span: None,
        }
    }

    #[test]
    fn test_infer_invisible_branch_pruning_prunes_hidden_branch() {
        let ir = transition(vec![
            branch(
                "branch_0",
                vec![next_assign("hidden", add_one(s_field("hidden")))],
            ),
            branch(
                "branch_1",
                vec![next_assign("visible", add_one(s_field("visible")))],
            ),
        ]);

        let prunable = infer_invisible_branch_pruning(&ir, &[invariant_reads("visible")]);
        assert_eq!(prunable.into_iter().collect::<Vec<_>>(), vec!["branch_0"]);
    }
}

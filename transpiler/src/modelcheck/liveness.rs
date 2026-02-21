use crate::ast::{SpecFunction, Type};
use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::config::LeadsToProperty;
use crate::modelcheck::evaluator::{eval_expr, CallEvaluator, EvalContext, MethodEvaluator};
use crate::modelcheck::explorer::{CounterexampleStep, CounterexampleTrace, StateDiffSummary};
use crate::modelcheck::graph::{detect_cyclic_sccs_with_witness, ExploredGraphIndex, GraphEdgeKey};
use crate::modelcheck::value::{RuntimeCollectionBounds, RuntimeValue};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Debug, Clone)]
pub struct ResolvedLeadsToObligation {
    pub name: String,
    pub from_name: String,
    pub to_name: String,
    from_fn: SpecFunction,
    to_fn: SpecFunction,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeadsToViolation {
    pub obligation_name: String,
    pub from_name: String,
    pub to_name: String,
    pub violating_component: BTreeSet<String>,
    pub representative_cycle_edge: GraphEdgeKey,
    pub counterexample: CounterexampleTrace,
}

#[derive(Clone, Copy, Default)]
pub struct LivenessHooks<'a> {
    pub call_evaluator: Option<&'a CallEvaluator<'a>>,
    pub method_evaluator: Option<&'a MethodEvaluator<'a>>,
}

pub fn resolve_leads_to_obligations(
    functions: &[SpecFunction],
    configured: &[LeadsToProperty],
) -> TranspileResult<Vec<ResolvedLeadsToObligation>> {
    let mut by_name = BTreeMap::new();
    for function in functions {
        by_name.insert(function.name.as_str(), function);
    }

    let mut resolved = Vec::with_capacity(configured.len());
    for obligation in configured {
        let from_fn = by_name.get(obligation.from.as_str()).ok_or_else(|| TranspileError::Config {
            message: format!(
                "Leads-to source predicate `{}` was selected in model config but was not found in parsed spec functions.",
                obligation.from
            ),
        })?;
        let to_fn = by_name.get(obligation.to.as_str()).ok_or_else(|| TranspileError::Config {
            message: format!(
                "Leads-to destination predicate `{}` was selected in model config but was not found in parsed spec functions.",
                obligation.to
            ),
        })?;

        validate_bool_state_predicate(from_fn)?;
        validate_bool_state_predicate(to_fn)?;

        resolved.push(ResolvedLeadsToObligation {
            name: obligation
                .name
                .as_ref()
                .cloned()
                .unwrap_or_else(|| format!("{}~>{}", obligation.from, obligation.to)),
            from_name: obligation.from.clone(),
            to_name: obligation.to.clone(),
            from_fn: (*from_fn).clone(),
            to_fn: (*to_fn).clone(),
        });
    }

    Ok(resolved)
}

pub fn check_leads_to_violations(
    graph: &ExploredGraphIndex,
    obligations: &[ResolvedLeadsToObligation],
    constants: Option<&RuntimeValue>,
    bounds: RuntimeCollectionBounds,
    hooks: LivenessHooks<'_>,
) -> TranspileResult<Option<LeadsToViolation>> {
    let cyclic_components = detect_cyclic_sccs_with_witness(graph);
    for obligation in obligations {
        let mut from_states = BTreeSet::new();
        let mut to_states = BTreeSet::new();
        for (key, node) in &graph.nodes {
            if eval_state_predicate(&obligation.from_fn, &node.state, constants, bounds, hooks)? {
                from_states.insert(key.clone());
            }
            if eval_state_predicate(&obligation.to_fn, &node.state, constants, bounds, hooks)? {
                to_states.insert(key.clone());
            }
        }

        for component in &cyclic_components {
            let has_from = component
                .members
                .iter()
                .any(|member| from_states.contains(member));
            let has_to = component
                .members
                .iter()
                .any(|member| to_states.contains(member));
            if !has_from || has_to {
                continue;
            }

            let cycle_edge = choose_component_cycle_edge(graph, component, &from_states)
                .or_else(|| component.representative_cycle_edge.clone())
                .ok_or_else(|| TranspileError::Config {
                    message: format!(
                        "Internal model-check error: cyclic SCC for `{}` had no cycle witness edge.",
                        obligation.name
                    ),
                })?;

            let counterexample =
                build_leads_to_counterexample(graph, &cycle_edge.from_key, &cycle_edge)?;

            return Ok(Some(LeadsToViolation {
                obligation_name: obligation.name.clone(),
                from_name: obligation.from_name.clone(),
                to_name: obligation.to_name.clone(),
                violating_component: component.members.clone(),
                representative_cycle_edge: cycle_edge,
                counterexample,
            }));
        }
    }

    Ok(None)
}

fn choose_component_cycle_edge(
    graph: &ExploredGraphIndex,
    component: &crate::modelcheck::graph::SccComponent,
    preferred_from_nodes: &BTreeSet<String>,
) -> Option<GraphEdgeKey> {
    for from_key in component
        .members
        .iter()
        .filter(|k| preferred_from_nodes.contains(*k))
    {
        if let Some(outgoing) = graph.successors.get(from_key) {
            for to_key in outgoing {
                if component.members.contains(to_key) {
                    return Some(GraphEdgeKey {
                        from_key: from_key.clone(),
                        to_key: to_key.clone(),
                    });
                }
            }
        }
    }
    None
}

fn build_leads_to_counterexample(
    graph: &ExploredGraphIndex,
    target_key: &str,
    cycle_edge: &GraphEdgeKey,
) -> TranspileResult<CounterexampleTrace> {
    let prefix = shortest_prefix_edges(graph, target_key);
    let initial_key = prefix
        .first()
        .map(|edge| edge.from_key.clone())
        .unwrap_or_else(|| target_key.to_string());
    let initial_state = graph
        .nodes
        .get(&initial_key)
        .ok_or_else(|| TranspileError::Config {
            message: format!(
                "Internal model-check error: missing initial trace node `{}` while building leads-to counterexample.",
                initial_key
            ),
        })?
        .state
        .clone();

    let mut steps = Vec::new();
    for edge in &prefix {
        steps.push(edge_to_trace_step(graph, edge)?);
    }
    steps.push(edge_to_trace_step(graph, cycle_edge)?);

    Ok(CounterexampleTrace {
        initial_state,
        steps,
    })
}

fn shortest_prefix_edges(graph: &ExploredGraphIndex, target_key: &str) -> Vec<GraphEdgeKey> {
    if graph
        .nodes
        .get(target_key)
        .map(|meta| meta.depth == 0)
        .unwrap_or(false)
    {
        return Vec::new();
    }

    let mut parents = BTreeMap::<String, GraphEdgeKey>::new();
    let mut visited = BTreeSet::new();
    let mut queue = VecDeque::new();

    for (key, node) in &graph.nodes {
        if node.depth == 0 {
            visited.insert(key.clone());
            queue.push_back(key.clone());
        }
    }

    while let Some(from_key) = queue.pop_front() {
        if from_key == target_key {
            break;
        }
        if let Some(outgoing) = graph.successors.get(&from_key) {
            for to_key in outgoing {
                if visited.insert(to_key.clone()) {
                    parents.insert(
                        to_key.clone(),
                        GraphEdgeKey {
                            from_key: from_key.clone(),
                            to_key: to_key.clone(),
                        },
                    );
                    queue.push_back(to_key.clone());
                }
            }
        }
    }

    let mut path = Vec::new();
    let mut cursor = target_key.to_string();
    while let Some(edge) = parents.get(&cursor) {
        path.push(edge.clone());
        cursor = edge.from_key.clone();
    }
    path.reverse();
    path
}

fn edge_to_trace_step(
    graph: &ExploredGraphIndex,
    edge: &GraphEdgeKey,
) -> TranspileResult<CounterexampleStep> {
    let from_state = graph
        .nodes
        .get(&edge.from_key)
        .ok_or_else(|| TranspileError::Config {
            message: format!(
                "Internal model-check error: missing from-state `{}` for trace edge.",
                edge.from_key
            ),
        })?
        .state
        .clone();
    let to_state = graph
        .nodes
        .get(&edge.to_key)
        .ok_or_else(|| TranspileError::Config {
            message: format!(
                "Internal model-check error: missing to-state `{}` for trace edge.",
                edge.to_key
            ),
        })?
        .state
        .clone();
    let action_branch = graph
        .edge_branches
        .get(edge)
        .and_then(|labels| labels.iter().next())
        .cloned()
        .unwrap_or_else(|| "<unknown>".to_string());

    Ok(CounterexampleStep {
        action_branch,
        state: to_state.clone(),
        diffs: summarize_state_diff_coarse(&from_state, &to_state),
    })
}

fn summarize_state_diff_coarse(
    before: &RuntimeValue,
    after: &RuntimeValue,
) -> Vec<StateDiffSummary> {
    if before == after {
        Vec::new()
    } else {
        vec![StateDiffSummary {
            path: "s".to_string(),
            before: before.canonical_key(),
            after: after.canonical_key(),
        }]
    }
}

fn eval_state_predicate(
    predicate: &SpecFunction,
    state: &RuntimeValue,
    constants: Option<&RuntimeValue>,
    bounds: RuntimeCollectionBounds,
    hooks: LivenessHooks<'_>,
) -> TranspileResult<bool> {
    let (state_param, constants_param) = validate_bool_state_predicate(predicate)?;
    let mut ctx = EvalContext::new(bounds).with_binding(state_param.to_string(), state.clone());
    if let (Some(param), Some(constants_value)) = (constants_param, constants) {
        ctx = ctx.with_binding(param.to_string(), constants_value.clone());
    }
    if let Some(call_evaluator) = hooks.call_evaluator {
        ctx = ctx.with_call_evaluator(call_evaluator);
    }
    if let Some(method_evaluator) = hooks.method_evaluator {
        ctx = ctx.with_method_evaluator(method_evaluator);
    }

    let value = eval_expr(&predicate.body, &ctx).map_err(|err| TranspileError::Config {
        message: format!(
            "Failed to evaluate predicate `{}` for leads-to checking: {}",
            predicate.name, err
        ),
    })?;
    match value {
        RuntimeValue::Bool(v) => Ok(v),
        other => Err(TranspileError::Config {
            message: format!(
                "Predicate `{}` did not evaluate to bool for leads-to checking (got `{}`).",
                predicate.name,
                other.canonical_key()
            ),
        }),
    }
}

fn validate_bool_state_predicate(
    predicate: &SpecFunction,
) -> TranspileResult<(&str, Option<&str>)> {
    if predicate.params.is_empty() || predicate.params.len() > 2 {
        return Err(TranspileError::Config {
            message: format!(
                "Predicate `{}` used by leads-to checking must have signature `(state[, constants])`.",
                predicate.name
            ),
        });
    }
    if !matches!(predicate.return_type, Type::Bool) {
        return Err(TranspileError::Config {
            message: format!(
                "Predicate `{}` used by leads-to checking must return bool.",
                predicate.name
            ),
        });
    }
    Ok((
        predicate.params[0].name.as_str(),
        predicate.params.get(1).map(|p| p.name.as_str()),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Expr, Generics, Literal, Parameter, VariableMode};
    use crate::modelcheck::explorer::ExploredState;
    use crate::modelcheck::graph::build_explored_graph_index;

    fn int_state(value: i128) -> RuntimeValue {
        RuntimeValue::Int(value)
    }

    fn predicate(name: &str, body: Expr) -> SpecFunction {
        SpecFunction {
            name: name.to_string(),
            generics: Generics::default(),
            params: vec![Parameter {
                name: "s".to_string(),
                ty: Type::Int,
                mode: None,
                variable_mode: VariableMode::Exec,
                span: None,
            }],
            return_type: Type::Bool,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body,
            span: None,
        }
    }

    fn eq_int(name: &str, value: i128) -> SpecFunction {
        predicate(
            name,
            Expr::Eq(
                Box::new(Expr::Ident("s".to_string())),
                Box::new(Expr::Literal(Literal::Int(value))),
            ),
        )
    }

    fn index_from_edges(nodes: &[i128], edges: &[(i128, i128, &str)]) -> ExploredGraphIndex {
        let explored: Vec<ExploredState> = nodes
            .iter()
            .enumerate()
            .map(|(depth, value)| ExploredState {
                state: int_state(*value),
                depth,
            })
            .collect();
        build_explored_graph_index(&explored, |state| {
            let from = match state {
                RuntimeValue::Int(v) => *v,
                _ => 0,
            };
            let successors = edges
                .iter()
                .filter(|(edge_from, _, _)| *edge_from == from)
                .map(
                    |(_, to, label)| crate::modelcheck::explorer::TracedSuccessor {
                        action_branch: (*label).to_string(),
                        state: int_state(*to),
                    },
                )
                .collect();
            Ok(successors)
        })
        .unwrap()
    }

    #[test]
    fn test_check_leads_to_violations_detects_cycle_without_to_and_emits_trace() {
        let from = eq_int("LFrom", 0);
        let to = eq_int("LTo", 2);
        let resolved = resolve_leads_to_obligations(
            &[from.clone(), to.clone()],
            &[LeadsToProperty {
                from: "LFrom".to_string(),
                to: "LTo".to_string(),
                name: Some("eventual_two".to_string()),
            }],
        )
        .unwrap();
        let index = index_from_edges(&[0, 1, 2], &[(0, 1, "b01"), (1, 0, "b10"), (1, 2, "b12")]);

        let violation = check_leads_to_violations(
            &index,
            &resolved,
            None,
            RuntimeCollectionBounds {
                max_seq_len: 4,
                max_set_len: 4,
                max_map_len: 4,
            },
            LivenessHooks::default(),
        )
        .unwrap()
        .expect("expected leads-to violation");

        assert_eq!(violation.obligation_name, "eventual_two");
        assert!(violation
            .violating_component
            .contains(&int_state(0).canonical_key()));
        assert!(violation
            .violating_component
            .contains(&int_state(1).canonical_key()));
        assert!(!violation.counterexample.steps.is_empty());
    }

    #[test]
    fn test_check_leads_to_violations_returns_none_when_to_holds_in_cycle() {
        let from = eq_int("LFrom", 0);
        let to = eq_int("LTo", 1);
        let resolved = resolve_leads_to_obligations(
            &[from.clone(), to.clone()],
            &[LeadsToProperty {
                from: "LFrom".to_string(),
                to: "LTo".to_string(),
                name: None,
            }],
        )
        .unwrap();
        let index = index_from_edges(&[0, 1], &[(0, 1, "b01"), (1, 0, "b10")]);

        let violation = check_leads_to_violations(
            &index,
            &resolved,
            None,
            RuntimeCollectionBounds {
                max_seq_len: 4,
                max_set_len: 4,
                max_map_len: 4,
            },
            LivenessHooks::default(),
        )
        .unwrap();

        assert!(violation.is_none());
    }
}

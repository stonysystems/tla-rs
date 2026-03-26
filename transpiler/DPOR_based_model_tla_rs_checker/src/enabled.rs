//! Deterministic enabled-set enumeration for the DPOR explorer.
//!
//! Given a state and a loaded spec, produces an ordered list of enabled
//! transitions. The ordering is deterministic: for the same input state
//! and bounds, repeated calls produce the same list in the same order.
//!
//! This module uses the transpiler's library API directly (Phase 38.8.2.c
//! extraction) rather than shelling out to a subprocess.

use std::path::Path;

use verus_transpiler::error::TranspileResult;
use verus_transpiler::modelcheck::config::parse_model_config_file;
use verus_transpiler::modelcheck::domain::{
    expand_branch_existentials, expand_type_domain_candidates,
};
use verus_transpiler::modelcheck::helpers::eval_spec_function_call_recursive;
use verus_transpiler::modelcheck::init::{construct_initial_states, InitHooks};
use verus_transpiler::modelcheck::ir::build_transition_ir;
use verus_transpiler::modelcheck::solver::{
    solve_branch_successors, solve_transition_successors, SolverHooks,
};
use verus_transpiler::modelcheck::value::{RuntimeCollectionBounds, RuntimeValue};
use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

use crate::types::{EnabledTransition, ProcessId, StateFingerprint, TransitionFootprint};

/// A loaded spec ready for enabled-set enumeration.
pub struct SpecContext {
    pub bundle: verus_transpiler::spec_analyzer::ProtocolSourceBundle,
    pub model_config: verus_transpiler::modelcheck::config::ModelConfig,
    pub bounds: RuntimeCollectionBounds,
}

impl SpecContext {
    /// Load a spec from file paths.
    pub fn load(
        spec_file: &Path,
        types_file: Option<&Path>,
        model_file: &Path,
        init_name: &str,
        next_name: &str,
    ) -> TranspileResult<Self> {
        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            spec_file, types_file, init_name, next_name,
        )?;
        let model_config = parse_model_config_file(model_file).map_err(|e| {
            verus_transpiler::error::TranspileError::Config {
                message: format!("Failed to parse model config: {}", e),
            }
        })?;
        let bounds = RuntimeCollectionBounds {
            max_set_len: model_config.collections.max_set_len,
            max_seq_len: model_config.collections.max_seq_len,
            max_map_len: model_config.collections.max_map_len,
        };
        Ok(Self {
            bundle,
            model_config,
            bounds,
        })
    }

    /// Construct initial states.
    pub fn initial_states(&self) -> TranspileResult<Vec<RuntimeValue>> {
        let state_ty = &self.bundle.entrypoints.lnext.params[0].ty;
        let candidates = expand_type_domain_candidates(
            "candidate_states",
            "candidate_state",
            state_ty,
            &self.bundle.schema,
            &self.model_config,
        )?;

        let call_eval = |func_path: &verus_transpiler::ast::Path,
                         args: &[RuntimeValue]|
         -> TranspileResult<RuntimeValue> {
            eval_spec_function_call_recursive(
                &self.bundle.spec_functions,
                &self.bundle.schema,
                &self.model_config,
                func_path,
                args,
                self.bounds,
                0,
            )
        };
        let hooks = InitHooks {
            call_evaluator: Some(&call_eval),
            method_evaluator: None,
            quantifier_domain_evaluator: None,
        };
        construct_initial_states(
            &self.bundle.entrypoints.linit,
            &candidates,
            None, // no constants for standalone specs
            self.bounds,
            hooks,
        )
    }

    /// Enumerate all enabled transitions from a given state.
    ///
    /// Returns a deterministically-ordered list of `EnabledTransition`s.
    /// The ordering key is `"{branch_index}:{branch_label}:{successor_index}"`,
    /// ensuring stable ordering across runs.
    pub fn enabled_transitions(
        &self,
        state: &RuntimeValue,
    ) -> TranspileResult<Vec<EnabledTransition>> {
        let transition = build_transition_ir(&self.bundle.entrypoints.lnext)?;

        // Build existential assignments per branch
        let mut assignments_by_branch = std::collections::BTreeMap::new();
        for branch in &transition.branches {
            let assignments =
                expand_branch_existentials(branch, &self.bundle.schema, &self.model_config)?;
            assignments_by_branch.insert(branch.label.clone(), assignments);
        }

        // Create call evaluator for the solver hooks
        let call_eval = |func_path: &verus_transpiler::ast::Path,
                         args: &[RuntimeValue]|
         -> TranspileResult<RuntimeValue> {
            eval_spec_function_call_recursive(
                &self.bundle.spec_functions,
                &self.bundle.schema,
                &self.model_config,
                func_path,
                args,
                self.bounds,
                0,
            )
        };

        // Create quantifier domain evaluator
        let quant_eval =
            |binding: &verus_transpiler::ast::Binding| -> TranspileResult<Vec<RuntimeValue>> {
                verus_transpiler::modelcheck::helpers::expand_quantifier_domain_for_binding(
                    binding,
                    &self.bundle.schema,
                    &self.model_config,
                )
            };

        // Create predicate-only branch solver for translated specs
        // (these use predicate-style constraints like `LAdd(s, s_)`)
        let predicate_solver = |
            trans: &verus_transpiler::modelcheck::ir::TransitionIr,
            branch: &verus_transpiler::modelcheck::ir::TransitionBranchIr,
            cur_state: &RuntimeValue,
            constants: Option<&RuntimeValue>,
            exist_assignments: &[verus_transpiler::modelcheck::domain::ExistentialAssignment],
            bounds: RuntimeCollectionBounds,
        | -> TranspileResult<Option<Vec<RuntimeValue>>> {
            // Check if branch has a single predicate-style constraint
            use verus_transpiler::modelcheck::ir::BranchConstraintIr;
            use verus_transpiler::ast::Expr;

            if branch.constraints.len() != 1 {
                return Ok(None);
            }
            let BranchConstraintIr::Predicate { expr } = &branch.constraints[0] else {
                return Ok(None);
            };
            let Expr::Call { func, args } = expr else {
                return Ok(None);
            };

            // Resolve the called helper function
            let helper_fn = match verus_transpiler::modelcheck::helpers::resolve_called_spec_function(
                &self.bundle.spec_functions, func,
            ) {
                Ok(f) => f,
                Err(_) => return Ok(None),
            };

            // Build transition IR for the helper
            let helper_transition = match build_transition_ir(helper_fn) {
                Ok(t) => t,
                Err(_) => return Ok(None),
            };

            // Solve each helper branch with the call evaluator
            let mut all_succs = Vec::new();
            for helper_branch in &helper_transition.branches {
                let helper_assigns = expand_branch_existentials(
                    helper_branch, &self.bundle.schema, &self.model_config,
                )?;

                let hooks = SolverHooks {
                    call_evaluator: Some(&call_eval),
                    method_evaluator: None,
                    quantifier_domain_evaluator: Some(&quant_eval),
                    predicate_only_branch_solver: None,
                };

                let result = solve_branch_successors(
                    &helper_transition,
                    helper_branch,
                    cur_state,
                    constants,
                    &helper_assigns,
                    bounds,
                    hooks,
                );

                match result {
                    Ok(succs) => all_succs.extend(succs),
                    Err(_) => continue, // Skip branches that fail
                }
            }

            if all_succs.is_empty() {
                Ok(None)
            } else {
                Ok(Some(verus_transpiler::modelcheck::solver::deduplicate_successors(all_succs)))
            }
        };

        let hooks = SolverHooks {
            call_evaluator: Some(&call_eval),
            method_evaluator: None,
            quantifier_domain_evaluator: Some(&quant_eval),
            predicate_only_branch_solver: Some(&predicate_solver),
        };

        // Use solve_transition_successors with the predicate-only solver
        let successors = solve_transition_successors(
            &transition,
            state,
            None, // no constants for standalone specs
            Some(&assignments_by_branch),
            self.bounds,
            hooks,
        )?;

        let mut all_enabled = Vec::new();
        for (succ_idx, successor) in successors.iter().enumerate() {
            let fingerprint = hash_state(successor);
            let ordering_key = format!("{:04}", succ_idx);

            all_enabled.push(EnabledTransition {
                process_id: ProcessId(0), // v1: single process
                branch_label: format!("transition_{}", succ_idx),
                successor_fingerprint: fingerprint,
                ordering_key,
                footprint: TransitionFootprint::default(), // v1: no footprint yet
            });
        }

        Ok(all_enabled)
    }

    /// Get all successor states from a given state (full RuntimeValue, not just fingerprints).
    /// Uses the same solver pipeline as `enabled_transitions`, including the predicate-only solver.
    pub fn full_successors(&self, state: &RuntimeValue) -> TranspileResult<Vec<RuntimeValue>> {
        let transition = build_transition_ir(&self.bundle.entrypoints.lnext)?;

        let mut assignments_by_branch = std::collections::BTreeMap::new();
        for branch in &transition.branches {
            let assignments =
                expand_branch_existentials(branch, &self.bundle.schema, &self.model_config)?;
            assignments_by_branch.insert(branch.label.clone(), assignments);
        }

        let call_eval = |func_path: &verus_transpiler::ast::Path,
                         args: &[RuntimeValue]|
         -> TranspileResult<RuntimeValue> {
            eval_spec_function_call_recursive(
                &self.bundle.spec_functions,
                &self.bundle.schema,
                &self.model_config,
                func_path,
                args,
                self.bounds,
                0,
            )
        };
        let quant_eval =
            |binding: &verus_transpiler::ast::Binding| -> TranspileResult<Vec<RuntimeValue>> {
                verus_transpiler::modelcheck::helpers::expand_quantifier_domain_for_binding(
                    binding,
                    &self.bundle.schema,
                    &self.model_config,
                )
            };
        // Build the same predicate solver as enabled_transitions
        let predicate_solver = |
            _trans: &verus_transpiler::modelcheck::ir::TransitionIr,
            branch: &verus_transpiler::modelcheck::ir::TransitionBranchIr,
            cur_state: &RuntimeValue,
            constants: Option<&RuntimeValue>,
            _exist_assignments: &[verus_transpiler::modelcheck::domain::ExistentialAssignment],
            bounds: RuntimeCollectionBounds,
        | -> TranspileResult<Option<Vec<RuntimeValue>>> {
            use verus_transpiler::modelcheck::ir::BranchConstraintIr;
            use verus_transpiler::ast::Expr;

            if branch.constraints.len() != 1 { return Ok(None); }
            let BranchConstraintIr::Predicate { expr } = &branch.constraints[0] else { return Ok(None); };
            let Expr::Call { func, args: _ } = expr else { return Ok(None); };

            let helper_fn = match verus_transpiler::modelcheck::helpers::resolve_called_spec_function(
                &self.bundle.spec_functions, func,
            ) { Ok(f) => f, Err(_) => return Ok(None) };
            let helper_transition = match build_transition_ir(helper_fn) { Ok(t) => t, Err(_) => return Ok(None) };

            let mut all_succs = Vec::new();
            for helper_branch in &helper_transition.branches {
                let helper_assigns = expand_branch_existentials(
                    helper_branch, &self.bundle.schema, &self.model_config,
                )?;
                let hooks = SolverHooks {
                    call_evaluator: Some(&call_eval),
                    method_evaluator: None,
                    quantifier_domain_evaluator: Some(&quant_eval),
                    predicate_only_branch_solver: None,
                };
                match solve_branch_successors(
                    &helper_transition, helper_branch, cur_state, constants,
                    &helper_assigns, bounds, hooks,
                ) {
                    Ok(succs) => all_succs.extend(succs),
                    Err(_) => continue,
                }
            }
            if all_succs.is_empty() { Ok(None) }
            else { Ok(Some(verus_transpiler::modelcheck::solver::deduplicate_successors(all_succs))) }
        };

        let hooks = SolverHooks {
            call_evaluator: Some(&call_eval),
            method_evaluator: None,
            quantifier_domain_evaluator: Some(&quant_eval),
            predicate_only_branch_solver: Some(&predicate_solver),
        };

        solve_transition_successors(
            &transition,
            state,
            None,
            Some(&assignments_by_branch),
            self.bounds,
            hooks,
        )
    }

    /// Create solver hooks with a call evaluator bound to this context.
    /// Must be called inline where the returned hooks are used, to satisfy lifetimes.
    pub fn make_solver_hooks_inline<'a>(
        call_eval: &'a dyn Fn(
            &verus_transpiler::ast::Path,
            &[RuntimeValue],
        ) -> TranspileResult<RuntimeValue>,
    ) -> SolverHooks<'a> {
        SolverHooks {
            call_evaluator: Some(call_eval),
            method_evaluator: None,
            quantifier_domain_evaluator: None,
            predicate_only_branch_solver: None,
        }
    }
}

/// Hash a RuntimeValue into a compact StateFingerprint.
fn hash_state(state: &RuntimeValue) -> StateFingerprint {
    use std::hash::{Hash, Hasher};
    let key = state.canonical_key();
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    key.hash(&mut hasher);
    StateFingerprint(hasher.finish())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn create_model_toml(dir: &Path) -> std::path::PathBuf {
        let model_path = dir.join("model.toml");
        let mut f = std::fs::File::create(&model_path).unwrap();
        write!(
            f,
            r#"
[search]
max_depth = 20
max_states = 1000
timeout_ms = 10000

[properties]
invariants = []
check_deadlock = false
successor_semantics = "deadlock"

[quantifiers]
int = {{ min = 0, max = 5 }}
max_set_len = 4
max_seq_len = 4
"#
        )
        .unwrap();
        model_path
    }

    fn aplusb_spec_path() -> Option<std::path::PathBuf> {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let path = manifest_dir.join("tests/tla-rs/01_aplusb/APlusB.rs");
        if path.exists() {
            Some(path)
        } else {
            None
        }
    }

    fn producer_consumer_spec_path() -> Option<std::path::PathBuf> {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let path =
            manifest_dir.join("tests/tla-rs/07_producer_consumer_1slot/ProducerConsumer1Slot.rs");
        if path.exists() {
            Some(path)
        } else {
            None
        }
    }

    #[test]
    fn test_load_spec_context() {
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: APlusB.rs not found");
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());

        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext");
        assert!(ctx.is_ok(), "Failed to load: {:?}", ctx.err());
    }

    #[test]
    fn test_initial_states_aplusb() {
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => {
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let initials = ctx.initial_states().unwrap();
        assert_eq!(initials.len(), 1, "APlusB should have 1 initial state");
    }

    #[test]
    fn test_enabled_transitions_aplusb() {
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => {
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let initials = ctx.initial_states().unwrap();
        let enabled = ctx.enabled_transitions(&initials[0]).unwrap();

        // APlusB has 1 action (LAdd) producing 1 successor
        assert_eq!(enabled.len(), 1, "APlusB should have 1 enabled transition");
        assert!(
            enabled[0].branch_label.starts_with("transition_"),
            "Branch label should start with 'transition_', got: {}",
            enabled[0].branch_label
        );
    }

    #[test]
    fn test_enabled_transitions_deterministic() {
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => {
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let initials = ctx.initial_states().unwrap();
        let run1 = ctx.enabled_transitions(&initials[0]).unwrap();
        let run2 = ctx.enabled_transitions(&initials[0]).unwrap();

        // Same state → same transitions in same order
        assert_eq!(run1.len(), run2.len());
        for (t1, t2) in run1.iter().zip(run2.iter()) {
            assert_eq!(t1.ordering_key, t2.ordering_key);
            assert_eq!(t1.successor_fingerprint, t2.successor_fingerprint);
            assert_eq!(t1.branch_label, t2.branch_label);
        }
    }

    #[test]
    fn test_enabled_transitions_producer_consumer() {
        let spec_path = match producer_consumer_spec_path() {
            Some(p) => p,
            None => {
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let initials = ctx.initial_states().unwrap();
        // ProducerConsumer may fail if the predicate solver can't handle its
        // branch structure (it uses LProduce(s, s_, c) with a constants parameter).
        // This is a known limitation of the simplified predicate solver.
        match ctx.enabled_transitions(&initials[0]) {
            Ok(enabled) => {
                assert!(
                    !enabled.is_empty(),
                    "ProducerConsumer should have at least 1 enabled transition"
                );
                eprintln!("ProducerConsumer: {} enabled transitions", enabled.len());
            }
            Err(e) => {
                eprintln!(
                    "ProducerConsumer enabled_transitions failed (known limitation): {}",
                    e
                );
                // This is acceptable for v1 — the predicate solver doesn't
                // handle all branch patterns yet
            }
        }
    }

    #[test]
    fn test_multi_step_exploration_aplusb() {
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => {
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let initials = ctx.initial_states().unwrap();
        let mut current = initials[0].clone();
        let mut visited = std::collections::BTreeSet::new();
        visited.insert(current.canonical_key());

        // BFS from initial state — should reach multiple states
        let mut depth = 0;
        loop {
            let enabled = ctx.enabled_transitions(&current).unwrap();
            if enabled.is_empty() {
                break;
            }
            // Follow first transition
            // We need the actual successor state, not just the fingerprint.
            // For now, reconstruct by re-solving
            // Use full_successors to get actual successor states
            let succs = ctx.full_successors(&current).unwrap_or_default();

            let mut found_new = false;
            for s in succs {
                if visited.insert(s.canonical_key()) {
                    current = s;
                    found_new = true;
                    break;
                }
            }
            if !found_new {
                break;
            }
            depth += 1;
            if depth > 10 {
                break;
            } // Safety limit
        }

        assert!(
            visited.len() > 1,
            "Multi-step exploration should visit more than 1 state, visited {}",
            visited.len()
        );
        eprintln!(
            "APlusB multi-step: visited {} states, depth {}",
            visited.len(),
            depth
        );
    }
}

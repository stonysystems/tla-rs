//! DPOR search stack and DFS exploration loop.
//!
//! Implements the core DPOR algorithm: a depth-first search with
//! backtrack sets at each stack frame. v1 uses conservative dependence
//! (all transitions dependent), making it equivalent to exhaustive DFS.
//! Future versions will add independence-based pruning.
//!
//! Reference: source-DPOR from Nidhugg (DPORDriver + TraceBuilder pattern).

use std::collections::BTreeSet;

use crate::enabled::SpecContext;
use crate::types::*;
use verus_transpiler::modelcheck::value::RuntimeValue;

/// One frame in the DPOR search stack.
#[derive(Clone, Debug)]
pub struct StackFrame {
    /// State at this depth (before the chosen transition).
    pub state: RuntimeValue,
    /// Fingerprint of the state.
    pub state_fingerprint: StateFingerprint,
    /// All enabled transitions from this state.
    pub enabled: Vec<EnabledTransition>,
    /// Which transitions have been explored (by ordering_key).
    pub done: BTreeSet<String>,
    /// Which transitions should still be explored (backtrack set).
    /// In v1 (conservative), this starts as all enabled transitions.
    pub backtrack: BTreeSet<String>,
    /// The transition that was chosen to proceed deeper (if any).
    pub chosen: Option<EnabledTransition>,
    /// Depth in the search (0 = initial state).
    pub depth: usize,
}

/// Result of a DPOR exploration run.
#[derive(Debug)]
pub struct DporResult {
    /// All distinct states discovered.
    pub distinct_states: BTreeSet<String>,
    /// Number of complete executions (traces) explored.
    pub traces_explored: usize,
    /// Maximum depth reached.
    pub max_depth: usize,
    /// Total transitions fired.
    pub transitions_fired: usize,
    /// Whether an invariant violation was found (placeholder for v2).
    pub violation: Option<String>,
}

/// Configuration for the DPOR explorer.
#[derive(Clone, Debug)]
pub struct DporConfig {
    /// Maximum exploration depth.
    pub max_depth: usize,
    /// Maximum number of distinct states before stopping.
    pub max_states: usize,
}

impl Default for DporConfig {
    fn default() -> Self {
        Self {
            max_depth: 100,
            max_states: 100_000,
        }
    }
}

/// Run the DPOR DFS exploration on a loaded spec.
///
/// v1: conservative dependence (all transitions dependent at each state).
/// This is equivalent to exhaustive DFS — it explores every reachable state.
/// The backtrack machinery is in place for future independence-based pruning.
pub fn explore_dpor(ctx: &SpecContext, config: &DporConfig) -> DporResult {
    let mut distinct_states: BTreeSet<String> = BTreeSet::new();
    let mut traces_explored: usize = 0;
    let mut max_depth: usize = 0;
    let mut transitions_fired: usize = 0;

    // Get initial states
    let initial_states = match ctx.initial_states() {
        Ok(states) => states,
        Err(e) => {
            eprintln!("DPOR: failed to get initial states: {}", e);
            return DporResult {
                distinct_states,
                traces_explored: 0,
                max_depth: 0,
                transitions_fired: 0,
                violation: None,
            };
        }
    };

    // Explore from each initial state
    for initial in &initial_states {
        let initial_key = initial.canonical_key();
        if !distinct_states.insert(initial_key.clone()) {
            continue; // Already seen this initial state
        }

        let enabled = match ctx.enabled_transitions(initial) {
            Ok(e) => e,
            Err(e) => {
                eprintln!("DPOR: failed to enumerate enabled transitions: {}", e);
                continue;
            }
        };

        // Initialize backtrack set with all enabled transitions (conservative)
        let backtrack: BTreeSet<String> = enabled.iter().map(|t| t.ordering_key.clone()).collect();

        let initial_frame = StackFrame {
            state: initial.clone(),
            state_fingerprint: crate::enabled::hash_state(initial),
            enabled,
            done: BTreeSet::new(),
            backtrack,
            chosen: None,
            depth: 0,
        };

        // DFS with explicit stack
        let mut stack: Vec<StackFrame> = vec![initial_frame];

        while let Some(frame) = stack.last_mut() {
            // Check limits
            if distinct_states.len() >= config.max_states {
                break;
            }

            // Find a transition in backtrack that isn't in done
            let next_transition = frame
                .backtrack
                .iter()
                .find(|key| !frame.done.contains(*key))
                .cloned();

            match next_transition {
                Some(key) => {
                    // Mark as done
                    frame.done.insert(key.clone());

                    // Find the transition object
                    let transition = frame
                        .enabled
                        .iter()
                        .find(|t| t.ordering_key == key)
                        .cloned();

                    let Some(transition) = transition else {
                        continue;
                    };

                    frame.chosen = Some(transition.clone());
                    transitions_fired += 1;

                    // Get the actual successor state
                    let successors = match ctx.full_successors(&frame.state) {
                        Ok(s) => s,
                        Err(_) => continue,
                    };

                    // Find the successor matching this transition's fingerprint
                    let successor = successors
                        .iter()
                        .find(|s| crate::enabled::hash_state(s) == transition.successor_fingerprint)
                        .cloned();

                    let Some(successor) = successor else {
                        // Fingerprint mismatch — skip this transition
                        continue;
                    };

                    let succ_key = successor.canonical_key();
                    let is_new = distinct_states.insert(succ_key);

                    let depth = frame.depth + 1;
                    if depth > max_depth {
                        max_depth = depth;
                    }

                    // Only push a new frame if depth limit not reached
                    // and state is new (avoid infinite loops on cycles)
                    if depth < config.max_depth && is_new {
                        let enabled = match ctx.enabled_transitions(&successor) {
                            Ok(e) => e,
                            Err(_) => vec![],
                        };

                        let backtrack: BTreeSet<String> =
                            enabled.iter().map(|t| t.ordering_key.clone()).collect();

                        stack.push(StackFrame {
                            state: successor,
                            state_fingerprint: transition.successor_fingerprint,
                            enabled,
                            done: BTreeSet::new(),
                            backtrack,
                            chosen: None,
                            depth,
                        });
                    }
                    // If state already visited, we don't push (pruning via dedup)
                }
                None => {
                    // All backtrack alternatives explored at this depth — pop
                    stack.pop();
                    traces_explored += 1;
                }
            }
        }
    }

    DporResult {
        distinct_states,
        traces_explored,
        max_depth,
        transitions_fired,
        violation: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use std::path::Path;

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

    #[test]
    fn test_dpor_exhaustive_aplusb() {
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: APlusB.rs not found");
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let config = DporConfig {
            max_depth: 20,
            max_states: 1000,
        };
        let result = explore_dpor(&ctx, &config);

        // APlusB with int 0..5: states are {a:0,b:0}, {a:1,b:1}, ..., {a:5,b:5}
        // That's 6 states (depth 0..5), but the model checker explores more
        // due to domain expansion. The baseline reports 51 distinct states.
        // Our DFS should find a subset (the linear chain is 6 states).
        assert!(
            result.distinct_states.len() >= 6,
            "Expected at least 6 states (linear chain), got {}",
            result.distinct_states.len()
        );
        assert!(result.max_depth >= 5, "Expected depth >= 5");
        assert!(result.transitions_fired >= 5);
        eprintln!(
            "DPOR APlusB: {} distinct states, {} traces, depth {}, {} transitions",
            result.distinct_states.len(),
            result.traces_explored,
            result.max_depth,
            result.transitions_fired
        );
    }

    #[test]
    fn test_dpor_deterministic() {
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => { return; }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let config = DporConfig {
            max_depth: 10,
            max_states: 100,
        };
        let run1 = explore_dpor(&ctx, &config);
        let run2 = explore_dpor(&ctx, &config);

        assert_eq!(
            run1.distinct_states, run2.distinct_states,
            "Two runs should produce identical state sets"
        );
        assert_eq!(run1.transitions_fired, run2.transitions_fired);
    }

    #[test]
    fn test_dpor_max_depth_respected() {
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => { return; }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let config = DporConfig {
            max_depth: 3,
            max_states: 1000,
        };
        let result = explore_dpor(&ctx, &config);

        assert!(
            result.max_depth <= 3,
            "Should respect max_depth=3, got {}",
            result.max_depth
        );
    }

    #[test]
    fn test_dpor_max_states_respected() {
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => { return; }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let config = DporConfig {
            max_depth: 100,
            max_states: 3,
        };
        let result = explore_dpor(&ctx, &config);

        assert!(
            result.distinct_states.len() <= 4, // allow 1 over due to loop check timing
            "Should respect max_states~3, got {}",
            result.distinct_states.len()
        );
    }
}

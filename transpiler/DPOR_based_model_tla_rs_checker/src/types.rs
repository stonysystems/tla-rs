//! Core DPOR runtime types (Phase 38.7.1 / 38.8.1.b).
//!
//! These types are the foundation for the DPOR explorer.
//! See `design.md` §"Core DPOR Runtime Types" for rationale.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

/// Identifies a process/actor in the protocol.
/// For distributed protocols: server/node index.
/// For single-process specs: always `ProcessId(0)`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProcessId(pub u32);

/// Identifies a specific action branch within the Next predicate.
/// E.g., "LTMRcvPrepared", "LTMCommit", "LAdd" — corresponds to
/// one disjunct in `Next == A1 \/ A2 \/ ...`.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ActionId {
    pub branch_label: String,
    pub process: ProcessId,
}

/// Compact state identity for dedup and comparison.
/// Mirrors Phase 36's canonical_key() / u64 fingerprint scheme.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct StateFingerprint(pub u64);

/// Lamport vector clock indexed by ProcessId.
/// Used to track happens-before between events.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VectorClock {
    pub clocks: BTreeMap<ProcessId, u64>,
}

impl VectorClock {
    /// Increment the clock for a specific process.
    pub fn tick(&mut self, process: ProcessId) {
        *self.clocks.entry(process).or_insert(0) += 1;
    }

    /// Merge another clock into this one (pointwise max).
    pub fn merge(&mut self, other: &VectorClock) {
        for (&pid, &ts) in &other.clocks {
            let entry = self.clocks.entry(pid).or_insert(0);
            *entry = (*entry).max(ts);
        }
    }

    /// Check if this clock happens-before another (strict partial order).
    pub fn happens_before(&self, other: &VectorClock) -> bool {
        // self <= other (pointwise) AND self != other
        let leq = self
            .clocks
            .iter()
            .all(|(&pid, &ts)| ts <= *other.clocks.get(&pid).unwrap_or(&0));
        leq && self != other
    }

    /// Get the timestamp for a specific process.
    pub fn get(&self, process: ProcessId) -> u64 {
        *self.clocks.get(&process).unwrap_or(&0)
    }
}

/// A single step in an execution trace.
/// Represents one process taking one action, producing a successor state.
#[derive(Clone, Debug)]
pub struct Event {
    /// Global sequence number (0-indexed).
    pub seq: usize,
    /// Which process took which action.
    pub action: ActionId,
    /// State fingerprint before this step.
    pub pre_state: StateFingerprint,
    /// State fingerprint after this step.
    pub post_state: StateFingerprint,
    /// Lamport vector clock at this event.
    pub clock: VectorClock,
}

/// An ordered prefix of an execution: a sequence of events from the initial state.
#[derive(Clone, Debug)]
pub struct ExecutionPrefix {
    /// The events in order.
    pub events: Vec<Event>,
    /// Fingerprint of the initial state.
    pub initial_state: StateFingerprint,
}

/// The set of processes that are enabled (have at least one valid transition)
/// in a given state.
pub type EnabledSet = BTreeSet<ProcessId>;

/// At each event in the trace, records which alternative processes should be
/// explored at this decision point (source-DPOR backtrack insertion).
#[derive(Clone, Debug, Default)]
pub struct BacktrackInfo {
    /// Processes to try as alternatives at this decision point.
    pub backtrack: BTreeSet<ProcessId>,
    /// Processes already explored at this decision point.
    pub done: BTreeSet<ProcessId>,
}

/// Per-event sleep set (v2+, initially empty).
pub type SleepSet = BTreeSet<ActionId>;

// =====================================================================
// DPOR Stepping Contract (Phase 38.8.2.b)
// =====================================================================

/// A transition that is enabled in a given state.
/// Represents one concrete choice the explorer can make.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EnabledTransition {
    /// Which process would take this step.
    pub process_id: ProcessId,
    /// Which action branch this transition belongs to.
    pub branch_label: String,
    /// Fingerprint of the successor state produced by this transition.
    pub successor_fingerprint: StateFingerprint,
    /// Deterministic ordering key — transitions are sorted by this
    /// to ensure reproducible exploration order.
    pub ordering_key: String,
    /// Read/write footprint: which state fields this branch reads and writes.
    /// Used by the dependence checker to determine independence.
    /// Format: (read_fields, write_fields) where each is a sorted set of field paths.
    pub footprint: TransitionFootprint,
}

/// Read/write footprint for a transition, used for dependence checking.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TransitionFootprint {
    /// State fields read by this transition (sorted).
    pub reads: BTreeSet<String>,
    /// State fields written by this transition (sorted).
    pub writes: BTreeSet<String>,
}

impl TransitionFootprint {
    /// Two transitions are independent if their read/write sets don't conflict.
    /// Conflict = one writes a field the other reads or writes.
    pub fn independent_of(&self, other: &TransitionFootprint) -> bool {
        // Check: self.writes ∩ other.reads == ∅
        //    AND self.writes ∩ other.writes == ∅
        //    AND self.reads ∩ other.writes == ∅
        self.writes.is_disjoint(&other.reads)
            && self.writes.is_disjoint(&other.writes)
            && self.reads.is_disjoint(&other.writes)
    }
}

/// A scheduled step: records which transition was actually taken at a depth.
#[derive(Clone, Debug)]
pub struct ScheduledStep {
    /// The transition that was chosen.
    pub transition: EnabledTransition,
    /// All transitions that were enabled at this state (including the chosen one).
    pub enabled: Vec<EnabledTransition>,
    /// Fingerprint of the state before this step.
    pub pre_state: StateFingerprint,
    /// Depth in the exploration (0-indexed).
    pub depth: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_process_id_ordering() {
        let p0 = ProcessId(0);
        let p1 = ProcessId(1);
        let p2 = ProcessId(2);
        assert!(p0 < p1);
        assert!(p1 < p2);
        assert_eq!(p0, ProcessId(0));
    }

    #[test]
    fn test_vector_clock_tick() {
        let mut vc = VectorClock::default();
        let p0 = ProcessId(0);
        let p1 = ProcessId(1);

        assert_eq!(vc.get(p0), 0);
        vc.tick(p0);
        assert_eq!(vc.get(p0), 1);
        vc.tick(p0);
        assert_eq!(vc.get(p0), 2);
        assert_eq!(vc.get(p1), 0);
    }

    #[test]
    fn test_vector_clock_merge() {
        let p0 = ProcessId(0);
        let p1 = ProcessId(1);

        let mut vc1 = VectorClock::default();
        vc1.tick(p0);
        vc1.tick(p0); // p0=2, p1=0

        let mut vc2 = VectorClock::default();
        vc2.tick(p1);
        vc2.tick(p1);
        vc2.tick(p1); // p0=0, p1=3

        vc1.merge(&vc2);
        assert_eq!(vc1.get(p0), 2);
        assert_eq!(vc1.get(p1), 3);
    }

    #[test]
    fn test_vector_clock_happens_before() {
        let p0 = ProcessId(0);
        let p1 = ProcessId(1);

        let mut vc1 = VectorClock::default();
        vc1.tick(p0); // [1, 0]

        let mut vc2 = VectorClock::default();
        vc2.tick(p0);
        vc2.tick(p1); // [1, 1]

        // vc1 happens-before vc2 (vc1 <= vc2 pointwise, and vc1 != vc2)
        assert!(vc1.happens_before(&vc2));
        assert!(!vc2.happens_before(&vc1));

        // A clock does not happen-before itself
        assert!(!vc1.happens_before(&vc1));
    }

    #[test]
    fn test_vector_clock_concurrent() {
        let p0 = ProcessId(0);
        let p1 = ProcessId(1);

        let mut vc1 = VectorClock::default();
        vc1.tick(p0); // [1, 0]

        let mut vc2 = VectorClock::default();
        vc2.tick(p1); // [0, 1]

        // Neither happens-before the other (concurrent)
        assert!(!vc1.happens_before(&vc2));
        assert!(!vc2.happens_before(&vc1));
    }

    #[test]
    fn test_backtrack_info_default() {
        let info = BacktrackInfo::default();
        assert!(info.backtrack.is_empty());
        assert!(info.done.is_empty());
    }

    #[test]
    fn test_execution_prefix_construction() {
        let prefix = ExecutionPrefix {
            events: vec![Event {
                seq: 0,
                action: ActionId {
                    branch_label: "LAdd".to_string(),
                    process: ProcessId(0),
                },
                pre_state: StateFingerprint(0),
                post_state: StateFingerprint(1),
                clock: VectorClock::default(),
            }],
            initial_state: StateFingerprint(0),
        };
        assert_eq!(prefix.events.len(), 1);
        assert_eq!(prefix.events[0].action.branch_label, "LAdd");
    }

    #[test]
    fn test_state_fingerprint_equality() {
        let f1 = StateFingerprint(42);
        let f2 = StateFingerprint(42);
        let f3 = StateFingerprint(99);
        assert_eq!(f1, f2);
        assert_ne!(f1, f3);
    }

    #[test]
    fn test_action_id_ordering() {
        let a1 = ActionId {
            branch_label: "A".to_string(),
            process: ProcessId(0),
        };
        let a2 = ActionId {
            branch_label: "B".to_string(),
            process: ProcessId(0),
        };
        let a3 = ActionId {
            branch_label: "A".to_string(),
            process: ProcessId(1),
        };
        // BTreeSet ordering works
        let mut set = BTreeSet::new();
        set.insert(a2.clone());
        set.insert(a1.clone());
        set.insert(a3.clone());
        assert_eq!(set.len(), 3);
    }

    #[test]
    fn test_transition_footprint_independent() {
        let fp1 = TransitionFootprint {
            reads: ["x".to_string()].into(),
            writes: ["y".to_string()].into(),
        };
        let fp2 = TransitionFootprint {
            reads: ["z".to_string()].into(),
            writes: ["w".to_string()].into(),
        };
        assert!(fp1.independent_of(&fp2));
        assert!(fp2.independent_of(&fp1));
    }

    #[test]
    fn test_transition_footprint_dependent_write_read() {
        let fp1 = TransitionFootprint {
            reads: BTreeSet::new(),
            writes: ["x".to_string()].into(),
        };
        let fp2 = TransitionFootprint {
            reads: ["x".to_string()].into(),
            writes: BTreeSet::new(),
        };
        // fp1 writes x, fp2 reads x → dependent
        assert!(!fp1.independent_of(&fp2));
        assert!(!fp2.independent_of(&fp1));
    }

    #[test]
    fn test_transition_footprint_dependent_write_write() {
        let fp1 = TransitionFootprint {
            reads: BTreeSet::new(),
            writes: ["x".to_string()].into(),
        };
        let fp2 = TransitionFootprint {
            reads: BTreeSet::new(),
            writes: ["x".to_string()].into(),
        };
        // Both write x → dependent
        assert!(!fp1.independent_of(&fp2));
    }

    #[test]
    fn test_enabled_transition_construction() {
        let t = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "LAdd".to_string(),
            successor_fingerprint: StateFingerprint(42),
            ordering_key: "0:LAdd".to_string(),
            footprint: TransitionFootprint {
                reads: ["a".to_string()].into(),
                writes: ["a".to_string(), "b".to_string()].into(),
            },
        };
        assert_eq!(t.process_id, ProcessId(0));
        assert_eq!(t.branch_label, "LAdd");
        assert_eq!(t.footprint.writes.len(), 2);
    }

    #[test]
    fn test_scheduled_step_construction() {
        let transition = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "LAdd".to_string(),
            successor_fingerprint: StateFingerprint(1),
            ordering_key: "0:LAdd".to_string(),
            footprint: TransitionFootprint::default(),
        };
        let step = ScheduledStep {
            transition: transition.clone(),
            enabled: vec![transition],
            pre_state: StateFingerprint(0),
            depth: 0,
        };
        assert_eq!(step.depth, 0);
        assert_eq!(step.enabled.len(), 1);
    }
}

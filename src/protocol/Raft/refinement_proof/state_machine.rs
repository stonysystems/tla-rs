use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use vstd::prelude::*;
use vstd::{map::*, seq::*, set::*};

verus! {

    // =========================================================================
    // Distributed Raft System State
    // =========================================================================

    /// The global state of a distributed Raft cluster.
    /// Models N servers each running the Raft protocol, plus a network of messages.
    pub struct RaftDistributedState {
        pub server_states: Seq<LState>,     // Per-server Raft state (indexed by server ID)
        pub server_constants: Seq<LConstants>, // Per-server constants
        pub network: Set<LRaftMessage>,     // Messages in transit (multiset modeled as set)
        pub num_servers: int,               // Number of servers in the cluster
    }

    /// Well-formedness of the distributed state
    pub open spec fn WellFormedRaftDistributed(ds: RaftDistributedState) -> bool {
        &&& ds.num_servers > 0
        &&& ds.server_states.len() == ds.num_servers
        &&& ds.server_constants.len() == ds.num_servers
        &&& (forall |i: int| 0 <= i < ds.num_servers ==> {
            &&& ds.server_constants[i].my_id == i
            &&& ds.server_constants[i].quorum_size == ds.num_servers / 2 + 1
            &&& ds.server_constants[i].servers == Set::new(|j: int| 0 <= j < ds.num_servers)
        })
    }

    /// Distributed system initialization
    pub open spec fn RaftDistributedInit(ds: RaftDistributedState) -> bool {
        &&& WellFormedRaftDistributed(ds)
        &&& (forall |i: int| 0 <= i < ds.num_servers ==>
            LInit(ds.server_states[i], ds.server_constants[i]))
        &&& ds.network == Set::<LRaftMessage>::empty()
    }

    /// Distributed system step: one server takes a step
    pub open spec fn RaftDistributedNext(ds: RaftDistributedState, ds_: RaftDistributedState) -> bool {
        &&& WellFormedRaftDistributed(ds)
        &&& WellFormedRaftDistributed(ds_)
        &&& ds_.num_servers == ds.num_servers
        &&& ds_.server_constants == ds.server_constants
        &&& exists |server_id: int| {
            &&& 0 <= server_id < ds.num_servers
            // The chosen server transitions
            &&& LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id])
            // All other servers remain unchanged
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        }
    }

    // =========================================================================
    // Behavior (sequence of distributed states)
    // =========================================================================

    pub type RaftBehavior = Seq<RaftDistributedState>;

    /// A valid Raft behavior: initial state followed by valid transitions
    pub open spec fn IsValidRaftBehavior(b: RaftBehavior) -> bool {
        &&& b.len() > 0
        &&& RaftDistributedInit(b[0])
        &&& (forall |i: int| #![trigger b[i]] 0 <= i < b.len() - 1 ==> RaftDistributedNext(b[i], b[i + 1]))
    }

    // =========================================================================
    // Abstract Sequential State Machine
    // =========================================================================

    /// The abstract state: a simple sequential log of committed values.
    /// This is what the Raft protocol "refines" — a single ordered log
    /// that all correct servers eventually agree on.
    pub struct RaftSystemState {
        pub committed_log: Seq<int>,        // Committed values in order
        pub server_ids: Set<int>,           // The set of server IDs (constant)
    }

    /// Abstract initial state: empty committed log
    pub open spec fn RaftSystemInit(rs: RaftSystemState, server_ids: Set<int>) -> bool {
        &&& rs.committed_log == Seq::<int>::empty()
        &&& rs.server_ids == server_ids
    }

    /// Abstract next step: extend the committed log by one or more entries.
    /// The existing prefix is preserved and at least one new entry is added.
    /// This allows a single distributed step to commit multiple log entries
    /// (e.g., when LAdvanceCommitIndex jumps commit_index by several entries).
    pub open spec fn RaftSystemNextAppendCommitted(
        rs: RaftSystemState,
        rs_: RaftSystemState,
    ) -> bool {
        &&& rs_.committed_log.len() > rs.committed_log.len()
        &&& (forall |k: int| #![trigger rs_.committed_log[k]]
             0 <= k < rs.committed_log.len() ==>
             rs_.committed_log[k] == rs.committed_log[k])
        &&& rs_.server_ids == rs.server_ids
    }

    /// Abstract next-state relation: either stutter or extend committed log
    pub open spec fn RaftSystemNext(rs: RaftSystemState, rs_: RaftSystemState) -> bool {
        ||| rs_ == rs   // stutter
        ||| RaftSystemNextAppendCommitted(rs, rs_)
    }

    // =========================================================================
    // Committed Log Extraction
    // =========================================================================

    /// Extract the committed log prefix from the distributed state.
    /// The committed log at step i is the longest prefix of any server's log
    /// such that every entry up to that point is backed by a majority of servers
    /// having that entry in their logs.
    ///
    /// Formally: entry at index k is committed if there exists a majority quorum Q
    /// such that for every server j in Q, j's log has length > k and j's log[k]
    /// matches the entry. The committed log is the longest prefix of such entries.
    ///
    /// For safety, we use the strongest definition: the committed log is the
    /// prefix up to the minimum commit_index among all servers that are leaders
    /// in the current term, or we look at majority agreement on log entries.
    ///
    /// Simplified definition: extract from the leader's commit_index.
    pub open spec fn GetCommittedLog(ds: RaftDistributedState) -> Seq<int> {
        // The committed log is derived from the longest commit prefix
        // backed by majority agreement. For well-behaved behaviors,
        // this equals the leader's log[0..commit_index].
        //
        // We define it as the log prefix up to the maximum commit_index
        // among all servers, projected through any server's log.
        // Safety invariants ensure all servers agree on committed entries.
        let max_commit = MaxCommitIndex(ds);
        if max_commit <= 0 {
            Seq::<int>::empty()
        } else {
            // Use the first server that has commit_index >= max_commit
            // (Safety invariants guarantee all such servers agree)
            let server_id = choose |id: int| 0 <= id < ds.num_servers
                && ds.server_states[id].commit_index >= max_commit
                && ds.server_states[id].log.len() >= max_commit;
            ExtractLogValues(ds.server_states[server_id].log, max_commit)
        }
    }

    /// Maximum commit_index across all servers
    pub open spec fn MaxCommitIndex(ds: RaftDistributedState) -> int
        decreases ds.num_servers
    {
        if ds.num_servers <= 0 {
            0
        } else {
            let last_commit = ds.server_states[ds.num_servers - 1].commit_index;
            let rest_max = MaxCommitIndex(RaftDistributedState {
                server_states: ds.server_states.subrange(0, ds.num_servers - 1),
                server_constants: ds.server_constants.subrange(0, ds.num_servers - 1),
                network: ds.network,
                num_servers: ds.num_servers - 1,
            });
            if last_commit > rest_max { last_commit } else { rest_max }
        }
    }

    /// Extract values from log entries up to a given length
    pub open spec fn ExtractLogValues(log: Seq<LLogEntry>, len: int) -> Seq<int>
        decreases len
    {
        if len <= 0 || len > log.len() {
            Seq::<int>::empty()
        } else if len == 1 {
            seq![log[0].value]
        } else {
            ExtractLogValues(log, len - 1).push(log[len - 1].value)
        }
    }

    // =========================================================================
    // Refinement Relation
    // =========================================================================

    /// The refinement relation: a distributed Raft state maps to an abstract state
    /// if the abstract committed log matches the committed log extracted from
    /// the distributed state.
    pub open spec fn RaftSystemRefinement(
        ds: RaftDistributedState,
        rs: RaftSystemState
    ) -> bool {
        &&& rs.server_ids == Set::new(|j: int| 0 <= j < ds.num_servers)
        &&& rs.committed_log == GetCommittedLog(ds)
    }

    /// Top-level correctness: the abstract behavior refines the distributed behavior
    pub open spec fn RaftSystemBehaviorRefinementCorrect(
        low_level_behavior: RaftBehavior,
        high_level_behavior: Seq<RaftSystemState>
    ) -> bool {
        &&& high_level_behavior.len() == low_level_behavior.len()
        &&& high_level_behavior.len() > 0
        &&& RaftSystemInit(
            high_level_behavior[0],
            Set::new(|j: int| 0 <= j < low_level_behavior[0].num_servers)
        )
        &&& (forall |i: int| #![trigger low_level_behavior[i]] 0 <= i < low_level_behavior.len() ==>
            RaftSystemRefinement(low_level_behavior[i], high_level_behavior[i]))
        &&& (forall |i: int| #![trigger high_level_behavior[i]] 0 <= i < high_level_behavior.len() - 1 ==>
            RaftSystemNext(high_level_behavior[i], high_level_behavior[i + 1]))
    }

    // =========================================================================
    // Helper: Seq-based max commit index (avoids WellFormedness constraints)
    // =========================================================================

    /// Maximum commit_index across a sequence of server states.
    /// This is equivalent to MaxCommitIndex but takes only the server_states
    /// sequence, avoiding the need for WellFormedRaftDistributed in proofs.
    pub open spec fn max_commit_index_seq(states: Seq<LState>) -> int
        decreases states.len()
    {
        if states.len() <= 0 {
            0
        } else {
            let last_commit = states[states.len() - 1].commit_index;
            let rest_max = max_commit_index_seq(states.subrange(0, states.len() - 1));
            if last_commit > rest_max { last_commit } else { rest_max }
        }
    }

    /// Equivalence: MaxCommitIndex(ds) == max_commit_index_seq(ds.server_states)
    /// when ds.server_states.len() == ds.num_servers
    pub proof fn lemma_max_commit_index_eq_seq(ds: RaftDistributedState)
        requires ds.server_states.len() == ds.num_servers
        ensures MaxCommitIndex(ds) == max_commit_index_seq(ds.server_states)
        decreases ds.num_servers
    {
        if ds.num_servers > 0 {
            let sub_ds = RaftDistributedState {
                server_states: ds.server_states.subrange(0, ds.num_servers - 1),
                server_constants: ds.server_constants.subrange(0, ds.num_servers - 1),
                network: ds.network,
                num_servers: ds.num_servers - 1,
            };
            assert(sub_ds.server_states.len() == ds.num_servers - 1);
            lemma_max_commit_index_eq_seq(sub_ds);
        }
    }

    /// max_commit_index_seq is at least each server's commit_index
    pub proof fn lemma_max_commit_seq_ge_server(states: Seq<LState>, j: int)
        requires 0 <= j < states.len()
        ensures max_commit_index_seq(states) >= states[j].commit_index
        decreases states.len()
    {
        if states.len() > 0 {
            if j == states.len() - 1 {
                // j is the last element; directly compared in the definition
            } else {
                // j < states.len() - 1; recurse on subrange
                let sub = states.subrange(0, states.len() - 1);
                assert(sub[j] == states[j]);
                lemma_max_commit_seq_ge_server(sub, j);
                // max_commit_index_seq(sub) >= sub[j].commit_index == states[j].commit_index
                // max_commit_index_seq(states) >= max_commit_index_seq(sub)
            }
        }
    }

    /// If every server's commit_index in states' >= that in states,
    /// then max_commit_index_seq(states') >= max_commit_index_seq(states).
    pub proof fn lemma_max_commit_seq_monotone(
        states: Seq<LState>, states_: Seq<LState>
    )
        requires
            states.len() == states_.len(),
            forall |j: int| 0 <= j < states.len()
                ==> #[trigger] states_[j].commit_index >= states[j].commit_index,
        ensures
            max_commit_index_seq(states_) >= max_commit_index_seq(states)
        decreases states.len()
    {
        if states.len() > 0 {
            let n = states.len();
            let sub = states.subrange(0, n - 1);
            let sub_ = states_.subrange(0, n - 1);

            // Per-element monotonicity for the subrange
            assert forall |j: int| 0 <= j < sub.len()
            implies #[trigger] sub_[j].commit_index >= sub[j].commit_index by {
                assert(sub[j] == states[j]);
                assert(sub_[j] == states_[j]);
            }

            lemma_max_commit_seq_monotone(sub, sub_);
            // max_commit_index_seq(sub_) >= max_commit_index_seq(sub)
            // states_[n-1].commit_index >= states[n-1].commit_index
            // max_commit_index_seq(states_) = max(states_[n-1].commit_index, max_commit_index_seq(sub_))
            //                                >= max(states[n-1].commit_index, max_commit_index_seq(sub))
            //                                = max_commit_index_seq(states)
        }
    }

    // =========================================================================
    // Helper Lemma: ExtractLogValues length
    // =========================================================================

    pub proof fn lemma_extract_log_values_len(log: Seq<LLogEntry>, len: int)
        requires 0 <= len <= log.len()
        ensures ExtractLogValues(log, len).len() == len
        decreases len
    {
        if len > 0 {
            lemma_extract_log_values_len(log, len - 1);
        }
    }
}

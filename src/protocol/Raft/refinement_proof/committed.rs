use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::invariants::*;
use crate::protocol::Raft::refinement_proof::induction::*;
use vstd::prelude::*;
use vstd::{map::*, seq::*, set::*};

verus! {

    // =========================================================================
    // Prefix predicate for sequences
    // =========================================================================

    /// s1 is a prefix of s2 (or equal)
    pub open spec fn IsPrefix(s1: Seq<int>, s2: Seq<int>) -> bool {
        &&& s1.len() <= s2.len()
        &&& (forall |k: int| #![trigger s2[k]]
             0 <= k < s1.len() ==> s1[k] == s2[k])
    }

    // =========================================================================
    // Per-server commit_index is monotonically non-decreasing
    // =========================================================================
    //
    // All Raft actions either preserve or increase a server's commit_index:
    // - LTimeout, LClientRequest, LSendAppendEntries: frame (commit_index unchanged)
    // - LGrantVote, LReceiveVoteGranted, LBecomeLeader: commit_index unchanged
    // - LHandleAppendResponse, LHandleAppendReject: commit_index unchanged
    // - LStepDown (step_down_if_needed): commit_index unchanged (..s preserves it)
    // - LFollowerAppendEntries: commit_index = min(max(old, ae_leader_commit), new_log_len)
    // - LAdvanceCommitIndex: commit_index increases

    pub proof fn lemma_commit_index_nondecreasing_for_server(
        ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int, j: int
    )
        requires
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            CommitIndexBounded(ds),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            ServerTookStep(ds, ds_, server_id),
            0 <= j < ds.num_servers,
        ensures
            ds_.server_states[j].commit_index >= ds.server_states[j].commit_index
    {
        if j != server_id {
            // Non-stepping server: state unchanged
            assert(ds_.server_states[j] == ds.server_states[j]);
        }
        // For j == server_id: all actions have s_.commit_index >= s.commit_index.
        // LFollowerAppendEntries: min(ae_leader_commit, new_log_len) >= s.commit_index
        //   because ae_leader_commit > s.commit_index and new_log_len >= s.log.len()
        //   >= s.commit_index (from CommitIndexBounded).
        // All other branches: commit_index unchanged or increased.
    }

    // =========================================================================
    // MaxCommitIndex is monotonically non-decreasing
    // =========================================================================

    /// Helper: MaxCommitIndex is at least each server's commit_index.
    /// Uses seq-based helper to avoid sub-state WellFormedness issues.
    pub proof fn lemma_max_commit_index_ge_server(
        ds: RaftDistributedState, j: int
    )
        requires
            WellFormedRaftDistributed(ds),
            0 <= j < ds.num_servers,
        ensures
            MaxCommitIndex(ds) >= ds.server_states[j].commit_index
    {
        // Establish equivalence: MaxCommitIndex(ds) == max_commit_index_seq(ds.server_states)
        lemma_max_commit_index_eq_seq(ds);
        // Use the seq-based lemma which doesn't need WellFormedness for recursion
        lemma_max_commit_seq_ge_server(ds.server_states, j);
    }

    /// MaxCommitIndex is non-decreasing across a distributed step.
    /// Uses seq-based helpers for clean recursive reasoning.
    pub proof fn lemma_max_commit_index_nondecreasing(
        ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int
    )
        requires
            RaftSafetyInvariant(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            ServerTookStep(ds, ds_, server_id),
        ensures
            MaxCommitIndex(ds_) >= MaxCommitIndex(ds)
    {
        // Step 1: Per-server commit_index is non-decreasing
        assert forall |j: int| 0 <= j < ds.num_servers
        implies #[trigger] ds_.server_states[j].commit_index
                >= ds.server_states[j].commit_index by {
            lemma_commit_index_nondecreasing_for_server(ds, ds_, server_id, j);
        }

        // Step 2: Convert to seq-based helpers
        lemma_max_commit_index_eq_seq(ds);
        lemma_max_commit_index_eq_seq(ds_);

        // Step 3: Apply seq-based monotonicity
        lemma_max_commit_seq_monotone(ds.server_states, ds_.server_states);
    }

    // =========================================================================
    // Committed log is monotonically non-decreasing (prefix chain)
    // =========================================================================
    //
    // GetCommittedLog(ds) is a prefix of GetCommittedLog(ds_) when
    // ds →step ds_. This requires:
    // 1. MaxCommitIndex is non-decreasing (proved above)
    // 2. Log entries in the committed prefix are preserved (needs StateMachineSafety)

    /// Prefix preservation via a common server s that qualifies in both ds and ds_.
    /// s.commit_index(ds_) >= MaxCommitIndex(ds) and log preserved → prefix matches.
    proof fn lemma_committed_log_prefix_via_server(
        ds: RaftDistributedState, ds_: RaftDistributedState, s: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            CommitIndexBounded(ds),
            StateMachineSafety(ds),
            WellFormedRaftDistributed(ds_),
            CommitIndexBounded(ds_),
            StateMachineSafety(ds_),
            ds_.num_servers == ds.num_servers,
            MaxCommitIndex(ds) > 0,
            MaxCommitIndex(ds_) >= MaxCommitIndex(ds),
            0 <= s < ds.num_servers,
            ds.server_states[s].commit_index >= MaxCommitIndex(ds),
            ds.server_states[s].log.len() >= MaxCommitIndex(ds),
            ds_.server_states[s].commit_index >= ds.server_states[s].commit_index,
            ds_.server_states[s].log.len() >= ds.server_states[s].log.len(),
            forall |k: int| #![trigger ds.server_states[s].log[k]]
                0 <= k < ds.server_states[s].log.len() ==>
                ds_.server_states[s].log[k] == ds.server_states[s].log[k],
        ensures
            forall |k: int| #![trigger GetCommittedLog(ds_)[k]]
                0 <= k < GetCommittedLog(ds).len()
                ==> GetCommittedLog(ds)[k] == GetCommittedLog(ds_)[k]
    {
        let old_log = GetCommittedLog(ds);
        let old_max = MaxCommitIndex(ds);
        lemma_committed_log_len(ds);
        lemma_committed_log_len(ds_);

        assert forall |k: int| #![trigger GetCommittedLog(ds_)[k]]
            0 <= k < old_log.len()
        implies GetCommittedLog(ds)[k] == GetCommittedLog(ds_)[k]
        by {
            lemma_committed_log_entry_via_server(ds, s, k);
            // ds.server_states[s].log[k] == ds_.server_states[s].log[k] (from requires)
            lemma_committed_log_entry_via_server(ds_, s, k);
        };
    }

    /// GetCommittedLog(ds)[k] == server.log[k].value for any server with
    /// commit_index > k and log.len() > k, given SMS(ds).
    /// This allows using any qualifying server to read committed log entries.
    proof fn lemma_committed_log_entry_via_server(
        ds: RaftDistributedState, server_id: int, k: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            CommitIndexBounded(ds),
            StateMachineSafety(ds),
            MaxCommitIndex(ds) > 0,
            0 <= server_id < ds.num_servers,
            ds.server_states[server_id].commit_index > k,
            ds.server_states[server_id].log.len() > k,
            0 <= k < MaxCommitIndex(ds),
        ensures
            GetCommittedLog(ds)[k] == ds.server_states[server_id].log[k].value,
    {
        lemma_max_commit_index_witness(ds);
        let chosen = choose |id: int| 0 <= id < ds.num_servers
            && ds.server_states[id].commit_index >= MaxCommitIndex(ds)
            && ds.server_states[id].log.len() >= MaxCommitIndex(ds);
        // GetCommittedLog(ds)[k] == chosen.log[k].value
        lemma_extract_log_values_index(ds.server_states[chosen].log, MaxCommitIndex(ds), k);
        // SMS(ds): chosen.log[k] == server_id.log[k] (both have commit_index > k)
        assert(StateMachineSafety(ds));
    }

    pub proof fn lemma_committed_log_monotone(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
            RaftSafetyInvariant(ds_),
        ensures
            IsPrefix(GetCommittedLog(ds), GetCommittedLog(ds_))
    {
        // Extract step parameters first (in this function where RaftDistributedNext is available)
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |sid: int| {
            &&& 0 <= sid < ds.num_servers
            &&& LNext(ds.server_states[sid], ds_.server_states[sid],
                       ds.server_constants[sid])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        // Length monotonicity (needs RaftSafetyInvariant for commit_index_nondecreasing)
        lemma_max_commit_index_nondecreasing(ds, ds_, server_id);
        lemma_committed_log_len(ds);
        lemma_committed_log_len(ds_);

        // Prefix preservation: delegate to core with minimal invariants
        lemma_committed_log_monotone_core(ds, ds_, server_id);
    }

    /// Core prefix preservation: takes only WellFormed, CommitIndexBounded, SMS.
    /// No LogMatching/LeaderCompleteness in scope to avoid quantifier blow-up.
    proof fn lemma_committed_log_monotone_core(
        ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            CommitIndexBounded(ds),
            StateMachineSafety(ds),
            WellFormedRaftDistributed(ds_),
            CommitIndexBounded(ds_),
            StateMachineSafety(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= server_id < ds.num_servers,
            ServerTookStep(ds, ds_, server_id),
            MaxCommitIndex(ds_) >= MaxCommitIndex(ds),
        ensures
            forall |k: int| #![trigger GetCommittedLog(ds_)[k]]
                0 <= k < GetCommittedLog(ds).len()
                ==> GetCommittedLog(ds)[k] == GetCommittedLog(ds_)[k]
    {
        let old_max = MaxCommitIndex(ds);
        if old_max > 0 {
            lemma_max_commit_index_witness(ds);
            let s0 = choose |id: int| 0 <= id < ds.num_servers
                && ds.server_states[id].commit_index >= old_max
                && ds.server_states[id].log.len() >= old_max;
            if s0 != server_id {
                assert(ds_.server_states[s0] == ds.server_states[s0]);
                lemma_committed_log_prefix_via_server(ds, ds_, s0);
            } else {
                lemma_commit_index_nondecreasing_for_server(ds, ds_, server_id, s0);
                lemma_committed_log_prefix_via_server(ds, ds_, s0);
            }
        }
    }

    // =========================================================================
    // Committed log entries are unique across servers
    // =========================================================================
    //
    // If two servers both have commit_index > k, they agree on log[k].
    // This is a direct consequence of StateMachineSafety.

    pub proof fn lemma_committed_entries_agree(
        ds: RaftDistributedState, i: int, j: int, k: int
    )
        requires
            RaftSafetyInvariant(ds),
            0 <= i < ds.num_servers,
            0 <= j < ds.num_servers,
            0 <= k < ds.server_states[i].commit_index,
            0 <= k < ds.server_states[j].commit_index,
            k < ds.server_states[i].log.len(),
            k < ds.server_states[j].log.len(),
        ensures
            ds.server_states[i].log[k] == ds.server_states[j].log[k]
    {
        assert(StateMachineSafety(ds));
    }

    // =========================================================================
    // Abstract step follows from committed log monotonicity
    // =========================================================================
    //
    // Given that the committed log is a prefix chain, the abstract state
    // transition is a valid RaftSystemNext step.

    pub proof fn lemma_abstract_step_valid(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        rs: RaftSystemState, rs_: RaftSystemState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
            RaftSafetyInvariant(ds_),
            RaftSystemRefinement(ds, rs),
            RaftSystemRefinement(ds_, rs_),
        ensures
            RaftSystemNext(rs, rs_),
    {
        lemma_committed_log_monotone(ds, ds_);

        let old_log = GetCommittedLog(ds);
        let new_log = GetCommittedLog(ds_);

        // rs.committed_log == old_log, rs_.committed_log == new_log
        // old_log is a prefix of new_log

        if old_log.len() == new_log.len() {
            // Same length + prefix → same log.
            // Need to show rs_ == rs.
            // rs.committed_log == old_log == new_log == rs_.committed_log
            // rs.server_ids == rs_.server_ids (both derived from num_servers)
            assert(rs_.server_ids == rs.server_ids);
            // For log equality with same length, prefix implies equality
            assert forall |k: int| #![trigger old_log[k]]
                0 <= k < old_log.len()
            implies old_log[k] == new_log[k]
            by {
                // From IsPrefix
            }
            // Extensional equality: same committed_log and same server_ids → same struct
            assert(rs_.committed_log =~= rs.committed_log);
            assert(rs_.server_ids =~= rs.server_ids);
        } else {
            // new_log is strictly longer: RaftSystemNextAppendCommitted
            assert(new_log.len() > old_log.len());
            // Prefix preservation: forall k < old_log.len(). old_log[k] == new_log[k]
            // → rs_.committed_log[k] == rs.committed_log[k]
            // This gives us RaftSystemNextAppendCommitted(rs, rs_)
        }
    }
}

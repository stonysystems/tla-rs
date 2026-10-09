use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::membership::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::invariants::*;
use crate::protocol::Raft::refinement_proof::dynamic_invariant::*;
use vstd::prelude::*;
use vstd::{map::*, seq::*, set::*};

verus! {

    // =========================================================================
    // Helper predicate: identifies which server took the step
    // =========================================================================

    pub open spec fn ServerTookStep(
        ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int
    ) -> bool {
        &&& 0 <= server_id < ds.num_servers
        &&& LNext(ds.server_states[server_id], ds_.server_states[server_id],
                   ds.server_constants[server_id])
        &&& (forall |j: int| #![trigger ds_.server_states[j]]
            0 <= j < ds.num_servers && j != server_id ==>
            ds_.server_states[j] == ds.server_states[j])
    }

    // =========================================================================
    // Main induction theorem: the invariant is preserved by every step
    // =========================================================================
    //
    // Every step is an honest protocol step or a reboot, including steps that
    // propose and commit membership changes. Commit certificates are recorded
    // by the transition, never required of it; dynamic_*.rs prove that each
    // one is backed by a quorum of the phase that governs its index.

    pub proof fn lemma_next_preserves_invariant(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            DynamicInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            DynamicInvariant(ds_),
    {
        lemma_dynamic_invariant_inductive(ds, ds_);
    }

    // =========================================================================
    // Full induction: invariant holds for all steps of a valid behavior
    // =========================================================================

    pub proof fn lemma_invariant_holds_throughout_behavior(b: RaftBehavior, i: int)
        requires
            IsValidRaftBehavior(b),
            0 <= i < b.len(),
        ensures
            RaftSafetyInvariant(b[i]),
            ElectionSafety(b[i]),
    {
        lemma_dynamic_invariant_holds_throughout_behavior(b, i);
        lemma_dynamic_election_safety(b[i]);
    }

    /// End-to-end safety for physical Raft histories, with membership
    /// changes. At every reachable behavior state, every committed entry is
    /// covered by one global commit certificate. Consequently, two servers
    /// cannot commit different physical entries at the same log index.
    pub proof fn lemma_committed_histories_are_safe(
        b: RaftBehavior,
        behavior_index: int,
    )
        requires
            IsValidRaftBehavior(b),
            0 <= behavior_index < b.len(),
        ensures
            CommittedEntriesHaveLogCertificates(b[behavior_index]),
            StateMachineSafety(b[behavior_index]),
            forall |left: int, right: int, log_index: int| #![trigger b[behavior_index].server_states[left], b[behavior_index].server_states[right].log[log_index]] #![trigger b[behavior_index].server_states[right], b[behavior_index].server_states[left].log[log_index]]
                0 <= left < b[behavior_index].num_servers
                && 0 <= right < b[behavior_index].num_servers
                && 0 <= log_index
                    < b[behavior_index].server_states[left].commit_index
                && 0 <= log_index
                    < b[behavior_index].server_states[right].commit_index
                && log_index
                    < b[behavior_index].server_states[left].log.len()
                && log_index
                    < b[behavior_index].server_states[right].log.len()
                ==> b[behavior_index].server_states[left].log[log_index]
                    == b[behavior_index].server_states[right].log[log_index],
    {
        lemma_invariant_holds_throughout_behavior(b, behavior_index);
        assert(RaftSafetyInvariant(b[behavior_index]));
    }

    /// Certificate-level formulation of dynamic commitment. Unlike the
    /// legacy EntryCommittedAt predicate, this definition records which
    /// membership phase and quorum authorized the physical entry.
    pub open spec fn DynamicallyCommittedAt(
        ds: RaftDistributedState,
        log_index: int,
        entry: LLogEntry,
    ) -> bool {
        &&& ds.log_commit_certificates.dom().contains(log_index)
        &&& ds.log_commit_certificates[log_index].log_index == log_index
        &&& ds.log_commit_certificates[log_index].entry == entry
    }

    // `DynamicLeaderCompleteness` now lives in `invariants.rs`, stated directly
    // over the certificate map, so it can become a conjunct of
    // `RaftSafetyInvariant` without `invariants.rs` having to import this
    // module. It reaches here through the glob import.

    /// History agrees with any node's currently committed physical prefix.
    pub proof fn lemma_local_commit_matches_history(
        ds: RaftDistributedState, sid: int, k: int,
    )
        requires
            CommitHistoryValid(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexBounded(ds),
            0 <= sid < ds.num_servers,
            0 <= k < ds.server_states[sid].commit_index,
        ensures
            k < ds.committed_history.len(),
            ds.committed_history[k] == ds.server_states[sid].log[k],
    {
        assert(ds.log_commit_certificates[k].entry == ds.committed_history[k]);
        assert(ds.log_commit_certificates[k].entry == ds.server_states[sid].log[k]);
    }

    /// Once a node commits an entry, the same entry remains in its durable log
    /// and in abstract history at every later state, across intervening reboots.
    pub proof fn lemma_committed_entry_survives_reboots(
        b: RaftBehavior, earlier: int, later: int, sid: int, k: int,
    )
        requires
            IsValidRaftBehavior(b),
            0 <= earlier <= later < b.len(),
            0 <= sid < b[earlier].num_servers,
            0 <= k < b[earlier].server_states[sid].commit_index,
        ensures
            k < b[later].committed_history.len(),
            b[later].committed_history[k] == b[earlier].server_states[sid].log[k],
            0 <= sid < b[later].num_servers,
            k < b[later].server_states[sid].log.len(),
            b[later].server_states[sid].log[k] == b[earlier].server_states[sid].log[k],
        decreases later - earlier
    {
        lemma_invariant_holds_throughout_behavior(b, later);
        if earlier == later {
            lemma_local_commit_matches_history(b[earlier], sid, k);
        } else {
            lemma_committed_entry_survives_reboots(b, earlier, later - 1, sid, k);
            lemma_invariant_holds_throughout_behavior(b, later - 1);
            crate::protocol::Raft::refinement_proof::committed::lemma_committed_history_monotone(
                b[later - 1], b[later]);
            if RaftDistributedNormalNext(b[later - 1], b[later]) {
                crate::protocol::Raft::refinement_proof::message_invariants::lemma_log_append_only(
                    b[later - 1], b[later]);
            } else {
                let rebooted = choose |i: int|
                    #![trigger RaftDistributedReboot(b[later - 1], b[later], i)]
                    RaftDistributedReboot(b[later - 1], b[later], i);
                crate::protocol::Raft::refinement_proof::recovery::lemma_reboot_frame(
                    b[later - 1], b[later], rebooted);
            }
        }
    }

    /// Safety across time, not just agreement among the current commit indices.
    pub proof fn lemma_commits_at_different_times_agree(
        b: RaftBehavior, earlier: int, later: int, left: int, right: int, k: int,
    )
        requires
            IsValidRaftBehavior(b),
            0 <= earlier <= later < b.len(),
            0 <= left < b[earlier].num_servers,
            0 <= right < b[later].num_servers,
            0 <= k < b[earlier].server_states[left].commit_index,
            k < b[later].server_states[right].commit_index,
        ensures
            b[earlier].server_states[left].log[k] == b[later].server_states[right].log[k],
    {
        lemma_committed_entry_survives_reboots(b, earlier, later, left, k);
        lemma_invariant_holds_throughout_behavior(b, later);
        lemma_local_commit_matches_history(b[later], right, k);
    }

}

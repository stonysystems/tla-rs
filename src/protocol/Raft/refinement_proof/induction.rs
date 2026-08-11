use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::membership::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::invariants::*;
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
    // Main induction theorem: RaftSafetyInvariant is preserved by steps
    // =========================================================================
    //
    // Delegates to lemma_safety_invariant_inductive in invariants.rs, which
    // proves all conjuncts of RaftSafetyInvariant including the supporting
    // invariants (VotesGrantedAreServers, CandidateOrLeaderVotedForSelf,
    // VotersVotedForCandidate) and the core safety properties.

    pub proof fn lemma_next_preserves_invariant(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            RaftSafetyInvariant(ds_),
    {
        // Delegate to the composite induction lemma in invariants.rs,
        // which proves all conjuncts of RaftSafetyInvariant (including
        // VotesGrantedAreServers, CandidateOrLeaderVotedForSelf,
        // VotersVotedForCandidate, and the 4 core safety invariants).
        lemma_safety_invariant_inductive(ds, ds_);
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
        decreases i
    {
        if i == 0 {
            lemma_init_establishes_invariant(b[0]);
        } else {
            lemma_invariant_holds_throughout_behavior(b, i - 1);
            lemma_next_preserves_invariant(b[i - 1], b[i]);
        }
    }

    /// End-to-end dynamic-membership safety for physical Raft histories.
    /// At every reachable behavior state, every committed Data or
    /// Configuration entry is covered by one global commit certificate.
    /// Consequently, two servers cannot commit different
    /// physical entries at the same log index.
    pub proof fn lemma_dynamic_membership_committed_histories_are_safe(
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
}

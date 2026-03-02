use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
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
}

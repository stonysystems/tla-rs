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

    /// Every concrete transition in a reachable Raft behavior commits only
    /// a legal chain of membership phases.
    ///
    /// This lifts the distributed one-step theorem through the established
    /// behavior invariant: the pre-state of every behavior step satisfies
    /// RaftSafetyInvariant, so the transition-wide membership result applies.
    pub proof fn lemma_behavior_step_membership_commit_intervals_are_legal(
        b: RaftBehavior,
        step_index: int,
    )
        requires
            IsValidRaftBehavior(b),
            0 <= step_index < b.len() - 1,
        ensures
            forall |server_id: int|
                #![trigger b[step_index].server_states[server_id]]
                0 <= server_id
                    < b[step_index].num_servers
                ==> {
                    let pre_state =
                        b[step_index].server_states[server_id];
                    let post_state =
                        b[step_index + 1].server_states[server_id];
                    let initial_phase = MembershipPhase::Stable {
                        config: b[step_index]
                            .server_constants[server_id].servers,
                    };

                    &&& pre_state.commit_index
                        <= post_state.commit_index
                    &&& active_membership_phase_from_raft_log(
                        pre_state.log,
                        pre_state.commit_index,
                        initial_phase,
                    ) == active_membership_phase_from_raft_log(
                        post_state.log,
                        pre_state.commit_index,
                        initial_phase,
                    )
                    &&& forall |committed_len: int|
                        pre_state.commit_index < committed_len
                            <= post_state.commit_index
                        ==> is_legal_phase_progression(
                            active_membership_phase_from_raft_log(
                                post_state.log,
                                committed_len - 1,
                                initial_phase,
                            ),
                            #[trigger] active_membership_phase_from_raft_log(
                                post_state.log,
                                committed_len,
                                initial_phase,
                            ),
                        )
                },
    {
        lemma_invariant_holds_throughout_behavior(
            b,
            step_index,
        );

        assert(RaftDistributedNext(
            b[step_index],
            b[step_index + 1],
        ));

        lemma_distributed_next_membership_commit_intervals_are_legal(
            b[step_index],
            b[step_index + 1],
        );
    }
}

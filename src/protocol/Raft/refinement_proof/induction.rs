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
    /// Configuration entry is covered by one valid dynamic-quorum
    /// certificate. Consequently, two servers cannot commit different
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
            LogCommitCertificatesValid(b[behavior_index]),
            StateMachineSafety(b[behavior_index]),
            forall |left: int, right: int, log_index: int|
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

    /// Legacy fixed-majority Leader Completeness at every reachable state.
    ///
    /// This is deliberately kept as its own induction rather than folded into
    /// `RaftSafetyInvariant`: the inherited proof of
    /// `lemma_leader_completeness_inductive` rests on `assume(false)` cases,
    /// and the certificate-based committed-history theorem must stay
    /// independent of them.
    pub proof fn lemma_leader_completeness_holds_throughout_behavior(
        b: RaftBehavior,
        i: int,
    )
        requires
            IsValidRaftBehavior(b),
            0 <= i < b.len(),
        ensures
            LeaderCompleteness(b[i]),
        decreases i
    {
        if i == 0 {
            lemma_init_establishes_leader_completeness(b[0]);
        } else {
            lemma_leader_completeness_holds_throughout_behavior(b, i - 1);
            lemma_invariant_holds_throughout_behavior(b, i - 1);
            lemma_leader_completeness_inductive(b[i - 1], b[i]);
        }
    }

    /// Certified Configuration Leader Completeness, unconditionally, for every
    /// certificate governed by a Stable phase over the whole server set: a
    /// higher-term leader always holds such a certified boundary.
    ///
    /// This is the membership-stable fragment of Milestone B. The genuinely
    /// dynamic cases — a Joint phase, or a Stable phase over a proper subset —
    /// are out of reach of this route, because their quorums need not meet the
    /// legacy fixed-majority threshold that `EntryCommittedAt` demands.
    pub proof fn lemma_stable_certified_boundary_present_in_later_leader(
        b: RaftBehavior,
        behavior_index: int,
        index: int,
        config: Set<int>,
        leader_id: int,
    )
        requires
            IsValidRaftBehavior(b),
            0 <= behavior_index < b.len(),
            b[behavior_index].configuration_commit_certificates.dom()
                .contains(index),
            b[behavior_index].configuration_commit_certificates[index]
                .governing_phase
                == (MembershipPhase::Stable { config: config }),
            config.len() == b[behavior_index].num_servers,
            0 <= index,
            0 <= leader_id < b[behavior_index].num_servers,
            b[behavior_index].server_states[leader_id].role is Leader,
            b[behavior_index].server_states[leader_id].current_term
                > b[behavior_index].configuration_commit_certificates[index]
                    .entry.term,
        ensures
            b[behavior_index].server_states[leader_id].log.len() > index,
            b[behavior_index].server_states[leader_id].log[index]
                == b[behavior_index].configuration_commit_certificates[index]
                    .entry,
    {
        lemma_invariant_holds_throughout_behavior(b, behavior_index);
        lemma_leader_completeness_holds_throughout_behavior(b, behavior_index);
        lemma_legacy_leader_completeness_covers_stable_certificate(
            b[behavior_index],
            index,
            config,
            leader_id,
        );
    }

    /// Behaviour-level Configuration Leader Completeness under dynamic
    /// membership, conditional on the first-missing-boundary provenance.
    ///
    /// In every reachable state of every valid behaviour, a leader whose term
    /// exceeds a certified Configuration entry's term contains that exact
    /// entry at its certified log index. The only hypothesis beyond
    /// reachability is `FirstMissingConfigurationBoundaryProvenance`; the
    /// log-transfer step it ultimately rests on is discharged by the inherited
    /// static-Raft lemma, not by anything specific to membership changes.
    pub proof fn lemma_configuration_leader_completeness_throughout_behavior(
        b: RaftBehavior,
        behavior_index: int,
    )
        requires
            IsValidRaftBehavior(b),
            0 <= behavior_index < b.len(),
            FirstMissingConfigurationBoundaryProvenance(b[behavior_index]),
        ensures
            CertifiedConfigurationLeaderCompleteness(b[behavior_index]),
    {
        lemma_invariant_holds_throughout_behavior(b, behavior_index);
        lemma_safety_invariant_implies_configuration_leader_completeness(
            b[behavior_index],
        );
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

    /// Strong dynamic Leader Completeness statement. Its preservation is the
    /// remaining election-provenance obligation for leaders elected from a
    /// stale committed configuration; committed-history safety above does not
    /// rely on this unproved strengthening.
    pub open spec fn DynamicLeaderCompleteness(
        ds: RaftDistributedState,
    ) -> bool {
        forall |log_index: int, entry: LLogEntry, leader_id: int|
            0 <= log_index
            && DynamicallyCommittedAt(ds, log_index, entry)
            && 0 <= leader_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term > entry.term
            ==> {
                &&& ds.server_states[leader_id].log.len() > log_index
                &&& ds.server_states[leader_id].log[log_index] == entry
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

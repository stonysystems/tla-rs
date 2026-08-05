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
        // Subsumed: Configuration Leader Completeness is now a conjunct of the
        // global invariant, so it holds of any reachable state outright. The
        // Stable-membership route via legacy fixed-majority Leader
        // Completeness is no longer needed.
        lemma_invariant_holds_throughout_behavior(b, behavior_index);
        assert(CertifiedConfigurationLeaderCompleteness(b[behavior_index]));
    }

    /// Milestone B, behaviour level and unconditional: in every reachable
    /// state, a leader whose term exceeds a certified Configuration entry's
    /// term contains that exact entry at its certified log index.
    ///
    /// No hypothesis about membership phases, election snapshots, log lengths
    /// or divergence — Configuration Leader Completeness is now a conjunct of
    /// `RaftSafetyInvariant`, established at initialization and preserved by
    /// every transition.
    pub proof fn lemma_certified_configuration_leader_completeness_throughout_behavior(
        b: RaftBehavior,
        behavior_index: int,
    )
        requires
            IsValidRaftBehavior(b),
            0 <= behavior_index < b.len(),
        ensures
            CertifiedConfigurationLeaderCompleteness(b[behavior_index]),
    {
        lemma_invariant_holds_throughout_behavior(b, behavior_index);
    }

    /// Behaviour-level agreement at certified membership boundaries, with no
    /// membership-phase hypothesis whatsoever.
    ///
    /// In every reachable state, any server that has committed past a certified
    /// Configuration boundary holds exactly the certified entry there. This
    /// holds under joint consensus as well as stable membership, and needs no
    /// assumption about which phase anyone was elected under.
    pub proof fn lemma_certified_boundary_agrees_throughout_behavior(
        b: RaftBehavior,
        behavior_index: int,
        index: int,
        server_id: int,
    )
        requires
            IsValidRaftBehavior(b),
            0 <= behavior_index < b.len(),
            b[behavior_index].configuration_commit_certificates.dom()
                .contains(index),
            0 <= server_id < b[behavior_index].num_servers,
            index < b[behavior_index].server_states[server_id].commit_index,
            index < b[behavior_index].server_states[server_id].log.len(),
        ensures
            b[behavior_index].server_states[server_id].log[index]
                == b[behavior_index].configuration_commit_certificates[index]
                    .entry,
    {
        lemma_invariant_holds_throughout_behavior(b, behavior_index);
        lemma_certified_boundary_agrees_with_committed_server(
            b[behavior_index],
            index,
            server_id,
        );
    }

    /// Behaviour-level joint-consensus Configuration Leader Completeness.
    ///
    /// In every reachable state, a leader elected under a phase that is the
    /// certificate's governing phase — or one legal joint-consensus step
    /// beyond it — holds that certified boundary. This covers `Joint` phases
    /// and `Stable` phases over proper subsets, so it is the genuinely
    /// dynamic-membership case rather than the fixed-majority fragment.
    ///
    /// The only remaining hypothesis is that the two phases are one legal step
    /// apart; the log-transfer step is discharged from the global invariant.
    pub proof fn lemma_certified_boundary_present_in_related_phase_leader(
        b: RaftBehavior,
        behavior_index: int,
        index: int,
        leader_id: int,
        election_phase: MembershipPhase,
    )
        requires
            IsValidRaftBehavior(b),
            0 <= behavior_index < b.len(),
            b[behavior_index].configuration_commit_certificates.dom()
                .contains(index),
            0 <= leader_id < b[behavior_index].num_servers,
            b[behavior_index].server_states[leader_id].role is Leader,
            b[behavior_index].server_states[leader_id].current_term
                > b[behavior_index].configuration_commit_certificates[index]
                    .entry.term,
            b[behavior_index].server_states[leader_id]
                .election_membership_phase == Some(election_phase),
            is_legal_phase_progression(
                b[behavior_index].configuration_commit_certificates[index]
                    .governing_phase,
                election_phase,
            ),
        ensures
            b[behavior_index].server_states[leader_id].log.len() > index,
            b[behavior_index].server_states[leader_id].log[index]
                == b[behavior_index].configuration_commit_certificates[index]
                    .entry,
    {
        // Subsumed: the phase-relatedness hypothesis is no longer needed, since
        // Configuration Leader Completeness now holds of every reachable state
        // unconditionally.
        lemma_invariant_holds_throughout_behavior(b, behavior_index);
        assert(CertifiedConfigurationLeaderCompleteness(b[behavior_index]));
    }

    /// Milestone C's membership-stable fragment: for every dynamically
    /// certified log entry — Data or Configuration — governed by a Stable
    /// phase over the whole server set, every strictly higher-term leader
    /// holds that exact entry at that index, in every reachable state.
    ///
    /// This is `DynamicLeaderCompleteness` restricted to the stable fragment.
    /// The Joint-phase cases remain open for the same quorum-threshold reason
    /// that bounds the Configuration-only result.
    pub proof fn lemma_stable_certified_entry_present_in_later_leader(
        b: RaftBehavior,
        behavior_index: int,
        index: int,
        config: Set<int>,
        leader_id: int,
    )
        requires
            IsValidRaftBehavior(b),
            0 <= behavior_index < b.len(),
            b[behavior_index].log_commit_certificates.dom().contains(index),
            b[behavior_index].log_commit_certificates[index].governing_phase
                == (MembershipPhase::Stable { config: config }),
            config.len() == b[behavior_index].num_servers,
            0 <= leader_id < b[behavior_index].num_servers,
            b[behavior_index].server_states[leader_id].role is Leader,
            b[behavior_index].server_states[leader_id].current_term
                > b[behavior_index].log_commit_certificates[index].entry.term,
        ensures
            b[behavior_index].server_states[leader_id].log.len() > index,
            b[behavior_index].server_states[leader_id].log[index]
                == b[behavior_index].log_commit_certificates[index].entry,
    {
        lemma_invariant_holds_throughout_behavior(b, behavior_index);
        lemma_leader_completeness_holds_throughout_behavior(b, behavior_index);
        lemma_legacy_leader_completeness_covers_stable_log_certificate(
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

    // `DynamicLeaderCompleteness` now lives in `invariants.rs`, stated directly
    // over the certificate map, so it can become a conjunct of
    // `RaftSafetyInvariant` without `invariants.rs` having to import this
    // module. It reaches here through the glob import.

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

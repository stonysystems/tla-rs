//! The inductive invariant for Raft with membership changes, and its
//! preservation by every protocol step and reboot.
//!
//! See docs/raft-joint-consensus-proof-plan.md.

use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::membership::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::invariants::*;
use crate::protocol::Raft::refinement_proof::message_invariants::*;
use crate::protocol::Raft::refinement_proof::static_safety::*;
use crate::protocol::Raft::refinement_proof::dynamic_safety::*;
use crate::protocol::Raft::refinement_proof::dynamic_logs::*;
use crate::protocol::Raft::refinement_proof::dynamic_winners::*;
use crate::protocol::Raft::refinement_proof::dynamic_completeness::*;
use crate::protocol::Raft::refinement_proof::dynamic_election::*;
use vstd::prelude::*;

verus! {

    // =========================================================================
    // Unique winners are preserved
    // =========================================================================

    /// A step adds at most one election record, for the server it promotes.
    pub open spec fn election_records_step(
        ds: RaftDistributedState, ds_: RaftDistributedState, nv: int, nt: int,
    ) -> bool {
        &&& forall |v: int, t: int| #![trigger ds.election_log_len.dom().contains((v, t))]
            ds.election_log_len.dom().contains((v, t)) ==> ds_.election_log_len.dom().contains((v, t))
        &&& forall |v: int, t: int|
            #![trigger ds_.election_log_len.dom().contains((v, t))]
            ds_.election_log_len.dom().contains((v, t)) && !ds.election_log_len.dom().contains((v, t))
            ==> v == nv && t == nt
    }

    pub proof fn lemma_election_records_step(ds: RaftDistributedState, ds_: RaftDistributedState) -> (res: (int, int))
        requires
            WellFormedRaftDistributed(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            election_records_step(ds, ds_, res.0, res.1),
    {
        if RaftDistributedNormalNext(ds, ds_) {
            let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
            assert(RaftServerStepWitness(ds, ds_, server_id, sp, rf));
            let nt = ds_.server_states[server_id].current_term;
            assert forall |v: int, t: int| #![trigger ds.election_log_len.dom().contains((v, t))]
                ds.election_log_len.dom().contains((v, t)) implies ds_.election_log_len.dom().contains((v, t)) by {
                let p = (v, t);
                assert(ds.election_log_len.dom().contains((p.0, p.1)));
                assert(ds_.election_log_len[(p.0, p.1)] == ds.election_log_len[(p.0, p.1)]);
            }
            assert forall |v: int, t: int| #![trigger ds_.election_log_len.dom().contains((v, t))]
                ds_.election_log_len.dom().contains((v, t)) && !ds.election_log_len.dom().contains((v, t))
                implies v == server_id && t == nt by {}
            (server_id, nt)
        } else {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |v: int, t: int| #![trigger ds_.election_log_len.dom().contains((v, t))]
                ds_.election_log_len.dom().contains((v, t)) && !ds.election_log_len.dom().contains((v, t))
                implies v == 0 && t == 0 by {}
            (0, 0)
        }
    }

    pub proof fn lemma_unique_winners_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState, nv: int, nt: int,
    )
        requires
            UniqueWinners(ds),
            CompletenessCore(ds_),
            OneVotePerTermInNetwork(ds_),
            election_records_step(ds, ds_, nv, nt),
        ensures
            UniqueWinners(ds_),
    {
        assert(UniqueWinnersBelow(ds_, nt)) by {
            assert forall |a: int, b: int, t: int|
                #![trigger ds_.election_log_len.dom().contains((a, t)), ds_.election_log_len.dom().contains((b, t))]
                t < nt
                && ds_.election_log_len.dom().contains((a, t))
                && ds_.election_log_len.dom().contains((b, t))
                implies a == b by {
                assert(ds.election_log_len.dom().contains((a, t)));
                assert(ds.election_log_len.dom().contains((b, t)));
            }
        }
        assert forall |a: int, b: int, t: int|
            #![trigger ds_.election_log_len.dom().contains((a, t)), ds_.election_log_len.dom().contains((b, t))]
            ds_.election_log_len.dom().contains((a, t))
            && ds_.election_log_len.dom().contains((b, t))
            implies a == b by {
            if ds.election_log_len.dom().contains((a, t)) && ds.election_log_len.dom().contains((b, t)) {
            } else {
                assert(t == nt);
                lemma_two_winners_coincide(ds_, a, b, t);
            }
        }
    }

    // =========================================================================
    // The invariant
    // =========================================================================

    /// The part of the invariant beyond `RaftSafetyInvariant`.
    pub open spec fn DynamicExtra(ds: RaftDistributedState) -> bool {
        &&& LogMatching(ds)
        &&& AppendResponseLogAgreement(ds)
        &&& MatchIndexBounded(ds)
        &&& MatchIndexImpliesLogAgreement(ds)
        &&& CertificatesHeldByPhaseQuorum(ds)
        &&& AppendEntriesCommitCertified(ds)
        &&& ConfigurationCertificatesMatchLogCertificates(ds)
        &&& HistoryHeld(ds)
        &&& ConfigurationFollowedIsCommitted(ds)
        &&& ConfigurationEntriesLegal(ds)
        &&& CandidateLogBelowTerm(ds)
        &&& WinnerRecords(ds)
        &&& EntryHeldByWinner(ds)
        &&& UniqueWinners(ds)
    }

    pub open spec fn DynamicInvariant(ds: RaftDistributedState) -> bool {
        &&& RaftSafetyInvariant(ds)
        &&& DynamicExtra(ds)
    }

    pub proof fn lemma_dynamic_invariant_init(ds: RaftDistributedState)
        requires
            RaftDistributedInit(ds),
        ensures
            DynamicInvariant(ds),
    {
        lemma_init_establishes_invariant(ds);
        lemma_static_core_init(ds);
        assert forall |i: int| #![trigger ds.server_states[i]] 0 <= i < ds.num_servers
            implies ds.server_states[i].match_index == Map::<u64, u64>::empty() by {
            assert(LInit(ds.server_states[i], ds.server_constants[i]));
        }
        assert(ds.configuration_commit_certificates.dom() =~= Set::<int>::empty());
        lemma_history_held_init(ds);
        lemma_configuration_followed_init(ds);
        lemma_configuration_entries_legal_init(ds);
        lemma_candidate_log_below_init(ds);
        lemma_winner_records_init(ds);
        lemma_entry_held_by_winner_init(ds);
    }

    /// The generic invariant after a step: certificate coverage comes from
    /// the quorum argument, everything else from the generic proof.
    proof fn lemma_dynamic_safety_invariant_next(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            DynamicInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            RaftSafetyInvariant(ds_),
            ConfigurationCertificatesMatchLogCertificates(ds_),
    {
        lemma_dynamic_log_certificates_cover_inductive(ds, ds_);
        lemma_configuration_certificates_match_inductive(ds, ds_);
        lemma_configuration_coverage_from_log_coverage(ds_);
        if RaftDistributedNormalNext(ds, ds_) {
            lemma_safety_invariant_inductive(ds, ds_);
        } else {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            crate::protocol::Raft::refinement_proof::recovery::lemma_reboot_preserves_invariant(ds, ds_, sid);
        }
    }

    /// Replication and certificate invariants after a step.
    proof fn lemma_dynamic_replication_next(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            DynamicInvariant(ds),
            RaftSafetyInvariant(ds_),
            RaftDistributedNext(ds, ds_),
        ensures
            LogMatching(ds_),
            AppendResponseLogAgreement(ds_),
            MatchIndexBounded(ds_),
            MatchIndexImpliesLogAgreement(ds_),
            CertificatesHeldByPhaseQuorum(ds_),
            AppendEntriesCommitCertified(ds_),
    {
        lemma_dynamic_log_matching_inductive(ds, ds_);
        lemma_append_response_log_agreement_next(ds, ds_);
        lemma_match_index_bounded_next(ds, ds_);
        lemma_match_index_log_agreement_next(ds, ds_);
        lemma_dynamic_certificates_held_inductive(ds, ds_);
        lemma_append_entries_commit_certified_next(ds, ds_);
    }

    /// Log-shape and election invariants after a step.
    proof fn lemma_dynamic_logs_next(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            DynamicInvariant(ds),
            RaftSafetyInvariant(ds_),
            RaftDistributedNext(ds, ds_),
        ensures
            HistoryHeld(ds_),
            ConfigurationFollowedIsCommitted(ds_),
            ConfigurationEntriesLegal(ds_),
            CandidateLogBelowTerm(ds_),
            WinnerRecords(ds_),
            EntryHeldByWinner(ds_),
    {
        lemma_history_held_inductive(ds, ds_);
        lemma_configuration_followed_inductive(ds, ds_);
        lemma_configuration_entries_legal_inductive(ds, ds_);
        lemma_candidate_log_below_inductive(ds, ds_);
        lemma_winner_records_inductive(ds, ds_);
        lemma_entry_held_by_winner_inductive(ds, ds_);
    }

    #[verifier::spinoff_prover]
    pub proof fn lemma_dynamic_invariant_inductive(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            DynamicInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            DynamicInvariant(ds_),
    {
        lemma_dynamic_safety_invariant_next(ds, ds_);
        lemma_dynamic_replication_next(ds, ds_);
        lemma_dynamic_logs_next(ds, ds_);
        let (nv, nt) = lemma_election_records_step(ds, ds_);
        assert(CompletenessCore(ds_));
        lemma_unique_winners_inductive(ds, ds_, nv, nt);
    }

    pub proof fn lemma_dynamic_invariant_holds_throughout_behavior(b: RaftBehavior, i: int)
        requires
            IsValidRaftBehavior(b),
            0 <= i < b.len(),
        ensures
            DynamicInvariant(b[i]),
        decreases i
    {
        if i == 0 {
            lemma_dynamic_invariant_init(b[0]);
        } else {
            lemma_dynamic_invariant_holds_throughout_behavior(b, i - 1);
            lemma_dynamic_invariant_inductive(b[i - 1], b[i]);
        }
    }

    /// At most one leader per term, in every reachable state.
    pub proof fn lemma_dynamic_election_safety(ds: RaftDistributedState)
        requires
            DynamicInvariant(ds),
        ensures
            ElectionSafety(ds),
    {
        assert(LeaderElectionSnapshotRecorded(ds));
        assert forall |i: int, j: int| #![trigger ds.server_states[i], ds.server_states[j]]
            0 <= i < ds.num_servers && 0 <= j < ds.num_servers
            && ds.server_states[i].role is Leader
            && ds.server_states[j].role is Leader
            && ds.server_states[i].current_term == ds.server_states[j].current_term
            implies i == j by {
            assert(ds.election_log_len.dom().contains((i, ds.server_states[i].current_term)));
            assert(ds.election_log_len.dom().contains((j, ds.server_states[j].current_term)));
        }
    }

} // verus!

//! Reboots preserve durable protocol state and the history of commitment.
//! This is a model proof under ideal persistence, with no storage implementation.
use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::invariants::*;
use crate::protocol::Raft::refinement_proof::message_invariants::*;
use vstd::prelude::*;

verus! {
    pub proof fn lemma_commit_history_normal_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            CommitHistoryValid(ds),
            CommitIndexBounded(ds_),
            CommittedEntriesHaveLogCertificates(ds_),
            RaftDistributedNormalNext(ds, ds_),
        ensures CommitHistoryValid(ds_)
    {
        let sid = choose |sid: int| {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                    ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };
        let (sp, rf) = choose |sp: Seq<LRaftMessage>, rf: Option<int>|
            RaftServerStepWitness(ds, ds_, sid, sp, rf);
        let s_ = ds_.server_states[sid];
        assert(ds_.committed_history.len() >= ds.committed_history.len());
        assert forall |i: int| #![trigger ds_.server_states[i]]
            0 <= i < ds_.num_servers implies
                ds_.server_states[i].commit_index <= ds_.committed_history.len()
        by {
            if i != sid {
                assert(ds_.server_states[i] == ds.server_states[i]);
            }
        };
        assert forall |k: int| #![trigger ds_.committed_history[k]]
            0 <= k < ds_.committed_history.len() implies {
                &&& ds_.log_commit_certificates.dom().contains(k)
                &&& ds_.log_commit_certificates[k].entry == ds_.committed_history[k]
            }
        by {
            if s_.commit_index > ds.committed_history.len() {
                assert(ds_.committed_history[k] == s_.log[k]);
                assert(CommittedEntriesHaveLogCertificates(ds_));
            } else {
                assert(ds.committed_history[k] == ds_.committed_history[k]);
                assert(ds.log_commit_certificates.dom().contains(k));
                assert(ds_.log_commit_certificates[k].entry
                    == ds.log_commit_certificates[k].entry);
            }
        };
    }

    /// A concrete witness shows reboot is enabled for every well-formed node,
    /// including leaders and nodes with committed entries. No safety predicate
    /// is used as an enabling guard.
    pub open spec fn RebootState(ds: RaftDistributedState, sid: int) -> RaftDistributedState {
        let s = ds.server_states[sid];
        RaftDistributedState {
            server_states: ds.server_states.update(sid, LState {
                role: LServerRole::Follower,
                commit_index: 0,
                votes_granted: Set::<int>::empty(),
                election_membership_phase: None,
                match_index: Map::<u64, u64>::empty(),
                next_index: Map::<u64, u64>::empty(),
                ..s
            }),
            ..ds
        }
    }

    pub proof fn lemma_reboot_enabled(ds: RaftDistributedState, sid: int)
        requires WellFormedRaftDistributed(ds), 0 <= sid < ds.num_servers
        ensures
            RaftDistributedReboot(ds, RebootState(ds, sid), sid),
            RaftDistributedNext(ds, RebootState(ds, sid)),
            RebootState(ds, sid).server_states[sid].commit_index == 0,
            RebootState(ds, sid).server_states[sid].role is Follower,
            RebootState(ds, sid).network == ds.network,
            RebootState(ds, sid).committed_history == ds.committed_history,
    {
        assert(RaftDistributedReboot(ds, RebootState(ds, sid), sid));
    }

    pub proof fn lemma_reboot_frame(
        ds: RaftDistributedState, ds_: RaftDistributedState, sid: int,
    )
        requires RaftDistributedReboot(ds, ds_, sid)
        ensures
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            ds_.network == ds.network,
            ds_.vote_log_len == ds.vote_log_len,
            ds_.election_log_len == ds.election_log_len,
            ds_.configuration_commit_certificates == ds.configuration_commit_certificates,
            ds_.log_commit_certificates == ds.log_commit_certificates,
            ds_.committed_history == ds.committed_history,
            forall |i: int| #![trigger ds_.server_states[i]]
                0 <= i < ds.num_servers ==> {
                    &&& ds_.server_states[i].log == ds.server_states[i].log
                    &&& ds_.server_states[i].current_term == ds.server_states[i].current_term
                    &&& ds_.server_states[i].has_voted == ds.server_states[i].has_voted
                    &&& ds_.server_states[i].voted_for == ds.server_states[i].voted_for
                    &&& (i != sid ==> ds_.server_states[i] == ds.server_states[i])
                },
    {
        assert forall |i: int| #![trigger ds_.server_states[i]]
            0 <= i < ds.num_servers implies {
                &&& ds_.server_states[i].log == ds.server_states[i].log
                &&& ds_.server_states[i].current_term == ds.server_states[i].current_term
                &&& ds_.server_states[i].has_voted == ds.server_states[i].has_voted
                &&& ds_.server_states[i].voted_for == ds.server_states[i].voted_for
                &&& (i != sid ==> ds_.server_states[i] == ds.server_states[i])
            }
        by {
            if i != sid {
                assert(ds_.server_states[i] == ds.server_states[i]);
            }
        };
    }

    /// Connect the distributed behavior to the local protocol-or-reboot model.
    pub proof fn lemma_distributed_step_has_local_action(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires RaftDistributedNext(ds, ds_)
        ensures exists |sid: int| #![trigger ds.server_states[sid]] #![trigger ds_.server_states[sid]] #![trigger ds.server_constants[sid]] {
            &&& 0 <= sid < ds.num_servers
            &&& LNextWithReboot(ds.server_states[sid], ds_.server_states[sid],
                ds.server_constants[sid])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                    ds_.server_states[j] == ds.server_states[j])
        }
    {
        if RaftDistributedNormalNext(ds, ds_) {
            lemma_normal_next_implies_legacy(ds, ds_);
        } else {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            lemma_reboot_frame(ds, ds_, sid);
            assert(LNextWithReboot(ds.server_states[sid], ds_.server_states[sid],
                ds.server_constants[sid]));
        }
    }

    proof fn lemma_reboot_preserves_local(
        ds: RaftDistributedState, ds_: RaftDistributedState, sid: int,
    )
        requires
            RaftDistributedReboot(ds, ds_, sid),
            CommitHistoryValid(ds),
            StateMachineSafety(ds),
            CommittedMembershipPrefixAgreement(ds),
            LeaderHasRecordedElectionQuorum(ds),
            LeaderHasRecordedElectionLogProvenance(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexBounded(ds),
            CommitIndexNonnegative(ds),
            EntryTermLeaderWitness(ds),
            VotesGrantedAreServers(ds),
            CandidateOrLeaderVotedForSelf(ds),
            CandidateOrLeaderVotedForSelfId(ds),
            VotersVotedForCandidate(ds),
        ensures
            CommitHistoryValid(ds_),
            StateMachineSafety(ds_),
            CommittedMembershipPrefixAgreement(ds_),
            LeaderHasRecordedElectionQuorum(ds_),
            LeaderHasRecordedElectionLogProvenance(ds_),
            CommittedConfigurationsHaveCertificates(ds_),
            CommittedEntriesHaveLogCertificates(ds_),
            CommitIndexBounded(ds_),
            CommitIndexNonnegative(ds_),
            EntryTermLeaderWitness(ds_),
            VotesGrantedAreServers(ds_),
            CandidateOrLeaderVotedForSelf(ds_),
            CandidateOrLeaderVotedForSelfId(ds_),
            VotersVotedForCandidate(ds_),
    {
        lemma_reboot_frame(ds, ds_, sid);
        assert(CommitHistoryValid(ds_));
        assert(StateMachineSafety(ds_));
        assert(CommittedMembershipPrefixAgreement(ds_));
        assert(LeaderHasRecordedElectionQuorum(ds_));
        assert(LeaderHasRecordedElectionLogProvenance(ds_));
        assert(CommittedConfigurationsHaveCertificates(ds_));
        assert(CommittedEntriesHaveLogCertificates(ds_));
        assert(CommitIndexBounded(ds_));
        assert(CommitIndexNonnegative(ds_));
        assert forall |i: int, k: int|
            #![trigger entry_term_leader_witness_trigger(ds_, i, k)]
            0 <= i < ds_.num_servers && 0 <= k < ds_.server_states[i].log.len()
            && entry_term_leader_witness_trigger(ds_, i, k)
            implies exists |w: int| #![trigger ds_.server_states[w]] {
                &&& 0 <= w < ds_.num_servers
                &&& ds_.server_states[w].log.len() > k
                &&& ds_.server_states[w].log[k] == ds_.server_states[i].log[k]
            }
        by {
            assert(LogAppendOnly(ds, ds_));
            lemma_entry_term_old_entry_witness(ds, ds_, i, k);
        };
        assert(VotesGrantedAreServers(ds_));
        assert(CandidateOrLeaderVotedForSelf(ds_));
        assert(CandidateOrLeaderVotedForSelfId(ds_));
        assert(VotersVotedForCandidate(ds_));
    }

    proof fn lemma_reboot_preserves_messages(
        ds: RaftDistributedState, ds_: RaftDistributedState, sid: int,
    )
        requires
            RaftDistributedReboot(ds, ds_, sid),
            SenderIntegrity(ds),
            VoteResponseIntegrity(ds),
            VoteResponseSummaryStillValidAtOrAboveTerm(ds),
            VoteResponseHasRequestVote(ds),
            AppendEntriesIntegrity(ds),
            OneVotePerTermInNetwork(ds),
            RequestVoteSenderState(ds),
            RequestVoteSummaryStillValidAtSameTerm(ds),
            RequestVoteSummaryAlwaysValid(ds),
            RequestVoteLastLogTermBound(ds),
            RequestVoteLogParamsConsistent(ds),
            CandidateVoteDestinationUnique(ds),
            AppendEntriesCommitHistoryBound(ds),
        ensures
            SenderIntegrity(ds_),
            VoteResponseIntegrity(ds_),
            VoteResponseSummaryStillValidAtOrAboveTerm(ds_),
            VoteResponseHasRequestVote(ds_),
            AppendEntriesIntegrity(ds_),
            OneVotePerTermInNetwork(ds_),
            RequestVoteSenderState(ds_),
            RequestVoteSummaryStillValidAtSameTerm(ds_),
            RequestVoteSummaryAlwaysValid(ds_),
            RequestVoteLastLogTermBound(ds_),
            RequestVoteLogParamsConsistent(ds_),
            CandidateVoteDestinationUnique(ds_),
            AppendEntriesCommitHistoryBound(ds_),
    {
        lemma_reboot_frame(ds, ds_, sid);
        assert(SenderIntegrity(ds_));
        assert(VoteResponseIntegrity(ds_));
        assert(VoteResponseSummaryStillValidAtOrAboveTerm(ds_));
        assert(VoteResponseHasRequestVote(ds_));
        assert(AppendEntriesIntegrity(ds_));
        assert(OneVotePerTermInNetwork(ds_));
        assert(RequestVoteSenderState(ds_));
        assert(RequestVoteSummaryStillValidAtSameTerm(ds_));
        assert(RequestVoteSummaryAlwaysValid(ds_));
        assert(RequestVoteLastLogTermBound(ds_));
        assert(RequestVoteLogParamsConsistent(ds_));
        assert(CandidateVoteDestinationUnique(ds_));
        assert(AppendEntriesCommitHistoryBound(ds_));
    }

    proof fn lemma_reboot_preserves_history(
        ds: RaftDistributedState, ds_: RaftDistributedState, sid: int,
    )
        requires
            RaftDistributedReboot(ds, ds_, sid),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteLogLenEntryTermBound(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
            ElectionLogLenBounded(ds),
            ElectionLogLenEntryTermBound(ds),
            LeaderElectionSnapshotRecorded(ds),
            CurrentTermGeLogTerms(ds),
            LogTermsMonotonic(ds),
            TermsNonNegative(ds),
        ensures
            VoteLogLenCoversNetwork(ds_),
            VoteLogLenBounded(ds_),
            VoteLogLenEntryTermBound(ds_),
            VoteGrantedLogUpToDateAtVoteTime(ds_),
            ElectionLogLenBounded(ds_),
            ElectionLogLenEntryTermBound(ds_),
            LeaderElectionSnapshotRecorded(ds_),
            CurrentTermGeLogTerms(ds_),
            LogTermsMonotonic(ds_),
            TermsNonNegative(ds_),
    {
        lemma_reboot_frame(ds, ds_, sid);
        assert(VoteLogLenCoversNetwork(ds_));
        assert(VoteLogLenBounded(ds_));
        assert(VoteLogLenEntryTermBound(ds_));
        assert(VoteGrantedLogUpToDateAtVoteTime(ds_));
        assert(ElectionLogLenBounded(ds_));
        assert(ElectionLogLenEntryTermBound(ds_));
        assert(LeaderElectionSnapshotRecorded(ds_));
        assert(CurrentTermGeLogTerms(ds_));
        assert(LogTermsMonotonic(ds_));
        assert(TermsNonNegative(ds_));
    }

    pub proof fn lemma_reboot_preserves_invariant(
        ds: RaftDistributedState, ds_: RaftDistributedState, sid: int,
    )
        requires RaftSafetyInvariant(ds), RaftDistributedReboot(ds, ds_, sid)
        ensures RaftSafetyInvariant(ds_)
    {
        lemma_reboot_frame(ds, ds_, sid);
        lemma_reboot_preserves_local(ds, ds_, sid);
        lemma_reboot_preserves_messages(ds, ds_, sid);
        lemma_reboot_preserves_history(ds, ds_, sid);
    }

    /// Reboot a prefix of the cluster, one environment step per node.
    pub open spec fn RebootPrefix(ds: RaftDistributedState, count: int) -> RaftDistributedState
        decreases count
    {
        if count <= 0 {
            ds
        } else {
            RebootState(RebootPrefix(ds, count - 1), count - 1)
        }
    }

    /// Regression theorem: every node may lose volatile commitment knowledge
    /// while the previously committed history and in-flight packets survive.
    pub proof fn lemma_reboot_prefix_preserves_history(
        ds: RaftDistributedState, count: int,
    )
        requires
            RaftSafetyInvariant(ds),
            0 <= count <= ds.num_servers,
        ensures
            RaftSafetyInvariant(RebootPrefix(ds, count)),
            RebootPrefix(ds, count).num_servers == ds.num_servers,
            RebootPrefix(ds, count).committed_history == ds.committed_history,
            RebootPrefix(ds, count).network == ds.network,
            forall |i: int| #![trigger RebootPrefix(ds, count).server_states[i]]
                0 <= i < count ==> {
                    &&& RebootPrefix(ds, count).server_states[i].commit_index == 0
                    &&& RebootPrefix(ds, count).server_states[i].role is Follower
                },
        decreases count
    {
        if count > 0 {
            lemma_reboot_prefix_preserves_history(ds, count - 1);
            let before = RebootPrefix(ds, count - 1);
            lemma_reboot_enabled(before, count - 1);
            lemma_reboot_preserves_invariant(before, RebootState(before, count - 1), count - 1);
        }
    }

    pub proof fn lemma_whole_cluster_reboot_preserves_commitment(ds: RaftDistributedState)
        requires RaftSafetyInvariant(ds)
        ensures
            RaftSafetyInvariant(RebootPrefix(ds, ds.num_servers)),
            GetKnownCommittedLog(RebootPrefix(ds, ds.num_servers)) == Seq::<int>::empty(),
            GetCommittedLog(RebootPrefix(ds, ds.num_servers)) == GetCommittedLog(ds),
            RebootPrefix(ds, ds.num_servers).committed_history == ds.committed_history,
    {
        lemma_reboot_prefix_preserves_history(ds, ds.num_servers);
        let after = RebootPrefix(ds, ds.num_servers);
        lemma_max_commit_index_eq_seq(after);
        lemma_max_commit_seq_achieved(after.server_states);
        let i = choose |i: int| #![trigger after.server_states[i]]
            0 <= i < after.server_states.len()
            && after.server_states[i].commit_index == max_commit_index_seq(after.server_states);
        assert(after.server_states[i].commit_index == 0);
        assert(MaxCommitIndex(after) == 0);
    }

    /// Repeated reboot does not invent terms, votes, log entries or commitment.
    pub proof fn lemma_reboot_is_idempotent(ds: RaftDistributedState, sid: int)
        requires WellFormedRaftDistributed(ds), 0 <= sid < ds.num_servers
        ensures RebootState(RebootState(ds, sid), sid) == RebootState(ds, sid)
    {
        assert(RebootState(RebootState(ds, sid), sid).server_states
            =~= RebootState(ds, sid).server_states);
    }

}

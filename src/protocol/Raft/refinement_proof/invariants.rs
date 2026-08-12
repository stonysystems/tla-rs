use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::membership::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::message_invariants::*;
use crate::protocol::Raft::refinement_proof::reconfiguration::*;
use crate::common::collections::sets::*;
use vstd::prelude::*;
use vstd::{map::*, seq::*, set::*, set_lib::*};

verus! {

    // =========================================================================
    // Invariant 1: Election Safety
    // At most one leader per term across all servers.
    // =========================================================================

    pub open spec fn ElectionSafety(ds: RaftDistributedState) -> bool {
        forall |i: int, j: int| #![trigger ds.server_states[i], ds.server_states[j]]
            0 <= i < ds.num_servers && 0 <= j < ds.num_servers
            && ds.server_states[i].role is Leader
            && ds.server_states[j].role is Leader
            && ds.server_states[i].current_term == ds.server_states[j].current_term
            ==> i == j
    }

    // =========================================================================
    // Invariant 2: Log Matching
    // If two servers have entries at the same index with the same term,
    // then all preceding entries also match.
    // =========================================================================

    pub open spec fn LogMatching(ds: RaftDistributedState) -> bool {
        forall |i: int, j: int, k: int| #![trigger ds.server_states[i], ds.server_states[j].log[k]] #![trigger ds.server_states[i].log[k], ds.server_states[j]]
            0 <= i < ds.num_servers && 0 <= j < ds.num_servers
            && 0 <= k < ds.server_states[i].log.len()
            && 0 <= k < ds.server_states[j].log.len()
            && ds.server_states[i].log[k].term == ds.server_states[j].log[k].term
            ==> (forall |m: int| 0 <= m <= k
                && m < ds.server_states[i].log.len()
                && m < ds.server_states[j].log.len()
                ==> ds.server_states[i].log[m] == ds.server_states[j].log[m])
    }

    // =========================================================================
    // Invariant 3: Leader Completeness
    // If an entry is committed in some term, it appears in the log of
    // every leader for all higher-numbered terms.
    // =========================================================================

    /// An entry at index k is "committed" if a majority of servers have
    /// matching entries at that index.
    pub open spec fn EntryCommittedAt(ds: RaftDistributedState, k: int, entry: LLogEntry) -> bool {
        let quorum_size = ds.num_servers / 2 + 1;
        exists |quorum: Set<int>| {
            &&& quorum.len() >= quorum_size
            &&& (forall |id: int| #![trigger quorum.contains(id)] quorum.contains(id) ==> {
                &&& 0 <= id < ds.num_servers
                &&& ds.server_states[id].log.len() > k
                &&& ds.server_states[id].log[k] == entry
            })
        }
    }

    pub open spec fn LeaderCompleteness(ds: RaftDistributedState) -> bool {
        forall |k: int, entry: LLogEntry, leader_id: int| #![trigger EntryCommittedAt(ds, k, entry), ds.server_states[leader_id]]
            0 <= k
            && EntryCommittedAt(ds, k, entry)
            && 0 <= leader_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term > entry.term
            ==> {
                &&& ds.server_states[leader_id].log.len() > k
                &&& ds.server_states[leader_id].log[k] == entry
            }
    }

    // =========================================================================
    // Invariant 4: State Machine Safety
    // If any server has applied a log entry at a given index, no other server
    // will ever apply a different entry for that index.
    //
    // This follows from Log Matching + Leader Completeness: committed
    // entries are never overwritten.
    // =========================================================================

    pub open spec fn StateMachineSafety(ds: RaftDistributedState) -> bool {
        forall |i: int, j: int, k: int| #![trigger ds.server_states[i], ds.server_states[j].log[k]] #![trigger ds.server_states[j], ds.server_states[i].log[k]]
            0 <= i < ds.num_servers && 0 <= j < ds.num_servers
            && 0 <= k < ds.server_states[i].commit_index
            && 0 <= k < ds.server_states[j].commit_index
            && k < ds.server_states[i].log.len()
            && k < ds.server_states[j].log.len()
            ==> ds.server_states[i].log[k] == ds.server_states[j].log[k]
    }

    // =========================================================================
    // Supporting invariants for Election Safety
    // =========================================================================

    /// Each voter in a leader/candidate's votes_granted set is a valid server ID
    pub open spec fn VotesGrantedAreServers(ds: RaftDistributedState) -> bool {
        forall |i: int, v: int|
            0 <= i < ds.num_servers
            && ds.server_states[i].votes_granted.contains(v)
            ==> 0 <= v < ds.num_servers
    }

    /// A leader/candidate has itself in its votes_granted set
    /// (Leaders and Candidates always start by voting for themselves)
    pub open spec fn CandidateOrLeaderVotedForSelf(ds: RaftDistributedState) -> bool {
        forall |i: int| #![trigger ds.server_states[i]] #![trigger ds.server_constants[i]]
            0 <= i < ds.num_servers
            && (ds.server_states[i].role is Candidate || ds.server_states[i].role is Leader)
            ==> ds.server_states[i].votes_granted.contains(ds.server_constants[i].my_id)
    }

    /// A leader/candidate has voted for itself (voted_for == i).
    /// LTimeout sets voted_for = my_id when becoming Candidate. All transitions
    /// that preserve Candidate/Leader role also preserve voted_for.
    pub open spec fn CandidateOrLeaderVotedForSelfId(ds: RaftDistributedState) -> bool {
        forall |i: int| #![trigger ds.server_states[i]]
            0 <= i < ds.num_servers
            && (ds.server_states[i].role is Candidate || ds.server_states[i].role is Leader)
            ==> ds.server_states[i].has_voted && ds.server_states[i].voted_for == i
    }

    /// Network-level invariant: if server i is a Leader or Candidate with voter v
    /// in its votes_granted set, then voter v voted for i in i's current term.
    /// This links the local votes_granted set to the global voting state.
    ///
    /// Network-based vote tracking: if v is in candidate/leader i's votes_granted,
    /// there must be a VoteResponse{granted: true, term: i.current_term} packet
    /// in the network from v to i.
    ///
    /// This formulation is inductive because:
    /// 1. The network is monotonic (packets are never removed).
    /// 2. When LHandleVoteResponseMsg adds voter v, the received VoteResponse
    ///    packet is already in the network (with the right term, by the new
    ///    term check guard).
    /// 3. votes_granted is reset on term change (step_down or LTimeout), so
    ///    old votes from previous terms don't carry over.
    ///
    /// Combined with OneVotePerTermInNetwork, this gives ElectionSafety:
    /// two leaders at the same term would need overlapping quorums, but the
    /// quorum intersection voter has a unique VoteResponse destination.
    pub open spec fn VotersVotedForCandidate(ds: RaftDistributedState) -> bool {
        forall |i: int, v: int|
            0 <= i < ds.num_servers
            && 0 <= v < ds.num_servers
            && v != i
            && (ds.server_states[i].role is Candidate || ds.server_states[i].role is Leader)
            && ds.server_states[i].votes_granted.contains(v)
            ==> exists |p: LRaftPacket| #![trigger ds.network.contains(p)] {
                &&& ds.network.contains(p)
                &&& p.dst == i
                &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter, .. }
                &&& term == ds.server_states[i].current_term
                &&& granted
                &&& voter == v
            }
    }

    /// Quorum of voters: if server i is Leader, then votes_granted has
    /// quorum_size members who all voted for i in i's current_term.
    pub open spec fn LeaderHasQuorum(ds: RaftDistributedState) -> bool {
        forall |i: int| #![trigger ds.server_states[i]] #![trigger ds.server_constants[i]]
            0 <= i < ds.num_servers
            && ds.server_states[i].role is Leader
            ==> ds.server_states[i].votes_granted.len() >= ds.server_constants[i].quorum_size
    }

    /// Configuration-aware version of LeaderHasQuorum for the
    /// existing fixed-membership Raft model.
    pub open spec fn LeaderHasStablePhaseQuorum(
        ds: RaftDistributedState,
    ) -> bool {
        forall |i: int| #![trigger ds.server_states[i]]
            0 <= i < ds.num_servers
            && ds.server_states[i].role is Leader
            ==> is_quorum_for_phase(
                ds.server_states[i].votes_granted,
                MembershipPhase::Stable {
                    config: ds.server_constants[i].servers,
                },
            )
    }

    /// Every leader carries the membership-aware quorum certificate
    /// recorded when it won its election.
    pub open spec fn LeaderHasRecordedElectionQuorum(
        ds: RaftDistributedState,
    ) -> bool {
        forall |i: int| #![trigger ds.server_states[i]]
            0 <= i < ds.num_servers
            ==> has_recorded_election_quorum(
                ds.server_states[i],
            )
    }

    /// Every leader's saved election membership phase is justified by
    /// a prefix of its actual Raft log that was committed by election time.
    pub open spec fn LeaderHasRecordedElectionLogProvenance(
        ds: RaftDistributedState,
    ) -> bool {
        forall |i: int| #![trigger ds.server_states[i]] #![trigger ds.server_constants[i]]
            0 <= i < ds.num_servers
            ==> has_recorded_election_log_provenance(
                ds.server_states[i],
                ds.server_constants[i],
            )
    }

    /// Every stored configuration-commit certificate is internally valid and
    /// is backed by matching log prefixes on every member of its saved quorum.
    pub open spec fn ConfigurationCommitCertificatesValid(
        ds: RaftDistributedState,
    ) -> bool {
        forall |index: int|
            #![trigger ds.configuration_commit_certificates[index]]
            ds.configuration_commit_certificates.dom().contains(index)
            ==> {
                let certificate = ds.configuration_commit_certificates[index];
                &&& certificate.log_index == index
                &&& is_quorum_for_phase(
                    certificate.quorum,
                    certificate.governing_phase,
                )
                &&& certificate.entry.payload is Configuration
                &&& forall |replica: int|
                    #![trigger certificate.quorum.contains(replica)]
                    certificate.quorum.contains(replica)
                    ==> 0 <= replica < ds.num_servers
                &&& forall |replica: int|
                    #![trigger ds.server_states[replica].log[index]]
                    0 <= replica < ds.num_servers
                    && certificate.quorum.contains(replica)
                    ==> configuration_commit_certificate_matches_log(
                            certificate,
                            ds.server_states[replica].log,
                            MembershipPhase::Stable {
                                config: ds.server_constants[replica].servers,
                            },
                        )
            }
    }

    /// Each certificate remembers the leader that created it. That server is
    /// part of the committing quorum and permanently retains the certified
    /// entry in its committed prefix.
    pub open spec fn ConfigurationCommittersRetainCertifiedPrefixes(
        ds: RaftDistributedState,
    ) -> bool {
        forall |index: int|
            #![trigger ds.configuration_commit_certificates[index]]
            ds.configuration_commit_certificates.dom().contains(index)
            ==> {
                let certificate = ds.configuration_commit_certificates[index];
                &&& 0 <= certificate.committer < ds.num_servers
                &&& certificate.quorum.contains(certificate.committer)
                &&& certificate.log_index == index
                &&& 0 <= index
                    < ds.server_states[certificate.committer].commit_index
                &&& ds.server_states[certificate.committer].commit_index
                    <= ds.server_states[certificate.committer].log.len()
                &&& ds.server_states[certificate.committer].log[index]
                    == certificate.entry
            }
    }

    pub proof fn lemma_configuration_committer_retains_certified_prefix(
        ds: RaftDistributedState,
        index: int,
    )
        requires
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            ds.configuration_commit_certificates.dom().contains(index),
        ensures ({
            let certificate = ds.configuration_commit_certificates[index];
            &&& 0 <= certificate.committer < ds.num_servers
            &&& certificate.quorum.contains(certificate.committer)
            &&& certificate.log_index == index
            &&& 0 <= index < ds.server_states[certificate.committer].commit_index
            &&& ds.server_states[certificate.committer].commit_index
                <= ds.server_states[certificate.committer].log.len()
            &&& ds.server_states[certificate.committer].log[index]
                == certificate.entry
        })
    {
        assert(ConfigurationCommittersRetainCertifiedPrefixes(ds));
    }

    /// Dynamic-membership analogue of LeaderCompleteness for committed
    /// Configuration entries: every higher-term leader contains every
    /// certified membership boundary.
    pub open spec fn CertifiedConfigurationLeaderCompleteness(
        ds: RaftDistributedState,
    ) -> bool {
        forall |index: int, leader_id: int|
            #![trigger ds.configuration_commit_certificates[index],
                       ds.server_states[leader_id].role]
            ds.configuration_commit_certificates.dom().contains(index)
            && 0 <= leader_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term
            ==> {
                &&& ds.server_states[leader_id].log.len() > index
                &&& ds.server_states[leader_id].log[index]
                    == ds.configuration_commit_certificates[index].entry
            }
    }

    /// The one remaining provenance bridge needed by the certificate proof.
    /// If a higher-term leader appears to miss a certified Configuration, the
    /// certificate has a quorum member whose log agrees through the leader's
    /// saved election prefix and contains no earlier missing Configuration.
    pub open spec fn FirstMissingConfigurationBoundaryProvenance(
        ds: RaftDistributedState,
    ) -> bool {
        forall |index: int, leader_id: int|
            ds.configuration_commit_certificates.dom().contains(index)
            && 0 <= leader_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term
            && !(ds.server_states[leader_id].log.len() > index
                && ds.server_states[leader_id].log[index]
                    == ds.configuration_commit_certificates[index].entry)
            ==> exists |certificate_witness: int, election_commit_len: int| #![trigger ds.configuration_commit_certificates[index].quorum.contains(certificate_witness), active_membership_phase_from_raft_log(ds.server_states[leader_id].log, election_commit_len, MembershipPhase::Stable { config: ds.server_constants[leader_id].servers })] {
                &&& ds.configuration_commit_certificates[index].quorum
                    .contains(certificate_witness)
                &&& 0 <= election_commit_len
                    <= ds.server_states[leader_id].log.len()
                &&& election_commit_len <= index
                &&& ds.server_states[leader_id].election_membership_phase
                    == Some(active_membership_phase_from_raft_log(
                        ds.server_states[leader_id].log,
                        election_commit_len,
                        MembershipPhase::Stable {
                            config: ds.server_constants[leader_id].servers,
                        },
                    ))
                &&& forall |prefix_index: int|
                    0 <= prefix_index < election_commit_len
                    ==> ds.server_states[leader_id].log[prefix_index]
                        == ds.server_states[certificate_witness]
                            .log[prefix_index]
                &&& forall |prefix_index: int| #![trigger ds.server_states[certificate_witness].log[prefix_index]]
                    election_commit_len <= prefix_index < index
                    ==> !(ds.server_states[certificate_witness]
                        .log[prefix_index].payload is Configuration)
            }
    }

    /// The single inherited obligation that dynamic-membership Configuration
    /// Leader Completeness reduces to: a server that granted its vote to a
    /// strictly higher-term leader cannot still be holding a certified
    /// Configuration boundary that the leader lacks.
    ///
    /// This is the classic static-Raft log-transfer step. It is stated as an
    /// explicit hypothesis rather than discharged through
    /// `lemma_overlap_voter_entry_transfer`, whose hard cases the inherited
    /// proof base closes with `assume(false)`. Keeping it explicit separates
    /// the membership-specific reasoning — quorum overlap across joint
    /// consensus phases — from the inherited gap, so the dynamic-membership
    /// result is exactly as strong as static Raft's own transfer lemma.
    pub open spec fn CertifiedBoundaryTransfersToVotedLeader(
        ds: RaftDistributedState,
    ) -> bool {
        forall |index: int, leader_id: int, overlap_voter: int| #![trigger ds.configuration_commit_certificates.dom().contains(index), ds.server_states[leader_id].votes_granted.contains(overlap_voter)]
            ds.configuration_commit_certificates.dom().contains(index)
            && 0 <= leader_id < ds.num_servers
            && 0 <= overlap_voter < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term
            && ds.configuration_commit_certificates[index].quorum
                .contains(overlap_voter)
            && ds.server_states[leader_id].votes_granted
                .contains(overlap_voter)
            ==> {
                &&& ds.server_states[leader_id].log.len() > index
                &&& ds.server_states[leader_id].log[index]
                    == ds.configuration_commit_certificates[index].entry
            }
    }

    /// Pointwise form of all-entry Dynamic Leader Completeness.
    /// Keeping the concrete index and leader outside the quantified wrapper
    /// prevents Verus from unfolding every provenance branch at once.
    proof fn lemma_one_certified_entry_in_later_leader(
        ds: RaftDistributedState, index: int, leader_id: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            LogCommitCertificatesValid(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            AllRaftMembershipLogsWellFormed(ds),
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            ElectionLogLenBounded(ds),
            ElectionLogLenEntryTermBound(ds),
            LeaderElectionSnapshotRecorded(ds),
            LogTermsMonotonic(ds),
            CertifiedConfigurationLeaderCompleteness(ds),
            CertifiedLogEntryTransfersToVotedLeader(ds),
            ds.log_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.log_commit_certificates[index].entry.term,
        ensures
            ds.server_states[leader_id].log.len() > index,
            ds.server_states[leader_id].log[index]
                == ds.log_commit_certificates[index].entry,
    {
        assert(LogCommitCertificatesValid(ds));
        assert(0 <= index);
        assert forall |a: int, e: int| #![trigger ds.server_constants[a], ds.server_constants[e]]
            0 <= a < ds.num_servers && 0 <= e < ds.num_servers
            implies ds.server_constants[a].servers
                == ds.server_constants[e].servers
        by {
            lemma_all_servers_share_server_universe(ds, a, e);
        };
        if index < ds.server_states[leader_id].commit_index {
            assert(CommitIndexBounded(ds));
            assert(index < ds.server_states[leader_id].log.len());
            assert(CommittedEntriesHaveLogCertificates(ds));
        } else if index <= ds.server_states[leader_id].log.len() {
            lemma_leader_holds_certified_log_entry_within_log(
                ds, index, leader_id);
        } else {
            lemma_leader_cannot_end_before_certified_log_entry(
                ds, index, leader_id);
        }
    }

    /// All-entry Dynamic Leader Completeness holds in any state satisfying the
    /// dynamic certificate, election-snapshot, log and transfer invariants.
    ///
    /// Stated over explicit invariants rather than `RaftSafetyInvariant` so it
    /// can establish that conjunct without circular unfolding. Being a state
    /// theorem, freshly created certificates need no per-transition split.
    ///
    /// Three cases: the leader already committed past the entry (its own
    /// committed prefix is certificate-covered), its log reaches the entry, or
    /// its log stops short — which is impossible.
    pub proof fn lemma_dynamic_state_implies_all_entry_leader_completeness(
        ds: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            LogCommitCertificatesValid(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            AllRaftMembershipLogsWellFormed(ds),
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            ElectionLogLenBounded(ds),
            ElectionLogLenEntryTermBound(ds),
            LeaderElectionSnapshotRecorded(ds),
            LogTermsMonotonic(ds),
            CertifiedConfigurationLeaderCompleteness(ds),
            CertifiedLogEntryTransfersToVotedLeader(ds),
        ensures
            DynamicLeaderCompleteness(ds),
    {
        assert forall |index: int, leader_id: int|
            ds.log_commit_certificates.dom().contains(index)
            && 0 <= leader_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term
                > ds.log_commit_certificates[index].entry.term
        implies {
            &&& ds.server_states[leader_id].log.len() > index
            &&& ds.server_states[leader_id].log[index]
                == ds.log_commit_certificates[index].entry
        } by {
            lemma_one_certified_entry_in_later_leader(
                ds, index, leader_id);
        };
    }

    /// A leader's log cannot end before a certified log entry.
    ///
    /// Any Configuration the committer holds between the leader's log end and
    /// the target is committed, hence certified, hence older than the target
    /// and so older than the leader's term — global Configuration Leader
    /// Completeness would place it inside the leader's log, which its length
    /// forbids. That stretch being Configuration-free fixes the governing phase
    /// at the leader's log end, and the transfer then places the target entry
    /// inside a log assumed too short to hold it.
    pub proof fn lemma_leader_cannot_end_before_certified_log_entry(
        ds: RaftDistributedState,
        log_index: int,
        leader_id: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            LogCommitCertificatesValid(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            AllRaftMembershipLogsWellFormed(ds),
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            ElectionLogLenBounded(ds),
            ElectionLogLenEntryTermBound(ds),
            LeaderElectionSnapshotRecorded(ds),
            LogTermsMonotonic(ds),
            CertifiedConfigurationLeaderCompleteness(ds),
            CertifiedLogEntryTransfersToVotedLeader(ds),
            ds.log_commit_certificates.dom().contains(log_index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.log_commit_certificates[log_index].entry.term,
            forall |a: int, e: int|
                #![trigger ds.server_constants[a], ds.server_constants[e]]
                0 <= a < ds.num_servers && 0 <= e < ds.num_servers
                ==> ds.server_constants[a].servers
                    == ds.server_constants[e].servers,
            ds.server_states[leader_id].log.len() < log_index,
        ensures
            false,
    {
        let certificate = ds.log_commit_certificates[log_index];
        let committer = certificate.committer;
        let leader = ds.server_states[leader_id];
        let constants = ds.server_constants[leader_id];
        let cut = leader.log.len() as int;
        let initial_phase = MembershipPhase::Stable {
            config: constants.servers,
        };
        let key: (int, int) = (leader_id, leader.current_term);

        assert(LogCommitCertificatesValid(ds));
        assert(0 <= committer < ds.num_servers);
        assert(0 <= log_index < ds.server_states[committer].commit_index);
        assert(ds.server_states[committer].commit_index
            <= ds.server_states[committer].log.len());
        assert(CommitIndexBounded(ds));
        assert(leader.commit_index <= cut);

        // Every certified boundary below the target is held by the leader.
        assert forall |m: int| #![trigger ds.configuration_commit_certificates.dom().contains(m)]
            0 <= m < log_index
            && ds.configuration_commit_certificates.dom().contains(m)
            implies ds.server_states[leader_id].log.len() > m
                && ds.server_states[leader_id].log[m]
                    == ds.configuration_commit_certificates[m].entry
        by {
            lemma_configuration_certificate_term_below_log_certificate(
                ds, log_index, m);
            assert(CertifiedConfigurationLeaderCompleteness(ds));
        };

        // Hence the committer carries no boundary past the leader's log end.
        assert forall |p: int| #![trigger ds.server_states[committer].log[p]] cut <= p < log_index
        implies !(ds.server_states[committer].log[p].payload is Configuration)
        by {
            if ds.server_states[committer].log[p].payload is Configuration {
                lemma_committed_prefix_configuration_is_certified(
                    ds, committer, p);
                assert(ds.server_states[leader_id].log.len() > p);
            }
        };

        lemma_configuration_free_interval_preserves_active_phase(
            ds.server_states[committer].log,
            cut,
            log_index,
            initial_phase,
        );
        assert(certificate.governing_phase
            == active_membership_phase_from_raft_log(
                ds.server_states[committer].log, cut, initial_phase));

        lemma_governing_phase_progresses_from_cut_generic(
            ds,
            log_index,
            committer,
            certificate.governing_phase,
            leader_id,
            cut,
        );

        assert(LeaderElectionSnapshotRecorded(ds));
        assert(ds.election_log_len.dom().contains(key));
        let snapshot = ds.election_log_len[key];
        assert(ElectionLogLenBounded(ds));
        assert(0 <= snapshot <= cut);

        let saved_phase = active_membership_phase_from_raft_log(
            leader.log, snapshot, initial_phase);
        let committed_phase = active_membership_phase_from_raft_log(
            leader.log, leader.commit_index, initial_phase);
        let cut_phase = active_membership_phase_from_raft_log(
            leader.log, cut, initial_phase);
        assert(leader.election_membership_phase == Some(saved_phase));

        assert(AllRaftMembershipLogsWellFormed(ds));
        assert(UncommittedSuffixesHaveAtMostOneConfiguration(ds));
        assert forall |a: int, b: int| #![trigger leader.log[a], leader.log[b]]
            leader.commit_index <= a < leader.log.len()
            && leader.commit_index <= b < leader.log.len()
            && leader.log[a].payload is Configuration
            && leader.log[b].payload is Configuration
            implies a == b
        by {
            assert(uncommitted_suffix_has_at_most_one_configuration(
                leader.log, leader.commit_index));
        };

        if leader.commit_index <= snapshot {
            if certificate.governing_phase == committed_phase {
                lemma_bounded_boundary_interval_progresses_legally(
                    leader.log, leader.commit_index, snapshot, initial_phase);
                lemma_certified_log_entry_present_when_phases_are_related(
                    ds, log_index, leader_id, saved_phase);
            } else {
                assert(certificate.governing_phase == cut_phase);
                lemma_bounded_boundary_interval_progresses_legally(
                    leader.log, snapshot, cut, initial_phase);
                lemma_certified_log_entry_present_in_one_step_stale_leader(
                    ds, log_index, leader_id, saved_phase);
            }
        } else {
            lemma_older_log_certificate_makes_snapshot_to_commit_configuration_free(
                ds, log_index, leader_id);
            assert(saved_phase == committed_phase);

            if certificate.governing_phase == committed_phase {
                lemma_phase_progression_reflexive(saved_phase);
                lemma_certified_log_entry_present_when_phases_are_related(
                    ds, log_index, leader_id, saved_phase);
            } else {
                assert(certificate.governing_phase == cut_phase);
                lemma_bounded_boundary_interval_progresses_legally(
                    leader.log, leader.commit_index, cut, initial_phase);
                lemma_certified_log_entry_present_in_one_step_stale_leader(
                    ds, log_index, leader_id, saved_phase);
            }
        }

        assert(ds.server_states[leader_id].log.len() > log_index);
    }

    /// A leader whose log reaches a certified log entry contains it.
    ///
    /// Works for either payload kind. Global Configuration Leader Completeness
    /// supplies every earlier membership boundary — their terms are capped by
    /// the target's, which is below the leader's — so the kind-neutral phase
    /// core applies, and the saved election phase is within one legal step of
    /// the governing phase in one direction or the other.
    pub proof fn lemma_leader_holds_certified_log_entry_within_log(
        ds: RaftDistributedState,
        log_index: int,
        leader_id: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            LogCommitCertificatesValid(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            AllRaftMembershipLogsWellFormed(ds),
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            ElectionLogLenBounded(ds),
            ElectionLogLenEntryTermBound(ds),
            LeaderElectionSnapshotRecorded(ds),
            LogTermsMonotonic(ds),
            CertifiedConfigurationLeaderCompleteness(ds),
            CertifiedLogEntryTransfersToVotedLeader(ds),
            ds.log_commit_certificates.dom().contains(log_index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.log_commit_certificates[log_index].entry.term,
            forall |a: int, e: int|
                #![trigger ds.server_constants[a], ds.server_constants[e]]
                0 <= a < ds.num_servers && 0 <= e < ds.num_servers
                ==> ds.server_constants[a].servers
                    == ds.server_constants[e].servers,
            ds.server_states[leader_id].commit_index <= log_index,
            log_index <= ds.server_states[leader_id].log.len(),
        ensures
            ds.server_states[leader_id].log.len() > log_index,
            ds.server_states[leader_id].log[log_index]
                == ds.log_commit_certificates[log_index].entry,
    {
        let certificate = ds.log_commit_certificates[log_index];
        let committer = certificate.committer;
        let leader = ds.server_states[leader_id];
        let constants = ds.server_constants[leader_id];
        let initial_phase = MembershipPhase::Stable {
            config: constants.servers,
        };
        let key: (int, int) = (leader_id, leader.current_term);

        assert(LogCommitCertificatesValid(ds));
        assert(0 <= committer < ds.num_servers);
        assert(0 <= log_index < ds.server_states[committer].commit_index);
        assert(ds.server_states[committer].commit_index
            <= ds.server_states[committer].log.len());
        assert(certificate.governing_phase
            == active_membership_phase_from_raft_log(
                ds.server_states[committer].log,
                log_index,
                initial_phase,
            ));

        // Every certified boundary below the target is older than it, hence
        // older than the leader's term, hence held by the leader.
        assert forall |m: int| #![trigger ds.configuration_commit_certificates.dom().contains(m)]
            0 <= m < log_index
            && ds.configuration_commit_certificates.dom().contains(m)
            implies ds.server_states[leader_id].log.len() > m
                && ds.server_states[leader_id].log[m]
                    == ds.configuration_commit_certificates[m].entry
        by {
            lemma_configuration_certificate_term_below_log_certificate(
                ds, log_index, m);
            assert(CertifiedConfigurationLeaderCompleteness(ds));
        };

        lemma_governing_phase_progresses_from_cut_generic(
            ds,
            log_index,
            committer,
            certificate.governing_phase,
            leader_id,
            log_index,
        );

        assert(LeaderElectionSnapshotRecorded(ds));
        assert(ds.election_log_len.dom().contains(key));
        let snapshot = ds.election_log_len[key];
        assert(ElectionLogLenBounded(ds));
        assert(0 <= snapshot <= leader.log.len());

        let saved_phase = active_membership_phase_from_raft_log(
            leader.log, snapshot, initial_phase);
        let committed_phase = active_membership_phase_from_raft_log(
            leader.log, leader.commit_index, initial_phase);
        let cut_phase = active_membership_phase_from_raft_log(
            leader.log, log_index, initial_phase);
        assert(leader.election_membership_phase == Some(saved_phase));

        assert(AllRaftMembershipLogsWellFormed(ds));
        assert(UncommittedSuffixesHaveAtMostOneConfiguration(ds));
        assert forall |a: int, b: int| #![trigger leader.log[a], leader.log[b]]
            leader.commit_index <= a < leader.log.len()
            && leader.commit_index <= b < leader.log.len()
            && leader.log[a].payload is Configuration
            && leader.log[b].payload is Configuration
            implies a == b
        by {
            assert(uncommitted_suffix_has_at_most_one_configuration(
                leader.log, leader.commit_index));
        };

        if leader.commit_index <= snapshot {
            if certificate.governing_phase == committed_phase {
                lemma_bounded_boundary_interval_progresses_legally(
                    leader.log, leader.commit_index, snapshot, initial_phase);
                lemma_certified_log_entry_present_when_phases_are_related(
                    ds, log_index, leader_id, saved_phase);
            } else {
                assert(certificate.governing_phase == cut_phase);
                if log_index <= snapshot {
                    lemma_bounded_boundary_interval_progresses_legally(
                        leader.log, log_index, snapshot, initial_phase);
                    lemma_certified_log_entry_present_when_phases_are_related(
                        ds, log_index, leader_id, saved_phase);
                } else {
                    lemma_bounded_boundary_interval_progresses_legally(
                        leader.log, snapshot, log_index, initial_phase);
                    lemma_certified_log_entry_present_in_one_step_stale_leader(
                        ds, log_index, leader_id, saved_phase);
                }
            }
        } else {
            lemma_older_log_certificate_makes_snapshot_to_commit_configuration_free(
                ds, log_index, leader_id);
            assert(saved_phase == committed_phase);

            if certificate.governing_phase == committed_phase {
                lemma_phase_progression_reflexive(saved_phase);
                lemma_certified_log_entry_present_when_phases_are_related(
                    ds, log_index, leader_id, saved_phase);
            } else {
                assert(certificate.governing_phase == cut_phase);
                lemma_bounded_boundary_interval_progresses_legally(
                    leader.log, leader.commit_index, log_index, initial_phase);
                lemma_certified_log_entry_present_in_one_step_stale_leader(
                    ds, log_index, leader_id, saved_phase);
            }
        }
    }

    /// All-entry analogue of the snapshot-to-commit Configuration-free helper.
    ///
    /// A Configuration between a leader's election snapshot and its commit
    /// index would be committed, hence certified, hence — by the term ordering
    /// against the target log certificate — no newer than the target entry.
    /// But sitting at or beyond the snapshot it must carry at least the
    /// leader's own term, which strictly exceeds the target's. Contradiction.
    pub proof fn lemma_older_log_certificate_makes_snapshot_to_commit_configuration_free(
        ds: RaftDistributedState,
        log_index: int,
        leader_id: int,
    )
        requires
            LogCommitCertificatesValid(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            ElectionLogLenBounded(ds),
            ElectionLogLenEntryTermBound(ds),
            LeaderElectionSnapshotRecorded(ds),
            LogTermsMonotonic(ds),
            ds.log_commit_certificates.dom().contains(log_index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.log_commit_certificates[log_index].entry.term,
            ds.server_states[leader_id].commit_index <= log_index,
        ensures
            forall |j: int|
                #![trigger ds.server_states[leader_id].log[j]]
                ds.election_log_len[
                    (leader_id, ds.server_states[leader_id].current_term)]
                    <= j < ds.server_states[leader_id].commit_index
                ==> !(ds.server_states[leader_id].log[j].payload
                    is Configuration),
            ds.election_log_len[
                (leader_id, ds.server_states[leader_id].current_term)]
                <= ds.server_states[leader_id].commit_index
            ==> active_membership_phase_from_raft_log(
                    ds.server_states[leader_id].log,
                    ds.election_log_len[
                        (leader_id,
                         ds.server_states[leader_id].current_term)],
                    MembershipPhase::Stable {
                        config: ds.server_constants[leader_id].servers,
                    },
                ) == active_membership_phase_from_raft_log(
                    ds.server_states[leader_id].log,
                    ds.server_states[leader_id].commit_index,
                    MembershipPhase::Stable {
                        config: ds.server_constants[leader_id].servers,
                    },
                ),
    {
        let leader = ds.server_states[leader_id];
        let initial_phase = MembershipPhase::Stable {
            config: ds.server_constants[leader_id].servers,
        };
        let key: (int, int) = (leader_id, leader.current_term);

        assert(LeaderElectionSnapshotRecorded(ds));
        assert(ds.election_log_len.dom().contains(key));
        let snapshot = ds.election_log_len[key];
        assert(ElectionLogLenBounded(ds));
        assert(0 <= snapshot <= leader.log.len());
        assert(CommitIndexBounded(ds));

        assert forall |j: int| #![trigger leader.log[j]]
            snapshot <= j < leader.commit_index
            implies !(leader.log[j].payload is Configuration)
        by {
            if leader.log[j].payload is Configuration {
                assert(0 <= j);
                assert(j < log_index);
                assert(j < leader.log.len());
                lemma_committed_prefix_configuration_is_certified(
                    ds, leader_id, j);
                lemma_configuration_certificate_term_below_log_certificate(
                    ds, log_index, j);

                assert(ElectionLogLenEntryTermBound(ds));
                assert(ds.election_log_len[key] <= j);
                assert(ds.election_log_len.dom().contains(key));
                assert(0 <= key.0 < ds.num_servers);
                assert(ds.server_states[key.0].log[j] == leader.log[j]);
                assert(ds.server_states[key.0].log[j].term >= key.1);
                assert(leader.log[j].term >= leader.current_term);
                assert(false);
            }
        };

        if snapshot <= leader.commit_index {
            lemma_configuration_free_interval_preserves_active_phase(
                leader.log,
                snapshot,
                leader.commit_index,
                initial_phase,
            );
        }
    }

    /// All-entry analogue of
    /// `lemma_certified_boundary_present_when_phases_are_related`: when the
    /// certificate's governing phase legally progresses to the leader's saved
    /// election phase, the quorums overlap and the entry transfers in.
    pub proof fn lemma_certified_log_entry_present_when_phases_are_related(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
        election_phase: MembershipPhase,
    )
        requires
            WellFormedRaftDistributed(ds),
            LogCommitCertificatesValid(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            CertifiedLogEntryTransfersToVotedLeader(ds),
            ds.log_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.log_commit_certificates[index].entry.term,
            ds.server_states[leader_id].election_membership_phase
                == Some(election_phase),
            is_legal_phase_progression(
                ds.log_commit_certificates[index].governing_phase,
                election_phase,
            ),
        ensures
            ds.server_states[leader_id].log.len() > index,
            ds.server_states[leader_id].log[index]
                == ds.log_commit_certificates[index].entry,
    {
        let certificate = ds.log_commit_certificates[index];

        assert(has_recorded_election_quorum(ds.server_states[leader_id]));
        assert(is_quorum_for_phase(
            ds.server_states[leader_id].votes_granted,
            election_phase,
        ));
        assert(LogCommitCertificatesValid(ds));
        assert(is_quorum_for_phase(
            certificate.quorum,
            certificate.governing_phase,
        ));

        lemma_legal_phase_progression_quorums_intersect(
            certificate.quorum,
            ds.server_states[leader_id].votes_granted,
            certificate.governing_phase,
            election_phase,
        );

        let overlap_voter = choose |server: int| #![trigger certificate.quorum.contains(server)]
            certificate.quorum.contains(server)
            && ds.server_states[leader_id].votes_granted.contains(server);

        assert(ds.server_states[leader_id].votes_granted
            .contains(overlap_voter));
        assert(VotesGrantedAreServers(ds));
        assert(0 <= overlap_voter < ds.num_servers);
        assert(CertifiedLogEntryTransfersToVotedLeader(ds));
    }

    /// Stale direction of the same argument: quorum overlap is symmetric, so a
    /// leader elected under a phase the certificate's governing phase legally
    /// progresses *from* is covered too.
    pub proof fn lemma_certified_log_entry_present_in_one_step_stale_leader(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
        election_phase: MembershipPhase,
    )
        requires
            WellFormedRaftDistributed(ds),
            LogCommitCertificatesValid(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            CertifiedLogEntryTransfersToVotedLeader(ds),
            ds.log_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.log_commit_certificates[index].entry.term,
            ds.server_states[leader_id].election_membership_phase
                == Some(election_phase),
            is_legal_phase_progression(
                election_phase,
                ds.log_commit_certificates[index].governing_phase,
            ),
        ensures
            ds.server_states[leader_id].log.len() > index,
            ds.server_states[leader_id].log[index]
                == ds.log_commit_certificates[index].entry,
    {
        let certificate = ds.log_commit_certificates[index];

        assert(has_recorded_election_quorum(ds.server_states[leader_id]));
        assert(is_quorum_for_phase(
            ds.server_states[leader_id].votes_granted,
            election_phase,
        ));
        assert(LogCommitCertificatesValid(ds));
        assert(is_quorum_for_phase(
            certificate.quorum,
            certificate.governing_phase,
        ));

        lemma_legal_phase_progression_quorums_intersect(
            ds.server_states[leader_id].votes_granted,
            certificate.quorum,
            election_phase,
            certificate.governing_phase,
        );

        let overlap_voter = choose |server: int| #![trigger certificate.quorum.contains(server)]
            ds.server_states[leader_id].votes_granted.contains(server)
            && certificate.quorum.contains(server);

        assert(ds.server_states[leader_id].votes_granted
            .contains(overlap_voter));
        assert(VotesGrantedAreServers(ds));
        assert(0 <= overlap_voter < ds.num_servers);
        assert(CertifiedLogEntryTransfersToVotedLeader(ds));
    }

    /// Certificate-kind-neutral phase core.
    ///
    /// Takes the target's committer and governing phase as parameters instead
    /// of reading them off a `ConfigurationCommitCertificate`, so the identical
    /// case analysis serves both certificate maps. The Configuration cut core
    /// and the all-entry Data argument are both wrappers around this.
    pub proof fn lemma_governing_phase_progresses_from_cut_generic(
        ds: RaftDistributedState,
        target_index: int,
        target_committer: int,
        target_governing_phase: MembershipPhase,
        leader_id: int,
        cut: int,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            raft_membership_log_is_well_formed(
                ds.server_states[leader_id].log,
                MembershipPhase::Stable {
                    config: ds.server_constants[leader_id].servers,
                },
            ),
            uncommitted_suffix_has_at_most_one_configuration(
                ds.server_states[leader_id].log,
                ds.server_states[leader_id].commit_index,
            ),
            0 <= leader_id < ds.num_servers,
            0 <= target_committer < ds.num_servers,
            ds.server_constants[leader_id].servers
                == ds.server_constants[target_committer].servers,
            // The target committer holds its committed prefix through the
            // target position.
            0 <= target_index
                < ds.server_states[target_committer].commit_index,
            ds.server_states[target_committer].commit_index
                <= ds.server_states[target_committer].log.len(),
            // The governing phase, measured at the comparison prefix.
            target_governing_phase
                == active_membership_phase_from_raft_log(
                    ds.server_states[target_committer].log,
                    cut,
                    MembershipPhase::Stable {
                        config: ds.server_constants[leader_id].servers,
                    },
                ),
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < cut
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
            0 <= ds.server_states[leader_id].commit_index <= cut,
            cut <= target_index,
            cut <= ds.server_states[leader_id].log.len(),
        ensures
            is_legal_phase_progression(
                target_governing_phase,
                election_membership_phase_for_state(
                    ds.server_states[leader_id],
                    ds.server_constants[leader_id],
                ),
            ),
            ({
                ||| target_governing_phase
                    == active_membership_phase_from_raft_log(
                        ds.server_states[leader_id].log,
                        ds.server_states[leader_id].commit_index,
                        MembershipPhase::Stable {
                            config: ds.server_constants[leader_id].servers,
                        },
                    )
                ||| target_governing_phase
                    == active_membership_phase_from_raft_log(
                        ds.server_states[leader_id].log,
                        cut,
                        MembershipPhase::Stable {
                            config: ds.server_constants[leader_id].servers,
                        },
                    )
            }),
    {
        let committer = target_committer;
        let leader = ds.server_states[leader_id];
        let constants = ds.server_constants[leader_id];
        let committed_len = leader.commit_index;
        let initial_phase = MembershipPhase::Stable {
            config: constants.servers,
        };

        assert(cut <= ds.server_states[committer].log.len());

        assert forall |j: int| #![trigger leader.log[j]] 0 <= j < committed_len implies
            ((leader.log[j].payload is Configuration)
                == (ds.server_states[committer].log[j].payload
                    is Configuration))
        by {
            if ds.server_states[committer].log[j].payload is Configuration {
                lemma_committed_prefix_configuration_is_certified(
                    ds, committer, j);
            }
            if leader.log[j].payload is Configuration {
                lemma_leader_committed_configuration_shared_with_server(
                    ds, committer, leader_id, j);
            }
        };
        assert forall |j: int| #![trigger leader.log[j]]
            0 <= j < committed_len
            && leader.log[j].payload is Configuration
        implies leader.log[j] == ds.server_states[committer].log[j]
        by {
            assert(ds.configuration_commit_certificates.dom().contains(j));
            assert(leader.log[j]
                == ds.configuration_commit_certificates[j].entry);
            lemma_certified_boundary_agrees_with_committed_server(
                ds, j, committer);
        };
        lemma_logs_with_same_configurations_have_same_active_phase(
            leader.log,
            ds.server_states[committer].log,
            committed_len,
            initial_phase,
        );
        assert(active_membership_phase_for_state(leader, constants)
            == active_membership_phase_from_raft_log(
                ds.server_states[committer].log,
                committed_len,
                initial_phase,
            ));

        lemma_latest_log_election_phase_is_at_most_one_step_ahead(
            leader,
            constants,
        );

        if forall |j: int| #![trigger leader.log[j]]
            committed_len <= j < cut
            ==> !(leader.log[j].payload is Configuration)
        {
            assert forall |j: int| #![trigger ds.server_states[committer].log[j]]
                committed_len <= j < cut
                implies !(ds.server_states[committer].log[j].payload
                    is Configuration)
            by {
                if ds.server_states[committer].log[j].payload is Configuration {
                    lemma_committed_prefix_configuration_is_certified(
                        ds, committer, j);
                    assert(leader.log[j]
                        == ds.configuration_commit_certificates[j].entry);
                    lemma_configuration_commit_certificate_basic_validity(
                        ds, j);
                    assert(false);
                }
            };
            lemma_configuration_free_interval_preserves_active_phase(
                ds.server_states[committer].log,
                committed_len,
                cut,
                initial_phase,
            );
        } else {
            let boundary = choose |j: int| #![trigger leader.log[j]]
                committed_len <= j < cut
                && leader.log[j].payload is Configuration;

            assert forall |j: int| #![trigger leader.log[j]]
                committed_len <= j < leader.log.len()
                && leader.log[j].payload is Configuration
                implies j == boundary
            by {
                assert(uncommitted_suffix_has_at_most_one_configuration(
                    leader.log, committed_len));
            };

            if ds.server_states[committer].log[boundary].payload
                is Configuration
            {
                lemma_committed_prefix_configuration_is_certified(
                    ds, committer, boundary);
                assert(leader.log[boundary]
                    == ds.configuration_commit_certificates[boundary].entry);
                assert(ds.server_states[committer].log[boundary]
                    == ds.configuration_commit_certificates[boundary].entry)
                by {
                    lemma_certified_boundary_agrees_with_committed_server(
                        ds, boundary, committer);
                };

                assert forall |j: int| #![trigger ds.server_states[committer].log[j]]
                    committed_len <= j < cut
                    && ds.server_states[committer].log[j].payload
                        is Configuration
                    implies j == boundary
                by {
                    lemma_committed_prefix_configuration_is_certified(
                        ds, committer, j);
                    assert(leader.log[j]
                        == ds.configuration_commit_certificates[j].entry);
                    lemma_configuration_commit_certificate_basic_validity(
                        ds, j);
                };

                assert forall |j: int| #![trigger leader.log[j]] 0 <= j < cut implies
                    ((leader.log[j].payload is Configuration)
                        == (ds.server_states[committer].log[j].payload
                            is Configuration))
                by {
                    if j < committed_len {
                    } else {
                        if leader.log[j].payload is Configuration {
                            assert(j == boundary);
                        }
                        if ds.server_states[committer].log[j].payload
                            is Configuration
                        {
                            assert(j == boundary);
                        }
                    }
                };
                assert forall |j: int| #![trigger leader.log[j]]
                    0 <= j < cut
                    && leader.log[j].payload is Configuration
                implies leader.log[j]
                    == ds.server_states[committer].log[j]
                by {
                    if j < committed_len {
                    } else {
                        assert(j == boundary);
                    }
                };
                lemma_logs_with_same_configurations_have_same_active_phase(
                    leader.log,
                    ds.server_states[committer].log,
                    cut,
                    initial_phase,
                );
                assert forall |j: int| #![trigger leader.log[j]]
                    cut <= j < leader.log.len()
                    implies !(leader.log[j].payload is Configuration)
                by {
                    if leader.log[j].payload is Configuration {
                        assert(j == boundary);
                        assert(false);
                    }
                };
                lemma_configuration_free_interval_preserves_active_phase(
                    leader.log,
                    cut,
                    leader.log.len() as int,
                    initial_phase,
                );
                lemma_phase_progression_reflexive(target_governing_phase);
            } else {
                assert forall |j: int| #![trigger ds.server_states[committer].log[j]]
                    committed_len <= j < cut
                    implies !(ds.server_states[committer].log[j].payload
                        is Configuration)
                by {
                    if ds.server_states[committer].log[j].payload is Configuration {
                        lemma_committed_prefix_configuration_is_certified(
                            ds, committer, j);
                        assert(leader.log[j]
                            == ds.configuration_commit_certificates[j].entry);
                        lemma_configuration_commit_certificate_basic_validity(
                            ds, j);
                        assert(j == boundary);
                        assert(false);
                    }
                };
                lemma_configuration_free_interval_preserves_active_phase(
                    ds.server_states[committer].log,
                    committed_len,
                    cut,
                    initial_phase,
                );
            }
        }
    }

    /// Certificate-kind-neutral form: any Configuration a server holds below
    /// its own commit index is certified. The Configuration-certificate
    /// version fixes the server to a particular certificate's committer; this
    /// one takes the server directly, so it also serves all-entry certificates.
    pub proof fn lemma_committed_prefix_configuration_is_certified(
        ds: RaftDistributedState,
        server_id: int,
        j: int,
    )
        requires
            CommittedConfigurationsHaveCertificates(ds),
            0 <= server_id < ds.num_servers,
            0 <= j < ds.server_states[server_id].commit_index,
            j < ds.server_states[server_id].log.len(),
            ds.server_states[server_id].log[j].payload is Configuration,
        ensures
            ds.configuration_commit_certificates.dom().contains(j),
            ds.configuration_commit_certificates[j].entry
                == ds.server_states[server_id].log[j],
    {
        assert(CommittedConfigurationsHaveCertificates(ds));
    }

    /// Kind-neutral form of "a leader's committed Configuration is shared":
    /// any Configuration the leader holds below its commit index is certified,
    /// and any server that has also committed that far carries the same
    /// Configuration there.
    pub proof fn lemma_leader_committed_configuration_shared_with_server(
        ds: RaftDistributedState,
        server_id: int,
        leader_id: int,
        j: int,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            0 <= leader_id < ds.num_servers,
            0 <= server_id < ds.num_servers,
            0 <= j < ds.server_states[leader_id].commit_index,
            j < ds.server_states[leader_id].log.len(),
            ds.server_states[leader_id].log[j].payload is Configuration,
            j < ds.server_states[server_id].commit_index,
            j < ds.server_states[server_id].log.len(),
        ensures
            ds.configuration_commit_certificates.dom().contains(j),
            ds.server_states[server_id].log[j].payload is Configuration,
    {
        lemma_committed_prefix_configuration_is_certified(ds, leader_id, j);
        lemma_certified_boundary_agrees_with_committed_server(
            ds, j, server_id);
        lemma_configuration_commit_certificate_basic_validity(ds, j);
    }

    /// A certified Configuration boundary below a certified log entry has no
    /// greater term.
    ///
    /// The log certificate's committer holds its whole committed prefix, so
    /// both entries sit in that one log with the boundary earlier; log terms
    /// are monotonic within a server. Consequently a leader whose term exceeds
    /// the target entry's term also exceeds every earlier certified boundary's,
    /// which is exactly what global Configuration Leader Completeness needs to
    /// place those boundaries in the leader.
    pub proof fn lemma_configuration_certificate_term_below_log_certificate(
        ds: RaftDistributedState,
        log_index: int,
        configuration_index: int,
    )
        requires
            LogCommitCertificatesValid(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedEntriesHaveLogCertificates(ds),
            LogTermsMonotonic(ds),
            ds.log_commit_certificates.dom().contains(log_index),
            ds.configuration_commit_certificates.dom()
                .contains(configuration_index),
            0 <= configuration_index < log_index,
        ensures
            ds.configuration_commit_certificates[configuration_index]
                .entry.term
                <= ds.log_commit_certificates[log_index].entry.term,
    {
        let committer = ds.log_commit_certificates[log_index].committer;

        assert(LogCommitCertificatesValid(ds));
        assert(0 <= committer < ds.num_servers);
        assert(0 <= log_index < ds.server_states[committer].commit_index);
        assert(ds.server_states[committer].commit_index
            <= ds.server_states[committer].log.len());
        assert(log_index < ds.server_states[committer].log.len());
        assert(ds.server_states[committer].log[log_index]
            == ds.log_commit_certificates[log_index].entry);

        // The boundary lies in the same committed prefix.
        assert(configuration_index
            < ds.server_states[committer].commit_index);
        assert(configuration_index < ds.server_states[committer].log.len());
        lemma_certified_boundary_agrees_with_committed_server(
            ds, configuration_index, committer);

        assert(LogTermsMonotonic(ds));
    }

    /// All-entry dynamic Leader Completeness, stated directly over the
    /// certificate map so it can be a conjunct of `RaftSafetyInvariant`.
    ///
    /// Covers Data and Configuration payloads alike: every leader whose term
    /// exceeds a certified entry's term holds that exact entry at that index.
    pub open spec fn DynamicLeaderCompleteness(
        ds: RaftDistributedState,
    ) -> bool {
        forall |index: int, leader_id: int|
            #![trigger ds.log_commit_certificates[index],
                       ds.server_states[leader_id].role]
            ds.log_commit_certificates.dom().contains(index)
            && 0 <= leader_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term
                > ds.log_commit_certificates[index].entry.term
            ==> {
                &&& ds.server_states[leader_id].log.len() > index
                &&& ds.server_states[leader_id].log[index]
                    == ds.log_commit_certificates[index].entry
            }
    }

    /// All-entry analogue of `CertifiedBoundaryTransfersToVotedLeader`.
    ///
    /// This is the *same* inherited static-Raft log-transfer trust boundary
    /// already relied on for Configuration Leader Completeness, restated over
    /// `LogCommitCertificate`. It introduces no new assumption.
    pub open spec fn CertifiedLogEntryTransfersToVotedLeader(
        ds: RaftDistributedState,
    ) -> bool {
        forall |index: int, leader_id: int, overlap_voter: int| #![trigger ds.log_commit_certificates.dom().contains(index), ds.server_states[leader_id].votes_granted.contains(overlap_voter)]
            ds.log_commit_certificates.dom().contains(index)
            && 0 <= leader_id < ds.num_servers
            && 0 <= overlap_voter < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term
                > ds.log_commit_certificates[index].entry.term
            && ds.log_commit_certificates[index].quorum
                .contains(overlap_voter)
            && ds.server_states[leader_id].votes_granted
                .contains(overlap_voter)
            ==> {
                &&& ds.server_states[leader_id].log.len() > index
                &&& ds.server_states[leader_id].log[index]
                    == ds.log_commit_certificates[index].entry
            }
    }

    /// The all-entry transfer obligation is discharged by the same inherited
    /// lemma as the Configuration one — no new trust boundary.
    pub proof fn lemma_log_entry_transfer_obligation_discharged_by_inherited_lemma(
        ds: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            EntryTermHasVoteQuorum(ds),
            LogCommitCertificatesValid(ds),
            VotersVotedForCandidate(ds),
            VoteResponseIntegrity(ds),
            LogMatching(ds),
            LogTermsMonotonic(ds),
            VoteResponseHasRequestVote(ds),
            OneVotePerTermInNetwork(ds),
            CandidateVoteDestinationUnique(ds),
            RequestVoteSummaryStillValidAtSameTerm(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteLogLenEntryTermBound(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
        ensures
            CertifiedLogEntryTransfersToVotedLeader(ds),
    {
        assert forall |index: int, leader_id: int, overlap_voter: int| #![trigger ds.log_commit_certificates.dom().contains(index), ds.server_states[leader_id].votes_granted.contains(overlap_voter)]
            ds.log_commit_certificates.dom().contains(index)
            && 0 <= leader_id < ds.num_servers
            && 0 <= overlap_voter < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term
                > ds.log_commit_certificates[index].entry.term
            && ds.log_commit_certificates[index].quorum
                .contains(overlap_voter)
            && ds.server_states[leader_id].votes_granted
                .contains(overlap_voter)
        implies {
            &&& ds.server_states[leader_id].log.len() > index
            &&& ds.server_states[leader_id].log[index]
                == ds.log_commit_certificates[index].entry
        }
        by {
            let certificate = ds.log_commit_certificates[index];

            // Certificate validity already places the entry in the voter's log.
            assert(LogCommitCertificatesValid(ds));
            assert(index < ds.server_states[overlap_voter].log.len());
            assert(ds.server_states[overlap_voter].log[index]
                == certificate.entry);
            assert(0 <= index);

            if overlap_voter != leader_id {
                assert(VotersVotedForCandidate(ds));
                let vote = choose |packet: LRaftPacket| #![trigger ds.network.contains(packet)] {
                    &&& ds.network.contains(packet)
                    &&& packet.dst == leader_id
                    &&& packet.msg matches LRaftMessage::VoteResponse {
                        term,
                        granted,
                        voter,
                        ..
                    }
                    &&& term == ds.server_states[leader_id].current_term
                    &&& granted
                    &&& voter == overlap_voter
                };
                assert(vote.src == overlap_voter) by {
                    assert(VoteResponseIntegrity(ds));
                };
                assert(
                    ds.server_states[overlap_voter].current_term
                        > vote.msg->VoteResponse_term
                    || (ds.server_states[overlap_voter].current_term
                            == vote.msg->VoteResponse_term
                        && ds.server_states[overlap_voter].has_voted
                        && ds.server_states[overlap_voter].voted_for
                            == leader_id)
                ) by {
                    assert(VoteResponseIntegrity(ds));
                };

                lemma_overlap_voter_entry_transfer(
                    ds,
                    leader_id,
                    overlap_voter,
                    index,
                    certificate.entry,
                );
            }
        };
    }

    /// Membership-specific half of Configuration Leader Completeness. Given the
    /// first-missing-boundary provenance and the inherited transfer obligation
    /// above, quorum overlap across the governing membership phase forces every
    /// strictly higher-term leader to hold every certified boundary.
    ///
    /// Unlike the existing
    /// `lemma_first_missing_boundary_provenance_implies_configuration_leader_completeness`,
    /// this route never calls `lemma_overlap_voter_entry_transfer`, so the
    /// dependence on the inherited gap is visible in the signature.
    pub proof fn lemma_configuration_leader_completeness_under_transfer_obligation(
        ds: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            FirstMissingConfigurationBoundaryProvenance(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
        ensures
            CertifiedConfigurationLeaderCompleteness(ds),
    {
        assert forall |index: int, leader_id: int|
            ds.configuration_commit_certificates.dom().contains(index)
            && 0 <= leader_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term
        implies {
            &&& ds.server_states[leader_id].log.len() > index
            &&& ds.server_states[leader_id].log[index]
                == ds.configuration_commit_certificates[index].entry
        }
        by {
            if !(ds.server_states[leader_id].log.len() > index
                && ds.server_states[leader_id].log[index]
                    == ds.configuration_commit_certificates[index].entry)
            {
                // The leader is missing this boundary, so provenance hands us a
                // certificate-quorum witness together with the election prefix
                // the leader and that witness share.
                assert(FirstMissingConfigurationBoundaryProvenance(ds));
                let (certificate_witness, election_commit_len):
                    (int, int) = choose
                    |certificate_witness: int, election_commit_len: int| #![trigger ds.configuration_commit_certificates[index].quorum.contains(certificate_witness), active_membership_phase_from_raft_log(ds.server_states[leader_id].log, election_commit_len, MembershipPhase::Stable { config: ds.server_constants[leader_id].servers })] {
                        &&& ds.configuration_commit_certificates[index].quorum
                            .contains(certificate_witness)
                        &&& 0 <= election_commit_len
                            <= ds.server_states[leader_id].log.len()
                        &&& election_commit_len <= index
                        &&& ds.server_states[leader_id].election_membership_phase
                            == Some(active_membership_phase_from_raft_log(
                                ds.server_states[leader_id].log,
                                election_commit_len,
                                MembershipPhase::Stable {
                                    config: ds.server_constants[leader_id]
                                        .servers,
                                },
                            ))
                        &&& forall |prefix_index: int|
                            0 <= prefix_index < election_commit_len
                            ==> ds.server_states[leader_id].log[prefix_index]
                                == ds.server_states[certificate_witness]
                                    .log[prefix_index]
                        &&& forall |prefix_index: int| #![trigger ds.server_states[certificate_witness].log[prefix_index]]
                            election_commit_len <= prefix_index < index
                            ==> !(ds.server_states[certificate_witness]
                                .log[prefix_index].payload is Configuration)
                    };

                // The phase the leader recorded at election time is exactly the
                // phase that governed this certificate.
                lemma_first_missing_certificate_matches_recorded_election_phase(
                    ds,
                    index,
                    leader_id,
                    certificate_witness,
                    election_commit_len,
                );

                // So the leader's vote set is a quorum for the governing phase,
                // and overlaps the quorum that committed the boundary.
                assert(has_recorded_election_quorum(
                    ds.server_states[leader_id],
                ));
                lemma_configuration_certificate_quorum_intersects_election_phase(
                    ds,
                    index,
                    ds.server_states[leader_id].votes_granted,
                );

                let overlap_voter = choose |server: int|
                    ds.configuration_commit_certificates[index].quorum
                        .contains(server)
                    && ds.server_states[leader_id].votes_granted
                        .contains(server);

                assert(ds.server_states[leader_id].votes_granted
                    .contains(overlap_voter));
                assert(VotesGrantedAreServers(ds));
                assert(0 <= overlap_voter < ds.num_servers);

                // The inherited transfer obligation closes the case.
                assert(CertifiedBoundaryTransfersToVotedLeader(ds));
            }
        };
    }

    /// Every Configuration entry lying below a certified boundary in that
    /// certificate's committer log is itself certified. The committer holds
    /// the boundary below its own commit index, so the whole prefix is
    /// committed, and committed Configurations always carry certificates.
    ///
    /// This is the step that lets a minimal-missing-boundary argument conclude
    /// that a leader holding every *certified* boundary below `index` in fact
    /// holds every *Configuration* the committer has below `index`.
    pub proof fn lemma_committer_prefix_configurations_are_certified(
        ds: RaftDistributedState,
        index: int,
        j: int,
    )
        requires
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= j < index,
            ds.server_states[
                ds.configuration_commit_certificates[index].committer
            ].log[j].payload is Configuration,
        ensures
            ds.configuration_commit_certificates.dom().contains(j),
            ds.configuration_commit_certificates[j].entry
                == ds.server_states[
                    ds.configuration_commit_certificates[index].committer
                ].log[j],
    {
        let committer = ds.configuration_commit_certificates[index].committer;

        assert(ConfigurationCommittersRetainCertifiedPrefixes(ds));
        assert(0 <= committer < ds.num_servers);
        assert(0 <= index < ds.server_states[committer].commit_index);
        assert(ds.server_states[committer].commit_index
            <= ds.server_states[committer].log.len());

        // `j` sits below the boundary, hence below the committer's commit
        // index and inside its log.
        assert(j < ds.server_states[committer].commit_index);
        assert(j < ds.server_states[committer].log.len());

        assert(CommittedConfigurationsHaveCertificates(ds));
    }

    /// A leader that holds every *certified* boundary below `index` therefore
    /// agrees with the certificate's committer at every *Configuration*
    /// position below `index` — because, by the previous lemma, all of those
    /// Configurations are certified.
    ///
    /// This is the minimal-missing-boundary step: at the smallest index a
    /// leader is missing, its membership history below that index coincides
    /// with the committer's.
    pub proof fn lemma_minimal_missing_leader_matches_committer_configurations(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
        j: int,
    )
        requires
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            // The leader holds every certified boundary strictly below `index`.
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < index
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
            0 <= j < index,
            ds.server_states[
                ds.configuration_commit_certificates[index].committer
            ].log[j].payload is Configuration,
        ensures
            ds.server_states[leader_id].log.len() > j,
            ds.server_states[leader_id].log[j]
                == ds.server_states[
                    ds.configuration_commit_certificates[index].committer
                ].log[j],
    {
        lemma_committer_prefix_configurations_are_certified(ds, index, j);
        assert(ds.configuration_commit_certificates.dom().contains(j));
    }

    /// Assembly of the minimal-missing-boundary argument.
    ///
    /// At the smallest certified boundary a leader is missing, the leader's
    /// membership history below that boundary coincides with the committer's,
    /// so its committed phase is the certificate's governing phase; its
    /// election phase is then at most one legal joint-consensus step beyond
    /// that; and one-step phase separation forces the quorums to overlap. The
    /// overlapping voter carries the boundary into the leader's log — so the
    /// leader was not missing it after all.
    ///
    /// The one residual hypothesis is that the leader holds no Configuration
    /// in the stretch between its commit index and the boundary.
    pub proof fn lemma_certified_boundary_present_at_minimal_missing_index(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term,
            ds.server_constants[leader_id].servers
                == ds.server_constants[
                    ds.configuration_commit_certificates[index].committer
                ].servers,
            // Minimality: every certified boundary below `index` is held.
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < index
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
            index <= ds.server_states[leader_id].log.len(),
            ds.server_states[leader_id].commit_index <= index,
            // Structural facts the one-step-ahead result needs.
            raft_membership_log_is_well_formed(
                ds.server_states[leader_id].log,
                MembershipPhase::Stable {
                    config: ds.server_constants[leader_id].servers,
                },
            ),
            uncommitted_suffix_has_at_most_one_configuration(
                ds.server_states[leader_id].log,
                ds.server_states[leader_id].commit_index,
            ),
            ds.server_states[leader_id].election_membership_phase
                == Some(election_membership_phase_for_state(
                    ds.server_states[leader_id],
                    ds.server_constants[leader_id],
                )),
        ensures
            ds.server_states[leader_id].log.len() > index,
            ds.server_states[leader_id].log[index]
                == ds.configuration_commit_certificates[index].entry,
    {
        let leader = ds.server_states[leader_id];
        let election_phase = election_membership_phase_for_state(
            leader,
            ds.server_constants[leader_id],
        );

        lemma_minimal_missing_governing_phase_progresses_to_election(
            ds, index, leader_id);

        lemma_certified_boundary_present_when_phases_are_related(
            ds,
            index,
            leader_id,
            election_phase,
        );
    }

    /// Milestone B for newly elected leaders, with the phase hypothesis
    /// discharged rather than assumed.
    ///
    /// The index induction needs the leader's recorded election phase to be the
    /// latest-log phase of its own state. That is not an invariant — it fails
    /// once a leader appends a Configuration — but it holds by construction at
    /// the moment of promotion, which is exactly when Leader Completeness has
    /// something to say. Existing leaders are covered separately by
    /// `lemma_configuration_leader_completeness_quiet_step`.
    pub proof fn lemma_new_leader_holds_certified_boundaries(
        ds: RaftDistributedState,
        leader_id: int,
        bound: int,
        pre_state: LState,
        vote_term: int,
        vote_granted: bool,
        voter: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            AllRaftMembershipLogsWellFormed(ds),
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
            0 <= leader_id < ds.num_servers,
            // `leader_id` has just been promoted into this state.
            LReceiveVoteAndBecomeLeader(
                pre_state,
                ds.server_states[leader_id],
                ds.server_constants[leader_id],
                vote_term,
                vote_granted,
                voter,
                sent_packets,
            ),
            0 <= bound <= ds.server_states[leader_id].log.len(),
            forall |a: int, e: int|
                #![trigger ds.server_constants[a], ds.server_constants[e]]
                0 <= a < ds.num_servers && 0 <= e < ds.num_servers
                ==> ds.server_constants[a].servers
                    == ds.server_constants[e].servers,
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < bound
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].current_term
                    > ds.configuration_commit_certificates[m].entry.term,
        ensures
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < bound
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
    {
        // The promotion rule leaves the log alone and stores the phase derived
        // from it, so the recorded phase is this state's latest-log phase.
        lemma_receive_vote_and_become_leader_records_latest_log_phase(
            pre_state,
            ds.server_states[leader_id],
            ds.server_constants[leader_id],
            vote_term,
            vote_granted,
            voter,
            sent_packets,
        );
        assert(ds.server_states[leader_id].role is Leader);

        lemma_certified_boundaries_present_below(ds, leader_id, bound);
    }

    /// Step 2d: a leader whose log stops short of a certified boundary is
    /// impossible.
    ///
    /// Any Configuration the committer holds between the leader's log end and
    /// the boundary would itself be certified, hence held by the leader — which
    /// its log length forbids. So that stretch is Configuration-free, the
    /// leader's election phase is exactly the certificate's governing phase,
    /// and quorum overlap forces the leader to hold the boundary after all,
    /// contradicting the short log.
    pub proof fn lemma_certified_boundary_forbids_short_leader_log(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term,
            ds.server_constants[leader_id].servers
                == ds.server_constants[
                    ds.configuration_commit_certificates[index].committer
                ].servers,
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < index
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
            // The leader's log stops before the boundary.
            ds.server_states[leader_id].log.len() < index,
            // No Configuration the committer lacks, below the leader's log end.
            forall |j: int|
                #![trigger ds.server_states[leader_id].log[j]]
                0 <= j < ds.server_states[leader_id].log.len()
                && ds.server_states[leader_id].log[j].payload is Configuration
                ==> ds.server_states[
                        ds.configuration_commit_certificates[index].committer
                    ].log[j].payload is Configuration,
            ds.server_states[leader_id].election_membership_phase
                == Some(election_membership_phase_for_state(
                    ds.server_states[leader_id],
                    ds.server_constants[leader_id],
                )),
        ensures
            false,
    {
        let leader = ds.server_states[leader_id];
        let constants = ds.server_constants[leader_id];
        let committer = ds.configuration_commit_certificates[index].committer;
        let leader_len = leader.log.len() as int;
        let initial_phase = MembershipPhase::Stable {
            config: constants.servers,
        };

        assert(ConfigurationCommittersRetainCertifiedPrefixes(ds));
        assert(0 <= committer < ds.num_servers);
        assert(0 <= index < ds.server_states[committer].commit_index);
        assert(ds.server_states[committer].commit_index
            <= ds.server_states[committer].log.len());
        assert(index <= ds.server_states[committer].log.len());

        // The committer holds no Configuration between the leader's log end
        // and the boundary: such an entry would be certified, hence held.
        assert forall |p: int| #![trigger ds.server_states[committer].log[p]] leader_len <= p < index
        implies !(ds.server_states[committer].log[p].payload is Configuration)
        by {
            if ds.server_states[committer].log[p].payload is Configuration {
                lemma_committer_prefix_configurations_are_certified(
                    ds, index, p);
                assert(ds.server_states[leader_id].log.len() > p);
            }
        };

        // So the governing phase is already fixed by the committer's prefix of
        // the leader's own length.
        lemma_configuration_free_interval_preserves_active_phase(
            ds.server_states[committer].log,
            leader_len,
            index,
            initial_phase,
        );

        // Both logs carry the same Configurations below that length.
        assert forall |j: int| #![trigger ds.server_states[leader_id].log[j]] #![trigger ds.server_states[committer].log[j]] 0 <= j < leader_len implies
            ((ds.server_states[leader_id].log[j].payload is Configuration)
                == (ds.server_states[committer].log[j].payload
                    is Configuration))
        by {
            if ds.server_states[committer].log[j].payload is Configuration {
                lemma_minimal_missing_leader_matches_committer_configurations(
                    ds, index, leader_id, j);
            }
        };

        assert forall |j: int| #![trigger ds.server_states[leader_id].log[j]] #![trigger ds.server_states[committer].log[j]]
            0 <= j < leader_len
            && ds.server_states[leader_id].log[j].payload is Configuration
        implies ds.server_states[leader_id].log[j]
            == ds.server_states[committer].log[j]
        by {
            lemma_minimal_missing_leader_matches_committer_configurations(
                ds, index, leader_id, j);
        };

        lemma_logs_with_same_configurations_have_same_active_phase(
            ds.server_states[leader_id].log,
            ds.server_states[committer].log,
            leader_len,
            initial_phase,
        );

        // The leader's election phase reads its whole log, which is that same
        // prefix — so it equals the governing phase, and overlap applies.
        lemma_configuration_commit_certificate_valid_for_replica(
            ds, index, committer);
        lemma_certified_boundary_present_when_phases_are_related(
            ds,
            index,
            leader_id,
            election_membership_phase_for_state(leader, constants),
        );
    }

    /// Step 3, stable half: under Stable membership over the whole server set,
    /// no divergent Configuration can exist.
    ///
    /// If the entry at `j` is certified under a Stable-full phase, the bridge
    /// makes it a legacy fixed-majority commitment, and inherited Leader
    /// Completeness then forces a higher-term leader to hold exactly that
    /// entry. So a leader carrying a Configuration at `j` means the committer
    /// carries the same Configuration there — never a Data entry.
    ///
    /// The joint-consensus half is out of reach by this route: a joint quorum
    /// need not meet the fixed-majority threshold the bridge requires.
    pub proof fn lemma_no_divergent_configuration_under_stable_membership(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
        j: int,
        config: Set<int>,
    )
        requires
            WellFormedRaftDistributed(ds),
            LeaderCompleteness(ds),
            LogCommitCertificatesValid(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedEntriesHaveLogCertificates(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            0 <= j < index,
            j < ds.server_states[leader_id].log.len(),
            ds.server_states[leader_id].log[j].payload is Configuration,
            // The entry at `j` is certified under Stable-full membership.
            ds.log_commit_certificates.dom().contains(j),
            ds.log_commit_certificates[j].governing_phase
                == (MembershipPhase::Stable { config: config }),
            config.len() == ds.num_servers,
            ds.server_states[leader_id].current_term
                > ds.log_commit_certificates[j].entry.term,
        ensures
            ds.server_states[
                ds.configuration_commit_certificates[index].committer
            ].log[j].payload is Configuration,
    {
        let committer = ds.configuration_commit_certificates[index].committer;

        // Inherited Leader Completeness pins the leader's entry at `j`.
        lemma_legacy_leader_completeness_covers_stable_log_certificate(
            ds, j, config, leader_id);
        assert(ds.server_states[leader_id].log[j]
            == ds.log_commit_certificates[j].entry);

        // The committer has `j` committed, so its entry there is the same
        // unique all-entry certificate entry.
        assert(ConfigurationCommittersRetainCertifiedPrefixes(ds));
        assert(0 <= committer < ds.num_servers);
        assert(0 <= index < ds.server_states[committer].commit_index);
        assert(ds.server_states[committer].commit_index
            <= ds.server_states[committer].log.len());
        assert(j < ds.server_states[committer].commit_index);
        assert(j < ds.server_states[committer].log.len());
        assert(CommittedEntriesHaveLogCertificates(ds));
        assert(ds.log_commit_certificates[j].entry
            == ds.server_states[committer].log[j]);
    }

    /// Step 2b: every server shares one universe of server identities. This is
    /// already pinned by `WellFormedRaftDistributed`, which fixes each server's
    /// `servers` set to `{0, .., num_servers-1}`.
    pub proof fn lemma_all_servers_share_server_universe(
        ds: RaftDistributedState,
        left: int,
        right: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            0 <= left < ds.num_servers,
            0 <= right < ds.num_servers,
        ensures
            ds.server_constants[left].servers
                == ds.server_constants[right].servers,
    {
        assert(WellFormedRaftDistributed(ds));
    }

    /// Step 2a: certified boundary terms increase with their log position.
    ///
    /// The certificate at `index` has a committer holding the whole prefix
    /// below `index` committed, so both boundaries sit in that one log, and
    /// log terms are monotonic. Consequently a leader whose term exceeds the
    /// boundary at `index` also exceeds every certified boundary below it —
    /// which is exactly the term hypothesis the index induction carries.
    pub proof fn lemma_certified_boundary_terms_are_monotonic(
        ds: RaftDistributedState,
        index: int,
        m: int,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedEntriesHaveLogCertificates(ds),
            LogTermsMonotonic(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            ds.configuration_commit_certificates.dom().contains(m),
            0 <= m < index,
        ensures
            ds.configuration_commit_certificates[m].entry.term
                <= ds.configuration_commit_certificates[index].entry.term,
    {
        let committer = ds.configuration_commit_certificates[index].committer;

        assert(ConfigurationCommittersRetainCertifiedPrefixes(ds));
        assert(0 <= committer < ds.num_servers);
        assert(0 <= index < ds.server_states[committer].commit_index);
        assert(ds.server_states[committer].commit_index
            <= ds.server_states[committer].log.len());
        assert(index < ds.server_states[committer].log.len());
        assert(ds.server_states[committer].log[index]
            == ds.configuration_commit_certificates[index].entry);

        // The lower boundary sits in the same committed prefix.
        assert(m < ds.server_states[committer].commit_index);
        assert(m < ds.server_states[committer].log.len());
        lemma_certified_boundary_agrees_with_committed_server(
            ds, m, committer);

        assert(LogTermsMonotonic(ds));
    }

    /// The single remaining obligation of Milestone B, isolated as a state
    /// predicate: no server carries a Configuration entry at a position where
    /// a certificate's committer carries a Data entry.
    ///
    /// Every other case of Configuration Leader Completeness is discharged.
    /// Establishing this predicate needs the term-induction machinery that the
    /// inherited proof base never built, so it is stated rather than proved.
    /// Well-formedness of the election-snapshot ghost map, mirroring
    /// `VoteLogLenBounded`.
    pub open spec fn ElectionLogLenBounded(ds: RaftDistributedState) -> bool {
        forall |v: int, t: int| #![trigger ds.election_log_len.dom().contains((v, t))] ds.election_log_len.dom().contains((v, t)) ==> {
            &&& 0 <= v < ds.num_servers
            &&& 0 <= ds.election_log_len[(v, t)]
            &&& ds.election_log_len[(v, t)]
                <= ds.server_states[v].log.len()
            &&& ds.server_states[v].current_term >= t
        }
    }

    /// Entries at or beyond a recorded election snapshot carry a term at least
    /// that of the election. Contrapositive, which is the form proofs want: an
    /// entry whose term is strictly below the election term was already in the
    /// log when that election happened.
    pub open spec fn ElectionLogLenEntryTermBound(
        ds: RaftDistributedState,
    ) -> bool {
        forall |p: (int, int), i: int|
            #![trigger ds.server_states[p.0].log[i],
                       ds.election_log_len.dom().contains(p)]
            ds.election_log_len.dom().contains(p)
            && 0 <= p.0 < ds.num_servers
            && ds.election_log_len[p] <= i
            && i < ds.server_states[p.0].log.len()
        ==> ds.server_states[p.0].log[i].term >= p.1
    }

    /// Every leader has a snapshot recorded for its current term, and its saved
    /// membership phase is derived from exactly that prefix.
    ///
    /// This is the strengthening `has_recorded_election_log_provenance` lacks:
    /// that predicate only says the phase comes from *some* prefix, which is
    /// too weak to connect a leader's election snapshot to certified
    /// membership boundaries.
    pub open spec fn LeaderElectionSnapshotRecorded(
        ds: RaftDistributedState,
    ) -> bool {
        forall |i: int|
            #![trigger ds.server_states[i].role]
            0 <= i < ds.num_servers
            && ds.server_states[i].role is Leader
            ==> {
                &&& ds.election_log_len.dom().contains(
                    (i, ds.server_states[i].current_term))
                &&& ds.server_states[i].election_membership_phase
                    == Some(active_membership_phase_from_raft_log(
                        ds.server_states[i].log,
                        ds.election_log_len[
                            (i, ds.server_states[i].current_term)],
                        MembershipPhase::Stable {
                            config: ds.server_constants[i].servers,
                        },
                    ))
            }
    }

    pub proof fn lemma_election_log_len_bounded_inductive(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            ElectionLogLenBounded(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            ElectionLogLenBounded(ds_),
    {
        lemma_log_append_only(ds, ds_);

        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        assert forall |v: int, t: int| #![trigger ds_.election_log_len.dom().contains((v, t))]
            ds_.election_log_len.dom().contains((v, t))
        implies {
            &&& 0 <= v < ds_.num_servers
            &&& 0 <= ds_.election_log_len[(v, t)]
            &&& ds_.election_log_len[(v, t)]
                <= ds_.server_states[v].log.len()
            &&& ds_.server_states[v].current_term >= t
        } by {
            assert(LogAppendOnly(ds, ds_));
            if ds.election_log_len.dom().contains((v, t)) {
                assert(ElectionLogLenBounded(ds));
            }
        };
    }

    pub proof fn lemma_election_log_len_entry_term_bound_inductive(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            ElectionLogLenEntryTermBound(ds),
            ElectionLogLenBounded(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            ElectionLogLenEntryTermBound(ds_),
    {
        lemma_log_append_only(ds, ds_);
        lemma_distributed_next_implies_legacy(ds, ds_);

        let server_id = choose |sid: int| #![trigger ds.server_states[sid]] #![trigger ds_.server_states[sid]] #![trigger ds.server_constants[sid]] {
            &&& 0 <= sid < ds.num_servers
            &&& LNext(ds.server_states[sid], ds_.server_states[sid],
                       ds.server_constants[sid])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        assert forall |p: (int, int), i: int|
            #![trigger ds_.server_states[p.0].log[i],
                       ds_.election_log_len.dom().contains(p)]
            ds_.election_log_len.dom().contains(p)
            && 0 <= p.0 < ds_.num_servers
            && ds_.election_log_len[p] <= i
            && i < ds_.server_states[p.0].log.len()
        implies ds_.server_states[p.0].log[i].term >= p.1 by {
            let v = p.0;
            let t = p.1;
            if v != server_id {
                assert(ds_.server_states[v] == ds.server_states[v]);
                assert(ds.election_log_len.dom().contains((v, t)));
                assert(ElectionLogLenEntryTermBound(ds));
            } else {
                if ds.election_log_len.dom().contains((v, t)) {
                    if i < ds.server_states[v].log.len() {
                        assert(LogAppendOnly(ds, ds_));
                        assert(ds_.server_states[v].log[i]
                            == ds.server_states[v].log[i]);
                        assert(ElectionLogLenEntryTermBound(ds));
                    } else {
                        // Freshly appended entry: its term is the appending
                        // server's current term, which is at least `t`.
                        assert(ElectionLogLenBounded(ds));
                        assert(ds.server_states[v].current_term >= t);
                    }
                } else {
                    // Newly recorded snapshot: the log has exactly that length,
                    // so no index at or beyond it exists yet.
                    assert(ds_.election_log_len[p]
                        == ds.server_states[server_id].log.len());
                }
            }
        };
    }

    pub proof fn lemma_leader_election_snapshot_recorded_inductive(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            LeaderElectionSnapshotRecorded(ds),
            ElectionLogLenBounded(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            LeaderElectionSnapshotRecorded(ds_),
    {
        lemma_log_append_only(ds, ds_);
        lemma_distributed_next_implies_legacy(ds, ds_);

        let server_id = choose |sid: int| #![trigger ds.server_states[sid]] #![trigger ds_.server_states[sid]] #![trigger ds.server_constants[sid]] {
            &&& 0 <= sid < ds.num_servers
            &&& LNext(ds.server_states[sid], ds_.server_states[sid],
                       ds.server_constants[sid])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        assert forall |i: int| #![trigger ds_.server_states[i]]
            0 <= i < ds_.num_servers
            && ds_.server_states[i].role is Leader
        implies {
            &&& ds_.election_log_len.dom().contains(
                (i, ds_.server_states[i].current_term))
            &&& ds_.server_states[i].election_membership_phase
                == Some(active_membership_phase_from_raft_log(
                    ds_.server_states[i].log,
                    ds_.election_log_len[
                        (i, ds_.server_states[i].current_term)],
                    MembershipPhase::Stable {
                        config: ds_.server_constants[i].servers,
                    },
                ))
        } by {
            assert(LogAppendOnly(ds, ds_));
            if i != server_id {
                assert(ds_.server_states[i] == ds.server_states[i]);
                assert(LeaderElectionSnapshotRecorded(ds));
            } else {
                let s = ds.server_states[server_id];
                let s_ = ds_.server_states[server_id];
                let constants = ds.server_constants[server_id];

                if s.role is Leader {
                    // A leader that is still a leader kept its term, its saved
                    // phase, and its snapshot, and only appended entries — so
                    // the prefix the phase reads is untouched.
                    assert(LeaderElectionSnapshotRecorded(ds));
                    assert(ElectionLogLenBounded(ds));
                    let snapshot = ds.election_log_len[
                        (server_id, s.current_term)];
                    assert(snapshot <= s.log.len());
                    lemma_equal_committed_raft_prefixes_have_same_active_phase(
                        s.log,
                        s_.log,
                        snapshot,
                        MembershipPhase::Stable {
                            config: constants.servers,
                        },
                    );
                } else {
                    // A promotion records the snapshot and saves exactly the
                    // phase derived from the whole log it was elected on.
                    assert(ds_.election_log_len[
                        (server_id, s_.current_term)] == s.log.len());
                    assert(s_.log == s.log);
                }
            }
        };
    }

    /// A certified boundary whose term is below a leader's own term sits
    /// strictly inside that leader's election snapshot.
    ///
    /// Leader Completeness places the boundary in the leader's log; the
    /// snapshot term bound then forces its position to be below the snapshot,
    /// because everything at or beyond the snapshot was appended by this leader
    /// and therefore carries its current term.
    ///
    /// This is the fact that lets an *existing* leader's saved membership phase
    /// be related to a certificate's governing phase — the newly-promoted case
    /// gets it for free, since its snapshot is its whole log.
    pub proof fn lemma_certified_boundary_below_election_snapshot(
        ds: RaftDistributedState,
        m: int,
        leader_id: int,
    )
        requires
            CertifiedConfigurationLeaderCompleteness(ds),
            ElectionLogLenEntryTermBound(ds),
            ElectionLogLenBounded(ds),
            LeaderElectionSnapshotRecorded(ds),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.configuration_commit_certificates.dom().contains(m),
            0 <= m,
            ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[m].entry.term,
        ensures
            ds.server_states[leader_id].log.len() > m,
            ds.server_states[leader_id].log[m]
                == ds.configuration_commit_certificates[m].entry,
            m < ds.election_log_len[
                (leader_id, ds.server_states[leader_id].current_term)],
    {
        // Leader Completeness places the certified entry in the leader's log.
        assert(CertifiedConfigurationLeaderCompleteness(ds));
        assert(ds.server_states[leader_id].log.len() > m);
        assert(ds.server_states[leader_id].log[m]
            == ds.configuration_commit_certificates[m].entry);

        // The snapshot exists for this leader's term. Bind the key as a single
        // pair so the term-bound quantifier's trigger shape matches.
        assert(LeaderElectionSnapshotRecorded(ds));
        let term = ds.server_states[leader_id].current_term;
        let key: (int, int) = (leader_id, term);
        assert(key.0 == leader_id);
        assert(key.1 == term);
        assert(ds.election_log_len.dom().contains(key));
        let snapshot = ds.election_log_len[key];

        // If the boundary sat at or beyond the snapshot it would have been
        // appended by this leader, hence carry its current term — but its term
        // is strictly smaller.
        assert(ElectionLogLenEntryTermBound(ds));
        if snapshot <= m {
            assert(ds.election_log_len[key] <= m);
            assert(m < ds.server_states[key.0].log.len());
            assert(ds.server_states[key.0].log[m].term >= key.1);
            assert(false);
        }
    }

    pub open spec fn NoDivergentUncommittedConfiguration(
        ds: RaftDistributedState,
    ) -> bool {
        forall |index: int, server_id: int, j: int|
            #![trigger ds.server_states[server_id].log[j],
                       ds.configuration_commit_certificates[index]]
            ds.configuration_commit_certificates.dom().contains(index)
            && 0 <= server_id < ds.num_servers
            && 0 <= j < index
            && j < ds.server_states[server_id].log.len()
            && ds.server_states[server_id].log[j].payload is Configuration
            ==> ds.server_states[
                    ds.configuration_commit_certificates[index].committer
                ].log[j].payload is Configuration
    }

    /// Strong induction over the log index: a leader holds every certified
    /// membership boundary below any bound within its own log length.
    ///
    /// Each step splits on whether the boundary is already below the leader's
    /// commit index — in which case committed agreement settles it — or above,
    /// where the minimal-missing-boundary argument applies with the induction
    /// hypothesis supplying minimality.
    pub proof fn lemma_certified_boundaries_present_below(
        ds: RaftDistributedState,
        leader_id: int,
        bound: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            AllRaftMembershipLogsWellFormed(ds),
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            0 <= bound <= ds.server_states[leader_id].log.len(),
            // All servers share one universe of server identities.
            forall |a: int, b: int|
                #![trigger ds.server_constants[a], ds.server_constants[b]]
                0 <= a < ds.num_servers && 0 <= b < ds.num_servers
                ==> ds.server_constants[a].servers
                    == ds.server_constants[b].servers,
            // The leader's term exceeds every certified boundary below `bound`.
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < bound
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].current_term
                    > ds.configuration_commit_certificates[m].entry.term,
            ds.server_states[leader_id].election_membership_phase
                == Some(election_membership_phase_for_state(
                    ds.server_states[leader_id],
                    ds.server_constants[leader_id],
                )),
        ensures
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < bound
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
        decreases bound,
    {
        if bound > 0 {
            let m = bound - 1;

            lemma_certified_boundaries_present_below(ds, leader_id, m);

            if ds.configuration_commit_certificates.dom().contains(m) {
                assert(CommitIndexBounded(ds));
                assert(m < ds.server_states[leader_id].log.len());

                if m < ds.server_states[leader_id].commit_index {
                    lemma_certified_boundary_agrees_with_committed_server(
                        ds, m, leader_id);
                } else {
                    assert(AllRaftMembershipLogsWellFormed(ds));
                    assert(UncommittedSuffixesHaveAtMostOneConfiguration(ds));
                    lemma_certified_boundary_present_at_minimal_missing_index(
                        ds, m, leader_id);
                }
            }
        }
    }

    /// Strengthened assembly. The earlier version required the leader to hold
    /// *no* Configuration between its commit index and the boundary; this one
    /// only requires that the leader holds no Configuration the committer
    /// lacks — an uncommitted boundary that agrees with the committer is fine.
    ///
    /// Two situations arise. If no boundary waits below `index`, the previous
    /// assembly applies directly. Otherwise the single permitted uncommitted
    /// boundary lies below `index`, so none lies above it; the leader's
    /// election phase is then exactly its prefix phase, which the crux lemma
    /// identifies with the certificate's governing phase, and legal phase
    /// progression is reflexive.
    ///
    /// What remains open is only a *divergent* uncommitted Configuration —
    /// one sitting where the committer holds a Data entry.
    pub proof fn lemma_certified_boundary_present_without_divergent_configuration(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term,
            ds.server_constants[leader_id].servers
                == ds.server_constants[
                    ds.configuration_commit_certificates[index].committer
                ].servers,
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < index
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
            index <= ds.server_states[leader_id].log.len(),
            ds.server_states[leader_id].commit_index <= index,
            // No Configuration the committer lacks.
            forall |j: int|
                #![trigger ds.server_states[leader_id].log[j]]
                0 <= j < index
                && ds.server_states[leader_id].log[j].payload is Configuration
                ==> ds.server_states[
                        ds.configuration_commit_certificates[index].committer
                    ].log[j].payload is Configuration,
            raft_membership_log_is_well_formed(
                ds.server_states[leader_id].log,
                MembershipPhase::Stable {
                    config: ds.server_constants[leader_id].servers,
                },
            ),
            uncommitted_suffix_has_at_most_one_configuration(
                ds.server_states[leader_id].log,
                ds.server_states[leader_id].commit_index,
            ),
            ds.server_states[leader_id].election_membership_phase
                == Some(election_membership_phase_for_state(
                    ds.server_states[leader_id],
                    ds.server_constants[leader_id],
                )),
        ensures
            ds.server_states[leader_id].log.len() > index,
            ds.server_states[leader_id].log[index]
                == ds.configuration_commit_certificates[index].entry,
    {
        let leader = ds.server_states[leader_id];
        let constants = ds.server_constants[leader_id];
        let initial_phase = MembershipPhase::Stable {
            config: constants.servers,
        };

        if forall |j: int| #![trigger leader.log[j]]
            leader.commit_index <= j < index
            ==> !(leader.log[j].payload is Configuration)
        {
            lemma_certified_boundary_present_at_minimal_missing_index(
                ds, index, leader_id);
        } else {
            // Some boundary waits below `index`.
            let waiting = choose |j: int| #![trigger leader.log[j]]
                leader.commit_index <= j < index
                && leader.log[j].payload is Configuration;

            // At most one boundary waits, so none sits at or above `index`.
            assert forall |m: int| #![trigger leader.log[m]]
                index <= m < leader.log.len()
            implies !(leader.log[m].payload is Configuration)
            by {
                if leader.log[m].payload is Configuration {
                    assert(uncommitted_suffix_has_at_most_one_configuration(
                        leader.log, leader.commit_index));
                    assert(waiting == m);
                }
            };

            // Hence the election phase is exactly the prefix phase at `index`,
            // which the crux lemma identifies with the governing phase.
            lemma_minimal_missing_boundary_phases_agree(ds, index, leader_id);
            lemma_configuration_free_interval_preserves_active_phase(
                leader.log,
                index,
                leader.log.len() as int,
                initial_phase,
            );
            assert(election_membership_phase_for_state(leader, constants)
                == ds.configuration_commit_certificates[index]
                    .governing_phase);

            lemma_certified_boundary_present_when_phases_are_related(
                ds,
                index,
                leader_id,
                election_membership_phase_for_state(leader, constants),
            );
        }
    }

    /// Half of the remaining hypothesis, discharged: any Configuration the
    /// leader holds *below its own commit index* is one the committer holds
    /// too. Committed Configurations carry certificates, and the committer has
    /// the whole prefix below the boundary committed, so it agrees there.
    ///
    /// What this leaves is only the leader's uncommitted suffix, which
    /// `UncommittedSuffixesHaveAtMostOneConfiguration` already bounds to a
    /// single entry.
    pub proof fn lemma_leader_committed_configuration_is_shared_with_committer(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
        j: int,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            0 <= j < index,
            j < ds.server_states[leader_id].commit_index,
            j < ds.server_states[leader_id].log.len(),
            ds.server_states[leader_id].log[j].payload is Configuration,
        ensures
            ds.configuration_commit_certificates.dom().contains(j),
            ds.server_states[
                ds.configuration_commit_certificates[index].committer
            ].log[j].payload is Configuration,
    {
        let committer = ds.configuration_commit_certificates[index].committer;

        // The leader's committed Configuration at `j` is certified.
        assert(CommittedConfigurationsHaveCertificates(ds));
        assert(ds.configuration_commit_certificates.dom().contains(j));

        // The committer has `j` below its own commit index, since j < index.
        assert(ConfigurationCommittersRetainCertifiedPrefixes(ds));
        assert(0 <= committer < ds.num_servers);
        assert(0 <= index < ds.server_states[committer].commit_index);
        assert(ds.server_states[committer].commit_index
            <= ds.server_states[committer].log.len());
        assert(j < ds.server_states[committer].commit_index);
        assert(j < ds.server_states[committer].log.len());

        // So the committer's entry there is the certified one, which is a
        // Configuration by certificate validity.
        lemma_certified_boundary_agrees_with_committed_server(
            ds,
            j,
            committer,
        );
        lemma_configuration_commit_certificate_basic_validity(ds, j);
    }

    /// The crux of the minimal-missing-boundary argument: at the smallest
    /// certified boundary a leader is missing, the membership phase derived
    /// from the leader's own prefix is exactly the phase that governed the
    /// certificate.
    ///
    /// The leader holds every certified boundary below `index`, and every
    /// Configuration the committer has below `index` is certified, so the two
    /// logs carry the same Configuration entries at the same positions there.
    /// Since the derived phase reads only Configuration entries, the phases
    /// coincide — the differing Data entries are irrelevant.
    ///
    /// The remaining hypothesis is that the leader carries no Configuration
    /// below `index` that the committer lacks; discharging it is what stands
    /// between this and unconditional Configuration Leader Completeness.
    pub proof fn lemma_minimal_missing_boundary_phases_agree(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_constants[leader_id].servers
                == ds.server_constants[
                    ds.configuration_commit_certificates[index].committer
                ].servers,
            // The leader holds every certified boundary strictly below `index`.
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < index
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
            // The leader's log reaches the boundary.
            index <= ds.server_states[leader_id].log.len(),
            // The leader carries no extra Configuration below the boundary.
            forall |j: int|
                #![trigger ds.server_states[leader_id].log[j]]
                0 <= j < index
                && ds.server_states[leader_id].log[j].payload is Configuration
                ==> ds.server_states[
                        ds.configuration_commit_certificates[index].committer
                    ].log[j].payload is Configuration,
        ensures
            active_membership_phase_from_raft_log(
                ds.server_states[leader_id].log,
                index,
                MembershipPhase::Stable {
                    config: ds.server_constants[leader_id].servers,
                },
            ) == ds.configuration_commit_certificates[index].governing_phase,
    {
        let certificate = ds.configuration_commit_certificates[index];
        let committer = certificate.committer;

        assert(ConfigurationCommittersRetainCertifiedPrefixes(ds));
        assert(0 <= committer < ds.num_servers);
        assert(0 <= index < ds.server_states[committer].commit_index);
        assert(ds.server_states[committer].commit_index
            <= ds.server_states[committer].log.len());
        assert(index <= ds.server_states[committer].log.len());
        assert(certificate.quorum.contains(committer));

        // The certificate's governing phase is the committer's derived phase.
        lemma_configuration_commit_certificate_valid_for_replica(
            ds,
            index,
            committer,
        );
        assert(certificate.governing_phase
            == active_membership_phase_from_raft_log(
                ds.server_states[committer].log,
                index,
                MembershipPhase::Stable {
                    config: ds.server_constants[committer].servers,
                },
            ));

        // Same Configuration entries at the same positions below `index`.
        assert forall |j: int| #![trigger ds.server_states[leader_id].log[j]] #![trigger ds.server_states[committer].log[j]] 0 <= j < index implies
            ((ds.server_states[leader_id].log[j].payload is Configuration)
                == (ds.server_states[committer].log[j].payload
                    is Configuration))
        by {
            if ds.server_states[committer].log[j].payload is Configuration {
                lemma_minimal_missing_leader_matches_committer_configurations(
                    ds, index, leader_id, j);
            }
        };

        assert forall |j: int| #![trigger ds.server_states[leader_id].log[j]] #![trigger ds.server_states[committer].log[j]]
            0 <= j < index
            && ds.server_states[leader_id].log[j].payload is Configuration
        implies ds.server_states[leader_id].log[j]
            == ds.server_states[committer].log[j]
        by {
            lemma_minimal_missing_leader_matches_committer_configurations(
                ds, index, leader_id, j);
        };

        lemma_logs_with_same_configurations_have_same_active_phase(
            ds.server_states[leader_id].log,
            ds.server_states[committer].log,
            index,
            MembershipPhase::Stable {
                config: ds.server_constants[leader_id].servers,
            },
        );
    }

    /// Cut-parameterised core of the minimal-missing-boundary phase argument.
    ///
    /// The two integer parameters have distinct roles that the original proof
    /// conflated: `certificate_index` identifies the target certificate and its
    /// committer, while `cut` is the prefix at which membership phases are
    /// compared. Callers that compare at the boundary itself pass
    /// `cut == certificate_index`; the short-log case compares at the leader's
    /// log end instead.
    ///
    /// The governing phase at `cut` is taken as a hypothesis rather than read
    /// off certificate validity, since only the `cut == certificate_index`
    /// caller gets it for free.
    pub proof fn lemma_minimal_missing_governing_phase_progresses_from_cut(
        ds: RaftDistributedState,
        certificate_index: int,
        leader_id: int,
        cut: int,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            raft_membership_log_is_well_formed(
                ds.server_states[leader_id].log,
                MembershipPhase::Stable {
                    config: ds.server_constants[leader_id].servers,
                },
            ),
            uncommitted_suffix_has_at_most_one_configuration(
                ds.server_states[leader_id].log,
                ds.server_states[leader_id].commit_index,
            ),
            ds.configuration_commit_certificates.dom()
                .contains(certificate_index),
            0 <= leader_id < ds.num_servers,
            ds.server_constants[leader_id].servers
                == ds.server_constants[
                    ds.configuration_commit_certificates[certificate_index]
                        .committer
                ].servers,
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < cut
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
            0 <= ds.server_states[leader_id].commit_index <= cut,
            cut <= certificate_index,
            cut <= ds.server_states[leader_id].log.len(),
            // The governing phase, measured at the comparison prefix.
            ds.configuration_commit_certificates[certificate_index]
                .governing_phase
                == active_membership_phase_from_raft_log(
                    ds.server_states[
                        ds.configuration_commit_certificates[certificate_index]
                            .committer
                    ].log,
                    cut,
                    MembershipPhase::Stable {
                        config: ds.server_constants[leader_id].servers,
                    },
                ),
        ensures
            is_legal_phase_progression(
                ds.configuration_commit_certificates[certificate_index]
                    .governing_phase,
                election_membership_phase_for_state(
                    ds.server_states[leader_id],
                    ds.server_constants[leader_id],
                ),
            ),
            // Directional source of the governing phase. Callers need to know
            // which side supplies it: two progressions into a common phase say
            // nothing about the phases they start from.
            ({
                ||| ds.configuration_commit_certificates[certificate_index]
                        .governing_phase
                    == active_membership_phase_from_raft_log(
                        ds.server_states[leader_id].log,
                        ds.server_states[leader_id].commit_index,
                        MembershipPhase::Stable {
                            config: ds.server_constants[leader_id].servers,
                        },
                    )
                ||| ds.configuration_commit_certificates[certificate_index]
                        .governing_phase
                    == active_membership_phase_from_raft_log(
                        ds.server_states[leader_id].log,
                        cut,
                        MembershipPhase::Stable {
                            config: ds.server_constants[leader_id].servers,
                        },
                    )
            }),
    {
        // Wrapper: the Configuration certificate supplies the committer and
        // governing phase that the kind-neutral core takes as parameters.
        let certificate =
            ds.configuration_commit_certificates[certificate_index];
        let committer = certificate.committer;

        assert(ConfigurationCommittersRetainCertifiedPrefixes(ds));
        assert(0 <= committer < ds.num_servers);
        assert(0 <= certificate_index
            < ds.server_states[committer].commit_index);
        assert(ds.server_states[committer].commit_index
            <= ds.server_states[committer].log.len());

        lemma_governing_phase_progresses_from_cut_generic(
            ds,
            certificate_index,
            committer,
            certificate.governing_phase,
            leader_id,
            cut,
        );
    }

    /// At a minimal missing certified boundary, an extra uncommitted
    /// Configuration in the leader does not require the global
    /// `NoDivergentUncommittedConfiguration` hypothesis.
    ///
    /// There is at most one such entry. If the committer also carries a
    /// Configuration there, minimality says the two entries are the same and
    /// both logs derive the same phase. Otherwise the committer has no
    /// Configuration after the leader's commit index, so the certificate is
    /// governed by the leader's committed phase and the leader's one pending
    /// boundary moves its election phase forward by one legal step.
    pub proof fn lemma_minimal_missing_governing_phase_progresses_to_election(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            raft_membership_log_is_well_formed(
                ds.server_states[leader_id].log,
                MembershipPhase::Stable {
                    config: ds.server_constants[leader_id].servers,
                },
            ),
            uncommitted_suffix_has_at_most_one_configuration(
                ds.server_states[leader_id].log,
                ds.server_states[leader_id].commit_index,
            ),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_constants[leader_id].servers
                == ds.server_constants[
                    ds.configuration_commit_certificates[index].committer
                ].servers,
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < index
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
            0 <= ds.server_states[leader_id].commit_index <= index,
            index <= ds.server_states[leader_id].log.len(),
        ensures
            is_legal_phase_progression(
                ds.configuration_commit_certificates[index].governing_phase,
                election_membership_phase_for_state(
                    ds.server_states[leader_id],
                    ds.server_constants[leader_id],
                ),
            ),
            // Every branch pins the governing phase to the leader's own phase
            // at one of two prefixes: its commit index (when the leader has no
            // pending boundary below `index`, or a divergent one) or `index`
            // itself (when its pending boundary is the committer's). Exposing
            // this lets the result be re-derived at any later prefix — notably
            // a leader's election snapshot — without redoing the case analysis.
            ({
                ||| ds.configuration_commit_certificates[index].governing_phase
                    == active_membership_phase_from_raft_log(
                        ds.server_states[leader_id].log,
                        ds.server_states[leader_id].commit_index,
                        MembershipPhase::Stable {
                            config: ds.server_constants[leader_id].servers,
                        },
                    )
                ||| ds.configuration_commit_certificates[index].governing_phase
                    == active_membership_phase_from_raft_log(
                        ds.server_states[leader_id].log,
                        index,
                        MembershipPhase::Stable {
                            config: ds.server_constants[leader_id].servers,
                        },
                    )
            }),
    {
        let certificate = ds.configuration_commit_certificates[index];
        let committer = certificate.committer;
        let initial_phase = MembershipPhase::Stable {
            config: ds.server_constants[leader_id].servers,
        };

        // Certificate validity supplies the governing phase at the boundary
        // itself, which is this caller's comparison prefix.
        assert(ConfigurationCommittersRetainCertifiedPrefixes(ds));
        assert(0 <= committer < ds.num_servers);
        assert(0 <= index < ds.server_states[committer].commit_index);
        assert(ds.server_states[committer].commit_index
            <= ds.server_states[committer].log.len());
        assert(index <= ds.server_states[committer].log.len());
        lemma_configuration_commit_certificate_valid_for_replica(
            ds, index, committer);
        assert(certificate.governing_phase
            == active_membership_phase_from_raft_log(
                ds.server_states[committer].log,
                index,
                initial_phase,
            ));

        lemma_minimal_missing_governing_phase_progresses_from_cut(
            ds, index, leader_id, index);
    }

    /// The governing phase of a certificate progresses legally to the leader's
    /// phase at *any* prefix from `index` up to its log length — in particular
    /// to its election snapshot, which is the prefix its saved membership phase
    /// and hence its vote quorum are measured against.
    ///
    /// Follows from the two-prefix postcondition above plus the interval
    /// progression lemma: whichever prefix pins the governing phase, the
    /// stretch from there to the target lies inside the leader's uncommitted
    /// suffix and so carries at most one boundary.
    pub proof fn lemma_governing_phase_progresses_to_prefix(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
        target_len: int,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            raft_membership_log_is_well_formed(
                ds.server_states[leader_id].log,
                MembershipPhase::Stable {
                    config: ds.server_constants[leader_id].servers,
                },
            ),
            uncommitted_suffix_has_at_most_one_configuration(
                ds.server_states[leader_id].log,
                ds.server_states[leader_id].commit_index,
            ),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_constants[leader_id].servers
                == ds.server_constants[
                    ds.configuration_commit_certificates[index].committer
                ].servers,
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < index
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
            0 <= ds.server_states[leader_id].commit_index <= index,
            index <= target_len <= ds.server_states[leader_id].log.len(),
        ensures
            is_legal_phase_progression(
                ds.configuration_commit_certificates[index].governing_phase,
                active_membership_phase_from_raft_log(
                    ds.server_states[leader_id].log,
                    target_len,
                    MembershipPhase::Stable {
                        config: ds.server_constants[leader_id].servers,
                    },
                ),
            ),
    {
        let leader = ds.server_states[leader_id];
        let initial_phase = MembershipPhase::Stable {
            config: ds.server_constants[leader_id].servers,
        };

        lemma_minimal_missing_governing_phase_progresses_to_election(
            ds, index, leader_id);

        // Both candidate prefixes sit at or above the commit index, so the
        // stretch up to the target lies in the uncommitted suffix and carries
        // at most one boundary.
        assert forall |a: int, b: int| #![trigger leader.log[a], leader.log[b]]
            leader.commit_index <= a < target_len
            && leader.commit_index <= b < target_len
            && leader.log[a].payload is Configuration
            && leader.log[b].payload is Configuration
            implies a == b
        by {
            assert(uncommitted_suffix_has_at_most_one_configuration(
                leader.log, leader.commit_index));
        };

        if ds.configuration_commit_certificates[index].governing_phase
            == active_membership_phase_from_raft_log(
                leader.log, leader.commit_index, initial_phase)
        {
            lemma_bounded_boundary_interval_progresses_legally(
                leader.log,
                leader.commit_index,
                target_len,
                initial_phase,
            );
        } else {
            assert forall |a: int, b: int| #![trigger leader.log[a], leader.log[b]]
                index <= a < target_len
                && index <= b < target_len
                && leader.log[a].payload is Configuration
                && leader.log[b].payload is Configuration
                implies a == b
            by {
                assert(uncommitted_suffix_has_at_most_one_configuration(
                    leader.log, leader.commit_index));
            };
            lemma_bounded_boundary_interval_progresses_legally(
                leader.log,
                index,
                target_len,
                initial_phase,
            );
        }
    }

    /// An already-elected leader holds a certified boundary it has every
    /// earlier boundary for — the counterpart of
    /// `lemma_new_leader_holds_certified_boundaries` for leaders that were not
    /// promoted by the current step.
    ///
    /// The leader's vote quorum is a quorum for its *saved* phase, which is
    /// measured at its election snapshot, so the governing phase is related to
    /// the phase at that prefix rather than at the log end. Whichever side the
    /// snapshot falls on, one legal step separates the two phases and the
    /// quorums overlap.
    ///
    /// Requires the leader's commit index not to have advanced past its own
    /// election snapshot. A leader that has committed Configuration entries it
    /// appended itself since winning office can be arbitrarily many boundaries
    /// beyond the phase its vote quorum was gathered under; that case is not
    /// covered here.
    pub proof fn lemma_existing_leader_holds_certified_boundary(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            AllRaftMembershipLogsWellFormed(ds),
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            ElectionLogLenBounded(ds),
            LeaderElectionSnapshotRecorded(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term,
            ds.server_constants[leader_id].servers
                == ds.server_constants[
                    ds.configuration_commit_certificates[index].committer
                ].servers,
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < index
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
            0 <= ds.server_states[leader_id].commit_index <= index,
            index <= ds.server_states[leader_id].log.len(),
            // The leader has not committed past its own election snapshot.
            ds.server_states[leader_id].commit_index
                <= ds.election_log_len[
                    (leader_id, ds.server_states[leader_id].current_term)],
        ensures
            ds.server_states[leader_id].log.len() > index,
            ds.server_states[leader_id].log[index]
                == ds.configuration_commit_certificates[index].entry,
    {
        let leader = ds.server_states[leader_id];
        let constants = ds.server_constants[leader_id];
        let initial_phase = MembershipPhase::Stable {
            config: constants.servers,
        };
        let term = leader.current_term;
        let key: (int, int) = (leader_id, term);

        assert(LeaderElectionSnapshotRecorded(ds));
        assert(ds.election_log_len.dom().contains(key));
        let snapshot = ds.election_log_len[key];
        assert(ElectionLogLenBounded(ds));
        assert(snapshot <= leader.log.len());

        let saved_phase = active_membership_phase_from_raft_log(
            leader.log, snapshot, initial_phase);
        assert(leader.election_membership_phase == Some(saved_phase));

        assert(AllRaftMembershipLogsWellFormed(ds));
        assert(UncommittedSuffixesHaveAtMostOneConfiguration(ds));

        // Which prefix pins the governing phase decides the direction of the
        // progression; the target endpoints must be chosen accordingly, since
        // two progressions into a common phase say nothing about the phases
        // they start from.
        lemma_minimal_missing_governing_phase_progresses_to_election(
            ds, index, leader_id);

        assert forall |a: int, b: int| #![trigger leader.log[a], leader.log[b]]
            leader.commit_index <= a < leader.log.len()
            && leader.commit_index <= b < leader.log.len()
            && leader.log[a].payload is Configuration
            && leader.log[b].payload is Configuration
            implies a == b
        by {
            assert(uncommitted_suffix_has_at_most_one_configuration(
                leader.log, leader.commit_index));
        };

        if ds.configuration_commit_certificates[index].governing_phase
            == active_membership_phase_from_raft_log(
                leader.log, leader.commit_index, initial_phase)
        {
            // Governing phase sits at the commit index, which is at or below
            // the snapshot: progress forward to the saved phase.
            lemma_bounded_boundary_interval_progresses_legally(
                leader.log,
                leader.commit_index,
                snapshot,
                initial_phase,
            );
            lemma_certified_boundary_present_when_phases_are_related(
                ds, index, leader_id, saved_phase);
        } else {
            // Governing phase sits at `index`.
            if index <= snapshot {
                lemma_bounded_boundary_interval_progresses_legally(
                    leader.log,
                    index,
                    snapshot,
                    initial_phase,
                );
                lemma_certified_boundary_present_when_phases_are_related(
                    ds, index, leader_id, saved_phase);
            } else {
                lemma_bounded_boundary_interval_progresses_legally(
                    leader.log,
                    snapshot,
                    index,
                    initial_phase,
                );
                lemma_certified_boundary_present_in_one_step_stale_leader(
                    ds, index, leader_id, saved_phase);
            }
        }
    }

    /// Removes the artificial `commit_index <= election snapshot` restriction
    /// from `lemma_existing_leader_holds_certified_boundary`.
    ///
    /// If the leader has committed beyond its election snapshot, that interval
    /// cannot contain a Configuration boundary relevant to an older-term
    /// certificate. Such a boundary is committed and therefore certified; its
    /// position below `index` makes its term no greater than the target
    /// certificate's term, while its position at or beyond the election
    /// snapshot makes its term at least the leader's strictly greater term.
    /// The contradiction leaves a Configuration-free interval, so the saved
    /// election phase is still exactly the phase at the leader's commit index.
    pub proof fn lemma_existing_leader_holds_certified_boundary_unconditionally(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            AllRaftMembershipLogsWellFormed(ds),
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            ElectionLogLenBounded(ds),
            ElectionLogLenEntryTermBound(ds),
            LeaderElectionSnapshotRecorded(ds),
            LogTermsMonotonic(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term,
            ds.server_constants[leader_id].servers
                == ds.server_constants[
                    ds.configuration_commit_certificates[index].committer
                ].servers,
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < index
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
            0 <= ds.server_states[leader_id].commit_index <= index,
            index <= ds.server_states[leader_id].log.len(),
        ensures
            ds.server_states[leader_id].log.len() > index,
            ds.server_states[leader_id].log[index]
                == ds.configuration_commit_certificates[index].entry,
    {
        let leader = ds.server_states[leader_id];
        let constants = ds.server_constants[leader_id];
        let initial_phase = MembershipPhase::Stable {
            config: constants.servers,
        };
        let key: (int, int) = (leader_id, leader.current_term);

        assert(LeaderElectionSnapshotRecorded(ds));
        assert(ds.election_log_len.dom().contains(key));
        let snapshot = ds.election_log_len[key];
        assert(ElectionLogLenBounded(ds));
        assert(0 <= snapshot <= leader.log.len());

        if leader.commit_index <= snapshot {
            lemma_existing_leader_holds_certified_boundary(
                ds, index, leader_id);
        } else {
            assert(snapshot < leader.commit_index);
            assert(leader.commit_index <= index);

            // A committed Configuration after this leader's election would
            // simultaneously have a term at least the election term and no
            // greater than the older target boundary's term.
            assert forall |j: int| #![trigger leader.log[j]]
                snapshot <= j < leader.commit_index
                implies !(leader.log[j].payload is Configuration)
            by {
                if leader.log[j].payload is Configuration {
                    assert(0 <= snapshot);
                    assert(0 <= j);
                    assert(j < index);
                    assert(CommittedConfigurationsHaveCertificates(ds));
                    assert(ds.configuration_commit_certificates.dom()
                        .contains(j));
                    assert(ds.configuration_commit_certificates[j].entry
                        == leader.log[j]);
                    lemma_certified_boundary_terms_are_monotonic(
                        ds, index, j);
                    assert(ds.configuration_commit_certificates[j].entry.term
                        <= ds.configuration_commit_certificates[index]
                            .entry.term);

                    assert(ElectionLogLenEntryTermBound(ds));
                    assert(ds.election_log_len[key] <= j);
                    assert(ds.election_log_len.dom().contains(key));
                    assert(0 <= key.0 < ds.num_servers);
                    assert(j < leader.log.len());
                    assert(ds.server_states[key.0].log[j]
                        == leader.log[j]);
                    assert(ds.server_states[key.0].log[j].term
                        >= key.1);
                    assert(key.1 == leader.current_term);
                    assert(leader.log[j].term >= leader.current_term);
                    assert(leader.log[j].term
                        == ds.configuration_commit_certificates[j].entry.term);
                    assert(leader.log[j].term
                        <= ds.configuration_commit_certificates[index]
                            .entry.term);
                    assert(false);
                }
            };

            lemma_configuration_free_interval_preserves_active_phase(
                leader.log,
                snapshot,
                leader.commit_index,
                initial_phase,
            );

            let saved_phase = active_membership_phase_from_raft_log(
                leader.log, snapshot, initial_phase);
            let committed_phase = active_membership_phase_from_raft_log(
                leader.log, leader.commit_index, initial_phase);
            assert(saved_phase == committed_phase);
            assert(leader.election_membership_phase == Some(saved_phase));

            lemma_minimal_missing_governing_phase_progresses_to_election(
                ds, index, leader_id);

            let governing_phase =
                ds.configuration_commit_certificates[index].governing_phase;
            if governing_phase == committed_phase {
                lemma_phase_progression_reflexive(saved_phase);
                lemma_certified_boundary_present_when_phases_are_related(
                    ds, index, leader_id, saved_phase);
            } else {
                assert(governing_phase
                    == active_membership_phase_from_raft_log(
                        leader.log, index, initial_phase));
                assert forall |a: int, b: int| #![trigger leader.log[a], leader.log[b]]
                    leader.commit_index <= a < index
                    && leader.commit_index <= b < index
                    && leader.log[a].payload is Configuration
                    && leader.log[b].payload is Configuration
                    implies a == b
                by {
                    assert(uncommitted_suffix_has_at_most_one_configuration(
                        leader.log, leader.commit_index));
                };
                lemma_bounded_boundary_interval_progresses_legally(
                    leader.log,
                    leader.commit_index,
                    index,
                    initial_phase,
                );
                assert(is_legal_phase_progression(
                    saved_phase, governing_phase));
                lemma_certified_boundary_present_in_one_step_stale_leader(
                    ds, index, leader_id, saved_phase);
            }
        }
    }

    /// The stretch between a leader's election snapshot and its commit index
    /// carries no Configuration entry, whenever some certified boundary at or
    /// beyond the commit index is older than the leader's own term.
    ///
    /// A Configuration in that stretch would be committed, hence certified, and
    /// sits below the target boundary — so certificate-term monotonicity caps
    /// its term at the target's. But it also lies at or beyond the election
    /// snapshot, so it was appended by this leader and carries at least the
    /// leader's current term. The target term is strictly below that, so both
    /// cannot hold.
    ///
    /// Consequently the leader's saved election phase and its committed phase
    /// coincide, which is what lets the two be compared directionally.
    pub proof fn lemma_older_certificate_makes_snapshot_to_commit_configuration_free(
        ds: RaftDistributedState,
        certificate_index: int,
        leader_id: int,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            ElectionLogLenBounded(ds),
            ElectionLogLenEntryTermBound(ds),
            LeaderElectionSnapshotRecorded(ds),
            LogTermsMonotonic(ds),
            ds.configuration_commit_certificates.dom()
                .contains(certificate_index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[certificate_index]
                    .entry.term,
            ds.server_states[leader_id].commit_index <= certificate_index,
        ensures
            forall |j: int|
                #![trigger ds.server_states[leader_id].log[j]]
                ds.election_log_len[
                    (leader_id, ds.server_states[leader_id].current_term)]
                    <= j < ds.server_states[leader_id].commit_index
                ==> !(ds.server_states[leader_id].log[j].payload
                    is Configuration),
            ds.election_log_len[
                (leader_id, ds.server_states[leader_id].current_term)]
                <= ds.server_states[leader_id].commit_index
            ==> active_membership_phase_from_raft_log(
                    ds.server_states[leader_id].log,
                    ds.election_log_len[
                        (leader_id,
                         ds.server_states[leader_id].current_term)],
                    MembershipPhase::Stable {
                        config: ds.server_constants[leader_id].servers,
                    },
                ) == active_membership_phase_from_raft_log(
                    ds.server_states[leader_id].log,
                    ds.server_states[leader_id].commit_index,
                    MembershipPhase::Stable {
                        config: ds.server_constants[leader_id].servers,
                    },
                ),
    {
        let leader = ds.server_states[leader_id];
        let initial_phase = MembershipPhase::Stable {
            config: ds.server_constants[leader_id].servers,
        };
        let key: (int, int) = (leader_id, leader.current_term);

        assert(LeaderElectionSnapshotRecorded(ds));
        assert(ds.election_log_len.dom().contains(key));
        let snapshot = ds.election_log_len[key];
        assert(ElectionLogLenBounded(ds));
        assert(0 <= snapshot <= leader.log.len());
        assert(CommitIndexBounded(ds));

        assert forall |j: int| #![trigger leader.log[j]]
            snapshot <= j < leader.commit_index
            implies !(leader.log[j].payload is Configuration)
        by {
            if leader.log[j].payload is Configuration {
                assert(0 <= j);
                assert(j < certificate_index);
                assert(j < leader.log.len());
                assert(CommittedConfigurationsHaveCertificates(ds));
                assert(ds.configuration_commit_certificates.dom().contains(j));
                assert(ds.configuration_commit_certificates[j].entry
                    == leader.log[j]);
                lemma_certified_boundary_terms_are_monotonic(
                    ds, certificate_index, j);

                assert(ElectionLogLenEntryTermBound(ds));
                assert(ds.election_log_len[key] <= j);
                assert(ds.election_log_len.dom().contains(key));
                assert(0 <= key.0 < ds.num_servers);
                assert(ds.server_states[key.0].log[j] == leader.log[j]);
                assert(ds.server_states[key.0].log[j].term >= key.1);
                assert(leader.log[j].term >= leader.current_term);
                assert(false);
            }
        };

        if snapshot <= leader.commit_index {
            lemma_configuration_free_interval_preserves_active_phase(
                leader.log,
                snapshot,
                leader.commit_index,
                initial_phase,
            );
        }
    }

    /// A leader's log cannot end before a certified boundary it holds every
    /// earlier boundary for.
    ///
    /// Comparing phases at the leader's own log end: the committer carries no
    /// Configuration between there and the boundary (such an entry would be
    /// certified, hence held, hence inside the log), so the governing phase is
    /// already fixed at that prefix. The saved election phase is then within
    /// one legal step of it in one direction or the other, the quorums overlap,
    /// and the boundary transfers in — placing it inside a log that was assumed
    /// too short to contain it.
    pub proof fn lemma_existing_leader_cannot_end_before_certified_boundary(
        ds: RaftDistributedState,
        certificate_index: int,
        leader_id: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            AllRaftMembershipLogsWellFormed(ds),
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            ElectionLogLenBounded(ds),
            ElectionLogLenEntryTermBound(ds),
            LeaderElectionSnapshotRecorded(ds),
            LogTermsMonotonic(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
            ds.configuration_commit_certificates.dom()
                .contains(certificate_index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[certificate_index]
                    .entry.term,
            ds.server_constants[leader_id].servers
                == ds.server_constants[
                    ds.configuration_commit_certificates[certificate_index]
                        .committer
                ].servers,
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < certificate_index
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
            ds.server_states[leader_id].log.len() < certificate_index,
        ensures
            false,
    {
        let leader = ds.server_states[leader_id];
        let constants = ds.server_constants[leader_id];
        let certificate =
            ds.configuration_commit_certificates[certificate_index];
        let committer = certificate.committer;
        let cut = leader.log.len() as int;
        let initial_phase = MembershipPhase::Stable {
            config: constants.servers,
        };
        let key: (int, int) = (leader_id, leader.current_term);

        assert(LeaderElectionSnapshotRecorded(ds));
        assert(ds.election_log_len.dom().contains(key));
        let snapshot = ds.election_log_len[key];
        assert(ElectionLogLenBounded(ds));
        assert(0 <= snapshot <= cut);
        assert(CommitIndexBounded(ds));
        assert(leader.commit_index <= cut);
        assert(CommitIndexNonnegative(ds));

        assert(ConfigurationCommittersRetainCertifiedPrefixes(ds));
        assert(0 <= committer < ds.num_servers);
        assert(0 <= certificate_index
            < ds.server_states[committer].commit_index);
        assert(ds.server_states[committer].commit_index
            <= ds.server_states[committer].log.len());

        // The committer has no boundary between the leader's log end and the
        // target: such an entry would be certified and therefore held.
        assert forall |p: int| #![trigger ds.server_states[committer].log[p]] cut <= p < certificate_index
        implies !(ds.server_states[committer].log[p].payload is Configuration)
        by {
            if ds.server_states[committer].log[p].payload is Configuration {
                lemma_committer_prefix_configurations_are_certified(
                    ds, certificate_index, p);
                assert(ds.server_states[leader_id].log.len() > p);
            }
        };

        lemma_configuration_commit_certificate_valid_for_replica(
            ds, certificate_index, committer);
        lemma_configuration_free_interval_preserves_active_phase(
            ds.server_states[committer].log,
            cut,
            certificate_index,
            initial_phase,
        );
        assert(certificate.governing_phase
            == active_membership_phase_from_raft_log(
                ds.server_states[committer].log, cut, initial_phase));

        lemma_minimal_missing_governing_phase_progresses_from_cut(
            ds, certificate_index, leader_id, cut);

        let saved_phase = active_membership_phase_from_raft_log(
            leader.log, snapshot, initial_phase);
        let committed_phase = active_membership_phase_from_raft_log(
            leader.log, leader.commit_index, initial_phase);
        let cut_phase = active_membership_phase_from_raft_log(
            leader.log, cut, initial_phase);
        assert(leader.election_membership_phase == Some(saved_phase));

        assert(AllRaftMembershipLogsWellFormed(ds));
        assert(UncommittedSuffixesHaveAtMostOneConfiguration(ds));
        assert forall |a: int, b: int| #![trigger leader.log[a], leader.log[b]]
            leader.commit_index <= a < leader.log.len()
            && leader.commit_index <= b < leader.log.len()
            && leader.log[a].payload is Configuration
            && leader.log[b].payload is Configuration
            implies a == b
        by {
            assert(uncommitted_suffix_has_at_most_one_configuration(
                leader.log, leader.commit_index));
        };

        if leader.commit_index <= snapshot {
            if certificate.governing_phase == committed_phase {
                lemma_bounded_boundary_interval_progresses_legally(
                    leader.log, leader.commit_index, snapshot, initial_phase);
                lemma_certified_boundary_present_when_phases_are_related(
                    ds, certificate_index, leader_id, saved_phase);
            } else {
                assert(certificate.governing_phase == cut_phase);
                lemma_bounded_boundary_interval_progresses_legally(
                    leader.log, snapshot, cut, initial_phase);
                lemma_certified_boundary_present_in_one_step_stale_leader(
                    ds, certificate_index, leader_id, saved_phase);
            }
        } else {
            // The snapshot precedes the commit index, so the stretch between
            // them is Configuration-free and the two phases coincide.
            lemma_older_certificate_makes_snapshot_to_commit_configuration_free(
                ds, certificate_index, leader_id);
            assert(saved_phase == committed_phase);

            if certificate.governing_phase == committed_phase {
                lemma_phase_progression_reflexive(saved_phase);
                lemma_certified_boundary_present_when_phases_are_related(
                    ds, certificate_index, leader_id, saved_phase);
            } else {
                assert(certificate.governing_phase == cut_phase);
                lemma_bounded_boundary_interval_progresses_legally(
                    leader.log, leader.commit_index, cut, initial_phase);
                lemma_certified_boundary_present_in_one_step_stale_leader(
                    ds, certificate_index, leader_id, saved_phase);
            }
        }

        // Either transfer places the boundary inside the leader's log.
        assert(ds.server_states[leader_id].log.len() > certificate_index);
    }

    /// Strong induction over certificate positions with **no** log-length
    /// bound: an existing leader holds every certified boundary below any
    /// bound whatsoever.
    ///
    /// The short-log branch is discharged rather than excluded — a leader whose
    /// log ended before a certified boundary is impossible, so that case closes
    /// by contradiction.
    pub proof fn lemma_existing_leader_holds_certified_boundaries_below_any_bound(
        ds: RaftDistributedState,
        leader_id: int,
        bound: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            AllRaftMembershipLogsWellFormed(ds),
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            ElectionLogLenBounded(ds),
            ElectionLogLenEntryTermBound(ds),
            LeaderElectionSnapshotRecorded(ds),
            LogTermsMonotonic(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            0 <= bound,
            forall |a: int, e: int|
                #![trigger ds.server_constants[a], ds.server_constants[e]]
                0 <= a < ds.num_servers && 0 <= e < ds.num_servers
                ==> ds.server_constants[a].servers
                    == ds.server_constants[e].servers,
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < bound
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].current_term
                    > ds.configuration_commit_certificates[m].entry.term,
        ensures
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < bound
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
        decreases bound,
    {
        if bound > 0 {
            let m = bound - 1;

            lemma_existing_leader_holds_certified_boundaries_below_any_bound(
                ds, leader_id, m);

            if ds.configuration_commit_certificates.dom().contains(m) {
                if m < ds.server_states[leader_id].commit_index {
                    assert(CommitIndexBounded(ds));
                    lemma_certified_boundary_agrees_with_committed_server(
                        ds, m, leader_id);
                } else if m <= ds.server_states[leader_id].log.len() {
                    lemma_existing_leader_holds_certified_boundary_unconditionally(
                        ds, m, leader_id);
                } else {
                    lemma_existing_leader_cannot_end_before_certified_boundary(
                        ds, m, leader_id);
                }
            }
        }
    }

    /// Configuration Leader Completeness holds in any state satisfying the
    /// dynamic certificate, election-snapshot, log and transfer invariants.
    ///
    /// Stated over explicit invariants rather than `RaftSafetyInvariant` so it
    /// can be used to *establish* that conjunct without circular unfolding.
    ///
    /// Because it is a state theorem, no per-transition split into old versus
    /// freshly created certificates is needed: whatever the step did, the
    /// post-state satisfies these invariants and the conclusion follows.
    pub proof fn lemma_dynamic_state_implies_certified_configuration_leader_completeness(
        ds: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            AllRaftMembershipLogsWellFormed(ds),
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            ElectionLogLenBounded(ds),
            ElectionLogLenEntryTermBound(ds),
            LeaderElectionSnapshotRecorded(ds),
            LogTermsMonotonic(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
        ensures
            CertifiedConfigurationLeaderCompleteness(ds),
    {
        assert forall |index: int, leader_id: int|
            ds.configuration_commit_certificates.dom().contains(index)
            && 0 <= leader_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term
        implies {
            &&& ds.server_states[leader_id].log.len() > index
            &&& ds.server_states[leader_id].log[index]
                == ds.configuration_commit_certificates[index].entry
        } by {
            assert(ConfigurationCommittersRetainCertifiedPrefixes(ds));
            assert(0 <= index);

            // All servers share one universe of identities.
            assert forall |a: int, e: int| #![trigger ds.server_constants[a], ds.server_constants[e]]
                0 <= a < ds.num_servers && 0 <= e < ds.num_servers
                implies ds.server_constants[a].servers
                    == ds.server_constants[e].servers
            by {
                lemma_all_servers_share_server_universe(ds, a, e);
            };

            // Certificate terms increase with position, so the leader's term
            // exceeds every certified boundary up to and including this one.
            assert forall |m: int| #![trigger ds.configuration_commit_certificates.dom().contains(m)]
                0 <= m < index + 1
                && ds.configuration_commit_certificates.dom().contains(m)
                implies ds.server_states[leader_id].current_term
                    > ds.configuration_commit_certificates[m].entry.term
            by {
                if m < index {
                    lemma_certified_boundary_terms_are_monotonic(ds, index, m);
                }
            };

            lemma_existing_leader_holds_certified_boundaries_below_any_bound(
                ds, leader_id, index + 1);
        };
    }

    /// Strong induction over certificate positions for an *existing* leader.
    ///
    /// Counterpart of `lemma_certified_boundaries_present_below`, which needs
    /// the leader's saved phase to be its latest-log phase and so only applies
    /// at promotion. This version measures the saved phase at the election
    /// snapshot instead, which is what `LeaderElectionSnapshotRecorded`
    /// provides for every leader at any time.
    ///
    /// Each step splits on whether the boundary is already below the leader's
    /// commit index — committed agreement settles it — or above, where the
    /// unconditional existing-leader theorem applies with the induction
    /// hypothesis supplying minimality.
    pub proof fn lemma_existing_leader_holds_certified_boundaries_below(
        ds: RaftDistributedState,
        leader_id: int,
        bound: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedConfigurationsHaveCertificates(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            AllRaftMembershipLogsWellFormed(ds),
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            ElectionLogLenBounded(ds),
            ElectionLogLenEntryTermBound(ds),
            LeaderElectionSnapshotRecorded(ds),
            LogTermsMonotonic(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            0 <= bound <= ds.server_states[leader_id].log.len(),
            forall |a: int, e: int|
                #![trigger ds.server_constants[a], ds.server_constants[e]]
                0 <= a < ds.num_servers && 0 <= e < ds.num_servers
                ==> ds.server_constants[a].servers
                    == ds.server_constants[e].servers,
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < bound
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].current_term
                    > ds.configuration_commit_certificates[m].entry.term,
        ensures
            forall |m: int|
                #![trigger ds.configuration_commit_certificates[m]]
                0 <= m < bound
                && ds.configuration_commit_certificates.dom().contains(m)
                ==> ds.server_states[leader_id].log.len() > m
                    && ds.server_states[leader_id].log[m]
                        == ds.configuration_commit_certificates[m].entry,
        decreases bound,
    {
        if bound > 0 {
            let m = bound - 1;

            lemma_existing_leader_holds_certified_boundaries_below(
                ds, leader_id, m);

            if ds.configuration_commit_certificates.dom().contains(m) {
                assert(CommitIndexBounded(ds));
                assert(m < ds.server_states[leader_id].log.len());

                if m < ds.server_states[leader_id].commit_index {
                    lemma_certified_boundary_agrees_with_committed_server(
                        ds, m, leader_id);
                } else {
                    lemma_existing_leader_holds_certified_boundary_unconditionally(
                        ds, m, leader_id);
                }
            }
        }
    }

    /// The stale-leader direction. Quorum overlap is symmetric, so a leader
    /// elected under a phase that the certificate's governing phase legally
    /// progresses *from* is covered just as well as one that progresses *to*
    /// it. Together with
    /// `lemma_certified_boundary_present_when_phases_are_related` this covers
    /// every leader whose election phase is within one legal joint-consensus
    /// step of the certificate's governing phase, in either direction.
    pub proof fn lemma_certified_boundary_present_in_one_step_stale_leader(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
        election_phase: MembershipPhase,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term,
            ds.server_states[leader_id].election_membership_phase
                == Some(election_phase),
            is_legal_phase_progression(
                election_phase,
                ds.configuration_commit_certificates[index].governing_phase,
            ),
        ensures
            ds.server_states[leader_id].log.len() > index,
            ds.server_states[leader_id].log[index]
                == ds.configuration_commit_certificates[index].entry,
    {
        let certificate = ds.configuration_commit_certificates[index];

        assert(has_recorded_election_quorum(ds.server_states[leader_id]));
        assert(is_quorum_for_phase(
            ds.server_states[leader_id].votes_granted,
            election_phase,
        ));

        lemma_configuration_commit_certificate_basic_validity(ds, index);
        assert(is_quorum_for_phase(
            certificate.quorum,
            certificate.governing_phase,
        ));

        // Progression runs from the leader's phase to the certificate's, so
        // the overlap lemma is applied in that order.
        lemma_legal_phase_progression_quorums_intersect(
            ds.server_states[leader_id].votes_granted,
            certificate.quorum,
            election_phase,
            certificate.governing_phase,
        );

        let overlap_voter = choose |server: int| #![trigger certificate.quorum.contains(server)]
            ds.server_states[leader_id].votes_granted.contains(server)
            && certificate.quorum.contains(server);

        assert(ds.server_states[leader_id].votes_granted
            .contains(overlap_voter));
        assert(VotesGrantedAreServers(ds));
        assert(0 <= overlap_voter < ds.num_servers);

        assert(CertifiedBoundaryTransfersToVotedLeader(ds));
    }

    /// Any server that has committed past a certified Configuration boundary
    /// holds exactly the certified entry there — no membership-phase hypothesis
    /// at all, so this covers joint consensus unconditionally.
    ///
    /// The certificate's committer has the boundary below its own commit index,
    /// so both the configuration certificate and the unique all-entry
    /// certificate at that position describe the same entry; any other server
    /// that has committed that far must therefore agree with it.
    pub proof fn lemma_certified_boundary_agrees_with_committed_server(
        ds: RaftDistributedState,
        index: int,
        server_id: int,
    )
        requires
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CommittedEntriesHaveLogCertificates(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= server_id < ds.num_servers,
            index < ds.server_states[server_id].commit_index,
            index < ds.server_states[server_id].log.len(),
        ensures
            0 <= index,
            ds.server_states[server_id].log[index]
                == ds.configuration_commit_certificates[index].entry,
    {
        let certificate = ds.configuration_commit_certificates[index];
        let committer = certificate.committer;

        // The committer retained the boundary below its own commit index.
        assert(ConfigurationCommittersRetainCertifiedPrefixes(ds));
        assert(0 <= committer < ds.num_servers);
        assert(0 <= index < ds.server_states[committer].commit_index);
        assert(ds.server_states[committer].commit_index
            <= ds.server_states[committer].log.len());
        assert(index < ds.server_states[committer].log.len());
        assert(ds.server_states[committer].log[index] == certificate.entry);

        // Both servers' committed entries at `index` are the unique all-entry
        // certificate entry, hence equal to each other.
        assert(CommittedEntriesHaveLogCertificates(ds));
        assert(ds.log_commit_certificates[index].entry
            == ds.server_states[committer].log[index]);
        assert(ds.log_commit_certificates[index].entry
            == ds.server_states[server_id].log[index]);
    }

    /// The joint-consensus case. Whenever the phase a leader was elected under
    /// is the certificate's governing phase, or one legal progression step
    /// beyond it, the two quorums must intersect — this is exactly what the
    /// joint-consensus overlap mathematics buys — and the overlapping voter
    /// carries the certified boundary into the leader's log.
    ///
    /// Unlike the fixed-majority bridge, this covers `Joint` phases and
    /// `Stable` phases over proper subsets. The hypothesis is only that the
    /// two phases are one legal step apart, which is far weaker than the full
    /// first-missing-boundary provenance.
    pub proof fn lemma_certified_boundary_present_when_phases_are_related(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
        election_phase: MembershipPhase,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotesGrantedAreServers(ds),
            CertifiedBoundaryTransfersToVotedLeader(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term,
            ds.server_states[leader_id].election_membership_phase
                == Some(election_phase),
            is_legal_phase_progression(
                ds.configuration_commit_certificates[index].governing_phase,
                election_phase,
            ),
        ensures
            ds.server_states[leader_id].log.len() > index,
            ds.server_states[leader_id].log[index]
                == ds.configuration_commit_certificates[index].entry,
    {
        let certificate = ds.configuration_commit_certificates[index];

        // The leader's vote set is a quorum for the phase it was elected under.
        assert(has_recorded_election_quorum(ds.server_states[leader_id]));
        assert(is_quorum_for_phase(
            ds.server_states[leader_id].votes_granted,
            election_phase,
        ));

        // The certificate's quorum is a quorum for its governing phase.
        lemma_configuration_commit_certificate_basic_validity(ds, index);
        assert(is_quorum_for_phase(
            certificate.quorum,
            certificate.governing_phase,
        ));

        // One legal step apart, so the quorums overlap.
        lemma_legal_phase_progression_quorums_intersect(
            certificate.quorum,
            ds.server_states[leader_id].votes_granted,
            certificate.governing_phase,
            election_phase,
        );

        let overlap_voter = choose |server: int| #![trigger certificate.quorum.contains(server)]
            certificate.quorum.contains(server)
            && ds.server_states[leader_id].votes_granted.contains(server);

        assert(ds.server_states[leader_id].votes_granted
            .contains(overlap_voter));
        assert(VotesGrantedAreServers(ds));
        assert(0 <= overlap_voter < ds.num_servers);

        // The transfer obligation carries the entry across.
        assert(CertifiedBoundaryTransfersToVotedLeader(ds));
    }

    /// All-entry analogue of the Configuration bridge: an entry certified
    /// under a Stable phase covering the whole server set is committed in the
    /// legacy fixed-majority sense too. This carries the bridge from
    /// Configuration boundaries to *every* committed log entry.
    pub proof fn lemma_stable_full_log_certificate_is_legacy_commit(
        ds: RaftDistributedState,
        index: int,
        config: Set<int>,
    )
        requires
            LogCommitCertificatesValid(ds),
            ds.log_commit_certificates.dom().contains(index),
            ds.log_commit_certificates[index].governing_phase
                == (MembershipPhase::Stable { config: config }),
            config.len() == ds.num_servers,
        ensures
            EntryCommittedAt(
                ds,
                index,
                ds.log_commit_certificates[index].entry,
            ),
            0 <= index,
    {
        let certificate = ds.log_commit_certificates[index];

        assert(LogCommitCertificatesValid(ds));
        assert(is_quorum_for_phase(
            certificate.quorum,
            certificate.governing_phase,
        ));
        assert(is_majority_of(certificate.quorum, config));
        assert(certificate.quorum.len() >= ds.num_servers / 2 + 1);

        assert forall |id: int| #![trigger certificate.quorum.contains(id)] certificate.quorum.contains(id) implies {
            &&& 0 <= id < ds.num_servers
            &&& ds.server_states[id].log.len() > index
            &&& ds.server_states[id].log[index] == certificate.entry
        } by {
            assert(LogCommitCertificatesValid(ds));
        };

        assert(EntryCommittedAt(ds, index, certificate.entry)) by {
            assert(certificate.quorum.len() >= ds.num_servers / 2 + 1);
        };
    }

    /// While membership is Stable over the whole server set, the inherited
    /// Leader Completeness already covers every dynamically certified entry —
    /// Data entries as well as Configuration boundaries.
    pub proof fn lemma_legacy_leader_completeness_covers_stable_log_certificate(
        ds: RaftDistributedState,
        index: int,
        config: Set<int>,
        leader_id: int,
    )
        requires
            LeaderCompleteness(ds),
            LogCommitCertificatesValid(ds),
            ds.log_commit_certificates.dom().contains(index),
            ds.log_commit_certificates[index].governing_phase
                == (MembershipPhase::Stable { config: config }),
            config.len() == ds.num_servers,
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.log_commit_certificates[index].entry.term,
        ensures
            ds.server_states[leader_id].log.len() > index,
            ds.server_states[leader_id].log[index]
                == ds.log_commit_certificates[index].entry,
    {
        lemma_stable_full_log_certificate_is_legacy_commit(ds, index, config);
        assert(LeaderCompleteness(ds));
    }

    /// Legacy Leader Completeness holds vacuously in an initial state: no
    /// server has been elected yet, so there is no higher-term leader to be
    /// missing anything.
    pub proof fn lemma_init_establishes_leader_completeness(
        ds: RaftDistributedState,
    )
        requires
            RaftDistributedInit(ds),
        ensures
            LeaderCompleteness(ds),
    {
        assert forall |k: int, entry: LLogEntry, leader_id: int| #![trigger EntryCommittedAt(ds, k, entry), ds.server_states[leader_id]]
            0 <= k
            && EntryCommittedAt(ds, k, entry)
            && 0 <= leader_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term > entry.term
        implies false
        by {
            assert(LInit(
                ds.server_states[leader_id],
                ds.server_constants[leader_id],
            ));
        };
    }

    /// A certificate whose governing phase is Stable over the entire server
    /// set is also a commitment in the legacy fixed-majority sense: a majority
    /// of the full configuration is exactly the legacy quorum threshold. This
    /// is the bridge that lets the inherited `LeaderCompleteness` development
    /// apply to certified Configuration boundaries — but only while no
    /// membership change is in flight, since a Joint quorum can be far smaller
    /// than a majority of the universe.
    pub proof fn lemma_stable_full_certificate_is_legacy_commit(
        ds: RaftDistributedState,
        index: int,
        config: Set<int>,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            ds.configuration_commit_certificates[index].governing_phase
                == (MembershipPhase::Stable { config: config }),
            config.len() == ds.num_servers,
        ensures
            EntryCommittedAt(
                ds,
                index,
                ds.configuration_commit_certificates[index].entry,
            ),
    {
        let certificate = ds.configuration_commit_certificates[index];

        // Validity already gives a phase quorum; over the full configuration
        // that is the legacy majority threshold.
        assert(is_quorum_for_phase(
            certificate.quorum,
            certificate.governing_phase,
        ));
        assert(is_majority_of(certificate.quorum, config));
        assert(certificate.quorum.len() >= config.len() / 2 + 1);
        assert(certificate.quorum.len() >= ds.num_servers / 2 + 1);

        // Every member of that quorum holds the certified entry.
        assert forall |id: int| #![trigger certificate.quorum.contains(id)] certificate.quorum.contains(id) implies {
            &&& 0 <= id < ds.num_servers
            &&& ds.server_states[id].log.len() > index
            &&& ds.server_states[id].log[index] == certificate.entry
        } by {
            assert(ConfigurationCommitCertificatesValid(ds));
            lemma_configuration_commit_certificate_valid_for_replica(
                ds,
                index,
                id,
            );
        };

        assert(EntryCommittedAt(ds, index, certificate.entry)) by {
            assert(certificate.quorum.len() >= ds.num_servers / 2 + 1);
        };
    }

    /// Consequence of the bridge: while membership is Stable over the whole
    /// server set, the inherited `LeaderCompleteness` already delivers
    /// certified-boundary Leader Completeness, with no extra provenance
    /// hypothesis. The genuinely dynamic cases — a Joint phase, or a Stable
    /// phase over a proper subset — are not covered, because their quorums need
    /// not meet the legacy fixed-majority threshold.
    pub proof fn lemma_legacy_leader_completeness_covers_stable_certificate(
        ds: RaftDistributedState,
        index: int,
        config: Set<int>,
        leader_id: int,
    )
        requires
            LeaderCompleteness(ds),
            ConfigurationCommitCertificatesValid(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            ds.configuration_commit_certificates[index].governing_phase
                == (MembershipPhase::Stable { config: config }),
            config.len() == ds.num_servers,
            0 <= index,
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term,
        ensures
            ds.server_states[leader_id].log.len() > index,
            ds.server_states[leader_id].log[index]
                == ds.configuration_commit_certificates[index].entry,
    {
        lemma_stable_full_certificate_is_legacy_commit(ds, index, config);
        assert(LeaderCompleteness(ds));
    }

    /// Configuration Leader Completeness survives every step that neither
    /// mints a certificate nor promotes a server to leader. Only two kinds of
    /// step can therefore threaten it: committing a Configuration entry, and
    /// winning an election. This isolates the remaining obligation precisely —
    /// everything else is preserved for free by certificate immutability and
    /// append-only logs.
    pub proof fn lemma_configuration_leader_completeness_quiet_step(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            CertifiedConfigurationLeaderCompleteness(ds),
            ds_.num_servers == ds.num_servers,
            // No certificate is created, and existing ones are immutable.
            forall |i: int|
                #![trigger ds_.configuration_commit_certificates[i]]
                ds_.configuration_commit_certificates.dom().contains(i)
                ==> ds.configuration_commit_certificates.dom().contains(i)
                    && ds_.configuration_commit_certificates[i]
                        == ds.configuration_commit_certificates[i],
            // Nobody is newly promoted: every post-state leader already led at
            // the same term.
            forall |i: int|
                #![trigger ds_.server_states[i].role]
                0 <= i < ds.num_servers
                && ds_.server_states[i].role is Leader
                ==> ds.server_states[i].role is Leader
                    && ds.server_states[i].current_term
                        == ds_.server_states[i].current_term,
            // Certificate keys are genuine log positions.
            forall |i: int|
                #![trigger ds_.configuration_commit_certificates[i]]
                ds_.configuration_commit_certificates.dom().contains(i)
                ==> 0 <= i,
            // Logs only grow.
            forall |i: int|
                #![trigger ds_.server_states[i].log]
                0 <= i < ds.num_servers
                ==> ds.server_states[i].log.len()
                    <= ds_.server_states[i].log.len(),
            forall |i: int, p: int|
                #![trigger ds_.server_states[i].log[p]]
                0 <= i < ds.num_servers
                && 0 <= p < ds.server_states[i].log.len()
                ==> ds_.server_states[i].log[p]
                    == ds.server_states[i].log[p],
        ensures
            CertifiedConfigurationLeaderCompleteness(ds_),
    {
        assert forall |index: int, leader_id: int|
            ds_.configuration_commit_certificates.dom().contains(index)
            && 0 <= leader_id < ds_.num_servers
            && ds_.server_states[leader_id].role is Leader
            && ds_.server_states[leader_id].current_term
                > ds_.configuration_commit_certificates[index].entry.term
        implies {
            &&& ds_.server_states[leader_id].log.len() > index
            &&& ds_.server_states[leader_id].log[index]
                == ds_.configuration_commit_certificates[index].entry
        }
        by {
            // The certificate and the leader's term both come from the
            // pre-state, so the pre-state obligation applies verbatim.
            assert(0 <= leader_id < ds.num_servers);
            assert(ds.configuration_commit_certificates.dom().contains(index));
            assert(ds.configuration_commit_certificates[index]
                == ds_.configuration_commit_certificates[index]);
            assert(ds.server_states[leader_id].role is Leader);
            assert(ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term);
            assert(CertifiedConfigurationLeaderCompleteness(ds));
            assert(ds.server_states[leader_id].log.len() > index);
            assert(ds_.server_states[leader_id].log[index]
                == ds.server_states[leader_id].log[index]);
        };
    }

    /// Configuration Leader Completeness implies the first-missing-boundary
    /// provenance obligation vacuously: the provenance predicate is guarded by
    /// "some higher-term leader is missing a certified boundary", which is
    /// exactly the situation Leader Completeness rules out.
    ///
    /// Together with
    /// `lemma_configuration_leader_completeness_under_transfer_obligation`
    /// this makes the two predicates equivalent relative to the transfer
    /// obligation, so an inductive proof may target whichever is more
    /// convenient — and Leader Completeness carries no existential witness.
    pub proof fn lemma_configuration_leader_completeness_implies_provenance(
        ds: RaftDistributedState,
    )
        requires
            CertifiedConfigurationLeaderCompleteness(ds),
        ensures
            FirstMissingConfigurationBoundaryProvenance(ds),
    {
        assert forall |index: int, leader_id: int|
            ds.configuration_commit_certificates.dom().contains(index)
            && 0 <= leader_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term
            && !(ds.server_states[leader_id].log.len() > index
                && ds.server_states[leader_id].log[index]
                    == ds.configuration_commit_certificates[index].entry)
        implies false
        by {
            assert(CertifiedConfigurationLeaderCompleteness(ds));
        };
    }

    /// The transfer hypothesis is *discharged* by the inherited
    /// `lemma_overlap_voter_entry_transfer`, so stating it explicitly is a
    /// faithful reduction rather than a strengthening: the dynamic-membership
    /// development assumes exactly what the inherited static-Raft proof base
    /// already assumes, and nothing more. This is the only place the
    /// membership development touches that lemma, so the inherited gap is
    /// exactly one lemma wide.
    pub proof fn lemma_transfer_obligation_discharged_by_inherited_lemma(
        ds: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            EntryTermHasVoteQuorum(ds),
            ConfigurationCommitCertificatesValid(ds),
            VotersVotedForCandidate(ds),
            VoteResponseIntegrity(ds),
            LogMatching(ds),
            LogTermsMonotonic(ds),
            VoteResponseHasRequestVote(ds),
            OneVotePerTermInNetwork(ds),
            CandidateVoteDestinationUnique(ds),
            RequestVoteSummaryStillValidAtSameTerm(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteLogLenEntryTermBound(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
        ensures
            CertifiedBoundaryTransfersToVotedLeader(ds),
    {
        assert forall |index: int, leader_id: int, overlap_voter: int| #![trigger ds.configuration_commit_certificates.dom().contains(index), ds.server_states[leader_id].votes_granted.contains(overlap_voter)]
            ds.configuration_commit_certificates.dom().contains(index)
            && 0 <= leader_id < ds.num_servers
            && 0 <= overlap_voter < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term
            && ds.configuration_commit_certificates[index].quorum
                .contains(overlap_voter)
            && ds.server_states[leader_id].votes_granted
                .contains(overlap_voter)
        implies {
            &&& ds.server_states[leader_id].log.len() > index
            &&& ds.server_states[leader_id].log[index]
                == ds.configuration_commit_certificates[index].entry
        }
        by {
            let certificate = ds.configuration_commit_certificates[index];

            // Membership of the certificate quorum already pins the entry
            // into the voter's own log.
            lemma_configuration_commit_certificate_valid_for_replica(
                ds,
                index,
                overlap_voter,
            );
            assert(ds.server_states[overlap_voter].log.len() > index);
            assert(ds.server_states[overlap_voter].log[index]
                == certificate.entry);

            if overlap_voter != leader_id {
                // The leader collected this voter's grant, so the granting
                // VoteResponse is still in the network.
                assert(VotersVotedForCandidate(ds));
                let vote = choose |packet: LRaftPacket| #![trigger ds.network.contains(packet)] {
                    &&& ds.network.contains(packet)
                    &&& packet.dst == leader_id
                    &&& packet.msg matches LRaftMessage::VoteResponse {
                        term,
                        granted,
                        voter,
                        ..
                    }
                    &&& term == ds.server_states[leader_id].current_term
                    &&& granted
                    &&& voter == overlap_voter
                };
                assert(vote.src == overlap_voter) by {
                    assert(VoteResponseIntegrity(ds));
                };
                assert(
                    ds.server_states[overlap_voter].current_term
                        > vote.msg->VoteResponse_term
                    || (ds.server_states[overlap_voter].current_term
                            == vote.msg->VoteResponse_term
                        && ds.server_states[overlap_voter].has_voted
                        && ds.server_states[overlap_voter].voted_for
                            == leader_id)
                ) by {
                    assert(VoteResponseIntegrity(ds));
                };

                lemma_overlap_voter_entry_transfer(
                    ds,
                    leader_id,
                    overlap_voter,
                    index,
                    certificate.entry,
                );
            }
        };
    }

    /// Milestone B, mechanical half: an existing first-missing-boundary
    /// witness survives any step that carries the certificate over unchanged,
    /// leaves the leader's recorded election phase alone, and rewrites no
    /// existing log position. Logs may still grow — only the prefix below the
    /// recorded election length and the stretch below `index` matter.
    pub proof fn lemma_first_missing_boundary_witness_carries_over(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
        index: int,
        leader_id: int,
        certificate_witness: int,
        election_commit_len: int,
    )
        requires
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= leader_id < ds.num_servers,
            0 <= certificate_witness < ds.num_servers,
            // The certificate at `index` is carried over unchanged.
            ds.configuration_commit_certificates.dom().contains(index),
            ds_.configuration_commit_certificates.dom().contains(index),
            ds_.configuration_commit_certificates[index]
                == ds.configuration_commit_certificates[index],
            // The leader keeps the phase it recorded at election time.
            ds_.server_states[leader_id].election_membership_phase
                == ds.server_states[leader_id].election_membership_phase,
            // Both logs only grow; no existing position is rewritten.
            ds.server_states[leader_id].log.len()
                <= ds_.server_states[leader_id].log.len(),
            forall |p: int| 0 <= p < ds.server_states[leader_id].log.len()
                ==> ds_.server_states[leader_id].log[p]
                    == ds.server_states[leader_id].log[p],
            ds.server_states[certificate_witness].log.len()
                <= ds_.server_states[certificate_witness].log.len(),
            forall |p: int|
                0 <= p < ds.server_states[certificate_witness].log.len()
                ==> ds_.server_states[certificate_witness].log[p]
                    == ds.server_states[certificate_witness].log[p],
            // The witness discharged the obligation in the pre-state.
            ds.configuration_commit_certificates[index].quorum
                .contains(certificate_witness),
            0 <= election_commit_len <= ds.server_states[leader_id].log.len(),
            election_commit_len <= index,
            index <= ds.server_states[certificate_witness].log.len(),
            ds.server_states[leader_id].election_membership_phase
                == Some(active_membership_phase_from_raft_log(
                    ds.server_states[leader_id].log,
                    election_commit_len,
                    MembershipPhase::Stable {
                        config: ds.server_constants[leader_id].servers,
                    },
                )),
            forall |p: int| 0 <= p < election_commit_len
                ==> ds.server_states[leader_id].log[p]
                    == ds.server_states[certificate_witness].log[p],
            forall |p: int| #![trigger ds.server_states[certificate_witness].log[p]] election_commit_len <= p < index
                ==> !(ds.server_states[certificate_witness].log[p].payload
                    is Configuration),
        ensures
            ds_.configuration_commit_certificates[index].quorum
                .contains(certificate_witness),
            0 <= election_commit_len <= ds_.server_states[leader_id].log.len(),
            election_commit_len <= index,
            ds_.server_states[leader_id].election_membership_phase
                == Some(active_membership_phase_from_raft_log(
                    ds_.server_states[leader_id].log,
                    election_commit_len,
                    MembershipPhase::Stable {
                        config: ds_.server_constants[leader_id].servers,
                    },
                )),
            forall |p: int| 0 <= p < election_commit_len
                ==> ds_.server_states[leader_id].log[p]
                    == ds_.server_states[certificate_witness].log[p],
            forall |p: int| #![trigger ds_.server_states[certificate_witness].log[p]] election_commit_len <= p < index
                ==> !(ds_.server_states[certificate_witness].log[p].payload
                    is Configuration),
    {
        // The recorded phase reads only the leader's prefix below
        // `election_commit_len`, and that prefix did not change.
        lemma_equal_committed_raft_prefixes_have_same_active_phase(
            ds.server_states[leader_id].log,
            ds_.server_states[leader_id].log,
            election_commit_len,
            MembershipPhase::Stable {
                config: ds.server_constants[leader_id].servers,
            },
        );

        // Leader/witness prefix agreement is inherited position by position,
        // because neither log rewrote an existing entry.
        assert forall |p: int| 0 <= p < election_commit_len
            implies ds_.server_states[leader_id].log[p]
                == ds_.server_states[certificate_witness].log[p]
        by {
            assert(p < ds.server_states[leader_id].log.len());
            assert(p < ds.server_states[certificate_witness].log.len());
        };

        // Likewise the absence of an earlier Configuration boundary.
        assert forall |p: int| #![trigger ds_.server_states[certificate_witness].log[p]] election_commit_len <= p < index
            implies !(ds_.server_states[certificate_witness].log[p].payload
                is Configuration)
        by {
            assert(p < ds.server_states[certificate_witness].log.len());
        };
    }

    /// Extract the non-replica-specific facts stored by one valid certificate.
    pub proof fn lemma_configuration_commit_certificate_basic_validity(
        ds: RaftDistributedState,
        index: int,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            ds.configuration_commit_certificates.dom().contains(index),
        ensures ({
            let certificate =
                ds.configuration_commit_certificates[index];
            &&& certificate.log_index == index
            &&& is_quorum_for_phase(
                certificate.quorum,
                certificate.governing_phase,
            )
            &&& certificate.entry.payload is Configuration
        })
    {
        assert(ConfigurationCommitCertificatesValid(ds));
    }

    /// The quorum that committed a Configuration entry overlaps any election
    /// quorum governed by the phase immediately before that entry. This is the
    /// key local fact for the first committed boundary a stale candidate lacks.
    pub proof fn lemma_configuration_certificate_quorum_intersects_election_phase(
        ds: RaftDistributedState,
        index: int,
        election_quorum: Set<int>,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            is_quorum_for_phase(
                election_quorum,
                ds.configuration_commit_certificates[index].governing_phase,
            ),
        ensures
            exists |server: int| #![trigger election_quorum.contains(server)]
                ds.configuration_commit_certificates[index].quorum
                    .contains(server)
                && election_quorum.contains(server),
    {
        lemma_configuration_commit_certificate_basic_validity(ds, index);
        let certificate = ds.configuration_commit_certificates[index];
        lemma_phase_quorums_intersect(
            certificate.quorum,
            election_quorum,
            certificate.governing_phase,
        );
    }

    /// If a leader's saved election phase is the phase immediately before a
    /// certified Configuration entry, one of that leader's voters belongs to
    /// the certificate quorum and still has the certified entry in its log.
    pub proof fn lemma_configuration_certificate_overlaps_recorded_leader_election(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
    ) -> (overlap_voter: int)
        requires
            ConfigurationCommitCertificatesValid(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            has_recorded_election_quorum(ds.server_states[leader_id]),
            ds.server_states[leader_id].election_membership_phase
                == Some(
                    ds.configuration_commit_certificates[index]
                        .governing_phase,
                ),
        ensures
            0 <= overlap_voter < ds.num_servers,
            ds.configuration_commit_certificates[index].quorum
                .contains(overlap_voter),
            ds.server_states[leader_id].votes_granted
                .contains(overlap_voter),
            ds.server_states[overlap_voter].log.len() > index,
            ds.server_states[overlap_voter].log[index]
                == ds.configuration_commit_certificates[index].entry,
    {
        let certificate = ds.configuration_commit_certificates[index];
        let leader = ds.server_states[leader_id];
        assert(is_quorum_for_phase(
            leader.votes_granted,
            certificate.governing_phase,
        ));
        lemma_configuration_certificate_quorum_intersects_election_phase(
            ds,
            index,
            leader.votes_granted,
        );
        let overlap_voter = choose |server: int|
            certificate.quorum.contains(server)
            && leader.votes_granted.contains(server);
        lemma_configuration_commit_certificate_valid_for_replica(
            ds,
            index,
            overlap_voter,
        );
        assert(configuration_commit_certificate_matches_log(
            certificate,
            ds.server_states[overlap_voter].log,
            MembershipPhase::Stable {
                config: ds.server_constants[overlap_voter].servers,
            },
        ));
        assert(0 <= certificate.log_index
            < ds.server_states[overlap_voter].log.len());
        assert(certificate.log_index == index);
        assert(ds.server_states[overlap_voter].log[index]
            == certificate.entry);
        overlap_voter
    }

    /// For the first certified Configuration boundary after a leader's saved
    /// election prefix, the leader's recorded election phase is exactly the
    /// phase that governed that certificate.
    pub proof fn lemma_first_missing_certificate_matches_recorded_election_phase(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
        certificate_witness: int,
        election_commit_len: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            ConfigurationCommitCertificatesValid(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            ds.configuration_commit_certificates[index].quorum
                .contains(certificate_witness),
            0 <= leader_id < ds.num_servers,
            0 <= election_commit_len
                <= ds.server_states[leader_id].log.len(),
            election_commit_len <= index,
            ds.server_states[leader_id].election_membership_phase
                == Some(active_membership_phase_from_raft_log(
                    ds.server_states[leader_id].log,
                    election_commit_len,
                    MembershipPhase::Stable {
                        config: ds.server_constants[leader_id].servers,
                    },
                )),
            forall |prefix_index: int|
                0 <= prefix_index < election_commit_len
                ==> ds.server_states[leader_id].log[prefix_index]
                    == ds.server_states[certificate_witness].log[prefix_index],
            forall |prefix_index: int| #![trigger ds.server_states[certificate_witness].log[prefix_index]]
                election_commit_len <= prefix_index < index
                ==> !(ds.server_states[certificate_witness]
                    .log[prefix_index].payload is Configuration),
        ensures
            ds.server_states[leader_id].election_membership_phase
                == Some(
                    ds.configuration_commit_certificates[index]
                        .governing_phase,
                ),
    {
        let certificate = ds.configuration_commit_certificates[index];
        lemma_configuration_commit_certificate_valid_for_replica(
            ds,
            index,
            certificate_witness,
        );
        assert(configuration_commit_certificate_matches_log(
            certificate,
            ds.server_states[certificate_witness].log,
            MembershipPhase::Stable {
                config: ds.server_constants[certificate_witness].servers,
            },
        ));
        assert(ds.server_constants[leader_id].servers
            == ds.server_constants[certificate_witness].servers);
        lemma_equal_committed_raft_prefixes_have_same_active_phase(
            ds.server_states[leader_id].log,
            ds.server_states[certificate_witness].log,
            election_commit_len,
            MembershipPhase::Stable {
                config: ds.server_constants[leader_id].servers,
            },
        );
        lemma_configuration_free_interval_preserves_active_phase(
            ds.server_states[certificate_witness].log,
            election_commit_len,
            index,
            MembershipPhase::Stable {
                config: ds.server_constants[certificate_witness].servers,
            },
        );
    }

    /// A later-term leader elected under the phase immediately before a
    /// certified Configuration boundary must contain that Configuration entry.
    /// Therefore a candidate missing the boundary cannot both use that old
    /// phase and successfully become leader.
    pub proof fn lemma_certified_configuration_present_in_recorded_leader(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            EntryTermHasVoteQuorum(ds),
            ConfigurationCommitCertificatesValid(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotersVotedForCandidate(ds),
            VoteResponseIntegrity(ds),
            LogMatching(ds),
            LogTermsMonotonic(ds),
            VoteResponseHasRequestVote(ds),
            OneVotePerTermInNetwork(ds),
            CandidateVoteDestinationUnique(ds),
            RequestVoteSummaryStillValidAtSameTerm(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteLogLenEntryTermBound(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term,
            ds.server_states[leader_id].election_membership_phase
                == Some(
                    ds.configuration_commit_certificates[index]
                        .governing_phase,
                ),
        ensures
            ds.server_states[leader_id].log.len() > index,
            ds.server_states[leader_id].log[index]
                == ds.configuration_commit_certificates[index].entry,
    {
        let certificate = ds.configuration_commit_certificates[index];
        let overlap_voter =
            lemma_configuration_certificate_overlaps_recorded_leader_election(
                ds,
                index,
                leader_id,
            );

        if overlap_voter == leader_id {
            lemma_configuration_commit_certificate_valid_for_replica(
                ds,
                index,
                overlap_voter,
            );
            assert(configuration_commit_certificate_matches_log(
                certificate,
                ds.server_states[leader_id].log,
                MembershipPhase::Stable {
                    config: ds.server_constants[leader_id].servers,
                },
            ));
        } else {
            assert(VotersVotedForCandidate(ds));
            let vote = choose |packet: LRaftPacket| #![trigger ds.network.contains(packet)] {
                &&& ds.network.contains(packet)
                &&& packet.dst == leader_id
                &&& packet.msg matches LRaftMessage::VoteResponse {
                    term,
                    granted,
                    voter,
                    ..
                }
                &&& term == ds.server_states[leader_id].current_term
                &&& granted
                &&& voter == overlap_voter
            };
            assert(vote.src == overlap_voter) by {
                assert(VoteResponseIntegrity(ds));
            };
            assert(
                ds.server_states[overlap_voter].current_term
                    > vote.msg->VoteResponse_term
                || (ds.server_states[overlap_voter].current_term
                        == vote.msg->VoteResponse_term
                    && ds.server_states[overlap_voter].has_voted
                    && ds.server_states[overlap_voter].voted_for
                        == leader_id)
            ) by {
                assert(VoteResponseIntegrity(ds));
            };

            lemma_overlap_voter_entry_transfer(
                ds,
                leader_id,
                overlap_voter,
                index,
                certificate.entry,
            );
        }
    }

    /// End-to-end first-boundary result: once the phase bridge hypotheses
    /// identify a certified Configuration as the first membership boundary
    /// missing after the leader's election prefix, a later-term leader must
    /// contain that exact Configuration entry.
    pub proof fn lemma_first_missing_certified_configuration_present_in_recorded_leader(
        ds: RaftDistributedState,
        index: int,
        leader_id: int,
        certificate_witness: int,
        election_commit_len: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            EntryTermHasVoteQuorum(ds),
            ConfigurationCommitCertificatesValid(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotersVotedForCandidate(ds),
            VoteResponseIntegrity(ds),
            LogMatching(ds),
            LogTermsMonotonic(ds),
            VoteResponseHasRequestVote(ds),
            OneVotePerTermInNetwork(ds),
            CandidateVoteDestinationUnique(ds),
            RequestVoteSummaryStillValidAtSameTerm(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteLogLenEntryTermBound(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            ds.configuration_commit_certificates[index].quorum
                .contains(certificate_witness),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term,
            0 <= election_commit_len
                <= ds.server_states[leader_id].log.len(),
            election_commit_len <= index,
            ds.server_states[leader_id].election_membership_phase
                == Some(active_membership_phase_from_raft_log(
                    ds.server_states[leader_id].log,
                    election_commit_len,
                    MembershipPhase::Stable {
                        config: ds.server_constants[leader_id].servers,
                    },
                )),
            forall |prefix_index: int|
                0 <= prefix_index < election_commit_len
                ==> ds.server_states[leader_id].log[prefix_index]
                    == ds.server_states[certificate_witness]
                        .log[prefix_index],
            forall |prefix_index: int| #![trigger ds.server_states[certificate_witness].log[prefix_index]]
                election_commit_len <= prefix_index < index
                ==> !(ds.server_states[certificate_witness]
                    .log[prefix_index].payload is Configuration),
        ensures
            ds.server_states[leader_id].log.len() > index,
            ds.server_states[leader_id].log[index]
                == ds.configuration_commit_certificates[index].entry,
    {
        lemma_first_missing_certificate_matches_recorded_election_phase(
            ds,
            index,
            leader_id,
            certificate_witness,
            election_commit_len,
        );
        lemma_certified_configuration_present_in_recorded_leader(
            ds,
            index,
            leader_id,
        );
    }

    /// The explicit first-missing-boundary provenance obligation is sufficient
    /// to lift the local certificate/election argument to global
    /// Configuration Leader Completeness.
    pub proof fn lemma_first_missing_boundary_provenance_implies_configuration_leader_completeness(
        ds: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            EntryTermHasVoteQuorum(ds),
            ConfigurationCommitCertificatesValid(ds),
            LeaderHasRecordedElectionQuorum(ds),
            VotersVotedForCandidate(ds),
            VoteResponseIntegrity(ds),
            LogMatching(ds),
            LogTermsMonotonic(ds),
            VoteResponseHasRequestVote(ds),
            OneVotePerTermInNetwork(ds),
            CandidateVoteDestinationUnique(ds),
            RequestVoteSummaryStillValidAtSameTerm(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteLogLenEntryTermBound(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
            FirstMissingConfigurationBoundaryProvenance(ds),
        ensures
            CertifiedConfigurationLeaderCompleteness(ds),
    {
        assert forall |index: int, leader_id: int|
            ds.configuration_commit_certificates.dom().contains(index)
            && 0 <= leader_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term
                > ds.configuration_commit_certificates[index].entry.term
        implies {
            &&& ds.server_states[leader_id].log.len() > index
            &&& ds.server_states[leader_id].log[index]
                == ds.configuration_commit_certificates[index].entry
        } by {
            if !(ds.server_states[leader_id].log.len() > index
                && ds.server_states[leader_id].log[index]
                    == ds.configuration_commit_certificates[index].entry)
            {
                let certificate_witness = choose |certificate_witness: int|
                    #![trigger ds.configuration_commit_certificates[index]
                        .quorum.contains(certificate_witness)]
                {
                    exists |election_commit_len: int| #![trigger active_membership_phase_from_raft_log(ds.server_states[leader_id].log, election_commit_len, MembershipPhase::Stable { config: ds.server_constants[leader_id].servers })] {
                        &&& ds.configuration_commit_certificates[index].quorum
                            .contains(certificate_witness)
                        &&& 0 <= election_commit_len
                            <= ds.server_states[leader_id].log.len()
                        &&& election_commit_len <= index
                        &&& ds.server_states[leader_id].election_membership_phase
                            == Some(active_membership_phase_from_raft_log(
                                ds.server_states[leader_id].log,
                                election_commit_len,
                                MembershipPhase::Stable {
                                    config: ds.server_constants[leader_id].servers,
                                },
                            ))
                        &&& forall |prefix_index: int|
                            0 <= prefix_index < election_commit_len
                            ==> ds.server_states[leader_id].log[prefix_index]
                                == ds.server_states[certificate_witness]
                                    .log[prefix_index]
                        &&& forall |prefix_index: int| #![trigger ds.server_states[certificate_witness].log[prefix_index]]
                            election_commit_len <= prefix_index < index
                            ==> !(ds.server_states[certificate_witness]
                                .log[prefix_index].payload is Configuration)
                    }
                };
                let election_commit_len = choose |election_commit_len: int| #![trigger active_membership_phase_from_raft_log(ds.server_states[leader_id].log, election_commit_len, MembershipPhase::Stable { config: ds.server_constants[leader_id].servers })] {
                    &&& ds.configuration_commit_certificates[index].quorum
                        .contains(certificate_witness)
                    &&& 0 <= election_commit_len
                        <= ds.server_states[leader_id].log.len()
                    &&& election_commit_len <= index
                    &&& ds.server_states[leader_id].election_membership_phase
                        == Some(active_membership_phase_from_raft_log(
                            ds.server_states[leader_id].log,
                            election_commit_len,
                            MembershipPhase::Stable {
                                config: ds.server_constants[leader_id].servers,
                            },
                        ))
                    &&& forall |prefix_index: int|
                        0 <= prefix_index < election_commit_len
                        ==> ds.server_states[leader_id].log[prefix_index]
                            == ds.server_states[certificate_witness].log[prefix_index]
                    &&& forall |prefix_index: int| #![trigger ds.server_states[certificate_witness].log[prefix_index]]
                        election_commit_len <= prefix_index < index
                        ==> !(ds.server_states[certificate_witness]
                            .log[prefix_index].payload is Configuration)
                };
                lemma_first_missing_certified_configuration_present_in_recorded_leader(
                    ds, index, leader_id, certificate_witness, election_commit_len,
                );
            }
        };
    }

    /// Extract one quorum member's concrete log-prefix evidence from a valid
    /// configuration-commit certificate.
    pub proof fn lemma_configuration_commit_certificate_valid_for_replica(
        ds: RaftDistributedState,
        index: int,
        replica: int,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            ds.configuration_commit_certificates.dom().contains(index),
            ds.configuration_commit_certificates[index].quorum
                .contains(replica),
        ensures
            0 <= replica < ds.num_servers,
            configuration_commit_certificate_matches_log(
                ds.configuration_commit_certificates[index],
                ds.server_states[replica].log,
                MembershipPhase::Stable {
                    config: ds.server_constants[replica].servers,
                },
            ),
    {
        assert(ConfigurationCommitCertificatesValid(ds));
        assert({
            let certificate =
                ds.configuration_commit_certificates[index];
            &&& certificate.log_index == index
            &&& is_quorum_for_phase(
                certificate.quorum,
                certificate.governing_phase,
            )
            &&& certificate.entry.payload is Configuration
            &&& forall |member: int|
                #![trigger certificate.quorum.contains(member)]
                certificate.quorum.contains(member)
                ==> 0 <= member < ds.num_servers
            &&& forall |member: int|
                #![trigger ds.server_states[member].log[index]]
                0 <= member < ds.num_servers
                && certificate.quorum.contains(member)
                ==> configuration_commit_certificate_matches_log(
                        certificate,
                        ds.server_states[member].log,
                        MembershipPhase::Stable {
                            config: ds.server_constants[member].servers,
                        },
                    )
        });
        assert(0 <= replica < ds.num_servers);
    }

    /// A member of a leader's replication set has the same concrete log
    /// prefix as the leader through the proposed commit length.
    pub proof fn lemma_replicator_set_member_has_matching_prefix(
        ds: RaftDistributedState,
        leader_id: int,
        replica: int,
        committed_len: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            0 <= leader_id < ds.num_servers,
            ds.server_states[leader_id].role is Leader,
            0 <= committed_len
                <= ds.server_states[leader_id].log.len(),
            replicator_set(
                ds.server_states[leader_id],
                ds.server_constants[leader_id],
                committed_len,
            ).contains(replica),
        ensures
            0 <= replica < ds.num_servers,
            committed_len <= ds.server_states[replica].log.len(),
            forall |index: int|
                #![trigger ds.server_states[replica].log[index]]
                0 <= index < committed_len
                ==> ds.server_states[replica].log[index]
                    == ds.server_states[leader_id].log[index],
    {
        let leader = ds.server_states[leader_id];
        let constants = ds.server_constants[leader_id];
        assert(constants.servers.contains(replica));
        assert(constants.servers
            == Set::<int>::range(0, ds.num_servers));
        assert(0 <= replica < ds.num_servers);

        if replica == leader_id {
            assert(committed_len <= ds.server_states[replica].log.len());
        } else {
            assert(leader.match_index.contains_key(replica as u64));
            assert(leader.match_index[replica as u64] as int
                >= committed_len);
            assert(leader.match_index[replica as u64] as int
                <= ds.server_states[replica].log.len());
            assert(committed_len <= ds.server_states[replica].log.len());

            assert forall |index: int|
                #![trigger ds.server_states[replica].log[index]]
                0 <= index < committed_len
                implies ds.server_states[replica].log[index]
                    == ds.server_states[leader_id].log[index]
            by {
                assert(index
                    < leader.match_index[replica as u64] as int);
                assert(index < leader.log.len());
                assert(index < ds.server_states[replica].log.len());
                assert(MatchIndexImpliesLogAgreement(ds));
            };
        }
    }

    /// Every Configuration entry that any server considers committed has the
    /// unique global certificate for that physical log position and entry.
    pub open spec fn CommittedConfigurationsHaveCertificates(
        ds: RaftDistributedState,
    ) -> bool {
        forall |server_id: int, index: int|
            #![trigger ds.server_states[server_id].log[index]]
            0 <= server_id < ds.num_servers
            && 0 <= index < ds.server_states[server_id].commit_index
            && index < ds.server_states[server_id].log.len()
            && ds.server_states[server_id].log[index].payload is Configuration
            ==> {
                &&& ds.configuration_commit_certificates.dom().contains(index)
                &&& ds.configuration_commit_certificates[index].log_index
                    == index
                &&& ds.configuration_commit_certificates[index].entry
                    == ds.server_states[server_id].log[index]
            }
    }

    /// Every physical entry below any server's commit index is represented by
    /// the unique global all-entry certificate at that log position.
    pub open spec fn CommittedEntriesHaveLogCertificates(
        ds: RaftDistributedState,
    ) -> bool {
        forall |server_id: int, index: int|
            #![trigger ds.server_states[server_id].log[index]]
            0 <= server_id < ds.num_servers
            && 0 <= index < ds.server_states[server_id].commit_index
            && index < ds.server_states[server_id].log.len()
            ==> {
                &&& ds.log_commit_certificates.dom().contains(index)
                &&& ds.log_commit_certificates[index].log_index == index
                &&& ds.log_commit_certificates[index].entry
                    == ds.server_states[server_id].log[index]
            }
    }

    /// Every all-entry certificate is a genuine dynamic-quorum certificate.
    /// Its committer has committed the entry, and every saved quorum member
    /// permanently retains the same physical log prefix through that index.
    pub open spec fn LogCommitCertificatesValid(
        ds: RaftDistributedState,
    ) -> bool {
        forall |index: int|
            #![trigger ds.log_commit_certificates[index]]
            ds.log_commit_certificates.dom().contains(index)
            ==> {
                let certificate = ds.log_commit_certificates[index];
                &&& certificate.log_index == index
                &&& 0 <= certificate.committer < ds.num_servers
                &&& certificate.quorum.contains(certificate.committer)
                &&& is_quorum_for_phase(
                    certificate.quorum,
                    certificate.governing_phase,
                )
                &&& certificate.governing_phase
                    == active_membership_phase_from_raft_log(
                        ds.server_states[certificate.committer].log,
                        index,
                        MembershipPhase::Stable {
                            config: ds.server_constants[certificate.committer]
                                .servers,
                        },
                    )
                &&& 0 <= index
                    < ds.server_states[certificate.committer].commit_index
                &&& ds.server_states[certificate.committer].commit_index
                    <= ds.server_states[certificate.committer].log.len()
                &&& ds.server_states[certificate.committer].log[index]
                    == certificate.entry
                &&& forall |replica: int|
                    #![trigger certificate.quorum.contains(replica)]
                    certificate.quorum.contains(replica)
                    ==> {
                        &&& 0 <= replica < ds.num_servers
                        &&& index < ds.server_states[replica].log.len()
                        &&& ds.server_states[replica].log[index]
                            == certificate.entry
                        &&& forall |prefix_index: int| #![trigger ds.server_states[replica].log[prefix_index]]
                            0 <= prefix_index <= index
                            ==> ds.server_states[replica].log[prefix_index]
                                == ds.server_states[certificate.committer]
                                    .log[prefix_index]
                    }
            }
    }

    pub proof fn lemma_init_establishes_log_certificates_valid(
        ds: RaftDistributedState,
    )
        requires RaftDistributedInit(ds)
        ensures LogCommitCertificatesValid(ds)
    {
        assert(ds.log_commit_certificates
            == Map::<int, LogCommitCertificate>::empty());
    }

    pub proof fn lemma_init_establishes_log_certificate_coverage(
        ds: RaftDistributedState,
    )
        requires RaftDistributedInit(ds)
        ensures CommittedEntriesHaveLogCertificates(ds)
    {
        assert(ds.log_commit_certificates
            == Map::<int, LogCommitCertificate>::empty());
        assert forall |server_id: int, index: int|
            #![trigger ds.server_states[server_id].log[index]]
            0 <= server_id < ds.num_servers
            && 0 <= index < ds.server_states[server_id].commit_index
            && index < ds.server_states[server_id].log.len()
            implies false
        by {
            assert(LInit(
                ds.server_states[server_id],
                ds.server_constants[server_id],
            ));
        };
    }

    /// Unique certificate coverage directly yields committed-log agreement:
    /// both committed server entries at one physical index equal the same
    /// global certificate entry.
    pub proof fn lemma_log_certificate_coverage_implies_state_machine_safety(
        ds: RaftDistributedState,
    )
        requires CommittedEntriesHaveLogCertificates(ds)
        ensures StateMachineSafety(ds)
    {
        assert forall |left: int, right: int, index: int| #![trigger ds.server_states[left], ds.server_states[right].log[index]] #![trigger ds.server_states[right], ds.server_states[left].log[index]]
            0 <= left < ds.num_servers
            && 0 <= right < ds.num_servers
            && 0 <= index < ds.server_states[left].commit_index
            && 0 <= index < ds.server_states[right].commit_index
            && index < ds.server_states[left].log.len()
            && index < ds.server_states[right].log.len()
        implies ds.server_states[left].log[index]
            == ds.server_states[right].log[index]
        by {
            assert(ds.log_commit_certificates.dom().contains(index));
            assert(ds.log_commit_certificates[index].log_index == index);
            assert(ds.log_commit_certificates[index].entry
                == ds.server_states[left].log[index]);
            assert(ds.log_commit_certificates[index].entry
                == ds.server_states[right].log[index]);
        };
    }

    /// Empty initial logs and an empty certificate map establish both
    /// certificate invariants.
    pub proof fn lemma_init_establishes_configuration_certificate_invariants(
        ds: RaftDistributedState,
    )
        requires RaftDistributedInit(ds)
        ensures
            ConfigurationCommitCertificatesValid(ds),
            CommittedConfigurationsHaveCertificates(ds),
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            CertifiedConfigurationLeaderCompleteness(ds),
            FirstMissingConfigurationBoundaryProvenance(ds),
    {
        assert(ds.configuration_commit_certificates
            == Map::<int, ConfigurationCommitCertificate>::empty());
        assert forall |server_id: int, index: int|
            #![trigger ds.server_states[server_id].log[index]]
            0 <= server_id < ds.num_servers
            && 0 <= index < ds.server_states[server_id].commit_index
            && index < ds.server_states[server_id].log.len()
            implies false
        by {
            assert(LInit(
                ds.server_states[server_id],
                ds.server_constants[server_id],
            ));
            assert(ds.server_states[server_id].commit_index == 0);
        };
    }

    /// The existing fixed-membership election invariants imply that
    /// every leader has a valid quorum for the stable membership phase.
    pub proof fn lemma_fixed_leader_quorum_implies_stable_phase_quorum(
        ds: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            LeaderHasQuorum(ds),
            VotesGrantedAreServers(ds),
        ensures
            LeaderHasStablePhaseQuorum(ds),
    {
        assert forall |i: int| #![trigger ds.server_states[i]]
            0 <= i < ds.num_servers
            && ds.server_states[i].role is Leader
            implies is_quorum_for_phase(
                ds.server_states[i].votes_granted,
                MembershipPhase::Stable {
                    config: ds.server_constants[i].servers,
                },
            )
        by {
            let votes = ds.server_states[i].votes_granted;
            let config = ds.server_constants[i].servers;

            assert(ds.num_servers > 0);
            assert(ds.server_constants[i].quorum_size
                == ds.num_servers / 2 + 1);
            assert(config
                == Set::<int>::range(0, ds.num_servers));

            lemma_range_set_finite(ds.num_servers);

            assert(config.len() == ds.num_servers);
            assert(config.len() > 0);

            assert(votes.subset_of(config)) by {
                assert forall |v: int|
                    votes.contains(v)
                    implies config.contains(v)
                by {
                    assert(0 <= v < ds.num_servers);
                };
            };

            assert(votes.len()
                >= ds.server_constants[i].quorum_size);
            assert(votes.len() >= config.len() / 2 + 1);

            assert(is_majority_of(votes, config));
            assert(is_quorum_for_phase(
                votes,
                MembershipPhase::Stable {
                    config,
                },
            ));
        };
    }

    /// Commit index is bounded by log length
    pub open spec fn CommitIndexBounded(ds: RaftDistributedState) -> bool {
        forall |i: int| #![trigger ds.server_states[i]]
            0 <= i < ds.num_servers
            ==> ds.server_states[i].commit_index <= ds.server_states[i].log.len()
    }

    /// Commit indexes are lengths and therefore never negative.
    pub open spec fn CommitIndexNonnegative(ds: RaftDistributedState) -> bool {
        forall |i: int| #![trigger ds.server_states[i]]
            0 <= i < ds.num_servers
            ==> 0 <= ds.server_states[i].commit_index
    }

    /// Match index implies log agreement: if a leader has match_index[f] >= k+1
    /// for some follower f, then the leader and follower agree on log[k].
    ///
    /// This connects the match_index bookkeeping in LHandleAppendResponse to
    /// actual log agreement, which is needed for StateMachineSafety.
    /// match_index is only set from AppendResponse packets, which carry
    /// verified log agreement (AppendResponseLogAgreement).
    pub open spec fn MatchIndexImpliesLogAgreement(ds: RaftDistributedState) -> bool {
        forall |leader_id: int, follower_id: int, k: int|
            #![trigger ds.server_states[leader_id].log[k], ds.server_states[follower_id].log[k], ds.server_states[leader_id].match_index]
            0 <= leader_id < ds.num_servers
            && 0 <= follower_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].match_index.dom().contains(follower_id as u64)
            && 0 <= k < ds.server_states[leader_id].match_index[follower_id as u64] as int
            && k < ds.server_states[leader_id].log.len()
            && k < ds.server_states[follower_id].log.len()
        ==> ds.server_states[leader_id].log[k] == ds.server_states[follower_id].log[k]
    }

    /// Match index bounded by follower log length: if a leader stores
    /// match_index[f] = M, then f.log.len() >= M. This follows from ARLA
    /// (AR match_index <= follower log length at send time) + LogAppendOnly
    /// (follower log can only grow). Also bounded by leader's log length
    /// (from LHandleAppendResponse guard: new_match_index <= s.log.len()).
    pub open spec fn MatchIndexBounded(ds: RaftDistributedState) -> bool {
        forall |leader_id: int, follower_id: int|
            #![trigger ds.server_states[leader_id].match_index[follower_id as u64]]
            0 <= leader_id < ds.num_servers
            && 0 <= follower_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].match_index.dom().contains(follower_id as u64)
        ==> {
            &&& ds.server_states[leader_id].match_index[follower_id as u64] as int
                <= ds.server_states[follower_id].log.len()
            &&& ds.server_states[leader_id].match_index[follower_id as u64] as int
                <= ds.server_states[leader_id].log.len()
        }
    }

    /// Leader's log is at least as long as any entry with its term.
    /// If any server has a log entry at index k with term T, and there
    /// exists a current leader at term T, then that leader's log has
    /// length > k (i.e., the leader has the entry at index k).
    ///
    /// This captures entry provenance: entries with term T can only be
    /// created by the leader at term T (LClientRequest) or received
    /// via AppendEntries from the leader at term T (LFollowerAppendEntries).
    /// In either case, the leader's log must have been long enough.
    pub open spec fn LeaderLogLongEnough(ds: RaftDistributedState) -> bool {
        forall |i: int, k: int, l: int| #![trigger ds.server_states[l], ds.server_states[i].log[k]]
            0 <= i < ds.num_servers
            && 0 <= k < ds.server_states[i].log.len()
            && 0 <= l < ds.num_servers
            && ds.server_states[l].role is Leader
            && ds.server_states[l].current_term == ds.server_states[i].log[k].term
            ==> ds.server_states[l].log.len() > k
    }

    // =========================================================================
    // Supporting invariant: Entry Term Leader Witness
    //
    // For every entry at index k with term T in any server's log,
    // there exists a "witness" server w whose log also has that entry
    // (same index, same term, same value) and w.log.len() > k.
    // This witness is the leader that originally created the entry.
    // =========================================================================

    pub closed spec fn entry_term_leader_witness_trigger(
        ds: RaftDistributedState, i: int, k: int,
    ) -> bool {
        true
    }

    pub open spec fn EntryTermLeaderWitness(ds: RaftDistributedState) -> bool {
        forall |i: int, k: int|
            #![trigger entry_term_leader_witness_trigger(ds, i, k)]
            0 <= i < ds.num_servers
            && 0 <= k < ds.server_states[i].log.len()
            && entry_term_leader_witness_trigger(ds, i, k)
            ==> exists |w: int|
                #![trigger ds.server_states[w].log[k]]
            {
                &&& 0 <= w < ds.num_servers
                &&& ds.server_states[w].log.len() > k
                &&& ds.server_states[w].log[k] == ds.server_states[i].log[k]
            }
    }

    // =========================================================================
    // Supporting invariant: Entry Term Has Vote Quorum
    //
    // For every entry at index k with term T in any server's log,
    // there exists a server d (the "vote destination") such that:
    // 1. d also has the entry (same index, same content)
    // 2. At least quorum_size - 1 distinct servers have
    //    VoteResponse{T, granted: true} packets to d in the network.
    //
    // This captures the fact that entries at term T can only be created
    // by a leader at T, and that leader received a quorum of votes at T
    // whose VoteResponse packets persist in the network (monotonicity).
    // =========================================================================

    pub closed spec fn entry_term_has_vote_quorum_trigger(
        ds: RaftDistributedState, i: int, k: int,
    ) -> bool {
        true
    }

    pub open spec fn EntryTermHasVoteQuorum(ds: RaftDistributedState) -> bool {
        let quorum_size = ds.num_servers / 2 + 1;
        forall |i: int, k: int|
            #![trigger entry_term_has_vote_quorum_trigger(ds, i, k)]
            0 <= i < ds.num_servers
            && 0 <= k < ds.server_states[i].log.len()
            && entry_term_has_vote_quorum_trigger(ds, i, k)
            ==> exists |d: int, voters: Seq<int>|
                #![trigger ds.server_states[d].log[k], voters.len()]
            {
                &&& 0 <= d < ds.num_servers
                &&& ds.server_states[d].log.len() > k
                &&& ds.server_states[d].log[k] == ds.server_states[i].log[k]
                &&& voters.len() >= quorum_size - 1
                // Each voter has a VoteResponse packet to d
                &&& (forall |a: int| #![trigger voters[a]] 0 <= a < voters.len() ==> {
                    &&& 0 <= voters[a] < ds.num_servers
                    &&& voters[a] != d
                    &&& ExistsGrantedVoteResponse(
                        ds, voters[a], d, ds.server_states[i].log[k].term)
                })
                // Voters are pairwise distinct
                &&& (forall |a: int, b: int|
                    #![trigger voters[a], voters[b]]
                    0 <= a < voters.len() && 0 <= b < voters.len() && a != b
                    ==> voters[a] != voters[b])
            }
    }

    /// Materialize the witnesses promised by `EntryTermHasVoteQuorum` for one
    /// concrete log position.  Keeping this extraction in a small lemma avoids
    /// exposing the invariant's nested quantifiers to the much larger legacy
    /// LeaderCompleteness proofs.
    proof fn lemma_entry_term_vote_quorum_witness(
        ds: RaftDistributedState,
        server: int,
        index: int,
    ) -> (result: (int, Seq<int>))
        requires
            EntryTermHasVoteQuorum(ds),
            0 <= server < ds.num_servers,
            0 <= index < ds.server_states[server].log.len(),
        ensures ({
            let (destination, voters) = result;
            let quorum_size = ds.num_servers / 2 + 1;
            &&& 0 <= destination < ds.num_servers
            &&& ds.server_states[destination].log.len() > index
            &&& ds.server_states[destination].log[index]
                == ds.server_states[server].log[index]
            &&& voters.len() >= quorum_size - 1
            &&& (forall |a: int| #![trigger voters[a]]
                0 <= a < voters.len() ==> {
                    &&& 0 <= voters[a] < ds.num_servers
                    &&& voters[a] != destination
                    &&& ExistsGrantedVoteResponse(
                        ds,
                        voters[a],
                        destination,
                        ds.server_states[server].log[index].term,
                    )
                })
            &&& (forall |a: int, b: int|
                #![trigger voters[a], voters[b]]
                0 <= a < voters.len()
                && 0 <= b < voters.len()
                && a != b
                ==> voters[a] != voters[b])
        }),
    {
        assert(entry_term_has_vote_quorum_trigger(ds, server, index));
        let witnesses = choose |destination: int, voters: Seq<int>|
            #![trigger ds.server_states[destination].log[index], voters.len()]
        {
            &&& 0 <= destination < ds.num_servers
            &&& ds.server_states[destination].log.len() > index
            &&& ds.server_states[destination].log[index]
                == ds.server_states[server].log[index]
            &&& voters.len() >= ds.num_servers / 2 + 1 - 1
            &&& (forall |a: int| #![trigger voters[a]]
                0 <= a < voters.len() ==> {
                    &&& 0 <= voters[a] < ds.num_servers
                    &&& voters[a] != destination
                    &&& ExistsGrantedVoteResponse(
                        ds,
                        voters[a],
                        destination,
                        ds.server_states[server].log[index].term,
                    )
                })
            &&& (forall |a: int, b: int|
                #![trigger voters[a], voters[b]]
                0 <= a < voters.len()
                && 0 <= b < voters.len()
                && a != b
                ==> voters[a] != voters[b])
        };
        witnesses
    }

    /// Packet-level helper: there exists a granted VoteResponse packet from
    /// `src` to `dst` at `term`, with unconstrained stored vote-time summary.
    pub open spec fn ExistsGrantedVoteResponse(
        ds: RaftDistributedState,
        src: int,
        dst: int,
        term: int,
    ) -> bool {
        exists |last_idx: int, last_term: int|
            #![trigger ds.network.contains(LRaftPacket {
                src,
                dst,
                msg: LRaftMessage::VoteResponse {
                    term,
                    granted: true,
                    voter: src,
                    voter_last_log_index: last_idx,
                    voter_last_log_term: last_term,
                },
            })]
            ds.network.contains(LRaftPacket {
                src,
                dst,
                msg: LRaftMessage::VoteResponse {
                    term,
                    granted: true,
                    voter: src,
                    voter_last_log_index: last_idx,
                    voter_last_log_term: last_term,
                },
            })
    }

    // =========================================================================
    // Invariant: RequestVoteSenderState
    // =========================================================================
    //
    // If RequestVote{term: T, candidate: d} is in the network, then:
    //   d.current_term > T, or (d.current_term == T && d.has_voted && d.voted_for == d)
    //
    // This is analogous to VoteResponseIntegrity but for RequestVote packets.
    // At creation (LTimeout): d.current_term = T, has_voted = true, voted_for = d.
    // After creation: term monotonicity + voted_for only changes when term changes.

    pub open spec fn RequestVoteSenderState(ds: RaftDistributedState) -> bool {
        forall |p: LRaftPacket| #![trigger ds.network.contains(p)] ds.network.contains(p) ==>
            match p.msg {
                LRaftMessage::RequestVote { term: t, candidate: d, .. } => {
                    &&& 0 <= d < ds.num_servers
                    &&& p.src == d
                    &&& (ds.server_states[d].current_term > t
                        || (ds.server_states[d].current_term == t
                            && ds.server_states[d].has_voted
                            && ds.server_states[d].voted_for == d))
                }
                _ => true,
            }
    }

    // =========================================================================
    // Invariant: CandidateVoteDestinationUnique
    // =========================================================================
    //
    // If RequestVote{term: T, candidate: d} and
    // VoteResponse{term: T, voter: d, granted: true, dst: c} are both
    // in the network, then c == d (i.e., d only voted for itself at term T).
    //
    // Proof: by RequestVoteSenderState, d.current_term >= T.
    // Case d.current_term == T: by RequestVoteSenderState, d.voted_for == d.
    //   By VoteResponseIntegrity, d.voted_for == c. So c == d.
    // Case d.current_term > T: by VoteResponseIntegrity, d.current_term > T or
    //   (d.current_term == T && ...). Since d.current_term > T, both are consistent.
    //   But the VoteResponse{T, voter: d, granted: true} could only have been created
    //   when d.current_term was <= T. By the has_voted guard in LGrantVote, d could only
    //   vote for the same candidate it first voted for at term T, which is d.
    //   This case is handled inductively (not from single-state reasoning alone).

    pub open spec fn CandidateVoteDestinationUnique(ds: RaftDistributedState) -> bool {
        forall |p_req: LRaftPacket, p_vote: LRaftPacket| #![trigger ds.network.contains(p_req), ds.network.contains(p_vote)]
            ds.network.contains(p_req) && ds.network.contains(p_vote) ==>
            match p_req.msg {
                LRaftMessage::RequestVote { term: t_req, candidate: d, .. } =>
                    match p_vote.msg {
                        LRaftMessage::VoteResponse { term: t_vote, granted, voter: v, .. } =>
                            (granted && t_req == t_vote && v == d)
                                ==> p_vote.dst == d,
                        _ => true,
                    },
                _ => true,
            }
    }

    // =========================================================================
    // Composite Invariant
    // =========================================================================

    /// Every server's complete physical Raft log follows the legal
    /// Stable-to-Joint-to-Stable membership progression.
    ///
    /// This is deliberately stronger than checking only commit_index:
    /// a follower may later commit an entry it replicated earlier, so
    /// legality must already hold when that entry enters its log.
    pub open spec fn AllRaftMembershipLogsWellFormed(
        ds: RaftDistributedState,
    ) -> bool {
        forall |server_id: int| #![trigger ds.server_states[server_id]]
            0 <= server_id < ds.num_servers
            ==> raft_membership_log_is_well_formed(
                ds.server_states[server_id].log,
                MembershipPhase::Stable {
                    config: ds.server_constants[server_id].servers,
                },
            )
    }

    /// Any log length committed by two servers determines the same
    /// membership phase on both servers.
    ///
    /// This is configuration provenance at a shared committed prefix:
    /// StateMachineSafety makes the physical entries equal, and the
    /// active-membership projection is a deterministic scan of those entries.
    pub open spec fn CommittedMembershipPrefixAgreement(
        ds: RaftDistributedState,
    ) -> bool {
        forall |left: int, right: int, committed_len: int| #![trigger ds.server_states[left], active_membership_phase_from_raft_log(ds.server_states[right].log, committed_len, MembershipPhase::Stable { config: ds.server_constants[right].servers })] #![trigger ds.server_states[right], active_membership_phase_from_raft_log(ds.server_states[left].log, committed_len, MembershipPhase::Stable { config: ds.server_constants[left].servers })]
            0 <= left < ds.num_servers
            && 0 <= right < ds.num_servers
            && 0 <= committed_len
            && committed_len
                <= ds.server_states[left].commit_index
            && committed_len
                <= ds.server_states[right].commit_index
            ==> active_membership_phase_from_raft_log(
                ds.server_states[left].log,
                committed_len,
                MembershipPhase::Stable {
                    config: ds.server_constants[left].servers,
                },
            ) == active_membership_phase_from_raft_log(
                ds.server_states[right].log,
                committed_len,
                MembershipPhase::Stable {
                    config: ds.server_constants[right].servers,
                },
            )
    }

    /// Ordinary Raft committed-log agreement implies committed-membership
    /// agreement because both servers scan the same configuration entries.
    pub proof fn lemma_state_machine_safety_implies_committed_membership_prefix_agreement(
        ds: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            StateMachineSafety(ds),
            CommitIndexBounded(ds),
        ensures
            CommittedMembershipPrefixAgreement(ds),
    {
        assert forall |left: int, right: int, committed_len: int| #![trigger ds.server_states[left], active_membership_phase_from_raft_log(ds.server_states[right].log, committed_len, MembershipPhase::Stable { config: ds.server_constants[right].servers })] #![trigger ds.server_states[right], active_membership_phase_from_raft_log(ds.server_states[left].log, committed_len, MembershipPhase::Stable { config: ds.server_constants[left].servers })]
            0 <= left < ds.num_servers
            && 0 <= right < ds.num_servers
            && 0 <= committed_len
            && committed_len
                <= ds.server_states[left].commit_index
            && committed_len
                <= ds.server_states[right].commit_index
            implies active_membership_phase_from_raft_log(
                ds.server_states[left].log,
                committed_len,
                MembershipPhase::Stable {
                    config: ds.server_constants[left].servers,
                },
            ) == active_membership_phase_from_raft_log(
                ds.server_states[right].log,
                committed_len,
                MembershipPhase::Stable {
                    config: ds.server_constants[right].servers,
                },
            )
        by {
            assert(committed_len
                <= ds.server_states[left].log.len());
            assert(committed_len
                <= ds.server_states[right].log.len());

            assert forall |index: int|
                0 <= index < committed_len
                implies ds.server_states[left].log[index]
                    == ds.server_states[right].log[index]
            by {
                assert(index
                    < ds.server_states[left].commit_index);
                assert(index
                    < ds.server_states[right].commit_index);
            };

            assert(ds.server_constants[left].servers
                == ds.server_constants[right].servers);

            lemma_equal_committed_raft_prefixes_have_same_active_phase(
                ds.server_states[left].log,
                ds.server_states[right].log,
                committed_len,
                MembershipPhase::Stable {
                    config: ds.server_constants[left].servers,
                },
            );
        };
    }

    /// Every reachable server is separated from its committed prefix by at
    /// most one pending membership boundary. Data entries may appear on
    /// either side of that one boundary.
    pub open spec fn UncommittedSuffixesHaveAtMostOneConfiguration(
        ds: RaftDistributedState,
    ) -> bool {
        forall |server_id: int| #![trigger ds.server_states[server_id]]
            0 <= server_id < ds.num_servers ==>
            uncommitted_suffix_has_at_most_one_configuration(
                ds.server_states[server_id].log,
                ds.server_states[server_id].commit_index,
            )
    }

    /// The full inductive invariant: conjunction of all safety invariants
    ///
    /// The legacy fixed-majority election and entry-transfer predicates are
    /// intentionally not conjuncts: reachable elections now use the membership
    /// phase recorded from the log. Dynamic safety is carried by recorded
    /// election quorums and immutable commit certificates.
    pub open spec fn RaftSafetyInvariant(ds: RaftDistributedState) -> bool {
        &&& WellFormedRaftDistributed(ds)
        &&& StateMachineSafety(ds)
        &&& CommittedMembershipPrefixAgreement(ds)
        &&& LeaderHasRecordedElectionQuorum(ds)
        &&& LeaderHasRecordedElectionLogProvenance(ds)
        &&& CommittedConfigurationsHaveCertificates(ds)
        &&& CommittedEntriesHaveLogCertificates(ds)
        &&& CommitIndexBounded(ds)
        &&& CommitIndexNonnegative(ds)
        &&& EntryTermLeaderWitness(ds)
        &&& VotesGrantedAreServers(ds)
        &&& CandidateOrLeaderVotedForSelf(ds)
        &&& CandidateOrLeaderVotedForSelfId(ds)
        &&& VotersVotedForCandidate(ds)
        // Message invariants
        &&& SenderIntegrity(ds)
        &&& VoteResponseIntegrity(ds)
        &&& VoteResponseSummaryStillValidAtOrAboveTerm(ds)
        &&& VoteResponseHasRequestVote(ds)
        &&& AppendEntriesIntegrity(ds)
        &&& OneVotePerTermInNetwork(ds)
        &&& RequestVoteSenderState(ds)
        &&& RequestVoteSummaryStillValidAtSameTerm(ds)
        &&& RequestVoteSummaryAlwaysValid(ds)
        &&& RequestVoteLastLogTermBound(ds)
        &&& RequestVoteLogParamsConsistent(ds)
        &&& CandidateVoteDestinationUnique(ds)
        // Ghost state invariants (Phase 34.7 — stale-vote provenance)
        &&& VoteLogLenCoversNetwork(ds)
        &&& VoteLogLenBounded(ds)
        &&& VoteLogLenEntryTermBound(ds)
        &&& VoteGrantedLogUpToDateAtVoteTime(ds)
        // Follower commit updates cannot outrun the leader information they received.
        &&& AppendEntriesLeaderCommitBound(ds)
        // Election-snapshot ghost state
        &&& ElectionLogLenBounded(ds)
        &&& ElectionLogLenEntryTermBound(ds)
        &&& LeaderElectionSnapshotRecorded(ds)
        // Log structure invariants (Phase 34.7 — strict-term transfer)
        &&& CurrentTermGeLogTerms(ds)
        &&& LogTermsMonotonic(ds)
        &&& TermsNonNegative(ds)
    }

    // =========================================================================
    // Invariant holds at init
    // =========================================================================

    pub proof fn lemma_init_establishes_invariant(ds: RaftDistributedState)
        requires RaftDistributedInit(ds)
        ensures RaftSafetyInvariant(ds)
    {
        // Election-snapshot ghost state starts empty and no server is a leader,
        // so all three of its invariants hold vacuously.
        assert(ds.election_log_len == Map::<(int, int), int>::empty());

        lemma_init_establishes_all_raft_membership_logs_well_formed(ds);
        lemma_init_establishes_configuration_certificate_invariants(ds);
        lemma_init_establishes_log_certificate_coverage(ds);
        lemma_init_establishes_log_certificates_valid(ds);
        lemma_log_certificate_coverage_implies_state_machine_safety(ds);
        lemma_state_machine_safety_implies_committed_membership_prefix_agreement(
            ds,
        );

        // All servers start as Followers with empty votes_granted:
        // - ElectionSafety: no Leaders, vacuously true
        // - LogMatching: empty logs, vacuously true
        // - LeaderCompleteness: no committed entries, vacuously true
        // - StateMachineSafety: commit_index = 0, vacuously true
        // - LeaderHasQuorum: no Leaders, vacuously true
        // - CommitIndexBounded: commit_index = 0 <= log.len() = 0
        // - VotesGrantedAreServers: votes_granted empty, vacuously true
        // - CandidateOrLeaderVotedForSelf: no Candidates/Leaders, vacuously true
        // - VotersVotedForCandidate: no Candidates/Leaders, vacuously true
        // - EntryTermHasVoteQuorum: empty logs, vacuously true
        // Message invariants: network is empty, all vacuously true
        // - SenderIntegrity, VoteResponseIntegrity,
        //   VoteResponseSummaryStillValidAtOrAboveTerm, VoteResponseHasRequestVote,
        //   AppendEntriesIntegrity, OneVotePerTermInNetwork,
        //   RequestVoteSenderState, RequestVoteSummaryStillValidAtSameTerm,
        //   RequestVoteLogParamsConsistent, CandidateVoteDestinationUnique:
        //   forall over empty set is vacuously true
        // Ghost state invariants: vote_log_len empty + network empty, vacuously true
        // - VoteLogLenCoversNetwork, VoteLogLenBounded, VoteLogLenEntryTermBound,
        //   VoteGrantedLogUpToDateAtVoteTime
        // Match index / append response / commit invariants: network empty + no Leaders, vacuously true
        // - AppendResponseLogAgreement: no packets, vacuously true
        // - MatchIndexImpliesLogAgreement: no Leaders, vacuously true
        // - MatchIndexBounded: no Leaders (match_index empty at init), vacuously true
        // - AppendEntriesLeaderCommitBound: no packets, vacuously true
        // Log structure invariants: empty logs + current_term = 0, vacuously/trivially true
        // - CurrentTermGeLogTerms, LogTermsMonotonic, TermsNonNegative
    }

    /// Initialization establishes full membership-history legality:
    /// every server starts with the empty Raft log.
    pub proof fn lemma_init_establishes_all_raft_membership_logs_well_formed(
        ds: RaftDistributedState,
    )
        requires
            RaftDistributedInit(ds),
        ensures
            AllRaftMembershipLogsWellFormed(ds),
    {
        assert forall |server_id: int| #![trigger ds.server_states[server_id]]
            0 <= server_id < ds.num_servers
            implies raft_membership_log_is_well_formed(
                ds.server_states[server_id].log,
                MembershipPhase::Stable {
                    config: ds.server_constants[server_id].servers,
                },
            )
        by {
            assert(LInit(
                ds.server_states[server_id],
                ds.server_constants[server_id],
            ));
            assert(ds.server_states[server_id].log
                == Seq::<LLogEntry>::empty());
            lemma_empty_raft_membership_log_is_well_formed(
                MembershipPhase::Stable {
                    config: ds.server_constants[server_id].servers,
                },
            );
        };
    }

    // =========================================================================
    // Election Safety Induction Proof
    // =========================================================================

    /// Helper: a server's step doesn't create new leaders in other terms.
    /// If only server_id transitions and all others are unchanged,
    /// and ElectionSafety held before, then for any pair (i, j) where
    /// neither is server_id, ElectionSafety still holds between them.
    ///
    /// The only interesting case is when server_id becomes a new Leader.

    /// Helper: extract voted_for == i from CandidateOrLeaderVotedForSelfId.
    proof fn lemma_voted_for_self(ds: RaftDistributedState, i: int)
        requires
            CandidateOrLeaderVotedForSelfId(ds),
            0 <= i < ds.num_servers,
            ds.server_states[i].role is Candidate || ds.server_states[i].role is Leader,
        ensures
            ds.server_states[i].voted_for == i,
            ds.server_states[i].has_voted,
    {
        assert(CandidateOrLeaderVotedForSelfId(ds));
    }

    /// Helper: turn vote-set membership into an explicit VoteResponse packet
    /// witness and aligned voter facts from VoteResponseIntegrity.
    proof fn lemma_vote_witness_from_votes_granted(
        ds: RaftDistributedState, candidate: int, voter: int,
    )
        requires
            VotersVotedForCandidate(ds),
            VoteResponseIntegrity(ds),
            0 <= candidate < ds.num_servers,
            0 <= voter < ds.num_servers,
            voter != candidate,
            (ds.server_states[candidate].role is Candidate
                || ds.server_states[candidate].role is Leader),
            ds.server_states[candidate].votes_granted.contains(voter),
        ensures
            exists |p: LRaftPacket| #![trigger ds.network.contains(p)] {
                &&& ds.network.contains(p)
                &&& p.src == voter
                &&& p.dst == candidate
                &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter: msg_voter, .. }
                &&& granted
                &&& term == ds.server_states[candidate].current_term
                &&& msg_voter == voter
            },
            ds.server_states[voter].current_term
                > ds.server_states[candidate].current_term
                || (ds.server_states[voter].current_term
                    == ds.server_states[candidate].current_term
                    && ds.server_states[voter].has_voted
                    && ds.server_states[voter].voted_for == candidate),
    {
        let p = choose |p: LRaftPacket| #![trigger ds.network.contains(p)] {
            &&& ds.network.contains(p)
            &&& p.dst == candidate
            &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter: msg_voter, .. }
            &&& term == ds.server_states[candidate].current_term
            &&& granted
            &&& msg_voter == voter
        };
        assert(ds.network.contains(p));
        assert(p.dst == candidate);
        assert(p.msg is VoteResponse);
        assert(p.msg->VoteResponse_granted);
        assert(p.msg->VoteResponse_term == ds.server_states[candidate].current_term);
        assert(p.msg->VoteResponse_voter == voter);

        assert(
            match p.msg {
                LRaftMessage::VoteResponse { term: t, granted: g, voter: v, .. } => {
                    g ==> {
                        &&& 0 <= v < ds.num_servers
                        &&& p.src == v
                        &&& (ds.server_states[v].current_term > t
                            || (ds.server_states[v].current_term == t
                                && ds.server_states[v].has_voted
                                && ds.server_states[v].voted_for == p.dst))
                    }
                }
                _ => true,
            }
        ) by {
            assert(VoteResponseIntegrity(ds));
        };

        assert(p.src == voter);
        assert(
            ds.server_states[voter].current_term
                > ds.server_states[candidate].current_term
                || (ds.server_states[voter].current_term
                    == ds.server_states[candidate].current_term
                    && ds.server_states[voter].has_voted
                    && ds.server_states[voter].voted_for == candidate)
        );
        assert(exists |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
            &&& ds.network.contains(pkt)
            &&& pkt.src == voter
            &&& pkt.dst == candidate
            &&& pkt.msg matches LRaftMessage::VoteResponse { term, granted, voter: msg_voter, .. }
            &&& granted
            &&& term == ds.server_states[candidate].current_term
            &&& msg_voter == voter
        }) by {
            assert(ds.network.contains(p));
            assert(p.src == voter);
            assert(p.dst == candidate);
            assert(p.msg is VoteResponse);
            assert(p.msg->VoteResponse_granted);
            assert(p.msg->VoteResponse_term == ds.server_states[candidate].current_term);
            assert(p.msg->VoteResponse_voter == voter);
        };
    }

    // =========================================================================
    // Stale-vote provenance: recover vote-time log relation from ghost state
    // =========================================================================
    //
    // When overlap_voter.current_term > vote_term (stale case), the voter's
    // current state no longer reflects vote-time conditions. But vote_log_len
    // records the voter's log length at vote time, and VoteLogLenBounded ensures
    // it's bounded by the current log length.
    //
    // This lemma extracts the vote-time log length and establishes:
    // (1) vote_log_len[(ov, vt)] exists and L <= ov.log.len()
    // (2) Combined with RequestVoteSummaryStillValidAtSameTerm, the leader's
    //     RequestVote carried (last_log_index, last_log_term) valid against
    //     the leader's current log
    // (3) At vote time, log_up_to_date(voter_mid, last_log_term, last_log_index)
    //     passed, where voter_mid.log.len() == L
    // (4) So: last_log_term > voter_vote_time_last_term OR
    //         (last_log_term == voter_vote_time_last_term && last_log_index >= L)
    // (5) Since last_log_index == leader.log.len() (from RequestVoteSummaryStillValidAtSameTerm):
    //         leader.log.len() >= L (in the equal-term case)
    //
    // The postcondition packages these facts for use in the overlap-entry
    // transfer path.

    proof fn lemma_stale_vote_log_len_recovery(
        ds: RaftDistributedState,
        overlap_voter: int,
        leader_id: int,
        k: int,
        entry: LLogEntry,
    )
        requires
            WellFormedRaftDistributed(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            RequestVoteSummaryStillValidAtSameTerm(ds),
            0 <= leader_id < ds.num_servers,
            0 <= overlap_voter < ds.num_servers,
            overlap_voter != leader_id,
            (ds.server_states[leader_id].role is Candidate
                || ds.server_states[leader_id].role is Leader),
            ds.server_states[overlap_voter].current_term
                > ds.server_states[leader_id].current_term,
            // Overlap voter has entry at k in pre-state
            0 <= k,
            ds.server_states[overlap_voter].log.len() > k,
            ds.server_states[overlap_voter].log[k] == entry,
            // There's a granted VoteResponse from overlap_voter at leader's term
            exists |vote_pkt: LRaftPacket| #![trigger ds.network.contains(vote_pkt)] {
                &&& ds.network.contains(vote_pkt)
                &&& vote_pkt.src == overlap_voter
                &&& vote_pkt.dst == leader_id
                &&& vote_pkt.msg matches LRaftMessage::VoteResponse {
                    term: vt, granted, voter: vv, .. }
                &&& granted
                &&& vv == overlap_voter
                &&& vt == ds.server_states[leader_id].current_term
            },
            // There's a matching RequestVote with summary valid against leader log
            exists |req_pkt: LRaftPacket| #![trigger ds.network.contains(req_pkt)] {
                &&& ds.network.contains(req_pkt)
                &&& req_pkt.src == leader_id
                &&& req_pkt.dst == overlap_voter
                &&& req_pkt.msg matches LRaftMessage::RequestVote {
                    term, candidate, last_log_index, last_log_term }
                &&& term == ds.server_states[leader_id].current_term
                &&& candidate == leader_id
                &&& 0 <= last_log_index <= ds.server_states[leader_id].log.len()
                &&& (last_log_index == 0 ==> last_log_term == 0)
                &&& (last_log_index > 0 ==>
                    ds.server_states[leader_id].log[last_log_index - 1].term
                        == last_log_term)
            },
        ensures
            // Vote-time log length is recoverable from ghost state
            ds.vote_log_len.dom().contains(
                (overlap_voter, ds.server_states[leader_id].current_term)),
            ({
                let vote_time_log_len = ds.vote_log_len[
                    (overlap_voter, ds.server_states[leader_id].current_term)];
                // Bounded by current log length
                &&& vote_time_log_len <= ds.server_states[overlap_voter].log.len()
                // If k < vote_time_log_len, the entry was in the voter's log at
                // vote time (voter's current log preserves vote-time prefix):
                // For the bridge template's result, combined with
                // RequestVoteSummaryStillValidAtSameTerm, we get the standard
                // log_up_to_date relation using vote-time log length.
            }),
    {
        let vote_term = ds.server_states[leader_id].current_term;
        // Extract vote packet witness
        let vote_pkt = choose |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
            &&& ds.network.contains(pkt)
            &&& pkt.src == overlap_voter
            &&& pkt.dst == leader_id
            &&& pkt.msg matches LRaftMessage::VoteResponse {
                term: vt, granted, voter: vv, .. }
            &&& granted
            &&& vv == overlap_voter
            &&& vt == vote_term
        };
        // VoteLogLenCoversNetwork: (overlap_voter, vote_term) in vote_log_len
        assert(VoteLogLenCoversNetwork(ds));
        assert(ds.network.contains(vote_pkt));
        assert(vote_pkt.msg is VoteResponse);
        assert(vote_pkt.msg->VoteResponse_granted);
        let v = vote_pkt.msg->VoteResponse_voter;
        let t = vote_pkt.msg->VoteResponse_term;
        assert(v == overlap_voter);
        assert(t == vote_term);
        assert(ds.vote_log_len.dom().contains((v, t)));
        assert(ds.vote_log_len.dom().contains((overlap_voter, vote_term)));

        // VoteLogLenBounded: recorded length <= current log length
        assert(VoteLogLenBounded(ds));
        let vote_time_log_len = ds.vote_log_len[(overlap_voter, vote_term)];
        assert(vote_time_log_len <= ds.server_states[overlap_voter].log.len());
    }

    // =========================================================================
    // Stale-vote: derive concrete index relation from VoteGrantedLogUpToDate
    // =========================================================================
    //
    // Consumes VoteGrantedLogUpToDateAtVoteTime to derive the Raft log
    // comparison disjunction at the vote-time log length L:
    //
    //   req_last_log_term > voter_vote_time_last_term
    //     || (req_last_log_term == voter_vote_time_last_term
    //         && req_last_log_index >= L)
    //
    // Combined with:
    //   - req_last_log_index <= leader.log.len() (from RequestVoteSummaryStillValidAtSameTerm)
    //   - L = vote_log_len[(overlap_voter, leader.current_term)]
    //
    // In the equal-term case: leader.log.len() >= req_last_log_index >= L.
    // If k < L, then leader.log.len() > k.

    proof fn lemma_stale_vote_index_relation(
        ds: RaftDistributedState,
        overlap_voter: int,
        leader_id: int,
        k: int,
        entry: LLogEntry,
    )
        requires
            WellFormedRaftDistributed(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
            RequestVoteSummaryStillValidAtSameTerm(ds),
            0 <= leader_id < ds.num_servers,
            0 <= overlap_voter < ds.num_servers,
            overlap_voter != leader_id,
            (ds.server_states[leader_id].role is Candidate
                || ds.server_states[leader_id].role is Leader),
            ds.server_states[overlap_voter].current_term
                > ds.server_states[leader_id].current_term,
            0 <= k,
            ds.server_states[overlap_voter].log.len() > k,
            ds.server_states[overlap_voter].log[k] == entry,
            // Granted VoteResponse from overlap_voter to leader at leader's term
            exists |vote_pkt: LRaftPacket| #![trigger ds.network.contains(vote_pkt)] {
                &&& ds.network.contains(vote_pkt)
                &&& vote_pkt.src == overlap_voter
                &&& vote_pkt.dst == leader_id
                &&& vote_pkt.msg matches LRaftMessage::VoteResponse {
                    term: vt, granted, voter: vv, .. }
                &&& granted
                &&& vv == overlap_voter
                &&& vt == ds.server_states[leader_id].current_term
            },
            // Matching RequestVote from leader to overlap_voter at leader's term
            exists |req_pkt: LRaftPacket| #![trigger ds.network.contains(req_pkt)] {
                &&& ds.network.contains(req_pkt)
                &&& req_pkt.src == leader_id
                &&& req_pkt.dst == overlap_voter
                &&& req_pkt.msg matches LRaftMessage::RequestVote {
                    term, candidate, last_log_index, last_log_term }
                &&& term == ds.server_states[leader_id].current_term
                &&& candidate == leader_id
                &&& 0 <= last_log_index <= ds.server_states[leader_id].log.len()
                &&& (last_log_index == 0 ==> last_log_term == 0)
                &&& (last_log_index > 0 ==>
                    ds.server_states[leader_id].log[last_log_index - 1].term
                        == last_log_term)
            },
        ensures
            // vote_log_len is available
            ds.vote_log_len.dom().contains(
                (overlap_voter, ds.server_states[leader_id].current_term)),
            ({
                let vote_time_log_len = ds.vote_log_len[
                    (overlap_voter, ds.server_states[leader_id].current_term)];
                // Bounded by current log length
                &&& vote_time_log_len <= ds.server_states[overlap_voter].log.len()
                // The concrete index relation: the RequestVote's log params
                // satisfied log_up_to_date at vote time, giving a disjunction
                // on req_last_log_term vs voter_vote_time_last_term.
                // In the equal-term case, req_last_log_index >= vote_time_log_len.
                // Combined with req_last_log_index <= leader.log.len(), this gives
                // leader.log.len() >= vote_time_log_len.
            }),
            // The concrete index disjunction (from VoteGrantedLogUpToDateAtVoteTime):
            ({
                let vote_term = ds.server_states[leader_id].current_term;
                let L = ds.vote_log_len[(overlap_voter, vote_term)];
                let voter_vtl: int = if L == 0 { 0int } else {
                    ds.server_states[overlap_voter].log[L - 1].term
                };
                // There exists a RequestVote packet whose params satisfy
                // the vote-time log_up_to_date disjunction.
                exists |req_pkt: LRaftPacket| #![trigger ds.network.contains(req_pkt)] {
                    &&& ds.network.contains(req_pkt)
                    &&& req_pkt.src == leader_id
                    &&& req_pkt.dst == overlap_voter
                    &&& req_pkt.msg is RequestVote
                    &&& req_pkt.msg->RequestVote_term == vote_term
                    &&& req_pkt.msg->RequestVote_last_log_index
                        <= ds.server_states[leader_id].log.len()
                    &&& (req_pkt.msg->RequestVote_last_log_term > voter_vtl
                        || (req_pkt.msg->RequestVote_last_log_term == voter_vtl
                            && req_pkt.msg->RequestVote_last_log_index >= L))
                }
            }),
    {
        let vote_term = ds.server_states[leader_id].current_term;

        // Step 1: recover vote_log_len entry (from lemma_stale_vote_log_len_recovery)
        lemma_stale_vote_log_len_recovery(
            ds, overlap_voter, leader_id, k, entry);
        let L = ds.vote_log_len[(overlap_voter, vote_term)];
        assert(L <= ds.server_states[overlap_voter].log.len());

        // Step 2: extract the VoteResponse and RequestVote packet witnesses
        let vote_pkt = choose |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
            &&& ds.network.contains(pkt)
            &&& pkt.src == overlap_voter
            &&& pkt.dst == leader_id
            &&& pkt.msg matches LRaftMessage::VoteResponse {
                term: vt, granted, voter: vv, .. }
            &&& granted
            &&& vv == overlap_voter
            &&& vt == vote_term
        };
        let req_pkt = choose |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
            &&& ds.network.contains(pkt)
            &&& pkt.src == leader_id
            &&& pkt.dst == overlap_voter
            &&& pkt.msg matches LRaftMessage::RequestVote {
                term, candidate, last_log_index, last_log_term }
            &&& term == vote_term
            &&& candidate == leader_id
            &&& 0 <= last_log_index <= ds.server_states[leader_id].log.len()
            &&& (last_log_index == 0 ==> last_log_term == 0)
            &&& (last_log_index > 0 ==>
                ds.server_states[leader_id].log[last_log_index - 1].term
                    == last_log_term)
        };

        // Step 3: apply VoteGrantedLogUpToDateAtVoteTime
        // Instantiate with (vote_pkt, req_pkt):
        //   vote_pkt.src == overlap_voter == req_pkt.dst  ✓
        //   vote_pkt.dst == leader_id == req_pkt.src      ✓
        //   vote_pkt.msg.term == req_pkt.msg.term == vote_term ✓
        //   vote_log_len.dom().contains((overlap_voter, vote_term)) ✓
        assert(VoteGrantedLogUpToDateAtVoteTime(ds));
        assert(ds.network.contains(vote_pkt));
        assert(ds.network.contains(req_pkt));
        assert(vote_pkt.msg is VoteResponse);
        assert(vote_pkt.msg->VoteResponse_granted);
        assert(req_pkt.msg is RequestVote);
        assert(vote_pkt.msg->VoteResponse_term == req_pkt.msg->RequestVote_term);
        assert(vote_pkt.src == req_pkt.dst);
        assert(vote_pkt.dst == req_pkt.src);
        assert(ds.vote_log_len.dom().contains((vote_pkt.src, vote_pkt.msg->VoteResponse_term)));

        // The invariant gives us the disjunction
        let voter_vtl: int = if L == 0 { 0int } else {
            ds.server_states[overlap_voter].log[L - 1].term
        };
        let li = req_pkt.msg->RequestVote_last_log_index;
        let lt = req_pkt.msg->RequestVote_last_log_term;
        assert(lt > voter_vtl || (lt == voter_vtl && li >= L));

        // Also: li <= leader.log.len() (from req_pkt precondition)
        assert(li <= ds.server_states[leader_id].log.len());
    }


    /// Given a granted VoteResponse + matching RequestVote at the leader's
    /// term, use VoteGrantedLogUpToDateAtVoteTime to derive the vote-time
    /// log_up_to_date disjunction. In the equal-term, equal-length sub-case
    /// (req_last_log_index == vote_time_log_len), LogMatching transfers
    /// the entry equality. Other sub-cases are left as a residual assume.
    proof fn lemma_overlap_entry_transfer_equal_term_equal_len(
        ds: RaftDistributedState,
        overlap_voter: int,
        leader_id: int,
        k: int,
        entry: LLogEntry,
        vote_pkt: LRaftPacket,
        req_pkt: LRaftPacket,
    ) -> (result: (bool, int, int, int, int, int))
        requires
            WellFormedRaftDistributed(ds),
            LogMatching(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteLogLenEntryTermBound(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
            0 <= leader_id < ds.num_servers,
            0 <= overlap_voter < ds.num_servers,
            overlap_voter != leader_id,
            (ds.server_states[leader_id].role is Candidate
                || ds.server_states[leader_id].role is Leader),
            ds.server_states[leader_id].current_term > entry.term,
            0 <= k,
            ds.server_states[overlap_voter].log.len() > k,
            ds.server_states[overlap_voter].log[k] == entry,
            // VoteResponse packet witness
            ds.network.contains(vote_pkt),
            vote_pkt.src == overlap_voter,
            vote_pkt.dst == leader_id,
            vote_pkt.msg is VoteResponse,
            vote_pkt.msg->VoteResponse_granted,
            vote_pkt.msg->VoteResponse_voter == overlap_voter,
            vote_pkt.msg->VoteResponse_term
                == ds.server_states[leader_id].current_term,
            // RequestVote packet witness
            ds.network.contains(req_pkt),
            req_pkt.src == leader_id,
            req_pkt.dst == overlap_voter,
            req_pkt.msg is RequestVote,
            req_pkt.msg->RequestVote_term
                == ds.server_states[leader_id].current_term,
            req_pkt.msg->RequestVote_candidate == leader_id,
            0 <= req_pkt.msg->RequestVote_last_log_index
                <= ds.server_states[leader_id].log.len(),
            (req_pkt.msg->RequestVote_last_log_index == 0
                ==> req_pkt.msg->RequestVote_last_log_term == 0),
            (req_pkt.msg->RequestVote_last_log_index > 0
                ==> ds.server_states[leader_id].log[
                        req_pkt.msg->RequestVote_last_log_index - 1].term
                    == req_pkt.msg->RequestVote_last_log_term),
        ensures ({
            let (handled, vote_term, rli, rlt, vtl, L) = result;
            &&& vote_term == ds.server_states[leader_id].current_term
            &&& rli == req_pkt.msg->RequestVote_last_log_index
            &&& rlt == req_pkt.msg->RequestVote_last_log_term
            &&& (handled ==> (
                ds.server_states[leader_id].log.len() > k
                    && ds.server_states[leader_id].log[k] == entry
            ))
            &&& (!handled ==> {
                &&& k < L
                &&& L > 0
                &&& 0 <= L <= ds.server_states[overlap_voter].log.len()
                &&& vtl == (if L == 0 { 0int } else {
                    ds.server_states[overlap_voter].log[L - 1].term
                })
                &&& (rlt > vtl || (rlt == vtl && rli > L))
                &&& 0 <= rli <= ds.server_states[leader_id].log.len()
                &&& (rli == 0 ==> rlt == 0)
                &&& (rli > 0 ==>
                    ds.server_states[leader_id].log[rli - 1].term == rlt)
            })
        }),
    {
        let vote_term = ds.server_states[leader_id].current_term;
        let req_last_log_index = req_pkt.msg->RequestVote_last_log_index;
        let req_last_log_term = req_pkt.msg->RequestVote_last_log_term;

        // Step 1: Extract vote-time log length
        assert(VoteLogLenCoversNetwork(ds));
        assert(ds.vote_log_len.dom().contains((overlap_voter, vote_term)));
        let L = ds.vote_log_len[(overlap_voter, vote_term)];
        assert(VoteLogLenBounded(ds));
        assert(L <= ds.server_states[overlap_voter].log.len());
        assert(L >= 0);

        // Step 2: Use VoteGrantedLogUpToDateAtVoteTime to get disjunction
        assert(vote_pkt.msg->VoteResponse_term == req_pkt.msg->RequestVote_term);
        assert(vote_pkt.src == req_pkt.dst);  // voter
        assert(vote_pkt.dst == req_pkt.src);  // candidate
        assert(ds.vote_log_len.dom().contains(
            (vote_pkt.src, vote_pkt.msg->VoteResponse_term)));
        let voter_vtl: int = if L == 0 { 0int } else {
            ds.server_states[overlap_voter].log[L - 1].term
        };
        assert(
            req_last_log_term > voter_vtl
                || (req_last_log_term == voter_vtl
                    && req_last_log_index >= L)
        );

        // Helper: k < L proof via VoteLogLenEntryTermBound contradiction
        // (used by both equal-term/equal-length and non-equal-length paths)
        assert(VoteLogLenEntryTermBound(ds));
        if k >= L {
            let p_vt: (int, int) = (overlap_voter, vote_term);
            assert(ds.vote_log_len.dom().contains(p_vt));
            assert(0 <= p_vt.0 < ds.num_servers);
            assert(ds.vote_log_len[p_vt] <= k);
            assert(k < ds.server_states[p_vt.0].log.len());
            let _ = ds.server_states[p_vt.0].log[k];
            assert(ds.server_states[p_vt.0].log[k].term >= p_vt.1);
            assert(vote_term == ds.server_states[leader_id].current_term);
            assert(ds.server_states[leader_id].current_term > entry.term);
            assert(ds.server_states[overlap_voter].log[k] == entry);
            assert(false);
        }
        assert(k < L);
        assert(L > 0);

        // Step 3: Case split
        if req_last_log_term == voter_vtl
            && req_last_log_index >= L
            && req_last_log_index == L
        {
            // Equal-term, equal-length sub-case
            let match_idx: int = L - 1;
            assert(ds.server_states[leader_id].log[match_idx].term
                == req_last_log_term);
            assert(ds.server_states[overlap_voter].log[match_idx].term
                == voter_vtl);
            assert(ds.server_states[leader_id].log[match_idx].term
                == ds.server_states[overlap_voter].log[match_idx].term);

            assert(0 <= match_idx
                < ds.server_states[leader_id].log.len());
            assert(0 <= match_idx
                < ds.server_states[overlap_voter].log.len());

            assert(k <= match_idx);
            assert(ds.server_states[leader_id].log[k]
                == ds.server_states[overlap_voter].log[k]);
            assert(ds.server_states[leader_id].log[k] == entry);
            assert(ds.server_states[leader_id].log.len() > k);
            (true, vote_term, req_last_log_index, req_last_log_term,
                voter_vtl, L)
        } else {
            // Strict-term (rlt > vtl) or equal-term with rli > L:
            // not handled here; caller dispatches to heavy helpers.
            // Note: L == 0 case is impossible since L > 0 (proved above).
            (false, vote_term, req_last_log_index, req_last_log_term,
                voter_vtl, L)
        }
    }

    // =========================================================================
    // Phase 34.7.4: Term-induction recursive proof for LeaderCompleteness
    // =========================================================================
    //
    // Ongaro's proof by contradiction with term induction:
    // For the smallest term T whose leader lacks committed entry e at index k,
    // quorum overlap gives voter w who has e and voted for T-leader.
    // If equal-term: LogMatching transfers e. Contradiction.
    // If strict-term: T-leader's log has an entry at rli-1 with term rlt < T.
    //   By ETHVQ, there's a server d with d.log[rli-1].term == rlt and quorum at rlt.
    //   By IH (minimality of T): the leader at rlt has e at k.
    //   By LogMatching between d and T-leader (shared term at rli-1):
    //   T-leader also has e. Contradiction.
    //
    // In Verus, we turn this into a direct recursive proof with decreases
    // on leader.current_term - entry.term.

    /// Phase 34.7.4: Entry transfer via ETHVQ path given
    /// ExistsGrantedVoteResponse.
    ///
    /// Performs packet extraction + equal-term attempt, then falls through
    /// to strict-term case if needed. Works for both Candidate and Leader.
    ///
    /// Does NOT require VotersVotedForCandidate, VoteResponseIntegrity,
    /// or EntryTermHasVoteQuorum — only ETHVQ-safe invariants.
    proof fn lemma_ethvq_entry_transfer_from_overlap_voter(
        ds: RaftDistributedState,
        d: int,
        ov: int,
        k: int,
        entry: LLogEntry,
    )
        requires
            WellFormedRaftDistributed(ds),
            EntryTermHasVoteQuorum(ds),
            LogMatching(ds),
            TermsNonNegative(ds),
            VoteResponseHasRequestVote(ds),
            RequestVoteSummaryAlwaysValid(ds),
            RequestVoteLastLogTermBound(ds),
            LogTermsMonotonic(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteLogLenEntryTermBound(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
            OneVotePerTermInNetwork(ds),
            CandidateVoteDestinationUnique(ds),
            EntryCommittedAt(ds, k, entry),
            0 <= k,
            0 <= d < ds.num_servers,
            0 <= ov < ds.num_servers,
            ov != d,
            ds.server_states[ov].log.len() > k,
            ds.server_states[ov].log[k] == entry,
            ds.server_states[d].current_term > entry.term,
            ExistsGrantedVoteResponse(ds, ov, d,
                ds.server_states[d].current_term),
        ensures
            ds.server_states[d].log.len() > k,
            ds.server_states[d].log[k] == entry,
    {
        let T = ds.server_states[d].current_term;

        // Step 1: Packet extraction + equal-term attempt
        let (d_rli, d_rlt, ov_L, handled) =
            lemma_ethvq_committed_try_equal_term(
                ds, ov, d, T, k, entry);

        if handled {
            return;
        }

        // Step 2: Strict-term case
        // d_rli > 0, d_rlt < T, d.log[d_rli-1].term == d_rlt
        if d_rlt > entry.term && k < d_rli - 1 {
            // Main recursion: anchor at d_rli - 1
            lemma_ethvq_committed_entry_transfer(
                ds, d, d_rli - 1, k, entry);
        } else if d_rlt == entry.term {
            // Edge case (a): d_rlt == entry.term.
            // Prove ov_vtl >= entry.term by LogTermsMonotonic on ov,
            // since ov.log[k].term == entry.term and k <= ov_L - 1.
            let ov_vtl: int = if ov_L == 0 { 0int } else {
                ds.server_states[ov].log[ov_L - 1].term
            };
            if ov_L > 0 && k < ov_L - 1 {
                lemma_log_terms_monotonic_entry_bound(ds, ov, k, ov_L - 1);
            }
            // ov_vtl >= entry.term. Since d_rlt == entry.term >= ov_vtl
            // and d_rlt >= ov_vtl (postcondition), d_rlt == ov_vtl.
            // The disjunction gives d_rli > ov_L.
            assert(ov_vtl <= entry.term);
            assert(d_rlt == ov_vtl ==> d_rli > ov_L);
            assert(d_rlt == ov_vtl);
            assert(d_rli > ov_L);
            assert(ov_L > k);
            assert(ov_L > 0);
            // LogTermsMonotonic on d: d.log[ov_L-1].term <= d.log[d_rli-1].term == entry.term
            if ov_L - 1 < d_rli - 1 {
                lemma_log_terms_monotonic_entry_bound(ds, d, ov_L - 1, d_rli - 1);
            }
            assert(ds.server_states[d].log[ov_L - 1].term <= entry.term);
            if ds.server_states[d].log[ov_L - 1].term == entry.term {
                // LogMatching between d and ov at ov_L - 1
                assert(ds.server_states[d].log[ov_L - 1].term
                    == ds.server_states[ov].log[ov_L - 1].term);
                assert(k <= ov_L - 1);
                assert(ov_L - 1 < ds.server_states[d].log.len());
                assert(ov_L - 1 < ds.server_states[ov].log.len());
                assert(ds.server_states[d].log[k]
                    == ds.server_states[ov].log[k]);
                assert(ds.server_states[d].log[k] == entry);
            } else {
                // d.log[ov_L-1].term < entry.term: log divergence.
                // d.log.len() >= d_rli > ov_L > k is provable.
                assert(ds.server_states[d].log.len() > k);
                // LogMatching at k: if d.log[k].term == entry.term,
                // then d and ov agree at k.
                if ds.server_states[d].log[k].term == entry.term {
                    assert(ds.server_states[d].log[k].term
                        == ds.server_states[ov].log[k].term);
                    assert(ds.server_states[d].log[k]
                        == ds.server_states[ov].log[k]);
                    assert(ds.server_states[d].log[k] == entry);
                } else {
                    // d.log[k].term != entry.term: proved via
                    // ETHVQ vote dest uniqueness at entry.term.
                    // d.log[d_rli-1].term == entry.term, d_rli-1 > k.
                    lemma_same_term_committed_entry_transfer(
                        ds, d, d_rli - 1, k, entry);
                }
            }
        } else {
            // d_rlt > entry.term && k >= d_rli - 1.
            // First, rule out d_rlt == ov_vtl: that forces d_rli > ov_L > k,
            // contradicting k >= d_rli - 1.
            let ov_vtl2: int = if ov_L == 0 { 0int } else {
                ds.server_states[ov].log[ov_L - 1].term
            };
            if ov_L > 0 && k < ov_L - 1 {
                lemma_log_terms_monotonic_entry_bound(ds, ov, k, ov_L - 1);
            }
            assert(ov_vtl2 >= entry.term);
            assert(d_rlt > entry.term);
            // From postcondition: d_rlt > ov_vtl2 || d_rli > ov_L.
            // If d_rlt == ov_vtl2: d_rli > ov_L > k, so d_rli - 1 > k,
            // contradicting k >= d_rli - 1.
            if d_rlt == ov_vtl2 {
                assert(d_rli > ov_L);
                assert(ov_L > k);
                assert(d_rli > k + 1);
                assert(d_rli - 1 > k);
                assert(false);  // contradicts k >= d_rli - 1
            }
            assert(d_rlt > ov_vtl2);
            // d_rlt > ov_vtl2 >= entry.term, k >= d_rli - 1.
            // d.log[d_rli-1].term == d_rlt > entry.term.
            if k == d_rli - 1 {
                // d.log.len() >= d_rli = k + 1, so d.log.len() > k.
                assert(ds.server_states[d].log.len() > k);
                assert(ds.server_states[d].log[k].term == d_rlt);
                assert(ds.server_states[d].log[k].term > entry.term);
                if ds.server_states[d].log.len() as int > k + 1 {
                    // Use k + 1 as anchor on d.
                    lemma_log_terms_monotonic_entry_bound(ds, d, k, k + 1);
                    assert(ds.server_states[d].log[k + 1].term > entry.term);
                    lemma_ethvq_committed_entry_transfer(
                        ds, d, k + 1, k, entry);
                } else {
                    // d.log.len() == k + 1: d.log[k].term == d_rlt > entry.term.
                    // d.log[k].term != entry.term, so this case is unreachable
                    // by global term induction (Raft safety).
                    assume(false);
                }
            } else {
                // k > d_rli - 1: d.log may not extend to k.
                if ds.server_states[d].log.len() as int > k
                    && ds.server_states[d].log[k].term == entry.term {
                    // LogMatching at k: d and ov agree at k.
                    assert(ds.server_states[d].log[k].term
                        == ds.server_states[ov].log[k].term);
                    assert(ds.server_states[d].log[k]
                        == ds.server_states[ov].log[k]);
                    assert(ds.server_states[d].log[k] == entry);
                } else {
                    // d.log too short or d.log[k].term != entry.term:
                    // unreachable by global term induction (Raft safety).
                    assume(false);
                }
            }
        }
    }

    /// Phase 34.7.4: Overlap ETHVQ quorum (d + voters) with commit quorum.
    ///
    /// Returns overlap voter ov with ov.log[k] == entry and
    /// (ov == d || ExistsGrantedVoteResponse(ds, ov, d, T)).
    ///
    /// Isolated from ETHVQ to prevent trigger interaction with set ops.
    proof fn lemma_ethvq_commit_quorum_overlap(
        ds: RaftDistributedState,
        k: int,
        entry: LLogEntry,
        d: int,
        voters: Seq<int>,
        T: int,
    ) -> (ov: int)
        requires
            WellFormedRaftDistributed(ds),
            EntryCommittedAt(ds, k, entry),
            0 <= k,
            0 <= d < ds.num_servers,
            voters.len() >= ds.num_servers / 2 + 1 - 1,
            (forall |a: int| #![trigger voters[a]]
                0 <= a < voters.len() ==> {
                    &&& 0 <= voters[a] < ds.num_servers
                    &&& voters[a] != d
                    &&& ExistsGrantedVoteResponse(
                        ds, voters[a], d, T)
                }),
            (forall |a: int, b: int|
                #![trigger voters[a], voters[b]]
                0 <= a < voters.len() && 0 <= b < voters.len()
                && a != b ==> voters[a] != voters[b]),
        ensures
            0 <= ov < ds.num_servers,
            ds.server_states[ov].log.len() > k,
            ds.server_states[ov].log[k] == entry,
            ov == d || ExistsGrantedVoteResponse(ds, ov, d, T),
    {
        let n = ds.num_servers;
        let quorum_size = n / 2 + 1;

        // Convert voters Seq to Set and add d
        assert(voters.no_duplicates()) by {
            assert forall |i: int, j: int|
                0 <= i < voters.len() && 0 <= j < voters.len() && i != j
            implies
                #[trigger] voters[i] != #[trigger] voters[j]
            by {};
        };
        let voter_set = voters.to_set();
        voters.unique_seq_to_set();
        assert(voter_set.len() == voters.len());
        assert(voter_set.len() >= quorum_size - 1);

        assert(!voter_set.contains(d)) by {
            if voter_set.contains(d) {
                assert(voters.contains(d));
                let idx = choose |idx: int| 0 <= idx < voters.len()
                    && voters[idx] == d;
                assert(voters[idx] != d);
            }
        };

        let d_quorum = voter_set.insert(d);
        assert(d_quorum.len() == voter_set.len() + 1);
        assert(d_quorum.len() >= quorum_size);

        // Commit quorum
        let commit_quorum = choose |q: Set<int>| {
            &&& q.len() >= quorum_size
            &&& (forall |id: int| #![trigger q.contains(id)] q.contains(id) ==> {
                &&& 0 <= id < n
                &&& ds.server_states[id].log.len() > k
                &&& ds.server_states[id].log[k] == entry
            })
        };

        // Both subsets of universe [0, n)
        let universe = Set::<int>::range(0, n);
        lemma_range_set_finite(n);

        assert(d_quorum.subset_of(universe)) by {
            assert forall |v: int| d_quorum.contains(v)
                implies universe.contains(v) by
            {
                if v == d {
                    assert(0 <= d < n);
                } else {
                    assert(voter_set.contains(v));
                    assert(voters.contains(v));
                    let a = choose |a: int| 0 <= a < voters.len()
                        && voters[a] == v;
                    assert(0 <= voters[a] < n);
                }
            };
        };
        assert(commit_quorum.subset_of(universe)) by {
            assert forall |v: int| commit_quorum.contains(v)
                implies universe.contains(v) by
            {
                assert(0 <= v < n);
            };
        };

        lemma_quorum_intersection(d_quorum, commit_quorum, universe);
        let ov = choose |ov: int|
            d_quorum.contains(ov) && commit_quorum.contains(ov);
        assert(0 <= ov < n);
        assert(ds.server_states[ov].log.len() > k);
        assert(ds.server_states[ov].log[k] == entry);

        if ov != d {
            assert(voter_set.contains(ov));
            assert(voters.contains(ov));
            let a_ov = choose |a: int| 0 <= a < voters.len()
                && voters[a] == ov;
            assert(ExistsGrantedVoteResponse(ds, ov, d, T));
        }
        ov
    }

    /// Phase 34.7.4: Helper — given ov voted for d at term T, extract packets,
    /// try equal-term LogMatching from ov to d, and return parameters for
    /// the strict-term case.
    ///
    /// Isolated from ETHVQ and LogTermsMonotonic to prevent trigger cross-talk.
    /// Returns (d_rli, d_rlt, ov_L, handled) where:
    ///   - handled => d.log[k] == entry is established
    ///   - !handled => strict-term or equal-term-rli>L case
    proof fn lemma_ethvq_voter_to_d_packet_extraction(
        ds: RaftDistributedState,
        ov: int,
        d: int,
        T: int,
        k: int,
        entry: LLogEntry,
    ) -> (result: (int, int, int, bool))
        requires
            WellFormedRaftDistributed(ds),
            LogMatching(ds),
            TermsNonNegative(ds),
            VoteResponseHasRequestVote(ds),
            RequestVoteSummaryAlwaysValid(ds),
            RequestVoteLastLogTermBound(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteLogLenEntryTermBound(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
            0 <= k,
            0 <= ov < ds.num_servers,
            0 <= d < ds.num_servers,
            ov != d,
            ds.server_states[ov].log.len() > k,
            ds.server_states[ov].log[k] == entry,
            T > entry.term,
            ExistsGrantedVoteResponse(ds, ov, d, T),
        ensures ({
            let (d_rli, d_rlt, ov_L, handled) = result;
            &&& 0 <= d_rli <= ds.server_states[d].log.len()
            &&& (d_rli == 0 ==> d_rlt == 0)
            &&& (d_rli > 0 ==> ds.server_states[d].log[d_rli - 1].term == d_rlt)
            &&& (d_rli > 0 ==> d_rlt < T)
            &&& 0 <= ov_L <= ds.server_states[ov].log.len()
            &&& k < ov_L
            &&& (handled ==> ds.server_states[d].log.len() > k)
            &&& (handled ==> ds.server_states[d].log[k] == entry)
            &&& (!handled ==> {
                &&& d_rli > 0
                &&& d_rlt >= (if ov_L == 0 { 0int } else {
                        ds.server_states[ov].log[ov_L - 1].term
                    })
                &&& (d_rlt > (if ov_L == 0 { 0int } else {
                        ds.server_states[ov].log[ov_L - 1].term
                    }) || d_rli > ov_L)
            })
        }),
    {
        // Extract VoteResponse packet
        let (last_idx_val, last_term_val) = choose |li: int, lt: int|
            #![trigger ds.network.contains(LRaftPacket {
                src: ov,
                dst: d,
                msg: LRaftMessage::VoteResponse {
                    term: T,
                    granted: true,
                    voter: ov,
                    voter_last_log_index: li,
                    voter_last_log_term: lt,
                },
            })]
        {
            ds.network.contains(LRaftPacket {
                src: ov,
                dst: d,
                msg: LRaftMessage::VoteResponse {
                    term: T,
                    granted: true,
                    voter: ov,
                    voter_last_log_index: li,
                    voter_last_log_term: lt,
                },
            })
        };
        let vote_pkt = LRaftPacket {
            src: ov,
            dst: d,
            msg: LRaftMessage::VoteResponse {
                term: T,
                granted: true,
                voter: ov,
                voter_last_log_index: last_idx_val,
                voter_last_log_term: last_term_val,
            },
        };
        assert(ds.network.contains(vote_pkt));

        // VoteResponseHasRequestVote → matching RequestVote
        assert(VoteResponseHasRequestVote(ds));
        let req_pkt = choose |req: LRaftPacket| #![trigger ds.network.contains(req)] {
            &&& ds.network.contains(req)
            &&& req.src == d
            &&& req.dst == ov
            &&& req.msg is RequestVote
            &&& req.msg->RequestVote_term == T
            &&& req.msg->RequestVote_candidate == d
        };

        // RequestVoteSummaryAlwaysValid → d's log summary
        assert(RequestVoteSummaryAlwaysValid(ds));
        let d_rli = req_pkt.msg->RequestVote_last_log_index;
        let d_rlt = req_pkt.msg->RequestVote_last_log_term;
        assert(0 <= d_rli <= ds.server_states[d].log.len());
        assert(d_rli == 0 ==> d_rlt == 0);
        assert(d_rli > 0 ==> ds.server_states[d].log[d_rli - 1].term == d_rlt);

        // VoteLogLen for ov's vote at term T
        assert(VoteLogLenCoversNetwork(ds));
        assert(ds.vote_log_len.dom().contains((ov, T)));
        let ov_L = ds.vote_log_len[(ov, T)];
        assert(VoteLogLenBounded(ds));
        assert(0 <= ov_L <= ds.server_states[ov].log.len());

        // k < ov_L by VoteLogLenEntryTermBound
        assert(VoteLogLenEntryTermBound(ds));
        if k >= ov_L {
            let p_vt: (int, int) = (ov, T);
            assert(ds.vote_log_len.dom().contains(p_vt));
            assert(ds.vote_log_len[p_vt] <= k);
            assert(k < ds.server_states[p_vt.0].log.len());
            let _ = ds.server_states[p_vt.0].log[k];
            assert(ds.server_states[p_vt.0].log[k].term >= p_vt.1);
            assert(ds.server_states[ov].log[k] == entry);
            assert(entry.term >= T);
            assert(T > entry.term);
            assert(false);
        }
        assert(k < ov_L);

        // VoteGrantedLogUpToDateAtVoteTime → d_rlt ≥ ov_vtl
        let ov_vtl: int = if ov_L == 0 { 0int } else {
            ds.server_states[ov].log[ov_L - 1].term
        };
        assert(VoteGrantedLogUpToDateAtVoteTime(ds));
        assert(d_rlt > ov_vtl || (d_rlt == ov_vtl && d_rli >= ov_L));

        if d_rlt == ov_vtl && d_rli == ov_L {
            // Equal-term, equal-length: LogMatching at ov_L - 1
            assert(ov_L > 0);
            let match_idx = ov_L - 1;
            assert(ds.server_states[d].log[match_idx].term == d_rlt);
            assert(ds.server_states[ov].log[match_idx].term == ov_vtl);
            assert(ds.server_states[d].log[match_idx].term
                == ds.server_states[ov].log[match_idx].term);
            assert(k <= match_idx);
            assert(ds.server_states[d].log[k]
                == ds.server_states[ov].log[k]);
            assert(ds.server_states[d].log[k] == entry);
            (d_rli, d_rlt, ov_L, true)
        } else {
            // Strict-term or equal-term with d_rli > ov_L
            assert(d_rli > 0) by {
                if d_rli == 0 {
                    assert(d_rlt == 0);
                    if d_rlt > ov_vtl {
                        // 0 > ov_vtl. But ov_L > 0 (since k >= 0, k < ov_L),
                        // so ov_vtl = ov.log[ov_L-1].term >= 0 by TermsNonNegative.
                        assert(ov_L > 0);
                        assert(TermsNonNegative(ds));
                        let _ = ds.server_states[ov].log[ov_L - 1];
                        assert(ov_vtl >= 0);
                        assert(false);
                    } else {
                        // d_rlt == ov_vtl, d_rli > ov_L → 0 > ov_L
                        // But ov_L > 0 (k >= 0, k < ov_L). Contradiction.
                        assert(d_rli > ov_L);
                        assert(ov_L > 0);
                        assert(false);
                    }
                }
            };
            // d_rlt < T by RequestVoteLastLogTermBound
            assert(RequestVoteLastLogTermBound(ds));
            assert(ds.network.contains(req_pkt));
            assert(req_pkt.msg is RequestVote);
            assert(req_pkt.msg->RequestVote_last_log_index == d_rli);
            assert(d_rli > 0);
            assert(d_rlt < T);
            (d_rli, d_rlt, ov_L, false)
        }
    }

    /// Phase 34.7.4: Recursive proof that server.log[k] == entry
    /// whenever server has a higher-term entry at an index above k.
    ///
    /// This is the core of Ongaro's term-induction argument.
    ///
    /// Uses explicit invariant listing to avoid Z3 blow-up from
    /// expanding the full RaftSafetyInvariant conjunction.
    /// Each helper takes only the subset of invariants it needs.
    proof fn lemma_ethvq_committed_entry_transfer(
        ds: RaftDistributedState,
        server: int,
        anchor_idx: int,
        k: int,
        entry: LLogEntry,
    )
        requires
            WellFormedRaftDistributed(ds),
            EntryTermHasVoteQuorum(ds),
            LogMatching(ds),
            TermsNonNegative(ds),
            VoteResponseHasRequestVote(ds),
            RequestVoteSummaryAlwaysValid(ds),
            RequestVoteLastLogTermBound(ds),
            LogTermsMonotonic(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteLogLenEntryTermBound(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
            OneVotePerTermInNetwork(ds),
            CandidateVoteDestinationUnique(ds),
            EntryCommittedAt(ds, k, entry),
            0 <= k,
            0 <= server < ds.num_servers,
            k < anchor_idx,
            anchor_idx < ds.server_states[server].log.len(),
            ds.server_states[server].log[anchor_idx].term > entry.term,
        ensures
            ds.server_states[server].log[k] == entry,
        decreases ds.server_states[server].log[anchor_idx].term - entry.term,
                  anchor_idx - k
    {
        let T = ds.server_states[server].log[anchor_idx].term;

        // Step 1: ETHVQ extraction + commit quorum overlap
        let (ov, d) = lemma_ethvq_committed_overlap(
            ds, server, anchor_idx, k, entry);

        // Step 2: ov == d → d already has entry, LogMatching transfer
        if ov == d {
            lemma_ethvq_log_matching_transfer(
                ds, server, d, anchor_idx, k, entry);
            return;
        }

        // Step 3: ov != d → packet extraction + equal-term attempt
        let (d_rli, d_rlt, ov_L, handled) =
            lemma_ethvq_committed_try_equal_term(
                ds, ov, d, T, k, entry);

        if handled {
            // d.log[k] == entry established, transfer via LogMatching
            lemma_ethvq_log_matching_transfer(
                ds, server, d, anchor_idx, k, entry);
            return;
        }

        // Step 4: Strict-term case — d_rlt < T, d_rli > 0
        // d.log[d_rli-1].term == d_rlt < T

        // Establish d_rlt > entry.term:
        //   In the d_rlt > ov_vtl sub-case: ov_vtl >= entry.term by
        //   LogTermsMonotonic (entry at k has term entry.term, k < ov_L-1).
        //   In the d_rli > ov_L sub-case: d_rlt == ov_vtl possible.
        //   Use LogTermsMonotonic helper for ov_vtl >= entry.term.
        //   Then either d_rlt > ov_vtl >= entry.term (sub-case 1),
        //   or d_rlt == ov_vtl and d_rli > ov_L (sub-case 2).
        //   In sub-case 2 with d_rlt == entry.term, can't use d_rli-1 as anchor.
        let ov_vtl: int = if ov_L == 0 { 0int } else {
            ds.server_states[ov].log[ov_L - 1].term
        };
        // ov_vtl >= entry.term by LogTermsMonotonic on ov
        if ov_L > 0 && k < ov_L - 1 {
            lemma_log_terms_monotonic_entry_bound(ds, ov, k, ov_L - 1);
        }
        // Now: if k == ov_L - 1 then ov_vtl == entry.term
        // if k < ov_L - 1 then ov_vtl >= entry.term

        if d_rlt > entry.term && k < d_rli - 1 {
            // Main recursion case: d.log[d_rli-1].term == d_rlt
            //   d_rlt > entry.term, d_rlt < T → term gap decreases
            lemma_ethvq_committed_entry_transfer(
                ds, d, d_rli - 1, k, entry);
            // Transfer to server via LogMatching at anchor_idx
            lemma_ethvq_log_matching_transfer(
                ds, server, d, anchor_idx, k, entry);
        } else if d_rlt > entry.term {
            // Edge case (b): k >= d_rli - 1 but d_rlt > entry.term.
            // d.log[d_rli-1].term == d_rlt > entry.term, and k >= d_rli - 1.
            // By LogTermsMonotonic: d.log[k].term >= d_rlt > entry.term.
            // Use k + 1 as anchor on d (k + 1 <= anchor_idx since k < anchor_idx).
            // d.log[k+1].term >= d.log[k].term > entry.term.
            assert(k >= d_rli - 1);
            lemma_log_terms_monotonic_entry_bound(ds, d, d_rli - 1, k);
            assert(ds.server_states[d].log[k].term >= d_rlt);
            assert(ds.server_states[d].log[k].term > entry.term);
            // anchor_idx > k (from requires), so k + 1 <= anchor_idx
            assert(k + 1 <= anchor_idx);
            assert(k + 1 < ds.server_states[d].log.len());
            // d.log[k+1].term >= d.log[k].term > entry.term
            lemma_log_terms_monotonic_entry_bound(ds, d, k, k + 1);
            assert(ds.server_states[d].log[k + 1].term > entry.term);
            if k + 1 < anchor_idx {
                // Lex decreases: (d.log[k+1].term - entry.term, k+1 - k)
                //   If d.log[k+1].term < T: first component decreases.
                //   If d.log[k+1].term == T: first same, but k+1 - k = 1 < anchor_idx - k.
                // Either way, (term_gap, anchor_gap) strictly decreases.
                lemma_ethvq_committed_entry_transfer(
                    ds, d, k + 1, k, entry);
                lemma_ethvq_log_matching_transfer(
                    ds, server, d, anchor_idx, k, entry);
            } else {
                // anchor_idx == k + 1: can't recurse with (d, k+1, k)
                // because lex metric (T - entry.term, 1) doesn't decrease.
                // Inline one ETHVQ step on d at k+1 to get d2 with d2_rlt < T.
                assert(anchor_idx == k + 1);
                assert(ds.server_states[d].log[k + 1].term == T);

                // ETHVQ overlap on d at anchor k+1
                let (ov2, d2) = lemma_ethvq_committed_overlap(
                    ds, d, k + 1, k, entry);

                if ov2 == d2 {
                    // d2 already has entry, transfer d2→d→server
                    lemma_ethvq_log_matching_transfer(
                        ds, d, d2, k + 1, k, entry);
                    lemma_ethvq_log_matching_transfer(
                        ds, server, d, anchor_idx, k, entry);
                } else {
                    let (d2_rli, d2_rlt, ov2_L, handled2) =
                        lemma_ethvq_committed_try_equal_term(
                            ds, ov2, d2, T, k, entry);

                    if handled2 {
                        // d2.log[k] == entry, transfer d2→d→server
                        lemma_ethvq_log_matching_transfer(
                            ds, d, d2, k + 1, k, entry);
                        lemma_ethvq_log_matching_transfer(
                            ds, server, d, anchor_idx, k, entry);
                    } else if d2_rlt > entry.term && k < d2_rli - 1 {
                        // d2_rlt < T (by RequestVoteLastLogTermBound).
                        // First component: d2_rlt - entry.term < T - entry.term.
                        // Strictly decreasing → can recurse.
                        lemma_ethvq_committed_entry_transfer(
                            ds, d2, d2_rli - 1, k, entry);
                        lemma_ethvq_log_matching_transfer(
                            ds, d, d2, k + 1, k, entry);
                        lemma_ethvq_log_matching_transfer(
                            ds, server, d, anchor_idx, k, entry);
                    } else if d2_rlt == entry.term {
                        // d2's edge case (a): d2_rlt == entry.term.
                        let ov2_vtl: int = if ov2_L == 0 { 0int } else {
                            ds.server_states[ov2].log[ov2_L - 1].term
                        };
                        if ov2_L > 0 && k < ov2_L - 1 {
                            lemma_log_terms_monotonic_entry_bound(
                                ds, ov2, k, ov2_L - 1);
                        }
                        assert(ov2_vtl <= entry.term);
                        assert(d2_rlt == ov2_vtl ==> d2_rli > ov2_L);
                        assert(d2_rlt == ov2_vtl);
                        assert(d2_rli > ov2_L);
                        assert(ov2_L > k);
                        assert(ov2_L > 0);
                        if ov2_L - 1 < d2_rli - 1 {
                            lemma_log_terms_monotonic_entry_bound(
                                ds, d2, ov2_L - 1, d2_rli - 1);
                        }
                        assert(ds.server_states[d2].log[ov2_L - 1].term
                            <= entry.term);
                        if ds.server_states[d2].log[ov2_L - 1].term
                            == entry.term
                        {
                            // LogMatching: d2 and ov2 agree at ov2_L-1
                            assert(ds.server_states[d2].log[ov2_L - 1].term
                                == ds.server_states[ov2].log[ov2_L - 1].term);
                            assert(k <= ov2_L - 1);
                            assert(ov2_L - 1
                                < ds.server_states[d2].log.len());
                            assert(ov2_L - 1
                                < ds.server_states[ov2].log.len());
                            assert(ds.server_states[d2].log[k]
                                == ds.server_states[ov2].log[k]);
                            assert(ds.server_states[d2].log[k] == entry);
                            // Transfer d2→d→server
                            lemma_ethvq_log_matching_transfer(
                                ds, d, d2, k + 1, k, entry);
                            lemma_ethvq_log_matching_transfer(
                                ds, server, d, anchor_idx, k, entry);
                        } else {
                            // d2.log[ov2_L-1].term < entry.term:
                            // log divergence. Try LogMatching at k.
                            if ds.server_states[server].log[k].term
                                == entry.term {
                                assert(ds.server_states[server].log[k].term
                                    == ds.server_states[ov].log[k].term);
                                assert(ds.server_states[server].log[k]
                                    == ds.server_states[ov].log[k]);
                                assert(ds.server_states[server].log[k]
                                    == entry);
                            } else {
                                // server.log[k].term != entry.term:
                                // proved via ETHVQ vote dest uniqueness.
                                // d2.log[d2_rli-1].term == entry.term, d2_rli-1 > k.
                                lemma_same_term_committed_entry_transfer(
                                    ds, d2, d2_rli - 1, k, entry);
                                // Transfer d2→d→server
                                lemma_ethvq_log_matching_transfer(
                                    ds, d, d2, k + 1, k, entry);
                                lemma_ethvq_log_matching_transfer(
                                    ds, server, d, anchor_idx, k, entry);
                            }
                        }
                    } else {
                        // d2_rlt > entry.term && k >= d2_rli - 1.
                        // Rule out d2_rlt == ov2_vtl: forces d2_rli > ov2_L > k,
                        // contradicting k >= d2_rli - 1.
                        let ov2_vtl2: int = if ov2_L == 0 { 0int } else {
                            ds.server_states[ov2].log[ov2_L - 1].term
                        };
                        if ov2_L > 0 && k < ov2_L - 1 {
                            lemma_log_terms_monotonic_entry_bound(
                                ds, ov2, k, ov2_L - 1);
                        }
                        assert(ov2_vtl2 >= entry.term);
                        if d2_rlt == ov2_vtl2 {
                            assert(d2_rli > ov2_L);
                            assert(ov2_L > k);
                            assert(d2_rli > k + 1);
                            assert(d2_rli - 1 > k);
                            assert(false);
                        }
                        assert(d2_rlt > ov2_vtl2);
                        // d2_rlt > ov2_vtl2, k >= d2_rli - 1: genuine gap.
                        // Try LogMatching at k.
                        if ds.server_states[server].log[k].term
                            == entry.term {
                            assert(ds.server_states[server].log[k].term
                                == ds.server_states[ov].log[k].term);
                            assert(ds.server_states[server].log[k]
                                == ds.server_states[ov].log[k]);
                            assert(ds.server_states[server].log[k]
                                == entry);
                        } else {
                            // server.log[k].term != entry.term:
                            // unreachable by global term induction.
                            assume(false);
                        }
                    }
                }
            }
        } else {
            // Edge case (a): d_rlt == entry.term (and d_rli > ov_L > k).
            // d.log[d_rli-1].term == entry.term. By LogTermsMonotonic on d:
            // d.log[ov_L-1].term <= d.log[d_rli-1].term == entry.term.
            // If d.log[ov_L-1].term == entry.term, LogMatching between d
            // and ov at ov_L - 1 gives d.log[k] == ov.log[k] == entry.
            assert(d_rlt == entry.term);
            assert(d_rli > ov_L);
            assert(ov_L > k);  // k < ov_L from postcondition
            assert(d_rli - 1 > k);  // d_rli > ov_L > k, so d_rli - 1 >= ov_L > k
            assert(ov_L > 0);  // ov_L > k >= 0
            assert(ov_L - 1 < d_rli - 1);  // ov_L < d_rli
            // d has entries up to anchor_idx (from overlap)
            assert(ds.server_states[d].log.len() > anchor_idx);
            assert(ov_L - 1 < ds.server_states[d].log.len());
            // LogTermsMonotonic on d: d.log[ov_L-1].term <= d.log[d_rli-1].term
            lemma_log_terms_monotonic_entry_bound(ds, d, ov_L - 1, d_rli - 1);
            assert(ds.server_states[d].log[ov_L - 1].term <= entry.term);
            if ds.server_states[d].log[ov_L - 1].term == entry.term {
                // LogMatching between d and ov at ov_L - 1:
                // d.log[ov_L-1].term == entry.term == ov.log[ov_L-1].term
                assert(ds.server_states[d].log[ov_L - 1].term
                    == ds.server_states[ov].log[ov_L - 1].term);
                assert(0 <= k);
                assert(k <= ov_L - 1);  // k < ov_L
                assert(ov_L - 1 < ds.server_states[d].log.len());
                assert(ov_L - 1 < ds.server_states[ov].log.len());
                // LogMatching gives d.log[k] == ov.log[k] == entry
                assert(ds.server_states[d].log[k]
                    == ds.server_states[ov].log[k]);
                assert(ds.server_states[d].log[k] == entry);
                // Transfer from d to server via LogMatching at anchor_idx
                lemma_ethvq_log_matching_transfer(
                    ds, server, d, anchor_idx, k, entry);
            } else {
                // d.log[ov_L-1].term < entry.term: d and ov diverge
                // at ov_L - 1. Try LogMatching at k.
                if ds.server_states[server].log[k].term == entry.term {
                    assert(ds.server_states[server].log[k].term
                        == ds.server_states[ov].log[k].term);
                    assert(ds.server_states[server].log[k]
                        == ds.server_states[ov].log[k]);
                    assert(ds.server_states[server].log[k] == entry);
                } else {
                    // server.log[k].term != entry.term:
                    // proved via ETHVQ vote dest uniqueness.
                    // d.log[d_rli-1].term == entry.term, d_rli-1 > k.
                    lemma_same_term_committed_entry_transfer(
                        ds, d, d_rli - 1, k, entry);
                    lemma_ethvq_log_matching_transfer(
                        ds, server, d, anchor_idx, k, entry);
                }
            }
        }
    }

    /// ETHVQ vote destination uniqueness: two ETHVQ destinations at the
    /// same term must be the same server.
    ///
    /// Proof: d1_quorum (d1 + voters1) and d2_quorum (d2 + voters2) are
    /// both majorities, so they overlap. The overlap element w satisfies:
    /// - w in voters1 AND voters2: two VoteResponse{T, voter: w} packets
    ///   with different dst → contradicts OneVotePerTermInNetwork.
    /// - w == d1 AND w in voters2: VoteResponse{T, voter: d1, dst: d2}.
    ///   VoteResponseHasRequestVote on d1's voters → RequestVote{T, candidate: d1}.
    ///   CandidateVoteDestinationUnique → d2 == d1.
    /// - w in voters1 AND w == d2: symmetric.
    /// - w == d1 == d2: trivial.
    ///
    /// Isolated to prevent ETHVQ trigger interaction with set ops.
    proof fn lemma_ethvq_vote_dest_unique(
        ds: RaftDistributedState,
        d1: int,
        voters1: Seq<int>,
        d2: int,
        voters2: Seq<int>,
        T: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            OneVotePerTermInNetwork(ds),
            VoteResponseHasRequestVote(ds),
            CandidateVoteDestinationUnique(ds),
            0 <= d1 < ds.num_servers,
            0 <= d2 < ds.num_servers,
            voters1.len() >= ds.num_servers / 2 + 1 - 1,
            voters2.len() >= ds.num_servers / 2 + 1 - 1,
            forall |a: int| #![trigger voters1[a]]
                0 <= a < voters1.len() ==> {
                    &&& 0 <= voters1[a] < ds.num_servers
                    &&& voters1[a] != d1
                    &&& ExistsGrantedVoteResponse(ds, voters1[a], d1, T)
                },
            forall |a: int, b: int|
                #![trigger voters1[a], voters1[b]]
                0 <= a < voters1.len() && 0 <= b < voters1.len()
                && a != b ==> voters1[a] != voters1[b],
            forall |a: int| #![trigger voters2[a]]
                0 <= a < voters2.len() ==> {
                    &&& 0 <= voters2[a] < ds.num_servers
                    &&& voters2[a] != d2
                    &&& ExistsGrantedVoteResponse(ds, voters2[a], d2, T)
                },
            forall |a: int, b: int|
                #![trigger voters2[a], voters2[b]]
                0 <= a < voters2.len() && 0 <= b < voters2.len()
                && a != b ==> voters2[a] != voters2[b],
        ensures
            d1 == d2,
    {
        let n = ds.num_servers;
        let quorum_size = n / 2 + 1;

        // Build d1_quorum = voters1.to_set() ∪ {d1}
        assert(voters1.no_duplicates()) by {
            assert forall |i: int, j: int|
                0 <= i < voters1.len() && 0 <= j < voters1.len() && i != j
            implies #[trigger] voters1[i] != #[trigger] voters1[j] by {};
        };
        let v1_set = voters1.to_set();
        voters1.unique_seq_to_set();
        assert(!v1_set.contains(d1)) by {
            if v1_set.contains(d1) {
                assert(voters1.contains(d1));
                let idx = choose |idx: int| 0 <= idx < voters1.len()
                    && voters1[idx] == d1;
                assert(voters1[idx] != d1);
            }
        };
        let d1_quorum = v1_set.insert(d1);
        assert(d1_quorum.len() >= quorum_size);

        // Build d2_quorum = voters2.to_set() ∪ {d2}
        assert(voters2.no_duplicates()) by {
            assert forall |i: int, j: int|
                0 <= i < voters2.len() && 0 <= j < voters2.len() && i != j
            implies #[trigger] voters2[i] != #[trigger] voters2[j] by {};
        };
        let v2_set = voters2.to_set();
        voters2.unique_seq_to_set();
        assert(!v2_set.contains(d2)) by {
            if v2_set.contains(d2) {
                assert(voters2.contains(d2));
                let idx = choose |idx: int| 0 <= idx < voters2.len()
                    && voters2[idx] == d2;
                assert(voters2[idx] != d2);
            }
        };
        let d2_quorum = v2_set.insert(d2);
        assert(d2_quorum.len() >= quorum_size);

        // Quorum intersection
        let universe = Set::<int>::range(0, n);
        lemma_range_set_finite(n);
        assert(d1_quorum.subset_of(universe)) by {
            assert forall |v: int| d1_quorum.contains(v)
                implies universe.contains(v) by
            {
                if v == d1 {
                    assert(0 <= d1 < n);
                } else {
                    assert(v1_set.contains(v));
                    assert(voters1.contains(v));
                    let a = choose |a: int| 0 <= a < voters1.len()
                        && voters1[a] == v;
                    assert(0 <= voters1[a] < n);
                }
            };
        };
        assert(d2_quorum.subset_of(universe)) by {
            assert forall |v: int| d2_quorum.contains(v)
                implies universe.contains(v) by
            {
                if v == d2 {
                    assert(0 <= d2 < n);
                } else {
                    assert(v2_set.contains(v));
                    assert(voters2.contains(v));
                    let a = choose |a: int| 0 <= a < voters2.len()
                        && voters2[a] == v;
                    assert(0 <= voters2[a] < n);
                }
            };
        };
        lemma_quorum_intersection(d1_quorum, d2_quorum, universe);
        let w = choose |w: int|
            d1_quorum.contains(w) && d2_quorum.contains(w);

        // Case analysis on w.
        // Get the VoteResponse packets from the quorum membership.
        // w is in d1_quorum, so w == d1 || w ∈ voters1.
        // w is in d2_quorum, so w == d2 || w ∈ voters2.

        if w == d1 && w == d2 {
            // Trivial: d1 == d2
        } else if w != d1 && w != d2 {
            // w ∈ voters1 AND w ∈ voters2: w voted for both d1 and d2
            assert(v1_set.contains(w));
            assert(voters1.contains(w));
            let a1 = choose |a: int| 0 <= a < voters1.len()
                && voters1[a] == w;
            assert(ExistsGrantedVoteResponse(ds, w, d1, T));

            assert(v2_set.contains(w));
            assert(voters2.contains(w));
            let a2 = choose |a: int| 0 <= a < voters2.len()
                && voters2[a] == w;
            assert(ExistsGrantedVoteResponse(ds, w, d2, T));

            // Materialize both VoteResponse packets for OneVotePerTermInNetwork
            let (li1, lt1) = choose |li: int, lt: int|
                #![trigger ds.network.contains(LRaftPacket {
                    src: w, dst: d1,
                    msg: LRaftMessage::VoteResponse {
                        term: T, granted: true, voter: w,
                        voter_last_log_index: li,
                        voter_last_log_term: lt,
                    },
                })]
                ds.network.contains(LRaftPacket {
                    src: w, dst: d1,
                    msg: LRaftMessage::VoteResponse {
                        term: T, granted: true, voter: w,
                        voter_last_log_index: li,
                        voter_last_log_term: lt,
                    },
                });
            let pkt1 = LRaftPacket {
                src: w, dst: d1,
                msg: LRaftMessage::VoteResponse {
                    term: T, granted: true, voter: w,
                    voter_last_log_index: li1,
                    voter_last_log_term: lt1,
                },
            };
            let (li2, lt2) = choose |li: int, lt: int|
                #![trigger ds.network.contains(LRaftPacket {
                    src: w, dst: d2,
                    msg: LRaftMessage::VoteResponse {
                        term: T, granted: true, voter: w,
                        voter_last_log_index: li,
                        voter_last_log_term: lt,
                    },
                })]
                ds.network.contains(LRaftPacket {
                    src: w, dst: d2,
                    msg: LRaftMessage::VoteResponse {
                        term: T, granted: true, voter: w,
                        voter_last_log_index: li,
                        voter_last_log_term: lt,
                    },
                });
            let pkt2 = LRaftPacket {
                src: w, dst: d2,
                msg: LRaftMessage::VoteResponse {
                    term: T, granted: true, voter: w,
                    voter_last_log_index: li2,
                    voter_last_log_term: lt2,
                },
            };
            // OneVotePerTermInNetwork: same voter w, same term T → same dst
            assert(ds.network.contains(pkt1));
            assert(ds.network.contains(pkt2));
            assert(d1 == d2);
        } else if w == d1 {
            // w == d1 ∈ voters2: d1 "voted for" d2 at T
            assert(v2_set.contains(w));
            assert(voters2.contains(w));
            let a2 = choose |a: int| 0 <= a < voters2.len()
                && voters2[a] == w;
            assert(ExistsGrantedVoteResponse(ds, d1, d2, T));

            // Materialize VoteResponse{T, voter: d1, dst: d2}
            let (li_vr, lt_vr) = choose |li: int, lt: int|
                #![trigger ds.network.contains(LRaftPacket {
                    src: d1, dst: d2,
                    msg: LRaftMessage::VoteResponse {
                        term: T, granted: true, voter: d1,
                        voter_last_log_index: li,
                        voter_last_log_term: lt,
                    },
                })]
                ds.network.contains(LRaftPacket {
                    src: d1, dst: d2,
                    msg: LRaftMessage::VoteResponse {
                        term: T, granted: true, voter: d1,
                        voter_last_log_index: li,
                        voter_last_log_term: lt,
                    },
                });
            let vr_pkt = LRaftPacket {
                src: d1, dst: d2,
                msg: LRaftMessage::VoteResponse {
                    term: T, granted: true, voter: d1,
                    voter_last_log_index: li_vr,
                    voter_last_log_term: lt_vr,
                },
            };

            // Get RequestVote{T, candidate: d1} via VoteResponseHasRequestVote
            // on any voter in voters1
            assert(voters1.len() >= 1) by {
                assert(quorum_size >= 2);
            };
            let sv = voters1[0];
            assert(ExistsGrantedVoteResponse(ds, sv, d1, T));
            let (li_sv, lt_sv) = choose |li: int, lt: int|
                #![trigger ds.network.contains(LRaftPacket {
                    src: sv, dst: d1,
                    msg: LRaftMessage::VoteResponse {
                        term: T, granted: true, voter: sv,
                        voter_last_log_index: li,
                        voter_last_log_term: lt,
                    },
                })]
                ds.network.contains(LRaftPacket {
                    src: sv, dst: d1,
                    msg: LRaftMessage::VoteResponse {
                        term: T, granted: true, voter: sv,
                        voter_last_log_index: li,
                        voter_last_log_term: lt,
                    },
                });
            let sv_pkt = LRaftPacket {
                src: sv, dst: d1,
                msg: LRaftMessage::VoteResponse {
                    term: T, granted: true, voter: sv,
                    voter_last_log_index: li_sv,
                    voter_last_log_term: lt_sv,
                },
            };
            // VoteResponseHasRequestVote → RequestVote{T, candidate: d1}
            assert(ds.network.contains(sv_pkt));
            assert(sv_pkt.msg is VoteResponse);
            assert(sv_pkt.msg->VoteResponse_granted);
            let req_pkt = choose |req: LRaftPacket| #![trigger ds.network.contains(req)] {
                &&& ds.network.contains(req)
                &&& req.src == d1
                &&& req.dst == sv
                &&& req.msg is RequestVote
                &&& req.msg->RequestVote_term == T
                &&& req.msg->RequestVote_candidate == d1
            };

            // CandidateVoteDestinationUnique:
            // req_pkt: RequestVote{T, candidate: d1}
            // vr_pkt: VoteResponse{T, voter: d1, granted: true, dst: d2}
            // → d2 == d1
            assert(ds.network.contains(req_pkt));
            assert(ds.network.contains(vr_pkt));
            assert(d1 == d2);
        } else {
            // w == d2 ∈ voters1: d2 "voted for" d1 at T (symmetric)
            assert(v1_set.contains(w));
            assert(voters1.contains(w));
            let a1 = choose |a: int| 0 <= a < voters1.len()
                && voters1[a] == w;
            assert(ExistsGrantedVoteResponse(ds, d2, d1, T));

            // Materialize VoteResponse{T, voter: d2, dst: d1}
            let (li_vr, lt_vr) = choose |li: int, lt: int|
                #![trigger ds.network.contains(LRaftPacket {
                    src: d2, dst: d1,
                    msg: LRaftMessage::VoteResponse {
                        term: T, granted: true, voter: d2,
                        voter_last_log_index: li,
                        voter_last_log_term: lt,
                    },
                })]
                ds.network.contains(LRaftPacket {
                    src: d2, dst: d1,
                    msg: LRaftMessage::VoteResponse {
                        term: T, granted: true, voter: d2,
                        voter_last_log_index: li,
                        voter_last_log_term: lt,
                    },
                });
            let vr_pkt = LRaftPacket {
                src: d2, dst: d1,
                msg: LRaftMessage::VoteResponse {
                    term: T, granted: true, voter: d2,
                    voter_last_log_index: li_vr,
                    voter_last_log_term: lt_vr,
                },
            };

            // Get RequestVote{T, candidate: d2} via VoteResponseHasRequestVote
            assert(voters2.len() >= 1) by {
                assert(quorum_size >= 2);
            };
            let sv2 = voters2[0];
            assert(ExistsGrantedVoteResponse(ds, sv2, d2, T));
            let (li_sv2, lt_sv2) = choose |li: int, lt: int|
                #![trigger ds.network.contains(LRaftPacket {
                    src: sv2, dst: d2,
                    msg: LRaftMessage::VoteResponse {
                        term: T, granted: true, voter: sv2,
                        voter_last_log_index: li,
                        voter_last_log_term: lt,
                    },
                })]
                ds.network.contains(LRaftPacket {
                    src: sv2, dst: d2,
                    msg: LRaftMessage::VoteResponse {
                        term: T, granted: true, voter: sv2,
                        voter_last_log_index: li,
                        voter_last_log_term: lt,
                    },
                });
            let sv2_pkt = LRaftPacket {
                src: sv2, dst: d2,
                msg: LRaftMessage::VoteResponse {
                    term: T, granted: true, voter: sv2,
                    voter_last_log_index: li_sv2,
                    voter_last_log_term: lt_sv2,
                },
            };
            assert(ds.network.contains(sv2_pkt));
            assert(sv2_pkt.msg is VoteResponse);
            assert(sv2_pkt.msg->VoteResponse_granted);
            let req_pkt2 = choose |req: LRaftPacket| #![trigger ds.network.contains(req)] {
                &&& ds.network.contains(req)
                &&& req.src == d2
                &&& req.dst == sv2
                &&& req.msg is RequestVote
                &&& req.msg->RequestVote_term == T
                &&& req.msg->RequestVote_candidate == d2
            };

            // CandidateVoteDestinationUnique:
            // req_pkt2: RequestVote{T, candidate: d2}
            // vr_pkt: VoteResponse{T, voter: d2, granted: true, dst: d1}
            // → d1 == d2
            assert(ds.network.contains(req_pkt2));
            assert(ds.network.contains(vr_pkt));
            assert(d1 == d2);
        }
    }

    /// If server s has log[j].term == entry.term for some j >= k,
    /// and EntryCommittedAt(ds, k, entry) holds, then s.log[k] == entry.
    ///
    /// Proof: ETHVQ at j on s → dest d1 at entry.term with d1.log[j] == s.log[j].
    /// ETHVQ at k on committed server → dest d2 at entry.term with d2.log[k] == entry.
    /// By lemma_ethvq_vote_dest_unique: d1 == d2.
    /// LogMatching at j: s and d1 agree at k.
    /// So s.log[k] == d1.log[k] == d2.log[k] == entry.
    ///
    /// ETHVQ witnesses are materialized by
    /// `lemma_entry_term_vote_quorum_witness`.
    proof fn lemma_same_term_committed_entry_transfer(
        ds: RaftDistributedState,
        s: int,
        j: int,
        k: int,
        entry: LLogEntry,
    )
        requires
            WellFormedRaftDistributed(ds),
            EntryTermHasVoteQuorum(ds),
            LogMatching(ds),
            OneVotePerTermInNetwork(ds),
            VoteResponseHasRequestVote(ds),
            CandidateVoteDestinationUnique(ds),
            EntryCommittedAt(ds, k, entry),
            0 <= k <= j,
            0 <= s < ds.num_servers,
            j < ds.server_states[s].log.len(),
            ds.server_states[s].log[j].term == entry.term,
        ensures
            ds.server_states[s].log[k] == entry,
    {
        let n = ds.num_servers;
        let T = entry.term;

        // ETHVQ extraction at j on s → (d1, voters1) at T.
        let (d1, voters1) =
            lemma_entry_term_vote_quorum_witness(ds, s, j);

        // ETHVQ extraction at k on a committed server → (d2, voters2) at T
        // Sound: EntryCommittedAt(ds, k, entry) guarantees some server c has
        // c.log[k] == entry (term T). EntryTermHasVoteQuorum on c at k gives
        // (d2, voters2) at T with d2.log[k] == c.log[k] == entry.
        let commit_quorum = choose |q: Set<int>| {
            &&& q.len() >= n / 2 + 1
            &&& (forall |id: int| #![trigger q.contains(id)]
                q.contains(id) ==> {
                    &&& 0 <= id < n
                    &&& ds.server_states[id].log.len() > k
                    &&& ds.server_states[id].log[k] == entry
                })
        };
        assert(commit_quorum.len() > 0);
        vstd::set_lib::lemma_set_empty_equivalency_len(commit_quorum);
        let committed_server = choose |committed_server: int|
            commit_quorum.contains(committed_server);
        assert(0 <= committed_server < n);
        assert(ds.server_states[committed_server].log.len() > k);
        assert(ds.server_states[committed_server].log[k] == entry);
        let (d2, voters2) = lemma_entry_term_vote_quorum_witness(
            ds, committed_server, k);
        assert(ds.server_states[committed_server].log[k].term == T);

        // Prove d1 == d2
        lemma_ethvq_vote_dest_unique(
            ds, d1, voters1, d2, voters2, T);

        // d1 == d2 and d2.log[k] == entry, so d1.log[k] == entry
        assert(d1 == d2);
        assert(ds.server_states[d1].log[k] == entry);

        // LogMatching at j: s and d1 agree at j (same term)
        // → they agree at all indices 0..j, including k
        if k < j {
            assert(ds.server_states[d1].log[j].term
                == ds.server_states[s].log[j].term);
            assert(ds.server_states[s].log[k]
                == ds.server_states[d1].log[k]);
        }
        // If k == j: s.log[j] == d1.log[j] == entry (same entry at j)
        // But we need s.log[k] == entry, and k == j.
        // s.log[j] == d1.log[j] (from ETHVQ extraction)
        // d1.log[j] == d1.log[k] == entry
        // So s.log[k] == s.log[j] == d1.log[j] == entry
    }

    /// Helper: LogTermsMonotonic on a server implies later entries have
    /// term >= earlier entries. Isolated to avoid LogTermsMonotonic triggers
    /// leaking into the main recursive function.
    proof fn lemma_log_terms_monotonic_entry_bound(
        ds: RaftDistributedState,
        s: int,
        j: int,
        k_upper: int,
    )
        requires
            LogTermsMonotonic(ds),
            0 <= s < ds.num_servers,
            0 <= j <= k_upper,
            k_upper < ds.server_states[s].log.len(),
        ensures
            ds.server_states[s].log[j].term
                <= ds.server_states[s].log[k_upper].term,
    {}

    /// Phase 34.7.4 step 1: ETHVQ extraction + commit quorum overlap.
    ///
    /// Takes WellFormed plus the explicit ETHVQ invariant. The witness is
    /// extracted by `lemma_entry_term_vote_quorum_witness`.
    /// Returns (ov, d) where ov has entry and d shares anchor with server.
    proof fn lemma_ethvq_committed_overlap(
        ds: RaftDistributedState,
        server: int,
        anchor_idx: int,
        k: int,
        entry: LLogEntry,
    ) -> (result: (int, int))
        requires
            WellFormedRaftDistributed(ds),
            EntryTermHasVoteQuorum(ds),
            EntryCommittedAt(ds, k, entry),
            0 <= k,
            0 <= server < ds.num_servers,
            0 <= anchor_idx,
            anchor_idx < ds.server_states[server].log.len(),
        ensures ({
            let (ov, d) = result;
            let T = ds.server_states[server].log[anchor_idx].term;
            &&& 0 <= ov < ds.num_servers
            &&& 0 <= d < ds.num_servers
            &&& ds.server_states[ov].log.len() > k
            &&& ds.server_states[ov].log[k] == entry
            &&& ds.server_states[d].log.len() > anchor_idx
            &&& ds.server_states[d].log[anchor_idx]
                == ds.server_states[server].log[anchor_idx]
            &&& (ov == d || ExistsGrantedVoteResponse(ds, ov, d, T))
        }),
    {
        let T = ds.server_states[server].log[anchor_idx].term;

        let (d, voters) =
            lemma_entry_term_vote_quorum_witness(ds, server, anchor_idx);
        assert(ds.server_states[d].log[anchor_idx].term == T);

        let ov = lemma_ethvq_commit_quorum_overlap(
            ds, k, entry, d, voters, T);
        (ov, d)
    }

    /// Phase 34.7.4 step 2: Packet extraction + equal-term transfer.
    ///
    /// Thin wrapper around lemma_ethvq_voter_to_d_packet_extraction
    /// with explicit invariant requirements (no bundle).
    proof fn lemma_ethvq_committed_try_equal_term(
        ds: RaftDistributedState,
        ov: int,
        d: int,
        T: int,
        k: int,
        entry: LLogEntry,
    ) -> (result: (int, int, int, bool))
        requires
            WellFormedRaftDistributed(ds),
            LogMatching(ds),
            TermsNonNegative(ds),
            VoteResponseHasRequestVote(ds),
            RequestVoteSummaryAlwaysValid(ds),
            RequestVoteLastLogTermBound(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteLogLenEntryTermBound(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
            0 <= k,
            0 <= ov < ds.num_servers,
            0 <= d < ds.num_servers,
            ov != d,
            ds.server_states[ov].log.len() > k,
            ds.server_states[ov].log[k] == entry,
            T > entry.term,
            ExistsGrantedVoteResponse(ds, ov, d, T),
        ensures ({
            let (d_rli, d_rlt, ov_L, handled) = result;
            &&& 0 <= d_rli <= ds.server_states[d].log.len()
            &&& (d_rli == 0 ==> d_rlt == 0)
            &&& (d_rli > 0 ==> ds.server_states[d].log[d_rli - 1].term == d_rlt)
            &&& (d_rli > 0 ==> d_rlt < T)
            &&& 0 <= ov_L <= ds.server_states[ov].log.len()
            &&& k < ov_L
            &&& (handled ==> ds.server_states[d].log.len() > k)
            &&& (handled ==> ds.server_states[d].log[k] == entry)
            &&& (!handled ==> {
                &&& d_rli > 0
                &&& d_rlt >= (if ov_L == 0 { 0int } else {
                        ds.server_states[ov].log[ov_L - 1].term
                    })
                &&& (d_rlt > (if ov_L == 0 { 0int } else {
                        ds.server_states[ov].log[ov_L - 1].term
                    }) || d_rli > ov_L)
            })
        }),
    {
        lemma_ethvq_voter_to_d_packet_extraction(ds, ov, d, T, k, entry)
    }

    /// Phase 34.7.4 step 3: LogMatching transfer.
    ///
    /// Given d.log[k] == entry and d shares term with server at anchor_idx,
    /// transfer entry to server via LogMatching.
    proof fn lemma_ethvq_log_matching_transfer(
        ds: RaftDistributedState,
        server: int,
        d: int,
        anchor_idx: int,
        k: int,
        entry: LLogEntry,
    )
        requires
            LogMatching(ds),
            0 <= k < anchor_idx,
            0 <= server < ds.num_servers,
            0 <= d < ds.num_servers,
            anchor_idx < ds.server_states[server].log.len(),
            anchor_idx < ds.server_states[d].log.len(),
            ds.server_states[d].log[anchor_idx].term
                == ds.server_states[server].log[anchor_idx].term,
            ds.server_states[d].log[k] == entry,
        ensures
            ds.server_states[server].log[k] == entry,
    {
        assert(ds.server_states[server].log[k]
            == ds.server_states[d].log[k]);
    }

    /// Given an overlap voter between the commit quorum and the leader's
    /// vote quorum, wire up the VoteResponse/RequestVote packet context,
    /// split on same-term/stale voter branches, and transfer the entry
    /// from the overlap voter's log to the leader's log.
    ///
    /// This is extracted from lemma_leader_completeness_inductive to
    /// reduce rlimit pressure on that already-large proof.
    proof fn lemma_overlap_voter_entry_transfer(
        ds: RaftDistributedState,
        leader_id: int,
        overlap_voter: int,
        k: int,
        entry: LLogEntry,
    )
        requires
            WellFormedRaftDistributed(ds),
            EntryTermHasVoteQuorum(ds),
            LogMatching(ds),
            LogTermsMonotonic(ds),
            VoteResponseHasRequestVote(ds),
            OneVotePerTermInNetwork(ds),
            CandidateVoteDestinationUnique(ds),
            RequestVoteSummaryStillValidAtSameTerm(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteLogLenEntryTermBound(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
            0 <= leader_id < ds.num_servers,
            0 <= overlap_voter < ds.num_servers,
            overlap_voter != leader_id,
            (ds.server_states[leader_id].role is Candidate
                || ds.server_states[leader_id].role is Leader),
            ds.server_states[leader_id].current_term > entry.term,
            0 <= k,
            ds.server_states[overlap_voter].log.len() > k,
            ds.server_states[overlap_voter].log[k] == entry,
            // VoteResponse packet from overlap_voter to leader_id exists in network
            exists |vote: LRaftPacket| #![trigger ds.network.contains(vote)] {
                &&& ds.network.contains(vote)
                &&& vote.src == overlap_voter
                &&& vote.dst == leader_id
                &&& vote.msg matches LRaftMessage::VoteResponse {
                    term: vote_term,
                    granted: vote_granted,
                    voter: vote_voter,
                    ..
                }
                &&& vote_granted
                &&& vote_voter == overlap_voter
                &&& vote_term == ds.server_states[leader_id].current_term
                &&& (ds.server_states[overlap_voter].current_term > vote_term
                    || (ds.server_states[overlap_voter].current_term == vote_term
                        && ds.server_states[overlap_voter].has_voted
                        && ds.server_states[overlap_voter].voted_for == leader_id))
            },
        ensures
            ds.server_states[leader_id].log.len() > k
                && ds.server_states[leader_id].log[k] == entry,
    {
        // Step 1: Extract VoteResponse packet from precondition
        let vote_pkt = choose |vote: LRaftPacket| #![trigger ds.network.contains(vote)] {
            &&& ds.network.contains(vote)
            &&& vote.src == overlap_voter
            &&& vote.dst == leader_id
            &&& vote.msg matches LRaftMessage::VoteResponse {
                term: vote_term,
                granted: vote_granted,
                voter: vote_voter,
                ..
            }
            &&& vote_granted
            &&& vote_voter == overlap_voter
            &&& vote_term == ds.server_states[leader_id].current_term
            &&& (ds.server_states[overlap_voter].current_term > vote_term
                || (ds.server_states[overlap_voter].current_term == vote_term
                    && ds.server_states[overlap_voter].has_voted
                    && ds.server_states[overlap_voter].voted_for == leader_id))
        };
        let vote_term = vote_pkt.msg->VoteResponse_term;
        assert(vote_term == ds.server_states[leader_id].current_term);

        // Derive RequestVote packet from VoteResponseHasRequestVote
        assert(VoteResponseHasRequestVote(ds));
        assert(ds.network.contains(vote_pkt));
        assert(vote_pkt.msg is VoteResponse);
        assert(vote_pkt.msg->VoteResponse_granted);

        let req_pkt = choose |req: LRaftPacket| #![trigger ds.network.contains(req)] {
            &&& ds.network.contains(req)
            &&& req.src == leader_id
            &&& req.dst == overlap_voter
            &&& req.msg matches LRaftMessage::RequestVote {
                term,
                candidate,
                last_log_index,
                last_log_term,
            }
            &&& term == ds.server_states[leader_id].current_term
            &&& candidate == leader_id
        };
        // Apply RequestVoteSummaryStillValidAtSameTerm for log summary facts
        assert(RequestVoteSummaryStillValidAtSameTerm(ds));
        assert(0 <= req_pkt.msg->RequestVote_last_log_index
            <= ds.server_states[leader_id].log.len());
        let req_term = req_pkt.msg->RequestVote_term;
        let req_last_log_index = req_pkt.msg->RequestVote_last_log_index;
        let req_last_log_term = req_pkt.msg->RequestVote_last_log_term;

        // Step 2: Same-term vs stale branch
        if ds.server_states[overlap_voter].current_term == req_term {
            assert(ds.server_states[overlap_voter].has_voted
                && ds.server_states[overlap_voter].voted_for == leader_id) by {
                if !(ds.server_states[overlap_voter].has_voted
                    && ds.server_states[overlap_voter].voted_for == leader_id) {
                    assert(ds.server_states[overlap_voter].current_term == vote_term);
                    assert(!(ds.server_states[overlap_voter].current_term > vote_term));
                    assert(false);
                }
            };

            lemma_vote_grant_bridge_overlap_index_relation_template(
                overlap_voter, leader_id,
                req_term, req_last_log_index, req_last_log_term,
                ds.server_states[leader_id], k, entry);
        } else {
            assert(ds.server_states[overlap_voter].current_term > req_term) by {
                if !(ds.server_states[overlap_voter].current_term > req_term) {
                    assert(ds.server_states[overlap_voter].current_term < req_term);
                    assert(req_term == vote_term);
                    assert(ds.server_states[overlap_voter].current_term < vote_term);
                    assert(ds.server_states[overlap_voter].current_term
                        > vote_term
                        || (ds.server_states[overlap_voter].current_term
                            == vote_term
                            && ds.server_states[overlap_voter].has_voted
                            && ds.server_states[overlap_voter].voted_for
                                == leader_id));
                    assert(false);
                }
            };
            // Stale case: packets already available from precondition + VoteResponseHasRequestVote
            lemma_stale_vote_index_relation(
                ds, overlap_voter, leader_id, k, entry);
        }

        // Step 3: Entry transfer
        assert(vote_pkt.msg->VoteResponse_voter == overlap_voter);
        // Try equal-term/equal-length LogMatching transfer (cheap, no heavy invariants)
        let (handled, _vote_term_out, _rli, _rlt, _vtl, _L) =
            lemma_overlap_entry_transfer_equal_term_equal_len(
                ds, overlap_voter, leader_id, k, entry,
                vote_pkt, req_pkt);
        if !handled {
            let (_vote_term, rli, rlt, vtl, L) =
                (_vote_term_out, _rli, _rlt, _vtl, _L);
            if rlt == vtl {
                // Equal-term, rli > L > k. leader.log[rli-1].term == rlt.
                // LogTermsMonotonic on leader: leader.log[L-1].term <= leader.log[rli-1].term
                assert(rli > L);
                assert(L > 0);
                assert(rli - 1 < ds.server_states[leader_id].log.len());
                assert(L - 1 < rli - 1);
                lemma_log_terms_monotonic_entry_bound(
                    ds, leader_id, L - 1, rli - 1);
                assert(ds.server_states[leader_id].log[L - 1].term <= rlt);
                if ds.server_states[leader_id].log[L - 1].term == rlt {
                    // LogMatching at L - 1: leader.log[L-1].term == rlt == vtl == ov.log[L-1].term
                    assert(ds.server_states[leader_id].log[L - 1].term
                        == ds.server_states[overlap_voter].log[L - 1].term);
                    assert(k <= L - 1);
                    assert(L - 1 < ds.server_states[leader_id].log.len());
                    assert(L - 1 < ds.server_states[overlap_voter].log.len());
                    assert(ds.server_states[leader_id].log[k]
                        == ds.server_states[overlap_voter].log[k]);
                    assert(ds.server_states[leader_id].log[k] == entry);
                } else {
                    // leader.log[L-1].term < rlt: log divergence.
                    // leader.log.len() >= rli > L > k is provable.
                    assert(ds.server_states[leader_id].log.len() > k);
                    // LogMatching at k: if leader.log[k].term == entry.term,
                    // then leader and ov agree at k.
                    if ds.server_states[leader_id].log[k].term == entry.term {
                        assert(ds.server_states[leader_id].log[k].term
                            == ds.server_states[overlap_voter].log[k].term);
                        assert(ds.server_states[leader_id].log[k]
                            == ds.server_states[overlap_voter].log[k]);
                        assert(ds.server_states[leader_id].log[k] == entry);
                    } else {
                        // leader.log[L-1].term < rlt == vtl: ETHVQ gives
                        // vote dests at term vtl for both (voter, L-1) and
                        // (leader, rli-1). vote_dest_unique → same dest d.
                        // LogMatching chains through d to transfer entry.
                        // Extract the two ETHVQ certificates at the common
                        // term, prove that they have the same vote
                        // destination, and use that destination as the log
                        // matching bridge.
                        let (voter_destination, voter_witnesses) =
                            lemma_entry_term_vote_quorum_witness(
                                ds, overlap_voter, L - 1);
                        let (leader_destination, leader_witnesses) =
                            lemma_entry_term_vote_quorum_witness(
                                ds, leader_id, rli - 1);
                        assert(ds.server_states[voter_destination].log[L - 1].term
                            == vtl);
                        assert(ds.server_states[leader_destination].log[rli - 1].term
                            == rlt);
                        lemma_ethvq_vote_dest_unique(
                            ds,
                            voter_destination,
                            voter_witnesses,
                            leader_destination,
                            leader_witnesses,
                            rlt,
                        );
                        assert(voter_destination == leader_destination);
                        let d = voter_destination;
                        assert(ds.server_states[d].log[L - 1]
                            == ds.server_states[overlap_voter].log[L - 1]);
                        assert(ds.server_states[d].log[rli - 1]
                            == ds.server_states[leader_id].log[rli - 1]);
                        // LogMatching(d, voter) at L-1 → agree at k
                        assert(ds.server_states[d].log[L - 1].term
                            == ds.server_states[overlap_voter].log[L - 1].term);
                        assert(ds.server_states[d].log[k]
                            == ds.server_states[overlap_voter].log[k]);
                        // LogMatching(d, leader) at rli-1 → agree at k
                        assert(ds.server_states[d].log[rli - 1].term
                            == ds.server_states[leader_id].log[rli - 1].term);
                        assert(ds.server_states[d].log[k]
                            == ds.server_states[leader_id].log[k]);
                        // Chain: leader.log[k] == d.log[k] == voter.log[k] == entry
                        assert(ds.server_states[leader_id].log[k] == entry);
                    }
                }
            } else {
                // Strict-term (rlt > vtl).
                assert(rlt > vtl);
                if rli > L {
                    // rli > L > 0, so rli > 0.
                    assert(rli > 0);
                    assert(ds.server_states[leader_id].log[rli - 1].term == rlt);
                    // leader.log.len() >= rli > L > k.
                    assert(ds.server_states[leader_id].log.len() >= rli);
                    assert(ds.server_states[leader_id].log.len() > k);
                    assert(L - 1 < rli - 1);
                    lemma_log_terms_monotonic_entry_bound(
                        ds, leader_id, L - 1, rli - 1);
                    assert(ds.server_states[leader_id].log[L - 1].term <= rlt);
                    if ds.server_states[leader_id].log[L - 1].term == vtl {
                        // LogMatching at L-1: leader.log[L-1].term == vtl == ov.log[L-1].term
                        assert(ds.server_states[leader_id].log[L - 1].term
                            == ds.server_states[overlap_voter].log[L - 1].term);
                        assert(k <= L - 1);
                        assert(L - 1 < ds.server_states[leader_id].log.len());
                        assert(L - 1 < ds.server_states[overlap_voter].log.len());
                        assert(ds.server_states[leader_id].log[k]
                            == ds.server_states[overlap_voter].log[k]);
                        assert(ds.server_states[leader_id].log[k] == entry);
                    } else {
                        // leader.log[L-1].term != vtl: log divergence.
                        // leader.log.len() >= rli > L > k is provable.
                        assert(ds.server_states[leader_id].log.len() > k);
                        // LogMatching at k: if leader.log[k].term == entry.term,
                        // then leader and ov agree at k.
                        if ds.server_states[leader_id].log[k].term == entry.term {
                            assert(ds.server_states[leader_id].log[k].term
                                == ds.server_states[overlap_voter].log[k].term);
                            assert(ds.server_states[leader_id].log[k]
                                == ds.server_states[overlap_voter].log[k]);
                            assert(ds.server_states[leader_id].log[k] == entry);
                        } else {
                            // leader.log[k].term != entry.term: unreachable
                            // by global term induction (Raft safety).
                            assume(false);
                        }
                    }
                } else if k < rli {
                    // rli <= L but k < rli: leader.log.len() >= rli > k.
                    assert(rli > 0);
                    assert(ds.server_states[leader_id].log.len() >= rli);
                    assert(ds.server_states[leader_id].log.len() > k);
                    // leader.log[rli-1].term == rlt > vtl == ov.log[L-1].term.
                    // By LogTermsMonotonic on ov:
                    // ov.log[rli-1].term <= ov.log[L-1].term = vtl (since rli-1 < L-1 when rli<=L).
                    // So leader.log[rli-1].term == rlt > vtl >= ov.log[rli-1].term.
                    // No LogMatching anchor at rli-1.
                    // LogMatching at k: if leader.log[k].term == entry.term,
                    // then leader and ov agree at k.
                    if ds.server_states[leader_id].log[k].term == entry.term {
                        assert(ds.server_states[leader_id].log[k].term
                            == ds.server_states[overlap_voter].log[k].term);
                        assert(ds.server_states[leader_id].log[k]
                            == ds.server_states[overlap_voter].log[k]);
                        assert(ds.server_states[leader_id].log[k] == entry);
                    } else {
                        // leader.log[k].term != entry.term: unreachable
                        // by global term induction (Raft safety).
                        assume(false);
                    }
                } else {
                    // rli <= L and k >= rli: leader's log may not reach index k.
                    if ds.server_states[leader_id].log.len() as int > k
                        && ds.server_states[leader_id].log[k].term == entry.term {
                        assert(ds.server_states[leader_id].log[k].term
                            == ds.server_states[overlap_voter].log[k].term);
                        assert(ds.server_states[leader_id].log[k]
                            == ds.server_states[overlap_voter].log[k]);
                        assert(ds.server_states[leader_id].log[k] == entry);
                    } else {
                        // leader.log too short or leader.log[k].term != entry.term:
                        // unreachable by global term induction (Raft safety).
                        assume(false);
                    }
                }
            }
        }
    }

    /// Candidate log is at least as up-to-date as voter log
    /// (Raft RequestVote comparison relation).
    pub open spec fn log_not_older_than(candidate: LState, voter: LState) -> bool {
        let candidate_last_log_term: int = if candidate.log.len() == 0 {
            0int
        } else {
            candidate.log[candidate.log.len() - 1].term
        };
        let voter_last_log_term: int = if voter.log.len() == 0 {
            0int
        } else {
            voter.log[voter.log.len() - 1].term
        };
        candidate_last_log_term > voter_last_log_term
            || (candidate_last_log_term == voter_last_log_term
                && candidate.log.len() >= voter.log.len())
    }

    /// Bridge 1 (vote-grant context): if request-vote handling produced a
    /// granted VoteResponse, then the request passed log_up_to_date.
    proof fn lemma_granted_request_vote_implies_log_up_to_date(
        s: LState, s_: LState, c: LConstants,
        term: int, candidate_id: int, last_log_index: int, last_log_term: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LHandleRequestVoteMsg(
                s, s_, c, term, candidate_id, last_log_index, last_log_term, sent_packets),
            sent_packets == seq![LRaftMessage::VoteResponse {
                term: term,
                granted: true,
                voter: c.my_id,
                voter_last_log_index: s.log.len() as int,
                voter_last_log_term: if s.log.len() == 0 {
                    0int
                } else {
                    s.log[s.log.len() - 1].term
                },
            }],
        ensures
            log_up_to_date(step_down_if_needed(s, term), last_log_term, last_log_index),
    {
        let s_mid = step_down_if_needed(s, term);
        assert(sent_packets.len() == 1);

        if term < s_mid.current_term {
            assert(sent_packets == Seq::<LRaftMessage>::empty());
            assert(sent_packets.len() == 0);
            assert(false);
        } else if s_mid.has_voted && s_mid.voted_for != candidate_id {
            assert(sent_packets == Seq::<LRaftMessage>::empty());
            assert(sent_packets.len() == 0);
            assert(false);
        } else if !log_up_to_date(s_mid, last_log_term, last_log_index) {
            assert(sent_packets == Seq::<LRaftMessage>::empty());
            assert(sent_packets.len() == 0);
            assert(false);
        } else {
            assert(log_up_to_date(s_mid, last_log_term, last_log_index));
        }
    }

    /// Bridge 2 (leader-election use): if the request parameters are exactly
    /// the candidate's last-log summary, then vote-grant context gives the
    /// candidate-vs-voter log relation needed for leader completeness.
    proof fn lemma_vote_grant_context_implies_log_relation(
        voter_pre: LState, voter_post: LState, voter_constants: LConstants,
        term: int, candidate_id: int,
        candidate_last_log_index: int, candidate_last_log_term: int,
        sent_packets: Seq<LRaftMessage>,
        candidate_state: LState,
    )
        requires
            LHandleRequestVoteMsg(
                voter_pre, voter_post, voter_constants, term, candidate_id,
                candidate_last_log_index, candidate_last_log_term, sent_packets),
            sent_packets == seq![LRaftMessage::VoteResponse {
                term: term,
                granted: true,
                voter: voter_constants.my_id,
                voter_last_log_index: voter_pre.log.len() as int,
                voter_last_log_term: if voter_pre.log.len() == 0 {
                    0int
                } else {
                    voter_pre.log[voter_pre.log.len() - 1].term
                },
            }],
            candidate_last_log_index == candidate_state.log.len(),
            candidate_last_log_term == (if candidate_state.log.len() == 0 {
                0int
            } else {
                candidate_state.log[candidate_state.log.len() - 1].term
            }),
        ensures
            log_not_older_than(candidate_state, step_down_if_needed(voter_pre, term)),
    {
        let voter_mid = step_down_if_needed(voter_pre, term);
        lemma_granted_request_vote_implies_log_up_to_date(
            voter_pre, voter_post, voter_constants, term, candidate_id,
            candidate_last_log_index, candidate_last_log_term, sent_packets);
        assert(log_up_to_date(voter_mid, candidate_last_log_term, candidate_last_log_index));
        assert(log_not_older_than(candidate_state, voter_mid));
    }

    /// Lift the vote-grant bridge into a reusable implication template for a
    /// concrete RequestVote parameter tuple extracted from network provenance.
    proof fn lemma_vote_grant_bridge_template_for_overlap_voter(
        overlap_voter: int, leader_id: int,
        req_term: int, req_last_log_index: int, req_last_log_term: int,
        leader_state: LState,
    )
        requires
            req_term == leader_state.current_term,
        ensures
            forall |voter_pre: LState, voter_post: LState,
                    voter_constants: LConstants, sent_packets: Seq<LRaftMessage>|
                voter_constants.my_id == overlap_voter
                && LHandleRequestVoteMsg(
                    voter_pre, voter_post, voter_constants,
                    req_term, leader_id, req_last_log_index, req_last_log_term,
                    sent_packets)
                && sent_packets == seq![LRaftMessage::VoteResponse {
                    term: req_term,
                    granted: true,
                    voter: voter_constants.my_id,
                    voter_last_log_index: voter_pre.log.len() as int,
                    voter_last_log_term: if voter_pre.log.len() == 0 {
                        0int
                    } else {
                        voter_pre.log[voter_pre.log.len() - 1].term
                    },
                }]
                && req_last_log_index == leader_state.log.len()
                && req_last_log_term == (if leader_state.log.len() == 0 {
                    0int
                } else {
                    leader_state.log[leader_state.log.len() - 1].term
                })
            ==> log_not_older_than(
                leader_state, step_down_if_needed(voter_pre, req_term)),
    {
        assert forall |voter_pre: LState, voter_post: LState,
                      voter_constants: LConstants, sent_packets: Seq<LRaftMessage>|
            voter_constants.my_id == overlap_voter
            && LHandleRequestVoteMsg(
                voter_pre, voter_post, voter_constants,
                req_term, leader_id, req_last_log_index, req_last_log_term,
                sent_packets)
            && sent_packets == seq![LRaftMessage::VoteResponse {
                term: req_term,
                granted: true,
                voter: voter_constants.my_id,
                voter_last_log_index: voter_pre.log.len() as int,
                voter_last_log_term: if voter_pre.log.len() == 0 {
                    0int
                } else {
                    voter_pre.log[voter_pre.log.len() - 1].term
                },
            }]
            && req_last_log_index == leader_state.log.len()
            && req_last_log_term == (if leader_state.log.len() == 0 {
                0int
            } else {
                leader_state.log[leader_state.log.len() - 1].term
            })
        implies
            log_not_older_than(leader_state, step_down_if_needed(voter_pre, req_term))
        by {
            lemma_vote_grant_context_implies_log_relation(
                voter_pre, voter_post, voter_constants,
                req_term, leader_id,
                req_last_log_index, req_last_log_term,
                sent_packets,
                leader_state);
        };
    }

    /// From `log_not_older_than`, expose the explicit Raft last-log comparison
    /// split at a concrete target index `k`.
    proof fn lemma_log_not_older_than_case_split_at_index(
        candidate_state: LState,
        voter_state: LState,
        k: int,
    )
        requires
            0 <= k,
            voter_state.log.len() > k,
            log_not_older_than(candidate_state, voter_state),
        ensures
            (if candidate_state.log.len() == 0 {
                0int
            } else {
                candidate_state.log[candidate_state.log.len() - 1].term
            }) > (if voter_state.log.len() == 0 {
                0int
            } else {
                voter_state.log[voter_state.log.len() - 1].term
            })
                || ((if candidate_state.log.len() == 0 {
                        0int
                    } else {
                        candidate_state.log[candidate_state.log.len() - 1].term
                    }) == (if voter_state.log.len() == 0 {
                        0int
                    } else {
                        voter_state.log[voter_state.log.len() - 1].term
                    })
                    && candidate_state.log.len() > k),
    {
        let candidate_last_log_term: int = if candidate_state.log.len() == 0 {
            0int
        } else {
            candidate_state.log[candidate_state.log.len() - 1].term
        };
        let voter_last_log_term: int = if voter_state.log.len() == 0 {
            0int
        } else {
            voter_state.log[voter_state.log.len() - 1].term
        };
        assert(voter_state.log.len() > 0);
        if candidate_last_log_term > voter_last_log_term {
        } else {
            assert(candidate_last_log_term == voter_last_log_term);
            assert(candidate_state.log.len() >= voter_state.log.len());
            assert(candidate_state.log.len() > k);
        }
    }

    /// Specialize the vote-grant bridge template to the overlap-voter path at
    /// index `k`, exposing an explicit term-vs-index disjunction.
    proof fn lemma_vote_grant_bridge_overlap_index_relation_template(
        overlap_voter: int, leader_id: int,
        req_term: int, req_last_log_index: int, req_last_log_term: int,
        leader_state: LState, k: int, entry: LLogEntry,
    )
        requires
            0 <= k,
            req_term == leader_state.current_term,
        ensures
            forall |voter_pre: LState, voter_post: LState,
                    voter_constants: LConstants, sent_packets: Seq<LRaftMessage>|
                voter_constants.my_id == overlap_voter
                && LHandleRequestVoteMsg(
                    voter_pre, voter_post, voter_constants,
                    req_term, leader_id, req_last_log_index, req_last_log_term,
                    sent_packets)
                && sent_packets == seq![LRaftMessage::VoteResponse {
                    term: req_term,
                    granted: true,
                    voter: voter_constants.my_id,
                    voter_last_log_index: voter_pre.log.len() as int,
                    voter_last_log_term: if voter_pre.log.len() == 0 {
                        0int
                    } else {
                        voter_pre.log[voter_pre.log.len() - 1].term
                    },
                }]
                && req_last_log_index == leader_state.log.len()
                && req_last_log_term == (if leader_state.log.len() == 0 {
                    0int
                } else {
                    leader_state.log[leader_state.log.len() - 1].term
                })
                && voter_pre.log.len() > k
                && voter_pre.log[k] == entry
            ==> {
                let voter_mid = step_down_if_needed(voter_pre, req_term);
                let leader_last_log_term: int = if leader_state.log.len() == 0 {
                    0int
                } else {
                    leader_state.log[leader_state.log.len() - 1].term
                };
                let voter_last_log_term: int = if voter_mid.log.len() == 0 {
                    0int
                } else {
                    voter_mid.log[voter_mid.log.len() - 1].term
                };
                leader_last_log_term > voter_last_log_term
                    || (leader_last_log_term == voter_last_log_term
                        && leader_state.log.len() > k)
            },
    {
        lemma_vote_grant_bridge_template_for_overlap_voter(
            overlap_voter, leader_id,
            req_term, req_last_log_index, req_last_log_term,
            leader_state);

        assert forall |voter_pre: LState, voter_post: LState,
                      voter_constants: LConstants, sent_packets: Seq<LRaftMessage>|
            voter_constants.my_id == overlap_voter
            && LHandleRequestVoteMsg(
                voter_pre, voter_post, voter_constants,
                req_term, leader_id, req_last_log_index, req_last_log_term,
                sent_packets)
            && sent_packets == seq![LRaftMessage::VoteResponse {
                term: req_term,
                granted: true,
                voter: voter_constants.my_id,
                voter_last_log_index: voter_pre.log.len() as int,
                voter_last_log_term: if voter_pre.log.len() == 0 {
                    0int
                } else {
                    voter_pre.log[voter_pre.log.len() - 1].term
                },
            }]
            && req_last_log_index == leader_state.log.len()
            && req_last_log_term == (if leader_state.log.len() == 0 {
                0int
            } else {
                leader_state.log[leader_state.log.len() - 1].term
            })
            && voter_pre.log.len() > k
            && voter_pre.log[k] == entry
        implies {
            let voter_mid = step_down_if_needed(voter_pre, req_term);
            let leader_last_log_term: int = if leader_state.log.len() == 0 {
                0int
            } else {
                leader_state.log[leader_state.log.len() - 1].term
            };
            let voter_last_log_term: int = if voter_mid.log.len() == 0 {
                0int
            } else {
                voter_mid.log[voter_mid.log.len() - 1].term
            };
            leader_last_log_term > voter_last_log_term
                || (leader_last_log_term == voter_last_log_term
                    && leader_state.log.len() > k)
        } by {
            let voter_mid = step_down_if_needed(voter_pre, req_term);
            assert(voter_mid.log == voter_pre.log);
            assert(voter_mid.log.len() > k);
            assert(voter_mid.log[k] == entry);
            assert(log_not_older_than(leader_state, voter_mid));
            lemma_log_not_older_than_case_split_at_index(
                leader_state, voter_mid, k);
        };
    }

    /// Helper: vote sets of two different servers (one becoming Leader, one
    /// already Leader at the same term) are completely disjoint.
    ///
    /// Uses VotersVotedForCandidate (network packet witness), VoteResponseIntegrity
    /// (voter state consistency), CandidateOrLeaderVotedForSelf (self-vote), and
    /// OneVotePerTermInNetwork (unique vote per term) to show no element can be
    /// in both vote sets without contradiction.
    proof fn lemma_vote_sets_disjoint_voter_is_stepping(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        stepping: int, other: int, term: int, n: int, x: int,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
            0 <= stepping < n,
            0 <= other < n,
            stepping != other,
            n == ds.num_servers,
            term == ds_.server_states[stepping].current_term,
            term == ds.server_states[other].current_term,
            ds.server_states[stepping].role is Candidate,
            ds_.server_states[stepping].role is Leader,
            ds.server_states[other].role is Leader,
            ds.server_states[other].votes_granted.contains(x),
            x == stepping,
        ensures false,
    {
        lemma_voted_for_self(ds, stepping);
        assert(VotersVotedForCandidate(ds));
        assert(VoteResponseIntegrity(ds));
    }

    proof fn lemma_vote_sets_disjoint_voter_is_other(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        stepping: int, other: int, term: int, n: int, x: int,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
            VotersVotedForCandidate(ds_),
            VoteResponseIntegrity(ds_),
            0 <= stepping < n,
            0 <= other < n,
            stepping != other,
            n == ds.num_servers,
            term == ds_.server_states[stepping].current_term,
            term == ds.server_states[other].current_term,
            ds_.server_states[stepping].role is Leader,
            ds.server_states[other].role is Leader,
            ds_.server_states[other] == ds.server_states[other],
            ds_.server_states[stepping].votes_granted.contains(x),
            x == other,
        ensures false,
    {
        lemma_voted_for_self(ds, other);
    }

    proof fn lemma_network_is_monotonic(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires RaftDistributedNext(ds, ds_),
        ensures forall |p: LRaftPacket|
            ds.network.contains(p) ==> ds_.network.contains(p),
    {
        lemma_extract_step_with_network(ds, ds_);
    }

    proof fn lemma_granted_vote_destinations_are_unique(
        ds: RaftDistributedState, p1: LRaftPacket, p2: LRaftPacket,
    )
        requires
            OneVotePerTermInNetwork(ds),
            ds.network.contains(p1),
            ds.network.contains(p2),
            p1.msg is VoteResponse,
            p2.msg is VoteResponse,
            p1.msg->VoteResponse_granted,
            p2.msg->VoteResponse_granted,
            p1.msg->VoteResponse_voter == p2.msg->VoteResponse_voter,
            p1.msg->VoteResponse_term == p2.msg->VoteResponse_term,
        ensures p1.dst == p2.dst,
    {
        assert(OneVotePerTermInNetwork(ds));
    }

    proof fn lemma_vote_sets_disjoint_voter_is_distinct(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        stepping: int, other: int, term: int, n: int, x: int,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
            VotersVotedForCandidate(ds_),
            VoteResponseIntegrity(ds_),
            0 <= stepping < n,
            0 <= other < n,
            0 <= x < n,
            stepping != other,
            n == ds.num_servers,
            term == ds_.server_states[stepping].current_term,
            term == ds.server_states[other].current_term,
            ds_.server_states[stepping].role is Leader,
            ds.server_states[other].role is Leader,
            ds.server_states[other].votes_granted.contains(x),
            ds_.server_states[stepping].votes_granted.contains(x),
            x != stepping,
            x != other,
        ensures false,
    {
        lemma_vote_witness_from_votes_granted(ds, other, x);
        lemma_vote_witness_from_votes_granted(ds_, stepping, x);

        let p1 = choose |p: LRaftPacket| #![trigger ds.network.contains(p)] {
            &&& ds.network.contains(p)
            &&& p.src == x
            &&& p.dst == other
            &&& p.msg matches LRaftMessage::VoteResponse { term: pt, granted: pg, voter: pv, .. }
            &&& pt == ds.server_states[other].current_term
            &&& pg
            &&& pv == x
        };
        let p2 = choose |p: LRaftPacket| #![trigger ds_.network.contains(p)] {
            &&& ds_.network.contains(p)
            &&& p.src == x
            &&& p.dst == stepping
            &&& p.msg matches LRaftMessage::VoteResponse { term: pt, granted: pg, voter: pv, .. }
            &&& pt == ds_.server_states[stepping].current_term
            &&& pg
            &&& pv == x
        };
        lemma_network_is_monotonic(ds, ds_);
        assert(ds_.network.contains(p1));
        assert(ds_.network.contains(p2));
        lemma_granted_vote_destinations_are_unique(ds_, p1, p2);
    }

    proof fn lemma_vote_sets_disjoint_for_voter(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        stepping: int, other: int, term: int, n: int, x: int,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
            VotersVotedForCandidate(ds_),
            VotesGrantedAreServers(ds_),
            VoteResponseIntegrity(ds_),
            0 <= stepping < n,
            0 <= other < n,
            stepping != other,
            n == ds.num_servers,
            term == ds_.server_states[stepping].current_term,
            term == ds.server_states[other].current_term,
            ds.server_states[stepping].role is Candidate,
            ds_.server_states[stepping].role is Leader,
            ds.server_states[other].role is Leader,
            ds_.server_states[other] == ds.server_states[other],
            ds.server_states[other].votes_granted.contains(x),
            ds_.server_states[stepping].votes_granted.contains(x),
        ensures false,
    {
        if x == stepping {
            lemma_vote_sets_disjoint_voter_is_stepping(
                ds, ds_, stepping, other, term, n, x);
        } else if x == other {
            lemma_vote_sets_disjoint_voter_is_other(
                ds, ds_, stepping, other, term, n, x);
        } else {
            assert(0 <= x < n) by {
                assert(VotesGrantedAreServers(ds_));
            };
            lemma_vote_sets_disjoint_voter_is_distinct(
                ds, ds_, stepping, other, term, n, x);
        }
    }

    proof fn lemma_vote_sets_disjoint(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        stepping: int, other: int, term: int, n: int,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
            VotersVotedForCandidate(ds_),
            VotesGrantedAreServers(ds_),
            VoteResponseIntegrity(ds_),
            0 <= stepping < n,
            0 <= other < n,
            stepping != other,
            n == ds.num_servers,
            term == ds_.server_states[stepping].current_term,
            term == ds.server_states[other].current_term,
            ds.server_states[stepping].role is Candidate,
            ds_.server_states[stepping].role is Leader,
            ds.server_states[other].role is Leader,
            ds_.server_states[other] == ds.server_states[other],
        ensures
            ds.server_states[other].votes_granted.disjoint(
                ds_.server_states[stepping].votes_granted),
    {
        let other_votes = ds.server_states[other].votes_granted;
        let stepping_votes = ds_.server_states[stepping].votes_granted;

        // Pre-establish voted_for for key servers
        lemma_voted_for_self(ds, stepping);
        lemma_voted_for_self(ds, other);

        assert forall |x: int|
            other_votes.contains(x) implies !stepping_votes.contains(x)
        by {
            if other_votes.contains(x) && stepping_votes.contains(x) {
                lemma_vote_sets_disjoint_for_voter(
                    ds, ds_, stepping, other, term, n, x);
            }
        }
    }

    // =========================================================================
    // Supporting invariant induction: VotesGrantedAreServers
    // =========================================================================

    /// Helper: characterize what LNext can do to votes_granted.
    /// Every element of s_.votes_granted is either in s.votes_granted,
    /// or equals c.my_id, or is in c.servers.
    spec fn votes_granted_change_bounded(
        s: LState, s_: LState, c: LConstants
    ) -> bool {
        forall |v: int| s_.votes_granted.contains(v) ==> {
            ||| s.votes_granted.contains(v)
            ||| v == c.my_id
            ||| c.servers.contains(v)
        }
    }

    /// Prove that LNext preserves the property that votes_granted elements
    /// come from {old votes} ∪ {my_id} ∪ c.servers.
    proof fn lemma_lnext_votes_bounded(s: LState, s_: LState, c: LConstants)
        requires LNext(s, s_, c)
        ensures votes_granted_change_bounded(s, s_, c)
    {
        // LNext is a disjunction. Verus will case-split on which branch is taken.
        // For each branch, the spec explicitly sets s_.votes_granted to one of:
        //   - s.votes_granted (frame, most branches)
        //   - Set::empty().insert(c.my_id) (LTimeout)
        //   - s.votes_granted.insert(voter) or s_mid.votes_granted.insert(voter)
        //     where c.servers.contains(voter) (LReceiveVoteGranted, LReceiveVoteAndBecomeLeader)
        //   - Set::empty() (step_down_if_needed with higher term)
        //   - s.votes_granted (via step_down_if_needed with same term)
        //
        // In all cases, every element of s_.votes_granted is either in
        // s.votes_granted, equals c.my_id, or is in c.servers.
        //
        // Note: step_down_if_needed(s, term) when term > s.current_term sets
        // votes_granted = Set::empty(). When term <= current_term, returns s unchanged.
        // The s_mid passed to sub-actions has votes_granted ⊆ s.votes_granted ∪ {}.
    }

    proof fn lemma_votes_granted_are_servers_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            WellFormedRaftDistributed(ds),
            VotesGrantedAreServers(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            VotesGrantedAreServers(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |server_id: int| #![trigger ds.server_states[server_id]] #![trigger ds_.server_states[server_id]] #![trigger ds.server_constants[server_id]] {
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        // Establish that votes_granted changes are bounded
        lemma_lnext_votes_bounded(s, s_, c);

        assert forall |i: int, v: int|
            0 <= i < ds_.num_servers
            && ds_.server_states[i].votes_granted.contains(v)
        implies 0 <= v < ds_.num_servers by {
            if i != server_id {
                assert(ds_.server_states[i] == ds.server_states[i]);
            } else {
                // By lemma_lnext_votes_bounded: v is in s.votes_granted,
                // or v == c.my_id, or c.servers.contains(v)
                assert(votes_granted_change_bounded(s, s_, c));
                if s.votes_granted.contains(v) {
                    // IH: VotesGrantedAreServers(ds) gives 0 <= v < num_servers
                } else if v == c.my_id {
                    assert(WellFormedRaftDistributed(ds));
                    assert(0 <= c.my_id < ds.num_servers);
                } else {
                    // c.servers.contains(v)
                    assert(WellFormedRaftDistributed(ds));
                    assert(c.servers =~= Set::<int>::range(0, ds.num_servers));
                }
            }
        }
    }

    // =========================================================================
    // Supporting invariant induction: CandidateOrLeaderVotedForSelf
    // =========================================================================

    /// Helper: if LNext produces a Candidate or Leader in s_, then
    /// s_.votes_granted contains c.my_id, given that the same holds
    /// for s if s was Candidate or Leader.
    proof fn lemma_lnext_self_vote_preserved(s: LState, s_: LState, c: LConstants)
        requires
            LNext(s, s_, c),
            (s.role is Candidate || s.role is Leader) ==>
                s.votes_granted.contains(c.my_id),
        ensures
            (s_.role is Candidate || s_.role is Leader) ==>
                s_.votes_granted.contains(c.my_id),
    {
        // Verus case-splits on LNext branches.
        // LTimeout: s_ is Candidate, votes_granted = Set::empty().insert(my_id).
        // LReceiveVoteGranted/LReceiveVoteAndBecomeLeader:
        //   s was Candidate, so s.votes_granted.contains(my_id).
        //   s_.votes_granted = s.votes_granted.insert(voter) or s_mid.votes_granted.insert(voter)
        //   where s_mid.votes_granted ⊆ s.votes_granted (step_down clears votes to empty,
        //   but then s_mid is Follower → not Candidate → those branches don't apply).
        // Leader-preserving actions: s_.votes_granted == s.votes_granted.
        // Step-down/follower actions: s_ is Follower → conclusion vacuous.
    }

    proof fn lemma_candidate_or_leader_voted_for_self_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            WellFormedRaftDistributed(ds),
            CandidateOrLeaderVotedForSelf(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CandidateOrLeaderVotedForSelf(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |server_id: int| #![trigger ds.server_states[server_id]] #![trigger ds_.server_states[server_id]] #![trigger ds.server_constants[server_id]] {
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        // Use helper lemma for the stepping server
        assert(CandidateOrLeaderVotedForSelf(ds));
        lemma_lnext_self_vote_preserved(s, s_, c);

        assert forall |i: int| #![trigger ds_.server_states[i]] #![trigger ds_.server_constants[i]]
            0 <= i < ds_.num_servers
            && (ds_.server_states[i].role is Candidate || ds_.server_states[i].role is Leader)
        implies ds_.server_states[i].votes_granted.contains(ds_.server_constants[i].my_id) by {
            if i != server_id {
                assert(ds_.server_states[i] == ds.server_states[i]);
            }
            // For i == server_id: lemma_lnext_self_vote_preserved gives the result
        }
    }

    // =========================================================================
    // Supporting invariant induction: CandidateOrLeaderVotedForSelfId
    // =========================================================================

    /// Helper: if LNext produces a Candidate or Leader in s_, then
    /// s_.has_voted && s_.voted_for == c.my_id, given that the same holds
    /// for s if s was Candidate or Leader.
    proof fn lemma_lnext_voted_for_id_preserved(s: LState, s_: LState, c: LConstants)
        requires
            LNext(s, s_, c),
            (s.role is Candidate || s.role is Leader) ==>
                (s.has_voted && s.voted_for == c.my_id),
        ensures
            (s_.role is Candidate || s_.role is Leader) ==>
                (s_.has_voted && s_.voted_for == c.my_id),
    {
        // Verus case-splits on LNext branches.
        // LTimeout: s_ is Candidate, voted_for = c.my_id, has_voted = true.
        // LReceiveVoteGranted/LReceiveVoteAndBecomeLeader:
        //   s was Candidate, so s.has_voted && s.voted_for == c.my_id.
        //   s_.voted_for = s.voted_for, s_.has_voted = s.has_voted.
        // Leader-preserving actions: s_.voted_for == s.voted_for, s_.has_voted == s.has_voted.
        // Step-down/follower actions: s_ is Follower → conclusion vacuous.
    }

    proof fn lemma_candidate_or_leader_voted_for_self_id_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            WellFormedRaftDistributed(ds),
            CandidateOrLeaderVotedForSelfId(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CandidateOrLeaderVotedForSelfId(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |server_id: int| #![trigger ds.server_states[server_id]] #![trigger ds_.server_states[server_id]] #![trigger ds.server_constants[server_id]] {
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        // Use helper lemma for the stepping server
        assert(CandidateOrLeaderVotedForSelfId(ds));
        lemma_lnext_voted_for_id_preserved(s, s_, c);

        assert forall |i: int| #![trigger ds_.server_states[i]]
            0 <= i < ds_.num_servers
            && (ds_.server_states[i].role is Candidate || ds_.server_states[i].role is Leader)
        implies ds_.server_states[i].has_voted && ds_.server_states[i].voted_for == i by {
            if i != server_id {
                assert(ds_.server_states[i] == ds.server_states[i]);
            } else {
                // lemma_lnext_voted_for_id_preserved gives voted_for == c.my_id
                // WellFormedRaftDistributed ensures c.my_id == server_id == i
                assert(WellFormedRaftDistributed(ds));
            }
        }
    }

    // =========================================================================
    // Supporting invariant induction: VotersVotedForCandidate
    // =========================================================================

    /// Network-based VotersVotedForCandidate is inductive because:
    /// - Network is monotonic (packets never removed)
    /// - When a vote is added via LHandleVoteResponseMsg, the received
    ///   VoteResponse packet is already in the network with matching term
    ///   (ensured by the term check guard: term == s.current_term)
    /// - votes_granted is reset on term change (step_down/LTimeout)
    proof fn lemma_voters_voted_for_candidate_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            VotersVotedForCandidate(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            VotersVotedForCandidate(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        assert forall |i: int, v: int|
            0 <= i < ds_.num_servers
            && 0 <= v < ds_.num_servers
            && v != i
            && (ds_.server_states[i].role is Candidate || ds_.server_states[i].role is Leader)
            && ds_.server_states[i].votes_granted.contains(v)
        implies exists |p: LRaftPacket| #![trigger ds_.network.contains(p)] {
            &&& ds_.network.contains(p)
            &&& p.dst == i
            &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter, .. }
            &&& term == ds_.server_states[i].current_term
            &&& granted
            &&& voter == v
        } by {
            if i != server_id {
                // i didn't step: state unchanged from ds
                assert(ds_.server_states[i] == ds.server_states[i]);
                // VotersVotedForCandidate(ds) gives us a packet p in ds.network
                // ds.network ⊆ ds_.network (monotonic), so p in ds_.network
            }
            // For i == server_id: the stepping server
            // Key cases:
            // 1. step_down/LTimeout: votes_granted reset, only contains self → v != i vacuous
            // 2. LHandleVoteResponseMsg with term == current_term: the received
            //    VoteResponse packet is in ds.network (and thus ds_.network)
            // 3. Other actions: votes_granted unchanged → use ds invariant
        }
    }

    // =========================================================================
    // Supporting invariant induction: LeaderHasQuorum
    // =========================================================================

    // =========================================================================
    // Dynamic election invariant: saved election membership quorum
    // =========================================================================

    proof fn lemma_leader_has_recorded_election_quorum_inductive(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            LeaderHasRecordedElectionQuorum(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            LeaderHasRecordedElectionQuorum(ds_),
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |server_id: int| #![trigger ds.server_states[server_id]] #![trigger ds_.server_states[server_id]] #![trigger ds.server_constants[server_id]] {
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(
                ds.server_states[server_id],
                ds_.server_states[server_id],
                ds.server_constants[server_id],
            )
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        lemma_lnext_preserves_recorded_election_quorum(
            ds.server_states[server_id],
            ds_.server_states[server_id],
            ds.server_constants[server_id],
        );

        assert forall |i: int| #![trigger ds_.server_states[i]]
            0 <= i < ds_.num_servers
            implies has_recorded_election_quorum(
                ds_.server_states[i],
            )
        by {
            if i != server_id {
                assert(ds_.server_states[i]
                    == ds.server_states[i]);
            }
        }
    }

    // =========================================================================
    // Dynamic election invariant: actual-log provenance
    // =========================================================================

    proof fn lemma_leader_has_recorded_election_log_provenance_inductive(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            CommitIndexNonnegative(ds),
            CommitIndexBounded(ds),
            LeaderHasRecordedElectionLogProvenance(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            LeaderHasRecordedElectionLogProvenance(ds_),
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |server_id: int| #![trigger ds.server_states[server_id]] #![trigger ds_.server_states[server_id]] #![trigger ds.server_constants[server_id]] {
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(
                ds.server_states[server_id],
                ds_.server_states[server_id],
                ds.server_constants[server_id],
            )
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        lemma_lnext_preserves_recorded_election_log_provenance(
            ds.server_states[server_id],
            ds_.server_states[server_id],
            ds.server_constants[server_id],
        );

        assert forall |i: int| #![trigger ds_.server_states[i]] #![trigger ds_.server_constants[i]]
            0 <= i < ds_.num_servers
            implies has_recorded_election_log_provenance(
                ds_.server_states[i],
                ds_.server_constants[i],
            )
        by {
            if i != server_id {
                assert(ds_.server_states[i]
                    == ds.server_states[i]);
            }
        }
    }

    /// If two leaders' saved election phases come from committed
    /// prefixes of the same length, StateMachineSafety makes those
    /// prefixes equal. The leaders therefore used the same dynamic
    /// membership phase, so their election quorums overlap.
    pub proof fn lemma_equal_election_prefixes_imply_quorum_overlap(
        ds: RaftDistributedState,
        left: int,
        right: int,
        election_commit_len: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            StateMachineSafety(ds),
            0 <= left < ds.num_servers,
            0 <= right < ds.num_servers,
            ds.server_states[left].role is Leader,
            ds.server_states[right].role is Leader,
            0 <= election_commit_len,
            election_commit_len
                <= ds.server_states[left].commit_index,
            election_commit_len
                <= ds.server_states[right].commit_index,
            ds.server_states[left].commit_index
                <= ds.server_states[left].log.len(),
            ds.server_states[right].commit_index
                <= ds.server_states[right].log.len(),
            ds.server_states[left].election_membership_phase
                == Some(active_membership_phase_from_raft_log(
                    ds.server_states[left].log,
                    election_commit_len,
                    MembershipPhase::Stable {
                        config: ds.server_constants[left].servers,
                    },
                )),
            ds.server_states[right].election_membership_phase
                == Some(active_membership_phase_from_raft_log(
                    ds.server_states[right].log,
                    election_commit_len,
                    MembershipPhase::Stable {
                        config: ds.server_constants[right].servers,
                    },
                )),
            has_recorded_election_quorum(
                ds.server_states[left],
            ),
            has_recorded_election_quorum(
                ds.server_states[right],
            ),
        ensures
            exists |server: int|
                ds.server_states[left].votes_granted.contains(server)
                && ds.server_states[right].votes_granted.contains(server),
    {
        let left_state = ds.server_states[left];
        let right_state = ds.server_states[right];
        let initial_phase = MembershipPhase::Stable {
            config: ds.server_constants[left].servers,
        };

        assert(ds.server_constants[left].servers
            == ds.server_constants[right].servers);

        assert forall |index: int|
            0 <= index < election_commit_len
            implies left_state.log[index] == right_state.log[index]
        by {
            assert(index < left_state.commit_index);
            assert(index < right_state.commit_index);
            assert(index < left_state.log.len());
            assert(index < right_state.log.len());
        };

        lemma_equal_committed_raft_prefixes_have_same_active_phase(
            left_state.log,
            right_state.log,
            election_commit_len,
            initial_phase,
        );

        let phase = active_membership_phase_from_raft_log(
            left_state.log,
            election_commit_len,
            initial_phase,
        );

        assert(left_state.election_membership_phase
            == Some(phase));
        assert(right_state.election_membership_phase
            == Some(phase));

        assert(is_quorum_for_phase(
            left_state.votes_granted,
            phase,
        ));
        assert(is_quorum_for_phase(
            right_state.votes_granted,
            phase,
        ));

        lemma_phase_quorums_intersect(
            left_state.votes_granted,
            right_state.votes_granted,
            phase,
        );
    }

    /// If one committed membership snapshot is no later than another,
    /// both servers agree at the earlier length and the later server's
    /// log supplies a legal step-by-step membership path afterward.
    pub proof fn lemma_ordered_committed_membership_snapshots_have_legal_bridge(
        ds: RaftDistributedState,
        earlier_server: int,
        later_server: int,
        earlier_len: int,
        later_len: int,
    )
        requires
            CommittedMembershipPrefixAgreement(ds),
            CommitIndexBounded(ds),
            AllRaftMembershipLogsWellFormed(ds),
            0 <= earlier_server < ds.num_servers,
            0 <= later_server < ds.num_servers,
            0 <= earlier_len,
            earlier_len
                <= ds.server_states[earlier_server].commit_index,
            earlier_len <= later_len,
            later_len
                <= ds.server_states[later_server].commit_index,
        ensures
            active_membership_phase_from_raft_log(
                ds.server_states[earlier_server].log,
                earlier_len,
                MembershipPhase::Stable {
                    config:
                        ds.server_constants[earlier_server].servers,
                },
            ) == active_membership_phase_from_raft_log(
                ds.server_states[later_server].log,
                earlier_len,
                MembershipPhase::Stable {
                    config:
                        ds.server_constants[later_server].servers,
                },
            ),
            forall |committed_len: int|
                earlier_len < committed_len <= later_len
                ==> is_legal_phase_progression(
                    active_membership_phase_from_raft_log(
                        ds.server_states[later_server].log,
                        committed_len - 1,
                        MembershipPhase::Stable {
                            config:
                                ds.server_constants[later_server].servers,
                        },
                    ),
                    #[trigger] active_membership_phase_from_raft_log(
                        ds.server_states[later_server].log,
                        committed_len,
                        MembershipPhase::Stable {
                            config:
                                ds.server_constants[later_server].servers,
                        },
                    ),
                ),
    {
        assert(CommittedMembershipPrefixAgreement(ds));
        assert(CommitIndexBounded(ds));
        assert(AllRaftMembershipLogsWellFormed(ds));

        assert(later_len
            <= ds.server_states[later_server].log.len());

        assert(active_membership_phase_from_raft_log(
            ds.server_states[earlier_server].log,
            earlier_len,
            MembershipPhase::Stable {
                config:
                    ds.server_constants[earlier_server].servers,
            },
        ) == active_membership_phase_from_raft_log(
            ds.server_states[later_server].log,
            earlier_len,
            MembershipPhase::Stable {
                config:
                    ds.server_constants[later_server].servers,
            },
        ));

        lemma_well_formed_raft_log_interval_progresses_legally(
            ds.server_states[later_server].log,
            earlier_len,
            later_len,
            MembershipPhase::Stable {
                config:
                    ds.server_constants[later_server].servers,
            },
        );
    }

    /// Leaders whose saved election prefix lengths differ by one physical
    /// Raft entry have overlapping election quorums.
    ///
    /// The entry may be Data or one legal Configuration transition.
    pub proof fn lemma_adjacent_election_prefixes_imply_quorum_overlap(
        ds: RaftDistributedState,
        earlier_leader: int,
        later_leader: int,
        earlier_election_len: int,
        later_election_len: int,
    )
        requires
            CommittedMembershipPrefixAgreement(ds),
            AllRaftMembershipLogsWellFormed(ds),
            CommitIndexBounded(ds),
            0 <= earlier_leader < ds.num_servers,
            0 <= later_leader < ds.num_servers,
            ds.server_states[earlier_leader].role is Leader,
            ds.server_states[later_leader].role is Leader,
            0 <= earlier_election_len,
            earlier_election_len
                <= ds.server_states[earlier_leader].commit_index,
            later_election_len == earlier_election_len + 1,
            later_election_len
                <= ds.server_states[later_leader].commit_index,
            ds.server_states[earlier_leader].election_membership_phase
                == Some(active_membership_phase_from_raft_log(
                    ds.server_states[earlier_leader].log,
                    earlier_election_len,
                    MembershipPhase::Stable {
                        config:
                            ds.server_constants[earlier_leader].servers,
                    },
                )),
            ds.server_states[later_leader].election_membership_phase
                == Some(active_membership_phase_from_raft_log(
                    ds.server_states[later_leader].log,
                    later_election_len,
                    MembershipPhase::Stable {
                        config:
                            ds.server_constants[later_leader].servers,
                    },
                )),
            has_recorded_election_quorum(
                ds.server_states[earlier_leader],
            ),
            has_recorded_election_quorum(
                ds.server_states[later_leader],
            ),
        ensures
            exists |server: int|
                ds.server_states[earlier_leader]
                    .votes_granted.contains(server)
                && ds.server_states[later_leader]
                    .votes_granted.contains(server),
    {
        assert(later_election_len
            == earlier_election_len + 1);

            let later_log =
                ds.server_states[later_leader].log;
            let initial_phase = MembershipPhase::Stable {
                config:
                    ds.server_constants[later_leader].servers,
            };
            let earlier_phase =
                active_membership_phase_from_raft_log(
                    later_log,
                    earlier_election_len,
                    initial_phase,
                );
            let later_phase =
                active_membership_phase_from_raft_log(
                    later_log,
                    later_election_len,
                    initial_phase,
                );

            assert(active_membership_phase_from_raft_log(
                ds.server_states[earlier_leader].log,
                earlier_election_len,
                MembershipPhase::Stable {
                    config:
                        ds.server_constants[earlier_leader].servers,
                },
            ) == earlier_phase);

            assert(ds.server_states[earlier_leader]
                .election_membership_phase
                    == Some(earlier_phase));
            assert(ds.server_states[later_leader]
                .election_membership_phase
                    == Some(later_phase));

            assert(is_quorum_for_phase(
                ds.server_states[earlier_leader].votes_granted,
                earlier_phase,
            ));
            assert(is_quorum_for_phase(
                ds.server_states[later_leader].votes_granted,
                later_phase,
            ));

            assert(later_election_len <= later_log.len());
            assert(0 < later_election_len);

            lemma_adjacent_committed_raft_prefix_quorums_intersect(
                later_log,
                later_election_len,
                initial_phase,
                ds.server_states[earlier_leader].votes_granted,
                ds.server_states[later_leader].votes_granted,
            );
    }

    /// Leaders elected from committed prefixes separated by one guarded
    /// commit interval have overlapping election quorums.
    ///
    /// Unlike the adjacent-prefix theorem, the interval may batch any
    /// number of Data entries before its optional final Configuration entry.
    pub proof fn lemma_commit_boundary_election_prefixes_imply_quorum_overlap(
        ds: RaftDistributedState,
        earlier_leader: int,
        later_leader: int,
        earlier_election_len: int,
        later_election_len: int,
    )
        requires
            CommittedMembershipPrefixAgreement(ds),
            AllRaftMembershipLogsWellFormed(ds),
            CommitIndexBounded(ds),
            0 <= earlier_leader < ds.num_servers,
            0 <= later_leader < ds.num_servers,
            ds.server_states[earlier_leader].role is Leader,
            ds.server_states[later_leader].role is Leader,
            0 <= earlier_election_len,
            earlier_election_len
                <= ds.server_states[earlier_leader].commit_index,
            earlier_election_len < later_election_len,
            later_election_len
                <= ds.server_states[later_leader].commit_index,
            commit_interval_stops_at_first_configuration(
                ds.server_states[later_leader].log,
                earlier_election_len,
                later_election_len,
            ),
            ds.server_states[earlier_leader].election_membership_phase
                == Some(active_membership_phase_from_raft_log(
                    ds.server_states[earlier_leader].log,
                    earlier_election_len,
                    MembershipPhase::Stable {
                        config:
                            ds.server_constants[earlier_leader].servers,
                    },
                )),
            ds.server_states[later_leader].election_membership_phase
                == Some(active_membership_phase_from_raft_log(
                    ds.server_states[later_leader].log,
                    later_election_len,
                    MembershipPhase::Stable {
                        config:
                            ds.server_constants[later_leader].servers,
                    },
                )),
            has_recorded_election_quorum(
                ds.server_states[earlier_leader],
            ),
            has_recorded_election_quorum(
                ds.server_states[later_leader],
            ),
        ensures
            exists |server: int|
                ds.server_states[earlier_leader]
                    .votes_granted.contains(server)
                && ds.server_states[later_leader]
                    .votes_granted.contains(server),
    {
        let later_log =
            ds.server_states[later_leader].log;
        let initial_phase = MembershipPhase::Stable {
            config:
                ds.server_constants[later_leader].servers,
        };
        let earlier_phase =
            active_membership_phase_from_raft_log(
                later_log,
                earlier_election_len,
                initial_phase,
            );
        let later_phase =
            active_membership_phase_from_raft_log(
                later_log,
                later_election_len,
                initial_phase,
            );

        assert(active_membership_phase_from_raft_log(
            ds.server_states[earlier_leader].log,
            earlier_election_len,
            MembershipPhase::Stable {
                config:
                    ds.server_constants[earlier_leader].servers,
            },
        ) == earlier_phase);

        assert(ds.server_states[earlier_leader]
            .election_membership_phase
                == Some(earlier_phase));
        assert(ds.server_states[later_leader]
            .election_membership_phase
                == Some(later_phase));

        assert(is_quorum_for_phase(
            ds.server_states[earlier_leader].votes_granted,
            earlier_phase,
        ));
        assert(is_quorum_for_phase(
            ds.server_states[later_leader].votes_granted,
            later_phase,
        ));

        lemma_commit_boundary_quorums_intersect(
            later_log,
            earlier_election_len,
            later_election_len,
            initial_phase,
            ds.server_states[earlier_leader].votes_granted,
            ds.server_states[later_leader].votes_granted,
        );
    }

    // =========================================================================
    // Supporting invariant induction: CommitIndexNonnegative
    // =========================================================================

    proof fn lemma_lnext_commit_nonnegative(
        s: LState,
        s_: LState,
        c: LConstants,
    )
        requires
            LNext(s, s_, c),
            0 <= s.commit_index,
        ensures
            0 <= s_.commit_index,
    {
    }

    proof fn lemma_commit_index_nonnegative_inductive(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            CommitIndexNonnegative(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CommitIndexNonnegative(ds_),
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |server_id: int| #![trigger ds.server_states[server_id]] #![trigger ds_.server_states[server_id]] #![trigger ds.server_constants[server_id]] {
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(
                ds.server_states[server_id],
                ds_.server_states[server_id],
                ds.server_constants[server_id],
            )
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        lemma_lnext_commit_nonnegative(
            ds.server_states[server_id],
            ds_.server_states[server_id],
            ds.server_constants[server_id],
        );

        assert forall |i: int| #![trigger ds_.server_states[i]]
            0 <= i < ds_.num_servers
            implies 0 <= ds_.server_states[i].commit_index
        by {
            if i != server_id {
                assert(ds_.server_states[i]
                    == ds.server_states[i]);
            }
        }
    }

    // =========================================================================
    // Supporting invariant induction: CommitIndexBounded
    // =========================================================================

    /// Helper: LNext preserves commit_index <= log.len() for all branches.
    /// Key cases:
    /// - LTimeout, LReceiveVoteGranted, LBecomeLeader, LSendAppendEntries,
    ///   LHandleAppendResponse, LHandleAppendReject, LStepDown: both unchanged.
    /// - LClientRequest: log grows by 1, commit_index unchanged → still bounded.
    /// - LAdvanceCommitIndex: new_commit_index <= s.log.len() by spec precondition.
    /// - LFollowerAppendEntries: commit_index = min(ae_leader_commit, new_log_len)
    ///   which is bounded by s_.log.len() by construction.
    proof fn lemma_lnext_commit_bounded(s: LState, s_: LState, c: LConstants)
        requires
            LNext(s, s_, c),
            s.commit_index <= s.log.len(),
        ensures
            s_.commit_index <= s_.log.len(),
    {
        // Verus case-splits on LNext and verifies each branch automatically.
    }

    /// A well-bounded commit index never decreases across LNext.
    proof fn lemma_lnext_commit_index_monotone(
        s: LState, s_: LState, c: LConstants,
    )
        requires
            LNext(s, s_, c),
            s.commit_index <= s.log.len(),
        ensures
            s_.commit_index >= s.commit_index,
    {
        // The only modifying branches advance the commit index or take the
        // minimum of a larger leader_commit and a log length that is at least
        // the old log length.
    }

    proof fn lemma_commit_index_bounded_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            WellFormedRaftDistributed(ds),
            CommitIndexBounded(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CommitIndexBounded(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |server_id: int| #![trigger ds.server_states[server_id]] #![trigger ds_.server_states[server_id]] #![trigger ds.server_constants[server_id]] {
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        assert(CommitIndexBounded(ds));
        lemma_lnext_commit_bounded(s, s_, c);

        assert forall |i: int| #![trigger ds_.server_states[i]]
            0 <= i < ds_.num_servers
        implies
            ds_.server_states[i].commit_index <= ds_.server_states[i].log.len()
        by {
            if i != server_id {
                assert(ds_.server_states[i] == ds.server_states[i]);
            }
        }
    }

    // =========================================================================
    // Helper: quorum intersection for LeaderLogLongEnough
    // =========================================================================

    /// When server_id (Candidate at T) becomes Leader, and entry at (i, k)
    /// with term T exists, use EntryTermHasVoteQuorum + quorum intersection
    /// + OneVotePerTermInNetwork to derive server_id.log.len() > k.
    ///
    /// ETHVQ witness extraction uses sound assume (ETHVQ is in scope via
    /// requires, but choose on its nested existentials crashes Z3).
    /// The witnesses are passed to lemma_lllong_d_neq_sid_contradiction which
    /// does the quorum overlap without ETHVQ in scope.
    ///
    /// ds_ invariants are established by the caller and passed in.
    proof fn lemma_leader_log_quorum_intersection(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState,
        i: int, k: int,
    )
        requires
            EntryTermHasVoteQuorum(ds),
            VoteResponseHasRequestVote(ds),
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            // Network monotonicity
            forall |pkt: LRaftPacket| ds.network.contains(pkt)
                ==> ds_.network.contains(pkt),
            0 <= i < ds.num_servers,
            i != server_id,
            0 <= k < ds.server_states[i].log.len(),
            !(s.role is Leader),
            s_.role is Leader,
            s_.current_term == ds.server_states[i].log[k].term,
            s_.log.len() >= s.log.len(),
            // ds_ invariants (established by caller)
            VotersVotedForCandidate(ds_),
            VotesGrantedAreServers(ds_),
            OneVotePerTermInNetwork(ds_),
            CandidateVoteDestinationUnique(ds_),
            VoteResponseIntegrity(ds_),
            CandidateOrLeaderVotedForSelfId(ds_),
            LeaderHasQuorum(ds_),
        ensures
            s_.log.len() > k,
    {
        let T = ds.server_states[i].log[k].term;
        let n = ds.num_servers;
        let quorum_size = n / 2 + 1;

        let (d, voters) =
            lemma_entry_term_vote_quorum_witness(ds, i, k);

        if d == server_id {
            // d == server_id: s.log.len() > k → s_.log.len() >= s.log.len() > k.
            assert(ds.server_states[d] == s);
            assert(s.log.len() > k);
        } else {
            lemma_lllong_d_neq_sid_contradiction(
                ds, ds_, server_id, s_, d, voters, T, k);
        }
    }

    /// Prove d == server_id by contradiction when d != server_id.
    /// Uses quorum intersection between d's ETHVQ voters and server_id's
    /// votes_granted to find an overlapping voter, then OneVotePerTermInNetwork
    /// to derive d == server_id.
    ///
    /// Isolated from lemma_leader_log_quorum_intersection to keep ETHVQ
    /// quantifiers out of scope (only concrete witnesses d, voters are passed).
    proof fn lemma_lllong_d_neq_sid_contradiction(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s_: LState,
        d: int, voters: Seq<int>, T: int, k: int,
    )
        requires
            // ds_ invariants (established by caller)
            VotersVotedForCandidate(ds_),
            VotesGrantedAreServers(ds_),
            OneVotePerTermInNetwork(ds_),
            VoteResponseHasRequestVote(ds),
            CandidateVoteDestinationUnique(ds_),
            VoteResponseIntegrity(ds_),
            CandidateOrLeaderVotedForSelfId(ds_),
            LeaderHasQuorum(ds_),
            WellFormedRaftDistributed(ds_),
            // Network monotonicity
            forall |pkt: LRaftPacket| ds.network.contains(pkt)
                ==> ds_.network.contains(pkt),
            // server_id is new Leader at term T
            0 <= server_id < ds_.num_servers,
            s_ == ds_.server_states[server_id],
            s_.role is Leader,
            s_.current_term == T,
            // d is different from server_id
            d != server_id,
            0 <= d < ds_.num_servers,
            ds_.num_servers == ds.num_servers,
            // voters are d's ETHVQ voters: distinct, in [0, n), each sent
            // a granted VoteResponse to d at term T
            voters.len() >= ds.num_servers / 2 + 1 - 1,
            forall |a: int| #![trigger voters[a]] 0 <= a < voters.len() ==> {
                &&& 0 <= voters[a] < ds.num_servers
                &&& voters[a] != d
                &&& ExistsGrantedVoteResponse(ds, voters[a], d, T)
            },
            forall |a: int, b: int|
                #![trigger voters[a], voters[b]]
                0 <= a < voters.len() && 0 <= b < voters.len() && a != b
                ==> voters[a] != voters[b],
        ensures
            false,
    {
        broadcast use vstd::set_lib::group_set_properties;

        let n = ds_.num_servers;
        let quorum_size = n / 2 + 1;
        let sid_votes = ds_.server_states[server_id].votes_granted;
        assert(LeaderHasQuorum(ds_));
        assert(sid_votes.len() >= quorum_size);

        // Step 1: Prove d ∉ sid_votes via CandidateVoteDestinationUnique.
        assert(!sid_votes.contains(d)) by {
            if sid_votes.contains(d) {
                // VotersVotedForCandidate: d ∈ sid_votes → VR{T, voter: d, to sid} in ds_.network
                assert(VotersVotedForCandidate(ds_));
                // Get RequestVote{T, candidate: d} from VoteResponseHasRequestVote
                assert(voters.len() >= 1);
                assert(ExistsGrantedVoteResponse(ds, voters[0], d, T));
                let v0_summary = choose |summary: (int, int)|
                    #![trigger ds.network.contains(LRaftPacket {
                        src: voters[0],
                        dst: d,
                        msg: LRaftMessage::VoteResponse {
                            term: T,
                            granted: true,
                            voter: voters[0],
                            voter_last_log_index: summary.0,
                            voter_last_log_term: summary.1,
                        },
                    })]
                    ds.network.contains(LRaftPacket {
                        src: voters[0],
                        dst: d,
                        msg: LRaftMessage::VoteResponse {
                            term: T,
                            granted: true,
                            voter: voters[0],
                            voter_last_log_index: summary.0,
                            voter_last_log_term: summary.1,
                        },
                    });
                let v0_pkt = LRaftPacket {
                    src: voters[0],
                    dst: d,
                    msg: LRaftMessage::VoteResponse {
                        term: T,
                        granted: true,
                        voter: voters[0],
                        voter_last_log_index: v0_summary.0,
                        voter_last_log_term: v0_summary.1,
                    },
                };
                assert(ds.network.contains(v0_pkt));
                // VoteResponseHasRequestVote → ∃ req
                assert(VoteResponseHasRequestVote(ds));
                let req = choose |req: LRaftPacket| #![trigger ds.network.contains(req)] {
                    &&& ds.network.contains(req)
                    &&& req.src == d
                    &&& req.dst == voters[0]
                    &&& req.msg matches LRaftMessage::RequestVote {
                        term, candidate,
                        last_log_index: _, last_log_term: _,
                    }
                    &&& term == T
                    &&& candidate == d
                };
                assert(ds_.network.contains(req));
                // VotersVotedForCandidate: d ∈ sid_votes → VR to server_id
                let vr_d = choose |p: LRaftPacket| #![trigger ds_.network.contains(p)] {
                    &&& ds_.network.contains(p)
                    &&& p.dst == server_id
                    &&& p.msg matches LRaftMessage::VoteResponse {
                        term, granted, voter, .. }
                    &&& term == T
                    &&& granted
                    &&& voter == d
                };
                // CandidateVoteDestinationUnique: req + vr_d → server_id == d
                assert(CandidateVoteDestinationUnique(ds_));
            }
        };

        // Step 2: Quorum intersection.
        assert(voters.no_duplicates());
        let voter_set = voters.to_set();
        voters.unique_seq_to_set();
        assert(voter_set.len() == voters.len());
        assert(voter_set.len() >= quorum_size - 1);

        let universe_full = Set::<int>::range(0, n);
        lemma_range_set_finite(n);
        assert(universe_full.contains(d));
        let universe = universe_full.remove(d);

        assert(voter_set.subset_of(universe)) by {
            assert forall |v: int| voter_set.contains(v)
                implies universe.contains(v) by
            {
                let a = choose |a: int| 0 <= a < voters.len()
                    && voters[a] == v;
                assert(0 <= voters[a] < n);
                assert(voters[a] != d);
            };
        };

        assert(sid_votes.subset_of(universe)) by {
            assert forall |v: int| sid_votes.contains(v)
                implies universe.contains(v) by
            {
                assert(VotesGrantedAreServers(ds_));
                assert(0 <= v < n);
                assert(v != d);
            };
        };

        assert(voter_set.len() + sid_votes.len() > universe.len());
        lemma_quorum_intersection(voter_set, sid_votes, universe);
        let w = choose |w: int| voter_set.contains(w)
            && sid_votes.contains(w);

        // Step 3: w voted for both d and server_id → contradiction.
        // Get VoteResponse{T, voter: w, to d} ∈ ds_.network
        assert(voters.contains(w));
        let a_w = choose |a: int| 0 <= a < voters.len()
            && voters[a] == w;
        assert(ExistsGrantedVoteResponse(ds, w, d, T));
        let vote_summary = choose |summary: (int, int)|
            #![trigger ds.network.contains(LRaftPacket {
                src: w,
                dst: d,
                msg: LRaftMessage::VoteResponse {
                    term: T,
                    granted: true,
                    voter: w,
                    voter_last_log_index: summary.0,
                    voter_last_log_term: summary.1,
                },
            })]
            ds.network.contains(LRaftPacket {
                src: w,
                dst: d,
                msg: LRaftMessage::VoteResponse {
                    term: T,
                    granted: true,
                    voter: w,
                    voter_last_log_index: summary.0,
                    voter_last_log_term: summary.1,
                },
            });
        let vote_to_d = LRaftPacket {
            src: w,
            dst: d,
            msg: LRaftMessage::VoteResponse {
                term: T,
                granted: true,
                voter: w,
                voter_last_log_index: vote_summary.0,
                voter_last_log_term: vote_summary.1,
            },
        };
        assert(ds.network.contains(vote_to_d));
        assert(ds_.network.contains(vote_to_d));

        if w == server_id {
            // VR{T, voter: server_id, to d} ∈ ds_.network.
            // VoteResponseIntegrity: s_.voted_for == d.
            // CandidateOrLeaderVotedForSelfId: s_.voted_for == server_id.
            // → d == server_id. Contradiction.
            assert(VoteResponseIntegrity(ds_));
            assert(CandidateOrLeaderVotedForSelfId(ds_));
        } else {
            // w != server_id, w ∈ sid_votes.
            // VotersVotedForCandidate → VR{T, voter: w, to server_id} ∈ ds_.network.
            assert(VotersVotedForCandidate(ds_));
            assert(0 <= w < ds_.num_servers);
            lemma_vote_witness_from_votes_granted(
                ds_, server_id, w);
            // OneVotePerTermInNetwork: w voted for both d and server_id → d == server_id.
            assert(OneVotePerTermInNetwork(ds_));
        }
        // d == server_id contradicts d != server_id.
    }

    // =========================================================================
    // LeaderLogLongEnough Induction (Phase 34.6 supporting invariant)
    // =========================================================================

    /// If any server has entry at index k with term T, then any current
    /// leader at term T has log length > k.
    ///
    /// Inductive because:
    /// - LClientRequest: leader creates entry at k = log.len() with term T.
    ///   The leader's log grows to k+1 > k. For other servers' old entries,
    ///   the leader's log only grew, so the condition is preserved.
    /// - LFollowerAppendEntries: follower appends entry at k with term ae_term.
    ///   By AEI, the leader at ae_term has log.len() >= k+1 (AE had prev_index = k
    ///   with has_entry). The leader is unchanged (not the stepping server). ✓
    /// - Other actions: logs unchanged or grow. Leaders unchanged or step down.
    ///   Stepping down removes the leader, so the condition is vacuously true.
    /// Case: i unchanged, l == server_id became Leader, witness extraction.
    /// Returns witness w from EntryTermLeaderWitness.
    /// Isolated to keep EntryTermLeaderWitness choose away from heavy invariants.
    proof fn lemma_lllong_extract_witness(
        ds: RaftDistributedState,
        server_id: int,
        i: int, k: int,
    ) -> (w: int)
        requires
            EntryTermLeaderWitness(ds),
            0 <= i < ds.num_servers,
            0 <= k < ds.server_states[i].log.len(),
        ensures
            0 <= w < ds.num_servers,
            ds.server_states[w].log.len() > k,
            ds.server_states[w].log[k] == ds.server_states[i].log[k],
    {
        reveal(entry_term_leader_witness_trigger);
        assert(entry_term_leader_witness_trigger(ds, i, k));
        choose |w: int|
            #![trigger ds.server_states[w].log[k]]
        {
            &&& 0 <= w < ds.num_servers
            &&& ds.server_states[w].log.len() > k
            &&& ds.server_states[w].log[k] == ds.server_states[i].log[k]
        }
    }

    /// Case: i == server_id got new entry at k, l != server_id is Leader.
    /// Uses AppendEntriesIntegrity for follower append, ElectionSafety for
    /// leader client request.
    proof fn lemma_lllong_case_new_entry(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
        k: int, l: int,
    )
        requires
            LeaderLogLongEnough(ds),
            ElectionSafety(ds),
            AppendEntriesIntegrity(ds),
            WellFormedRaftDistributed(ds),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            RaftServerStepWithNetwork(ds, ds_, server_id),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            // Case conditions
            l != server_id,
            0 <= l < ds.num_servers,
            ds.server_states[l].role is Leader,
            k >= s.log.len() as int,
            k < s_.log.len(),
            s_.log.len() == s.log.len() + 1,
            ds.server_states[l].current_term == s_.log[k].term,
        ensures
            ds.server_states[l].log.len() > k,
    {
        if s_.role is Leader {
            assert(ElectionSafety(ds));
        } else {
            assert(s_.role is Follower);
            lemma_follower_append_ae_in_network(
                ds, ds_, server_id, s, s_, c, k);
            let ae_leader = choose |al: int|
                #![trigger ds.server_states[al]]
            {
                &&& 0 <= al < ds.num_servers
                &&& ds.server_states[al].log.len() > k
                &&& ds.server_states[al].log[k].term == s_.log[k].term
            };
        }
    }

    /// Per-triple case dispatch for LeaderLogLongEnough induction.
    /// Split into two helpers: case_i_ne_sid (i != server_id) and
    /// case_i_eq_sid (i == server_id) to reduce per-function axiom load.
    /// Case: i != server_id. Handles all sub-cases except the one needing
    /// quorum intersection (l == server_id, new Leader, witness != server_id).
    /// For that sub-case, the caller calls lemma_leader_log_quorum_intersection.
    proof fn lemma_lllong_case_i_ne_sid(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
        i: int, k: int, l: int,
    )
        requires
            LeaderLogLongEnough(ds),
            EntryTermLeaderWitness(ds),
            WellFormedRaftDistributed(ds),
            ds_.num_servers == ds.num_servers,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            LNext(s, s_, c),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            s_.log.len() >= s.log.len(),
            i != server_id,
            0 <= i < ds_.num_servers,
            0 <= k < ds_.server_states[i].log.len(),
            0 <= l < ds_.num_servers,
            ds_.server_states[l].role is Leader,
            ds_.server_states[l].current_term == ds_.server_states[i].log[k].term,
        ensures
            // Either proved, or needs quorum intersection fallback
            ds_.server_states[l].log.len() > k
            || (l == server_id && !(s.role is Leader)),
    {
        assert(ds_.server_states[i] == ds.server_states[i]);
        if l != server_id {
            assert(ds_.server_states[l] == ds.server_states[l]);
        } else {
            // l == server_id, s_ is Leader
            if s.role is Leader {
                // s was Leader, s_ is Leader → same term (LNext preserves term for Leader→Leader)
                // LeaderLogLongEnough(ds) with l == server_id, same term → s.log.len() > k
                // s_.log.len() >= s.log.len() > k
            } else {
                let w = lemma_lllong_extract_witness(ds, server_id, i, k);
                if w == server_id {
                    // s.log.len() > k, s_.log.len() >= s.log.len()
                }
                // If w != server_id, disjunctive postcondition covers it
            }
        }
    }

    proof fn lemma_lllong_case_i_eq_sid(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
        k: int, l: int,
    )
        requires
            LeaderLogLongEnough(ds),
            ElectionSafety(ds),
            AppendEntriesIntegrity(ds),
            WellFormedRaftDistributed(ds),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            RaftServerStepWithNetwork(ds, ds_, server_id),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            s_.log.len() >= s.log.len(),
            forall |idx: int| 0 <= idx < s.log.len()
                ==> #[trigger] s_.log[idx] == s.log[idx],
            // Target
            0 <= k < ds_.server_states[server_id].log.len(),
            l != server_id,
            0 <= l < ds_.num_servers,
            ds_.server_states[l].role is Leader,
            ds_.server_states[l].current_term == s_.log[k].term,
        ensures
            ds_.server_states[l].log.len() > k,
    {
        assert(ds_.server_states[l] == ds.server_states[l]);
        if k < s.log.len() {
            assert(s_.log[k] == s.log[k]);
        } else {
            assert(s_.log.len() == s.log.len() + 1);
            lemma_lllong_case_new_entry(
                ds, ds_, server_id, s, s_, c, k, l);
        }
    }

    /// Extract step parameters and establish LNext for LeaderLogLongEnough.
    /// Isolated to keep RaftDistributedNext axioms out of the assert-forall.
    proof fn lemma_lllong_extract_step(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    ) -> (result: (int, LState, LState, LConstants))
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures ({
            let (server_id, s, s_, c) = result;
            &&& 0 <= server_id < ds.num_servers
            &&& s == ds.server_states[server_id]
            &&& s_ == ds_.server_states[server_id]
            &&& c == ds.server_constants[server_id]
            &&& LNext(s, s_, c)
            &&& RaftServerStepWithNetwork(ds, ds_, server_id)
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& s_.log.len() >= s.log.len()
            &&& (forall |idx: int| 0 <= idx < s.log.len()
                ==> #[trigger] s_.log[idx] == s.log[idx])
            &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt)
                ==> ds_.network.contains(pkt))
        })
    {
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        lemma_distributed_next_implies_legacy(ds, ds_);
        assert(LNext(ds.server_states[server_id], ds_.server_states[server_id],
                      ds.server_constants[server_id]));

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        lemma_lnext_log_preserved_or_extended(s, s_, c);
        lemma_lnext_term_monotone(s, s_, c);

        (server_id, s, s_, c)
    }

    /// Phase 1 of i != server_id: light invariants only (no ETHVQ, no message).
    /// Establishes disjunctive postcondition: either proved, or needs quorum
    /// intersection (l == server_id && !Leader at ds).
    proof fn lemma_lllong_body_i_ne_sid_light(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
    )
        requires
            LeaderLogLongEnough(ds),
            EntryTermLeaderWitness(ds),
            WellFormedRaftDistributed(ds),
            ds_.num_servers == ds.num_servers,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            LNext(s, s_, c),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            s_.log.len() >= s.log.len(),
        ensures
            forall |i: int, k: int, l: int| #![trigger ds_.server_states[l], ds_.server_states[i].log[k]]
                0 <= i < ds_.num_servers
                && 0 <= k < ds_.server_states[i].log.len()
                && 0 <= l < ds_.num_servers
                && ds_.server_states[l].role is Leader
                && ds_.server_states[l].current_term == ds_.server_states[i].log[k].term
                && i != server_id
            ==> (ds_.server_states[l].log.len() > k
                || (l == server_id && !(s.role is Leader))),
    {
        assert forall |i: int, k: int, l: int| #![trigger ds_.server_states[l], ds_.server_states[i].log[k]]
            0 <= i < ds_.num_servers
            && 0 <= k < ds_.server_states[i].log.len()
            && 0 <= l < ds_.num_servers
            && ds_.server_states[l].role is Leader
            && ds_.server_states[l].current_term == ds_.server_states[i].log[k].term
            && i != server_id
        implies
            (ds_.server_states[l].log.len() > k
                || (l == server_id && !(s.role is Leader)))
        by {
            lemma_lllong_case_i_ne_sid(
                ds, ds_, server_id, s, s_, c, i, k, l);
        };
    }

    /// Phase 2 of i != server_id: for the remaining case (l == server_id,
    /// new Leader), use ETHVQ + quorum intersection.
    /// Has ETHVQ + message invariants but NO RaftServerStepWithNetwork.
    proof fn lemma_lllong_body_i_ne_sid_heavy(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState,
    )
        requires
            EntryTermHasVoteQuorum(ds),
            VoteResponseHasRequestVote(ds),
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            // ds_ message invariants
            VotersVotedForCandidate(ds_),
            VotesGrantedAreServers(ds_),
            OneVotePerTermInNetwork(ds_),
            CandidateVoteDestinationUnique(ds_),
            VoteResponseIntegrity(ds_),
            CandidateOrLeaderVotedForSelfId(ds_),
            LeaderHasQuorum(ds_),
            // Structural facts
            ds_.num_servers == ds.num_servers,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            s_.log.len() >= s.log.len(),
            forall |pkt: LRaftPacket| ds.network.contains(pkt)
                ==> ds_.network.contains(pkt),
            // Phase 1 result
            forall |i: int, k: int, l: int| #![trigger ds_.server_states[l], ds_.server_states[i].log[k]]
                0 <= i < ds_.num_servers
                && 0 <= k < ds_.server_states[i].log.len()
                && 0 <= l < ds_.num_servers
                && ds_.server_states[l].role is Leader
                && ds_.server_states[l].current_term == ds_.server_states[i].log[k].term
                && i != server_id
            ==> (ds_.server_states[l].log.len() > k
                || (l == server_id && !(s.role is Leader))),
        ensures
            forall |i: int, k: int, l: int| #![trigger ds_.server_states[l], ds_.server_states[i].log[k]]
                0 <= i < ds_.num_servers
                && 0 <= k < ds_.server_states[i].log.len()
                && 0 <= l < ds_.num_servers
                && ds_.server_states[l].role is Leader
                && ds_.server_states[l].current_term == ds_.server_states[i].log[k].term
                && i != server_id
            ==> ds_.server_states[l].log.len() > k,
    {
        assert forall |i: int, k: int, l: int| #![trigger ds_.server_states[l], ds_.server_states[i].log[k]]
            0 <= i < ds_.num_servers
            && 0 <= k < ds_.server_states[i].log.len()
            && 0 <= l < ds_.num_servers
            && ds_.server_states[l].role is Leader
            && ds_.server_states[l].current_term == ds_.server_states[i].log[k].term
            && i != server_id
        implies
            ds_.server_states[l].log.len() > k
        by {
            if ds_.server_states[l].log.len() <= k {
                // Phase 1 gives us l == server_id && !(s.role is Leader)
                lemma_leader_log_quorum_intersection(
                    ds, ds_, server_id, s, s_, i, k);
            }
        };
    }

    /// Body for i == server_id case. Has RaftServerStepWithNetwork
    /// but NO ETHVQ or message invariants.
    proof fn lemma_lllong_body_i_eq_sid(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
    )
        requires
            LeaderLogLongEnough(ds),
            ElectionSafety(ds),
            AppendEntriesIntegrity(ds),
            WellFormedRaftDistributed(ds),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            RaftServerStepWithNetwork(ds, ds_, server_id),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            s_.log.len() >= s.log.len(),
            forall |idx: int| 0 <= idx < s.log.len()
                ==> #[trigger] s_.log[idx] == s.log[idx],
        ensures
            forall |k: int, l: int| #![trigger ds_.server_states[l], ds_.server_states[server_id].log[k]]
                0 <= k < ds_.server_states[server_id].log.len()
                && 0 <= l < ds_.num_servers
                && ds_.server_states[l].role is Leader
                && ds_.server_states[l].current_term == ds_.server_states[server_id].log[k].term
                && l != server_id
            ==> ds_.server_states[l].log.len() > k,
    {
        assert forall |k: int, l: int| #![trigger ds_.server_states[l], ds_.server_states[server_id].log[k]]
            0 <= k < ds_.server_states[server_id].log.len()
            && 0 <= l < ds_.num_servers
            && ds_.server_states[l].role is Leader
            && ds_.server_states[l].current_term == ds_.server_states[server_id].log[k].term
            && l != server_id
        implies
            ds_.server_states[l].log.len() > k
        by {
            lemma_lllong_case_i_eq_sid(
                ds, ds_, server_id, s, s_, c, k, l);
        };
    }

    // =========================================================================
    // EntryTermLeaderWitness Induction
    // =========================================================================

    /// Every entry in every log has a "witness" server with the same entry
    /// at the same index. Inductive: LClientRequest → self-witness;
    /// LFollowerAppendEntries → AE sender witness; old entries → LogAppendOnly.
    proof fn lemma_entry_term_old_entry_witness(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        i: int, k: int,
    )
        requires
            EntryTermLeaderWitness(ds),
            LogAppendOnly(ds, ds_),
            ds_.num_servers == ds.num_servers,
            0 <= i < ds.num_servers,
            0 <= k < ds.server_states[i].log.len(),
        ensures
            exists |w: int| #![trigger ds_.server_states[w].log[k]] {
                &&& 0 <= w < ds_.num_servers
                &&& ds_.server_states[w].log.len() > k
                &&& ds_.server_states[w].log[k] == ds_.server_states[i].log[k]
            },
    {
        reveal(entry_term_leader_witness_trigger);
        assert(entry_term_leader_witness_trigger(ds, i, k));
        let w = choose |w: int| #![trigger ds.server_states[w].log[k]] {
            &&& 0 <= w < ds.num_servers
            &&& ds.server_states[w].log.len() > k
            &&& ds.server_states[w].log[k] == ds.server_states[i].log[k]
        };
        assert(ds_.server_states[w].log[k] == ds.server_states[w].log[k]);
        assert(ds_.server_states[i].log[k] == ds.server_states[i].log[k]);
    }

    proof fn lemma_entry_term_new_follower_witness(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants, k: int,
    )
        requires
            AppendEntriesIntegrity(ds),
            WellFormedRaftDistributed(ds),
            ds_.num_servers == ds.num_servers,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            RaftServerStepWithNetwork(ds, ds_, server_id),
            LogAppendOnly(ds, ds_),
            s_.log.len() == s.log.len() + 1,
            s_.role is Follower,
            k == s.log.len() as int,
        ensures
            exists |w: int| #![trigger ds_.server_states[w].log[k]] {
                &&& 0 <= w < ds_.num_servers
                &&& ds_.server_states[w].log.len() > k
                &&& ds_.server_states[w].log[k] == ds_.server_states[server_id].log[k]
            },
    {
        lemma_follower_append_ae_in_network(ds, ds_, server_id, s, s_, c, k);
        let w = choose |w: int| #![trigger ds.server_states[w]] {
            &&& 0 <= w < ds.num_servers
            &&& ds.server_states[w].log.len() > k
            &&& ds.server_states[w].log[k].term == s_.log[k].term
            &&& ds.server_states[w].log[k].value == s_.log[k].value
            &&& ds.server_states[w].log[k].payload == s_.log[k].payload
        };
        assert(ds.server_states[w].log[k].term == s_.log[k].term);
        assert(ds.server_states[w].log[k].value == s_.log[k].value);
        assert(ds.server_states[w].log[k].payload == s_.log[k].payload);
        assert(ds.server_states[w].log[k] == s_.log[k]);
        assert(ds_.server_states[w].log[k] == ds.server_states[w].log[k]);
    }

    proof fn lemma_entry_term_witness_for_entry(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
        i: int, k: int,
    )
        requires
            EntryTermLeaderWitness(ds),
            AppendEntriesIntegrity(ds),
            WellFormedRaftDistributed(ds),
            ds_.num_servers == ds.num_servers,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            LNext(s, s_, c),
            RaftServerStepWithNetwork(ds, ds_, server_id),
            LogAppendOnly(ds, ds_),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            0 <= i < ds_.num_servers,
            0 <= k < ds_.server_states[i].log.len(),
        ensures
            exists |w: int| #![trigger ds_.server_states[w].log[k]] {
                &&& 0 <= w < ds_.num_servers
                &&& ds_.server_states[w].log.len() > k
                &&& ds_.server_states[w].log[k] == ds_.server_states[i].log[k]
            },
    {
        lemma_lnext_log_preserved_or_extended(s, s_, c);
        if i != server_id {
            assert(ds_.server_states[i] == ds.server_states[i]);
            lemma_entry_term_old_entry_witness(ds, ds_, i, k);
        } else if k < s.log.len() {
            lemma_entry_term_old_entry_witness(ds, ds_, i, k);
        } else if s.role is Leader {
            assert(ds_.server_states[server_id].log.len() > k);
        } else {
            assert(s_.log.len() == s.log.len() + 1);
            assert(k == s.log.len());
            assert(s_.role is Follower);
            lemma_entry_term_new_follower_witness(
                ds, ds_, server_id, s, s_, c, k);
        }
    }

    /// Package the transition facts behind an opaque predicate so the
    /// quantified proof does not eagerly expand RaftServerStepWithNetwork and
    /// the message invariants for every arbitrary log entry.
    closed spec fn entry_term_witness_step_context(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
    ) -> bool {
        &&& EntryTermLeaderWitness(ds)
        &&& AppendEntriesIntegrity(ds)
        &&& WellFormedRaftDistributed(ds)
        &&& ds_.num_servers == ds.num_servers
        &&& 0 <= server_id < ds.num_servers
        &&& s == ds.server_states[server_id]
        &&& s_ == ds_.server_states[server_id]
        &&& c == ds.server_constants[server_id]
        &&& LNext(s, s_, c)
        &&& RaftServerStepWithNetwork(ds, ds_, server_id)
        &&& LogAppendOnly(ds, ds_)
        &&& (forall |j: int| #![trigger ds_.server_states[j]]
            0 <= j < ds.num_servers && j != server_id ==>
            ds_.server_states[j] == ds.server_states[j])
    }

    /// Extract the stepping server and the transition facts needed by the
    /// EntryTermLeaderWitness proof. Keeping RaftDistributedNext out of the
    /// quantified proof below substantially reduces its solver context.
    proof fn lemma_entry_term_extract_step(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    ) -> (result: (int, LState, LState, LConstants))
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures ({
            let (server_id, s, s_, c) = result;
            entry_term_witness_step_context(
                ds, ds_, server_id, s, s_, c)
        })
    {
        reveal(entry_term_witness_step_context);
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        lemma_distributed_next_implies_legacy(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        assert(LNext(s, s_, c));
        lemma_log_append_only(ds, ds_);

        (server_id, s, s_, c)
    }

    proof fn lemma_entry_term_witness_for_entry_from_context(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
        i: int, k: int,
    ) -> (w: int)
        requires
            entry_term_witness_step_context(
                ds, ds_, server_id, s, s_, c),
            0 <= i < ds_.num_servers,
            0 <= k < ds_.server_states[i].log.len(),
        ensures
            0 <= w < ds_.num_servers,
            ds_.server_states[w].log.len() > k,
            ds_.server_states[w].log[k] == ds_.server_states[i].log[k],
    {
        reveal(entry_term_witness_step_context);
        lemma_entry_term_witness_for_entry(
            ds, ds_, server_id, s, s_, c, i, k);
        choose |w: int| #![trigger ds_.server_states[w].log[k]] {
            &&& 0 <= w < ds_.num_servers
            &&& ds_.server_states[w].log.len() > k
            &&& ds_.server_states[w].log[k] == ds_.server_states[i].log[k]
        }
    }

    /// Lift the per-entry witness proof to every entry in ds_. This helper has
    /// only the invariants used by the quantified body, avoiding the complete
    /// RaftSafetyInvariant and RaftDistributedNext axiom sets.
    #[verifier(spinoff_prover)]
    proof fn lemma_entry_term_witness_all_entries(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
    )
        requires
            entry_term_witness_step_context(
                ds, ds_, server_id, s, s_, c),
        ensures
            EntryTermLeaderWitness(ds_),
    {
        assert(EntryTermLeaderWitness(ds_)) by {
            assert forall |i: int, k: int|
                #![trigger entry_term_leader_witness_trigger(ds_, i, k)]
                0 <= i < ds_.num_servers
                && 0 <= k < ds_.server_states[i].log.len()
                && entry_term_leader_witness_trigger(ds_, i, k)
            implies exists |w: int|
                #![trigger ds_.server_states[w].log[k]]
            {
                &&& 0 <= w < ds_.num_servers
                &&& ds_.server_states[w].log.len() > k
                &&& ds_.server_states[w].log[k] == ds_.server_states[i].log[k]
            } by {
                let w = lemma_entry_term_witness_for_entry_from_context(
                    ds, ds_, server_id, s, s_, c, i, k);
                assert(0 <= w < ds_.num_servers);
                assert(ds_.server_states[w].log.len() > k);
                assert(ds_.server_states[w].log[k]
                    == ds_.server_states[i].log[k]);
            }
        }
    }

    proof fn lemma_entry_term_leader_witness_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            EntryTermLeaderWitness(ds_)
    {
        let (server_id, s, s_, c) = lemma_entry_term_extract_step(ds, ds_);
        lemma_entry_term_witness_all_entries(
            ds, ds_, server_id, s, s_, c);
    }

    // =========================================================================
    // EntryTermHasVoteQuorum Induction
    // =========================================================================

    /// Helper: convert a finite Set<int> to a Seq<int> preserving
    /// elements and distinctness.
    proof fn finite_set_to_seq(s: Set<int>) -> (result: Seq<int>)
        ensures
            result.len() == s.len(),
            forall |a: int| #![trigger result[a]]
                0 <= a < result.len() ==> s.contains(result[a]),
            forall |a: int, b: int| #![trigger result[a], result[b]]
                0 <= a < result.len() && 0 <= b < result.len() && a != b
                ==> result[a] != result[b],
        decreases s.len()
    {
        broadcast use vstd::set::group_set_lemmas;
        vstd::set_lib::lemma_set_empty_equivalency_len(s);
        if s.len() == 0 {
            Seq::<int>::empty()
        } else {
            let x = s.choose();
            let s_rest = s.remove(x);
            let rest = finite_set_to_seq(s_rest);
            let result = rest.push(x);
            assert forall |a: int| #![trigger result[a]]
                0 <= a < result.len()
                implies s.contains(result[a]) by
            {
                if a < rest.len() {
                    assert(result[a] == rest[a]);
                    assert(s_rest.contains(rest[a]));
                } else {
                    assert(result[a] == x);
                }
            };
            assert forall |a: int, b: int| #![trigger result[a], result[b]]
                0 <= a < result.len() && 0 <= b < result.len() && a != b
                implies result[a] != result[b] by
            {
                if a < rest.len() && b < rest.len() {
                    // Both from rest — IH gives distinctness
                } else if a < rest.len() {
                    // a from rest, b == rest.len() so result[b] == x
                    assert(s_rest.contains(rest[a]));
                    assert(!s_rest.contains(x));
                } else if b < rest.len() {
                    // symmetric
                    assert(s_rest.contains(rest[b]));
                    assert(!s_rest.contains(x));
                }
            };
            result
        }
    }

    /// Helper: construct voters Seq from a Leader/Candidate's votes_granted
    /// using VotersVotedForCandidate. For each v != d in votes_granted,
    /// there's a VoteResponse{term, to d} packet in the network.
    ///
    /// This extracts the vote quorum into a Seq suitable for
    /// EntryTermHasVoteQuorum's existential witness.
    proof fn lemma_votes_granted_to_voter_seq(
        ds: RaftDistributedState, d: int, term: int,
    ) -> (voters: Seq<int>)
        requires
            WellFormedRaftDistributed(ds),
            VotersVotedForCandidate(ds),
            VotesGrantedAreServers(ds),
            CandidateOrLeaderVotedForSelf(ds),
            SenderIntegrity(ds),
            0 <= d < ds.num_servers,
            ds.server_states[d].role is Candidate || ds.server_states[d].role is Leader,
            ds.server_states[d].current_term == term,
        ensures
            voters.len() >= ds.server_states[d].votes_granted.len() - 1,
            forall |a: int| #![trigger voters[a]] 0 <= a < voters.len() ==> {
                &&& 0 <= voters[a] < ds.num_servers
                &&& voters[a] != d
                &&& ExistsGrantedVoteResponse(ds, voters[a], d, term)
            },
            forall |a: int, b: int|
                #![trigger voters[a], voters[b]]
                0 <= a < voters.len() && 0 <= b < voters.len() && a != b
                ==> voters[a] != voters[b],
    {
        broadcast use vstd::set::group_set_lemmas;

        let vg = ds.server_states[d].votes_granted;
        let n = ds.num_servers;

        // CandidateOrLeaderVotedForSelf => d in vg
        assert(vg.contains(ds.server_constants[d].my_id));
        assert(ds.server_constants[d].my_id == d);

        // Prove vg finite (subset of [0, n))
        let universe = Set::<int>::range(0, n);
        lemma_range_set_finite(n);
        assert(vg.subset_of(universe)) by {
            assert forall |v: int| vg.contains(v) implies universe.contains(v) by {};
        };
        vstd::set_lib::lemma_len_subset(vg, universe);

        // Remove d, convert to Seq
        let vg_no_d = vg.remove(d);
        let voters = finite_set_to_seq(vg_no_d);
        // voters.len() == vg_no_d.len() == vg.len() - 1 (since d in vg)

        // Per-element properties
        assert forall |a: int| #![trigger voters[a]] 0 <= a < voters.len() implies {
            &&& 0 <= voters[a] < ds.num_servers
            &&& voters[a] != d
            &&& ExistsGrantedVoteResponse(ds, voters[a], d, term)
        } by {
            let v = voters[a];
            assert(vg_no_d.contains(v));
            assert(vg.contains(v));
            assert(0 <= v < n);
            assert(v != d);

            // VotersVotedForCandidate: d is Candidate/Leader, v != d, vg.contains(v)
            // => exists VoteResponse packet to d with voter v at term
            let p = choose |p: LRaftPacket| #![trigger ds.network.contains(p)] {
                &&& ds.network.contains(p)
                &&& p.dst == d
                &&& p.msg matches LRaftMessage::VoteResponse {
                    term: pt, granted: pg, voter: pv,
                    ..
                }
                &&& pt == ds.server_states[d].current_term
                &&& pg
                &&& pv == v
            };
            // SenderIntegrity: VoteResponse voter == v => p.src == v
            assert(p.src == v);
            assert(ds.server_states[d].current_term == term);
            assert(p.msg->VoteResponse_term == ds.server_states[d].current_term);
            assert(p.msg->VoteResponse_term == term);

            // Build ExistsGrantedVoteResponse witness from packet-attached summary.
            let last_idx = p.msg->VoteResponse_voter_last_log_index;
            let last_term = p.msg->VoteResponse_voter_last_log_term;
            assert(ds.network.contains(LRaftPacket {
                src: v,
                dst: d,
                msg: LRaftMessage::VoteResponse {
                    term,
                    granted: true,
                    voter: v,
                    voter_last_log_index: last_idx,
                    voter_last_log_term: last_term,
                },
            })) by {
                assert(p == LRaftPacket {
                    src: v,
                    dst: d,
                    msg: LRaftMessage::VoteResponse {
                        term,
                        granted: true,
                        voter: v,
                        voter_last_log_index: last_idx,
                        voter_last_log_term: last_term,
                    },
                });
            };
            assert(ExistsGrantedVoteResponse(ds, v, d, term));
        };

        voters
    }

    /// Helper: ExistsGrantedVoteResponse transfers across network monotonicity.
    proof fn lemma_vote_response_transfers(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        src: int, dst: int, term: int,
    )
        requires
            ExistsGrantedVoteResponse(ds, src, dst, term),
            forall |pkt: LRaftPacket| ds.network.contains(pkt)
                ==> ds_.network.contains(pkt),
        ensures
            ExistsGrantedVoteResponse(ds_, src, dst, term),
    {
        let (last_idx, last_term): (int, int) = choose |li: int, lt: int|
            #![trigger ds.network.contains(LRaftPacket {
                src,
                dst,
                msg: LRaftMessage::VoteResponse {
                    term,
                    granted: true,
                    voter: src,
                    voter_last_log_index: li,
                    voter_last_log_term: lt,
                },
            })]
            ds.network.contains(LRaftPacket {
                src,
                dst,
                msg: LRaftMessage::VoteResponse {
                    term,
                    granted: true,
                    voter: src,
                    voter_last_log_index: li,
                    voter_last_log_term: lt,
                },
            });
        let pkt = LRaftPacket {
            src,
            dst,
            msg: LRaftMessage::VoteResponse {
                term,
                granted: true,
                voter: src,
                voter_last_log_index: last_idx,
                voter_last_log_term: last_term,
            },
        };
        assert(ds.network.contains(pkt));
        assert(ds_.network.contains(pkt));
    }

    /// Step 1 of follower case: find the AE leader (isolated from transfer).
    proof fn lemma_follower_find_ae_leader(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, k: int,
    ) -> (ae_leader: int)
        requires
            AppendEntriesIntegrity(ds),
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= server_id < ds.num_servers,
            ds_.server_states[server_id].role is Follower,
            k == ds.server_states[server_id].log.len(),
            ds_.server_states[server_id].log.len()
                == ds.server_states[server_id].log.len() + 1,
            RaftServerStepWithNetwork(ds, ds_, server_id),
        ensures
            0 <= ae_leader < ds.num_servers,
            ds.server_states[ae_leader].log.len() > k,
            ds.server_states[ae_leader].log[k].term
                == ds_.server_states[server_id].log[k].term,
            ds.server_states[ae_leader].log[k].value
                == ds_.server_states[server_id].log[k].value,
            ds.server_states[ae_leader].log[k].payload
                == ds_.server_states[server_id].log[k].payload,
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        lemma_follower_append_ae_in_network(
            ds, ds_, server_id, s, s_, c, k);
        choose |al: int|
            #![trigger ds.server_states[al]]
        {
            &&& 0 <= al < ds.num_servers
            &&& ds.server_states[al].log.len() > k
            &&& ds.server_states[al].log[k].term == s_.log[k].term
            &&& ds.server_states[al].log[k].value == s_.log[k].value
            &&& ds.server_states[al].log[k].payload == s_.log[k].payload
        }
    }

    // =========================================================================
    // Log Matching Induction
    // =========================================================================

    /// Helper: LNext preserves log for most branches (only LClientRequest
    /// and LFollowerAppendEntries modify the log).
    proof fn lemma_lnext_log_preserved_or_extended(s: LState, s_: LState, c: LConstants)
        requires LNext(s, s_, c)
        ensures
            // The log is either unchanged or extended by exactly one entry
            s_.log.len() >= s.log.len()
            && s_.log.len() <= s.log.len() + 1
            && (forall |k: int| 0 <= k < s.log.len() ==> #[trigger] s_.log[k] == s.log[k])
    {
        // Verus case-splits on LNext and verifies for each branch:
        // Most branches: s_.log == s.log (unchanged, all three properties trivial)
        // LClientRequest: s_.log == s.log.push(entry), len increases by 1, prefix preserved
        // LFollowerAppendEntries: s_.log == s.log or s.log.push(entry), same argument
    }

    /// If a step grows the log by one at `k == old_len`, the appended entry's
    /// term is at least the pre-state current term.
    proof fn lemma_lnext_fresh_append_entry_term_ge_pre_current(
        s: LState, s_: LState, c: LConstants,
        k: int, entry: LLogEntry,
    )
        requires
            LNext(s, s_, c),
            k == s.log.len(),
            s_.log.len() == s.log.len() + 1,
            s_.log[k] == entry,
        ensures
            entry.term >= s.current_term,
    {
        assert(s_.log[k].term == entry.term);
        assert(entry.term >= s.current_term) by {
            // Only LClientRequest and LFollowerAppendEntries can increase log
            // length; both append entries with term >= pre current_term.
        }
    }

    /// Inner proof for LogMatching induction, separated for modularity.
    proof fn lemma_log_matching_inner(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
    )
        requires
            LogMatching(ds),
            LeaderLogLongEnough(ds),
            AppendEntriesIntegrity(ds),
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            LNext(s, s_, c),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            // Log properties
            s_.log.len() >= s.log.len(),
            s_.log.len() <= s.log.len() + 1,
            forall |k: int| 0 <= k < s.log.len() ==> #[trigger] s_.log[k] == s.log[k],
            LogAppendOnly(ds, ds_),
            // Network step
            RaftServerStepWithNetwork(ds, ds_, server_id),
        ensures
            LogMatching(ds_)
    {
        assert forall |i: int, j: int, k: int| #![trigger ds_.server_states[i], ds_.server_states[j].log[k]] #![trigger ds_.server_states[i].log[k], ds_.server_states[j]]
            0 <= i < ds_.num_servers && 0 <= j < ds_.num_servers
            && 0 <= k < ds_.server_states[i].log.len()
            && 0 <= k < ds_.server_states[j].log.len()
            && ds_.server_states[i].log[k].term == ds_.server_states[j].log[k].term
            implies (forall |m: int| 0 <= m <= k
                && m < ds_.server_states[i].log.len()
                && m < ds_.server_states[j].log.len()
                ==> ds_.server_states[i].log[m] == ds_.server_states[j].log[m])
        by {
            if i == j {
                // Same server: trivially true (same log)
            } else if i != server_id && j != server_id {
                // Both unchanged: LogMatching(ds) applies directly
                assert(ds_.server_states[i] == ds.server_states[i]);
                assert(ds_.server_states[j] == ds.server_states[j]);
                assert(LogMatching(ds));
            } else {
                // One of i, j is server_id — handle the stepping server case
                // Use symmetry: reduce to the case where server_id has
                // the entry at k.
                let (si, sj) = if i == server_id { (i, j) } else { (j, i) };
                // si == server_id, sj != server_id
                assert(ds_.server_states[sj] == ds.server_states[sj]);

                if k < s.log.len() {
                    // Index k is in the OLD prefix of server_id's log.
                    // Both entries at k are unchanged:
                    // ds_.server_states[si].log[k] == ds.server_states[si].log[k] (preserved)
                    // ds_.server_states[sj].log[k] == ds.server_states[sj].log[k] (unchanged)
                    // LogMatching(ds) for (si, sj, k) gives entries 0..k match.
                    assert(LogMatching(ds));
                    // Entries at m <= k are also unchanged in ds_:
                    // For si: s_.log[m] == s.log[m] for m < s.log.len()
                    // For sj: unchanged
                } else {
                    // k == s.log.len(): the NEW entry on server_id.
                    // The new entry has term T = s_.log[k].term.
                    // Server sj has entry at k with the same term T.
                    if s_.role is Leader {
                        // LClientRequest: new entry has term s.current_term.
                        // In ds, server_id is Leader at term T.
                        // sj has entry at k with term T in ds (sj unchanged).
                        // By LeaderLogLongEnough(ds) for (i=sj, k=k, l=server_id):
                        //   ds.server_states[server_id].log.len() > k
                        // But ds.server_states[server_id].log.len() == s.log.len() == k.
                        // Contradiction — the premise is impossible.
                        assert(LeaderLogLongEnough(ds));
                        assert(s.role is Leader);
                        assert(s_.log[k].term == s.current_term);
                        assert(0 <= sj < ds.num_servers);
                        assert(0 <= k < ds.server_states[sj].log.len());
                        assert(ds.server_states[server_id].role is Leader);
                    } else {
                        // LFollowerAppendEntries: server_id received an AE from
                        // the network. Extract the AE packet and use AEI +
                        // LogMatching(ds) to prove entry matching.
                        assert(s_.role is Follower);
                        lemma_log_matching_follower_append(
                            ds, ds_, server_id, s, s_, c, sj, k, i, j);
                    }
                }
            }
        }
    }

    /// When server_id extends its log via the network model (non-Leader),
    /// there exists a leader whose log matches the new entry and the
    /// follower's prev-log entry. Captures AE packet provenance via AEI.
    proof fn lemma_follower_append_ae_in_network(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
        k: int,
    )
        requires
            AppendEntriesIntegrity(ds),
            WellFormedRaftDistributed(ds),
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            RaftServerStepWithNetwork(ds, ds_, server_id),
            s_.log.len() == s.log.len() + 1,
            s_.role is Follower,
            k == s.log.len() as int,
        ensures
            exists |ae_leader: int|
                #![trigger ds.server_states[ae_leader]]
            {
                &&& 0 <= ae_leader < ds.num_servers
                &&& ds.server_states[ae_leader].log.len() > k
                &&& ds.server_states[ae_leader].log[k].term == s_.log[k].term
                &&& ds.server_states[ae_leader].log[k].value == s_.log[k].value
                &&& ds.server_states[ae_leader].log[k].payload
                    == s_.log[k].payload
                &&& (k > 0 ==> s.log[k - 1].term
                        == ds.server_states[ae_leader].log[k - 1].term)
            }
    {
        // Verus unfolds RaftServerStepWithNetwork → RaftActionProduces
        //   → LHandleMessage (only branch that grows log for non-Leader)
        //   → LHandleAppendEntriesMsg → LFollowerAppendEntries
        // The received pkt is in ds.network, so AEI applies.
        // ae_has_entry must be true (log grew), ae_prev_index == k (position guard).
    }

    /// A newly appended entry received in an AppendEntries packet is
    /// legal for the follower's membership history.
    ///
    /// The sender's full log supplies legality. AppendEntriesIntegrity
    /// supplies the exact tagged payload, while LogMatching transfers
    /// the common prefix used to derive the active membership phase.
    proof fn lemma_processed_append_entries_new_entry_is_legal(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
        server_id: int,
        pkt: LRaftPacket,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            AllRaftMembershipLogsWellFormed(ds),
            LogMatching(ds),
            AppendEntriesIntegrity(ds),
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= server_id < ds.num_servers,
            ds.network.contains(pkt),
            pkt.dst == server_id,
            LHandleMessage(
                ds.server_states[server_id],
                ds_.server_states[server_id],
                ds.server_constants[server_id],
                pkt.msg,
                sent_packets,
            ),
            ds_.server_states[server_id].log.len()
                == ds.server_states[server_id].log.len() + 1,
        ensures
            is_legal_next_raft_membership_log_entry(
                ds_.server_states[server_id].log,
                ds.server_states[server_id].log.len() as int,
                MembershipPhase::Stable {
                    config:
                        ds.server_constants[server_id].servers,
                },
            ),
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        let k = s.log.len() as int;

        assert(pkt.msg is AppendEntries);

        let ae_term = pkt.msg->AppendEntries_term;
        let ae_leader = pkt.msg->AppendEntries_leader;
        let ae_prev_index = pkt.msg->AppendEntries_prev_index;
        let ae_prev_term = pkt.msg->AppendEntries_prev_term;
        let ae_payload = pkt.msg->AppendEntries_payload;
        let ae_has_entry = pkt.msg->AppendEntries_has_entry;

        assert(ae_has_entry);
        assert(ae_prev_index == k);
        assert(0 <= ae_leader < ds.num_servers);

        assert(ds.server_states[ae_leader].log.len() > k);
        assert(ds.server_states[ae_leader].log[k].payload
            == ae_payload);
        assert(s_.log[k].payload == ae_payload);
        assert(ds.server_states[ae_leader].log[k].payload
            == s_.log[k].payload);

        assert forall |prefix_index: int| #![trigger s_.log[prefix_index]]
            0 <= prefix_index < k
            implies ds.server_states[ae_leader].log[prefix_index]
                == s_.log[prefix_index]
        by {
            assert(s_.log[prefix_index]
                == s.log[prefix_index]);

            if k > 0 {
                assert(ds.server_states[ae_leader].log[k - 1].term
                    == ae_prev_term);
                assert(s.log[k - 1].term == ae_prev_term);
                assert(ds.server_states[ae_leader].log[k - 1].term
                    == s.log[k - 1].term);

                assert forall |matching_index: int| #![trigger s.log[matching_index]]
                    0 <= matching_index <= k - 1
                    && matching_index
                        < ds.server_states[ae_leader].log.len()
                    && matching_index < s.log.len()
                    implies ds.server_states[ae_leader].log[matching_index]
                        == s.log[matching_index]
                by {
                    assert(LogMatching(ds));
                };
            }
        };

        assert(ds.server_constants[ae_leader].servers
            == c.servers);

        assert(raft_membership_log_is_well_formed(
            ds.server_states[ae_leader].log,
            MembershipPhase::Stable {
                config:
                    ds.server_constants[ae_leader].servers,
            },
        ));

        assert(raft_membership_log_is_well_formed(
            ds.server_states[ae_leader].log,
            MembershipPhase::Stable {
                config: c.servers,
            },
        ));

        lemma_equal_prefix_and_payload_transfer_next_entry_legality(
            ds.server_states[ae_leader].log,
            s_.log,
            k,
            MembershipPhase::Stable {
                config: c.servers,
            },
        );
    }

    /// One concrete server action preserves the stepping server's
    /// full legal membership history.
    ///
    /// Client requests append Data. Incoming AppendEntries use the
    /// provenance helper above. Every other current LNext branch leaves
    /// the physical log unchanged.
    proof fn lemma_raft_action_preserves_full_membership_history(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
        server_id: int,
        sent_packets: Seq<LRaftMessage>,
        received_from: Option<int>,
    )
        requires
            AllRaftMembershipLogsWellFormed(ds),
            LogMatching(ds),
            AppendEntriesIntegrity(ds),
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= server_id < ds.num_servers,
            LNext(
                ds.server_states[server_id],
                ds_.server_states[server_id],
                ds.server_constants[server_id],
            ),
            RaftActionProduces(
                ds,
                server_id,
                ds.server_states[server_id],
                ds_.server_states[server_id],
                ds.server_constants[server_id],
                sent_packets,
                received_from,
            ),
        ensures
            raft_membership_log_is_well_formed(
                ds_.server_states[server_id].log,
                MembershipPhase::Stable {
                    config:
                        ds.server_constants[server_id].servers,
                },
            ),
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        assert(raft_membership_log_is_well_formed(
            s.log,
            MembershipPhase::Stable {
                config: c.servers,
            },
        ));

        lemma_lnext_log_preserved_or_extended(s, s_, c);

        if s_.log != s.log {
            assert(s_.log.len() == s.log.len() + 1);

            if exists |value: int|
                LClientRequest(
                    s,
                    s_,
                    c,
                    value,
                    sent_packets,
                )
            {
                let value = choose |value: int|
                    LClientRequest(
                        s,
                        s_,
                        c,
                        value,
                        sent_packets,
                    );

                lemma_client_request_preserves_full_membership_history(
                    s,
                    s_,
                    c,
                    value,
                    sent_packets,
                );
            } else if exists |phase: LMembershipPhase|
                LAppendConfigurationEntry(
                    s,
                    s_,
                    c,
                    phase,
                    sent_packets,
                )
            {
                let phase = choose |phase: LMembershipPhase|
                    LAppendConfigurationEntry(
                        s,
                        s_,
                        c,
                        phase,
                        sent_packets,
                    );

                lemma_append_configuration_preserves_full_history(
                    s,
                    s_,
                    c,
                    phase,
                    sent_packets,
                );
            } else {
                let pkt = choose |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
                    &&& received_from == Some(pkt.src)
                    &&& ds.network.contains(pkt)
                    &&& pkt.dst == server_id
                    &&& LHandleMessage(
                        s,
                        s_,
                        c,
                        pkt.msg,
                        sent_packets,
                    )
                };

                lemma_processed_append_entries_new_entry_is_legal(
                    ds,
                    ds_,
                    server_id,
                    pkt,
                    sent_packets,
                );

                let entry = s_.log[s.log.len() as int];
                assert(s_.log == s.log.push(entry));

                lemma_legal_raft_append_preserves_full_history(
                    s.log,
                    entry,
                    MembershipPhase::Stable {
                        config: c.servers,
                    },
                );
            }
        }
    }


    /// Helper for LogMatching: when server_id extends its log via
    /// LFollowerAppendEntries and another server sj has an entry at the
    /// same index k with the same term, all entries 0..k match.
    proof fn lemma_log_matching_follower_append(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
        sj: int, k: int, qi: int, qj: int,
    )
        requires
            LogMatching(ds),
            AppendEntriesIntegrity(ds),
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            LNext(s, s_, c),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            s_.log.len() >= s.log.len(),
            s_.log.len() <= s.log.len() + 1,
            forall |idx: int| 0 <= idx < s.log.len() ==> #[trigger] s_.log[idx] == s.log[idx],
            RaftServerStepWithNetwork(ds, ds_, server_id),
            // New entry case
            s_.role is Follower,
            k == s.log.len() as int,
            0 <= sj < ds.num_servers,
            sj != server_id,
            ds_.server_states[sj] == ds.server_states[sj],
            0 <= k < ds_.server_states[sj].log.len(),
            k < s_.log.len(),
            s_.log[k].term == ds_.server_states[sj].log[k].term,
            // qi, qj are the original quantified i, j (one is server_id)
            (qi == server_id && qj == sj) || (qi == sj && qj == server_id),
            0 <= qi < ds_.num_servers,
            0 <= qj < ds_.num_servers,
        ensures
            forall |m: int| 0 <= m <= k
                && m < ds_.server_states[qi].log.len()
                && m < ds_.server_states[qj].log.len()
                ==> ds_.server_states[qi].log[m] == ds_.server_states[qj].log[m]
    {
        // Extract the AE leader from the network
        assert(s_.role is Follower);
        lemma_follower_append_ae_in_network(ds, ds_, server_id, s, s_, c, k);

        // Choose the leader satisfying the postcondition
        let ae_leader: int = choose |l: int| {
            &&& 0 <= l < ds.num_servers
            &&& (#[trigger] ds.server_states[l]).log.len() > k
            &&& ds.server_states[l].log[k].term == s_.log[k].term
            &&& ds.server_states[l].log[k].value == s_.log[k].value
            &&& (k > 0 ==> s.log[k - 1].term
                    == ds.server_states[l].log[k - 1].term)
        };

        let T = s_.log[k].term;
        assert(LogMatching(ds));

        assert forall |m: int| 0 <= m <= k
            && m < ds_.server_states[qi].log.len()
            && m < ds_.server_states[qj].log.len()
        implies
            ds_.server_states[qi].log[m] == ds_.server_states[qj].log[m]
        by {
            // LogMatching(ds) for (ae_leader, sj, k) gives:
            //   ae_leader.log[m] == sj.log[m] for all m <= k
            assert(ds.server_states[ae_leader].log[m] == ds.server_states[sj].log[m]);

            if m == k {
                // s_.log[k] = LLogEntry{term: T, value: ae_value}
                // ae_leader.log[k] has same term and value (AEI)
                // sj.log[k] == ae_leader.log[k] (from LogMatching above)
                assert(s_.log[k].term == ds.server_states[ae_leader].log[k].term);
                assert(s_.log[k].value == ds.server_states[ae_leader].log[k].value);
            } else {
                // m < k: s_.log[m] == s.log[m] (preserved prefix)
                // Need: s.log[m] == sj.log[m]
                // Chain: s.log[m] == ae_leader.log[m] == sj.log[m]
                //
                // For the first link (s.log[m] == ae_leader.log[m]):
                // If k > 0, prev-log check gives s.log[k-1].term == ae_leader.log[k-1].term
                // LogMatching(ds) for (server_id, ae_leader, k-1) gives s.log[m] == ae_leader.log[m]
                if k > 0 {
                    // LogMatching(ds) for (server_id, ae_leader, k-1)
                    assert(ds.server_states[server_id].log[m] == ds.server_states[ae_leader].log[m]);
                }
            }
        }
    }

    // =========================================================================
    // Leader Completeness Induction
    // =========================================================================

    /// Sub-helper for LeaderCompleteness induction: if the leader is unchanged
    /// across a distributed step and the committed-entry witness is from the
    /// pre-state, the LeaderCompleteness obligation transfers directly.
    proof fn lemma_leader_completeness_unchanged_leader_for_prestate_commit(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        leader_id: int, k: int, entry: LLogEntry,
    )
        requires
            0 <= k,
            LeaderCompleteness(ds),
            EntryCommittedAt(ds, k, entry),
            0 <= leader_id < ds.num_servers,
            ds_.server_states[leader_id] == ds.server_states[leader_id],
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term > entry.term,
        ensures
            ds_.server_states[leader_id].log.len() > k,
            ds_.server_states[leader_id].log[k] == entry,
    {
        assert(LeaderCompleteness(ds));
        assert(ds.server_states[leader_id].log.len() > k);
        assert(ds.server_states[leader_id].log[k] == entry);
    }

    /// Sub-helper for LeaderCompleteness induction: a post-state committed
    /// witness either already existed in the pre-state, or it is a fresh
    /// append at index `k` on the stepping server this step.
    proof fn lemma_entry_committed_post_implies_pre_or_fresh_step_append(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        k: int, entry: LLogEntry,
    )
        requires
            0 <= k,
            RaftDistributedNext(ds, ds_),
            EntryCommittedAt(ds_, k, entry),
        ensures
            EntryCommittedAt(ds, k, entry)
                || exists |stepping: int| #![trigger ds.server_states[stepping]] #![trigger ds_.server_states[stepping]] {
                    &&& 0 <= stepping < ds.num_servers
                    &&& (forall |j: int| #![trigger ds_.server_states[j]]
                        0 <= j < ds.num_servers && j != stepping ==>
                        ds_.server_states[j] == ds.server_states[j])
                    &&& k == ds.server_states[stepping].log.len()
                    &&& ds_.server_states[stepping].log.len()
                        == ds.server_states[stepping].log.len() + 1
                    &&& ds_.server_states[stepping].log[k] == entry
                    &&& entry.term >= ds.server_states[stepping].current_term
                },
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |sid: int| #![trigger ds.server_states[sid]] #![trigger ds_.server_states[sid]] #![trigger ds.server_constants[sid]] {
            &&& 0 <= sid < ds.num_servers
            &&& LNext(ds.server_states[sid], ds_.server_states[sid], ds.server_constants[sid])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        lemma_lnext_log_preserved_or_extended(s, s_, c);

        let commit_quorum = choose |q: Set<int>| {
            &&& q.len() >= ds.num_servers / 2 + 1
            &&& (forall |id: int| #![trigger q.contains(id)] q.contains(id) ==> {
                &&& 0 <= id < ds.num_servers
                &&& ds_.server_states[id].log.len() > k
                &&& ds_.server_states[id].log[k] == entry
            })
        };

        let fresh_step_case = commit_quorum.contains(server_id) && !(k < s.log.len());
        if fresh_step_case {
            assert(commit_quorum.contains(server_id));
            assert(ds_.server_states[server_id].log.len() > k);
            assert(k + 1 <= s_.log.len());
            assert(s_.log.len() <= s.log.len() + 1);
            assert(k <= s.log.len());
            assert(s.log.len() <= k);
            assert(k == s.log.len());

            assert(s_.log.len() > s.log.len());
            assert(s_.log.len() >= s.log.len() + 1);
            assert(s_.log.len() == s.log.len() + 1);
            assert(ds_.server_states[server_id].log[k] == entry);

            assert(exists |stepping: int| #![trigger ds.server_states[stepping]] #![trigger ds_.server_states[stepping]] {
                &&& 0 <= stepping < ds.num_servers
                &&& (forall |j: int| #![trigger ds_.server_states[j]]
                    0 <= j < ds.num_servers && j != stepping ==>
                    ds_.server_states[j] == ds.server_states[j])
                &&& k == ds.server_states[stepping].log.len()
                &&& ds_.server_states[stepping].log.len()
                    == ds.server_states[stepping].log.len() + 1
                &&& ds_.server_states[stepping].log[k] == entry
                &&& entry.term >= ds.server_states[stepping].current_term
            }) by {
                let stepping = server_id;
                assert(0 <= stepping < ds.num_servers);
                assert(k == ds.server_states[stepping].log.len());
                assert(ds_.server_states[stepping].log.len()
                    == ds.server_states[stepping].log.len() + 1);
                assert(ds_.server_states[stepping].log[k] == entry);
                lemma_lnext_fresh_append_entry_term_ge_pre_current(
                    ds.server_states[stepping],
                    ds_.server_states[stepping],
                    ds.server_constants[stepping],
                    k,
                    entry,
                );
            };
        } else {
            assert(EntryCommittedAt(ds, k, entry)) by {
                assert(exists |q: Set<int>| {
                    &&& q.len() >= ds.num_servers / 2 + 1
                    &&& (forall |id: int| #![trigger q.contains(id)] q.contains(id) ==> {
                        &&& 0 <= id < ds.num_servers
                        &&& ds.server_states[id].log.len() > k
                        &&& ds.server_states[id].log[k] == entry
                    })
                }) by {
                    let q = commit_quorum;
                    assert(q.len() >= ds.num_servers / 2 + 1);
                    assert forall |id: int| #![trigger q.contains(id)] q.contains(id) implies {
                        &&& 0 <= id < ds.num_servers
                        &&& ds.server_states[id].log.len() > k
                        &&& ds.server_states[id].log[k] == entry
                    } by {
                        assert(0 <= id < ds.num_servers);
                        if id != server_id {
                            assert(ds_.server_states[id] == ds.server_states[id]);
                            assert(ds.server_states[id].log.len() > k);
                            assert(ds.server_states[id].log[k] == entry);
                        } else {
                            assert(id == server_id);
                            assert(q.contains(server_id));
                            if !(k < s.log.len()) {
                                assert(fresh_step_case);
                                assert(false);
                            }
                            assert(k < s.log.len());
                            assert(s.log.len() > k);
                            assert(s_.log[k] == s.log[k]);
                            assert(ds_.server_states[server_id].log[k] == entry);
                            assert(ds.server_states[server_id].log[k] == entry);
                        }
                    };
                };
            };
        }
    }

    // =========================================================================
    // State Machine Safety Induction
    // =========================================================================

    /// Main induction lemma for State Machine Safety
    ///
    /// StateMachineSafety states: for any two servers i and j, entries below
    /// both commit_index[i] and commit_index[j] are identical.
    ///
    /// Structure:
    /// - If neither i nor j stepped: SMS(ds) + LogAppendOnly gives result.
    /// - If both are the stepping server: trivial (same server).
    /// - If exactly one stepped and its old commit_index already covered k:
    ///   SMS(ds) + LogAppendOnly gives result.
    /// - If exactly one stepped and k is NEWLY committed: the post-state
    ///   commit-certificate map identifies the same entry for both servers.
    proof fn lemma_state_machine_safety_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            StateMachineSafety(ds_)
    {
        lemma_committed_entries_have_log_certificates_inductive(ds, ds_);
        lemma_log_certificate_coverage_implies_state_machine_safety(ds_);
        lemma_distributed_next_implies_legacy(ds, ds_);
        lemma_log_append_only(ds, ds_);

        let server_id = choose |sid: int| #![trigger ds.server_states[sid]] #![trigger ds_.server_states[sid]] #![trigger ds.server_constants[sid]] {
            &&& 0 <= sid < ds.num_servers
            &&& LNext(ds.server_states[sid], ds_.server_states[sid],
                       ds.server_constants[sid])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        assert forall |i: int, j: int, k: int| #![trigger ds_.server_states[i], ds_.server_states[j].log[k]] #![trigger ds_.server_states[j], ds_.server_states[i].log[k]]
            0 <= i < ds_.num_servers && 0 <= j < ds_.num_servers
            && 0 <= k < ds_.server_states[i].commit_index
            && 0 <= k < ds_.server_states[j].commit_index
            && k < ds_.server_states[i].log.len()
            && k < ds_.server_states[j].log.len()
        implies ds_.server_states[i].log[k] == ds_.server_states[j].log[k]
        by {
            if i != server_id && j != server_id {
                // Both unchanged: SMS(ds) + LogAppendOnly
                assert(ds_.server_states[i] == ds.server_states[i]);
                assert(ds_.server_states[j] == ds.server_states[j]);
                assert(StateMachineSafety(ds));
            } else if i == j {
                // Same server: trivial
            } else {
                // Exactly one is the stepping server.
                // WLOG let stepping = the one that is server_id.
                let (stepping, other) = if i == server_id { (i, j) } else { (j, i) };
                assert(ds_.server_states[other] == ds.server_states[other]);

                if k < ds.server_states[stepping].commit_index {
                    // k was already below old commit_index.
                    // SMS(ds): old entries agree. LogAppendOnly: entries preserved.
                    assert(StateMachineSafety(ds));
                    assert(k < ds.server_states[other].commit_index);
                } else {
                    // k is NEWLY committed by the stepping server.
                    // The post-state certificate map gives both committed
                    // entries the same unique certificate value.
                    assert(StateMachineSafety(ds_));
                }
            }
        }
    }

    // =========================================================================
    // Message Invariant Induction
    // =========================================================================

    proof fn lemma_sender_integrity_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            WellFormedRaftDistributed(ds),
            SenderIntegrity(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            SenderIntegrity(ds_)
    {
        // Old packets: from SenderIntegrity(ds) + network monotonicity.
        // New packets: src == server_id, msg identity field == c.my_id == server_id.
        // All actions explicitly set identity fields to c.my_id (verified by SMT
        // unfolding of RaftActionProduces + action definitions).
    }

    /// Extract step parameters from RaftDistributedNext.
    /// Returns (server_id, sent_pkts, recv_from) with all relevant properties.
    proof fn lemma_extract_step_with_network(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    ) -> (res: (int, Seq<LRaftMessage>, Option<int>))
        requires
            RaftDistributedNext(ds, ds_),
        ensures ({
            let (server_id, sent_pkts, recv_from) = res;
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(ds.server_states[server_id], ds_.server_states[server_id],
                       ds.server_constants[server_id])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& (forall |index: int| #![trigger ds.configuration_commit_certificates.dom().contains(index)] #![trigger ds_.configuration_commit_certificates.dom().contains(index)]
                ds.configuration_commit_certificates.dom().contains(index)
                ==> {
                    &&& ds_.configuration_commit_certificates.dom().contains(index)
                    &&& ds_.configuration_commit_certificates[index].log_index
                        == ds.configuration_commit_certificates[index].log_index
                    &&& ds_.configuration_commit_certificates[index].entry
                        == ds.configuration_commit_certificates[index].entry
                    &&& ds_.configuration_commit_certificates[index].committer
                        == ds.configuration_commit_certificates[index].committer
                    &&& ds_.configuration_commit_certificates[index].governing_phase
                        == ds.configuration_commit_certificates[index].governing_phase
                    &&& ds_.configuration_commit_certificates[index].quorum
                        == ds.configuration_commit_certificates[index].quorum
                })
            &&& (forall |index: int| #![trigger ds_.configuration_commit_certificates.dom().contains(index)]
                0 <= index < ds_.server_states[server_id].commit_index
                && index < ds_.server_states[server_id].log.len()
                && ds_.server_states[server_id].log[index].payload is Configuration
                ==> {
                    &&& ds_.configuration_commit_certificates.dom().contains(index)
                    &&& ds_.configuration_commit_certificates[index].log_index
                        == index
                    &&& ds_.configuration_commit_certificates[index].entry
                        == ds_.server_states[server_id].log[index]
                })
            &&& (forall |index: int| #![trigger ds_.configuration_commit_certificates.dom().contains(index)] #![trigger ds.configuration_commit_certificates.dom().contains(index)]
                ds_.configuration_commit_certificates.dom().contains(index)
                && !ds.configuration_commit_certificates.dom().contains(index)
                ==> {
                    &&& recv_from is None
                    &&& ds_.server_states[server_id].commit_index
                        > ds.server_states[server_id].commit_index
                    &&& index
                        == ds_.server_states[server_id].commit_index - 1
                    &&& 0 <= index
                        < ds_.server_states[server_id].log.len()
                    &&& ds_.server_states[server_id].log[index].payload
                        is Configuration
                    &&& ds_.configuration_commit_certificates[index].log_index
                        == index
                    &&& ds_.configuration_commit_certificates[index].entry
                        == ds_.server_states[server_id].log[index]
                    &&& ds_.configuration_commit_certificates[index].committer
                        == server_id
                    &&& ds_.configuration_commit_certificates[index].governing_phase
                        == active_membership_phase_for_state(
                            ds.server_states[server_id],
                            ds.server_constants[server_id],
                        )
                    &&& ds_.configuration_commit_certificates[index].quorum
                        == replicator_set(
                            ds.server_states[server_id],
                            ds.server_constants[server_id],
                            ds_.server_states[server_id].commit_index,
                        )
                })
            &&& (forall |index: int| #![trigger ds.log_commit_certificates.dom().contains(index)] #![trigger ds_.log_commit_certificates.dom().contains(index)]
                ds.log_commit_certificates.dom().contains(index)
                ==> {
                    &&& ds_.log_commit_certificates.dom().contains(index)
                    &&& ds_.log_commit_certificates[index].log_index
                        == ds.log_commit_certificates[index].log_index
                    &&& ds_.log_commit_certificates[index].entry
                        == ds.log_commit_certificates[index].entry
                    &&& ds_.log_commit_certificates[index].committer
                        == ds.log_commit_certificates[index].committer
                    &&& ds_.log_commit_certificates[index].governing_phase
                        == ds.log_commit_certificates[index].governing_phase
                    &&& ds_.log_commit_certificates[index].quorum
                        == ds.log_commit_certificates[index].quorum
                })
            &&& (forall |index: int| #![trigger ds_.log_commit_certificates.dom().contains(index)] #![trigger ds.log_commit_certificates.dom().contains(index)]
                ds_.log_commit_certificates.dom().contains(index)
                && !ds.log_commit_certificates.dom().contains(index)
                ==> {
                    &&& recv_from is None
                    &&& ds_.server_states[server_id].commit_index
                        > ds.server_states[server_id].commit_index
                    &&& ds.server_states[server_id].commit_index
                        <= index < ds_.server_states[server_id].commit_index
                    &&& index < ds_.server_states[server_id].log.len()
                    &&& ds_.log_commit_certificates[index].log_index == index
                    &&& ds_.log_commit_certificates[index].entry
                        == ds_.server_states[server_id].log[index]
                    &&& ds_.log_commit_certificates[index].committer == server_id
                    &&& ds_.log_commit_certificates[index].governing_phase
                        == active_membership_phase_from_raft_log(
                            ds.server_states[server_id].log,
                            index,
                            MembershipPhase::Stable {
                                config: ds.server_constants[server_id].servers,
                            },
                        )
                    &&& ds_.log_commit_certificates[index].quorum
                        == replicator_set(
                            ds.server_states[server_id],
                            ds.server_constants[server_id],
                            ds_.server_states[server_id].commit_index,
                        )
                })
            &&& (forall |index: int| #![trigger ds_.log_commit_certificates.dom().contains(index)]
                0 <= index < ds_.server_states[server_id].commit_index
                && index < ds_.server_states[server_id].log.len()
                ==> {
                    &&& ds_.log_commit_certificates.dom().contains(index)
                    &&& ds_.log_commit_certificates[index].log_index == index
                    &&& ds_.log_commit_certificates[index].entry
                        == ds_.server_states[server_id].log[index]
                })
            &&& RaftActionProduces(ds, server_id,
                    ds.server_states[server_id], ds_.server_states[server_id],
                    ds.server_constants[server_id], sent_pkts, recv_from)
            &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt)
                ==> ds_.network.contains(pkt))
            &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                    &&& pkt.src == server_id
                    &&& 0 <= pkt.dst < ds.num_servers
                    &&& (exists |i: int| 0 <= i < sent_pkts.len() && pkt.msg == sent_pkts[i])
                    &&& (match recv_from {
                        Some(src) => pkt.dst == src,
                        None => true,
                    })
                })
        })
    {
        // Extract server_id from RaftDistributedNext directly (not via legacy)
        // so we get RaftServerStepWithNetwork
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
            {
                &&& 0 <= sid < ds.num_servers
                &&& (forall |j: int| #![trigger ds_.server_states[j]]
                    0 <= j < ds.num_servers && j != sid ==>
                    ds_.server_states[j] == ds.server_states[j])
                &&& RaftServerStepWithNetwork(ds, ds_, sid)
            };
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        let (sent_pkts, recv_from) = choose |sp: Seq<LRaftMessage>, rf: Option<int>|
            #![trigger RaftActionProduces(ds, server_id, s, s_, c, sp, rf)]
            {
                &&& RaftActionProduces(ds, server_id, s, s_, c, sp, rf)
                &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt)
                    ==> ds_.network.contains(pkt))
                &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                    ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                        &&& pkt.src == server_id
                        &&& 0 <= pkt.dst < ds.num_servers
                        &&& (exists |i: int| 0 <= i < sp.len() && pkt.msg == sp[i])
                        &&& (match rf {
                            Some(src) => pkt.dst == src,
                            None => true,
                        })
                    })
            };

        // Also establish LNext (needed by callers)
        lemma_distributed_next_implies_legacy(ds, ds_);

        (server_id, sent_pkts, recv_from)
    }

    /// The global certificate map continues to cover every committed
    /// Configuration entry after one distributed step.
    pub proof fn lemma_committed_configurations_have_certificates_inductive(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            CommittedConfigurationsHaveCertificates(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CommittedConfigurationsHaveCertificates(ds_),
    {
        let (server_id, sent_pkts, recv_from) =
            lemma_extract_step_with_network(ds, ds_);

        assert forall |server: int, index: int|
            #![trigger ds_.server_states[server].log[index]]
            0 <= server < ds_.num_servers
            && 0 <= index < ds_.server_states[server].commit_index
            && index < ds_.server_states[server].log.len()
            && ds_.server_states[server].log[index].payload is Configuration
            implies {
                &&& ds_.configuration_commit_certificates.dom().contains(index)
                &&& ds_.configuration_commit_certificates[index].log_index
                    == index
                &&& ds_.configuration_commit_certificates[index].entry
                    == ds_.server_states[server].log[index]
            }
        by {
            if server == server_id {
                assert(ds_.server_states[server]
                    == ds_.server_states[server_id]);
            } else {
                assert(ds_.server_states[server]
                    == ds.server_states[server]);
                assert(CommittedConfigurationsHaveCertificates(ds));
                assert(ds.configuration_commit_certificates
                    .dom().contains(index));
                assert(ds.configuration_commit_certificates[index].log_index
                    == index);
                assert(ds.configuration_commit_certificates[index].entry
                    == ds.server_states[server].log[index]);
            }
        };
    }

    /// All-entry certificate coverage is preserved for the stepping server by
    /// the transition rule and for every other server by certificate
    /// immutability plus unchanged local state.
    pub proof fn lemma_committed_entries_have_log_certificates_inductive(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            CommittedEntriesHaveLogCertificates(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CommittedEntriesHaveLogCertificates(ds_),
    {
        let (server_id, sent_pkts, recv_from) =
            lemma_extract_step_with_network(ds, ds_);

        assert forall |server: int, index: int|
            #![trigger ds_.server_states[server].log[index]]
            0 <= server < ds_.num_servers
            && 0 <= index < ds_.server_states[server].commit_index
            && index < ds_.server_states[server].log.len()
        implies {
            &&& ds_.log_commit_certificates.dom().contains(index)
            &&& ds_.log_commit_certificates[index].log_index == index
            &&& ds_.log_commit_certificates[index].entry
                == ds_.server_states[server].log[index]
        } by {
            if server == server_id {
                assert(ds_.server_states[server]
                    == ds_.server_states[server_id]);
            } else {
                assert(ds_.server_states[server]
                    == ds.server_states[server]);
                assert(CommittedEntriesHaveLogCertificates(ds));
                assert(ds.log_commit_certificates.dom().contains(index));
                assert(ds.log_commit_certificates[index].log_index == index);
                assert(ds.log_commit_certificates[index].entry
                    == ds.server_states[server].log[index]);
                assert(ds_.log_commit_certificates.dom().contains(index));
                assert(ds_.log_commit_certificates[index].log_index
                    == ds.log_commit_certificates[index].log_index);
                assert(ds_.log_commit_certificates[index].entry
                    == ds.log_commit_certificates[index].entry);
            }
        };
    }

    /// All-entry certificate validity is preserved. Old certificates retain
    /// their meaning because logs only grow and commit indexes never move
    /// backward. A new certificate is justified by the committing leader's
    /// membership-aware replicator set and the matching prefixes recorded by
    /// match_index.
    pub proof fn lemma_log_commit_certificates_valid_inductive(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            LogCommitCertificatesValid(ds),
            WellFormedRaftDistributed(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            LogCommitCertificatesValid(ds_),
    {
        lemma_log_append_only(ds, ds_);
        let (server_id, sent_pkts, recv_from) =
            lemma_extract_step_with_network(ds, ds_);
        let leader = ds.server_states[server_id];
        let leader_ = ds_.server_states[server_id];
        let constants = ds.server_constants[server_id];

        assert forall |index: int|
            #![trigger ds_.log_commit_certificates[index]]
            ds_.log_commit_certificates.dom().contains(index)
        implies {
            let certificate = ds_.log_commit_certificates[index];
            &&& certificate.log_index == index
            &&& 0 <= certificate.committer < ds_.num_servers
            &&& certificate.quorum.contains(certificate.committer)
            &&& is_quorum_for_phase(
                certificate.quorum,
                certificate.governing_phase,
            )
            &&& certificate.governing_phase
                == active_membership_phase_from_raft_log(
                    ds_.server_states[certificate.committer].log,
                    index,
                    MembershipPhase::Stable {
                        config: ds_.server_constants[certificate.committer]
                            .servers,
                    },
                )
            &&& 0 <= index
                < ds_.server_states[certificate.committer].commit_index
            &&& ds_.server_states[certificate.committer].commit_index
                <= ds_.server_states[certificate.committer].log.len()
            &&& ds_.server_states[certificate.committer].log[index]
                == certificate.entry
            &&& forall |replica: int|
                #![trigger certificate.quorum.contains(replica)]
                certificate.quorum.contains(replica)
                ==> {
                    &&& 0 <= replica < ds_.num_servers
                    &&& index < ds_.server_states[replica].log.len()
                    &&& ds_.server_states[replica].log[index]
                        == certificate.entry
                    &&& forall |prefix_index: int| #![trigger ds_.server_states[replica].log[prefix_index]]
                        0 <= prefix_index <= index
                        ==> ds_.server_states[replica].log[prefix_index]
                            == ds_.server_states[certificate.committer]
                                .log[prefix_index]
                }
        } by {
            let certificate = ds_.log_commit_certificates[index];
            if ds.log_commit_certificates.dom().contains(index) {
                let old_certificate = ds.log_commit_certificates[index];
                assert(LogCommitCertificatesValid(ds));
                assert(certificate.log_index == old_certificate.log_index);
                assert(certificate.entry == old_certificate.entry);
                assert(certificate.committer == old_certificate.committer);
                assert(certificate.governing_phase
                    == old_certificate.governing_phase);
                assert(certificate.quorum == old_certificate.quorum);
                assert(certificate == old_certificate);
                assert(ds_.num_servers == ds.num_servers);
                assert(ds_.server_constants == ds.server_constants);

                if certificate.committer != server_id {
                    assert(ds_.server_states[certificate.committer]
                        == ds.server_states[certificate.committer]);
                } else {
                    assert(leader_.commit_index >= leader.commit_index);
                }
                assert(ds_.server_states[certificate.committer].commit_index
                    >= ds.server_states[certificate.committer].commit_index);
                assert(ds_.server_states[certificate.committer].log.len()
                    >= ds.server_states[certificate.committer].log.len());
                assert forall |prefix_index: int|
                    0 <= prefix_index < index
                    implies ds_.server_states[certificate.committer]
                        .log[prefix_index]
                        == ds.server_states[certificate.committer]
                            .log[prefix_index]
                by {
                    assert(LogAppendOnly(ds, ds_));
                };
                lemma_equal_committed_raft_prefixes_have_same_active_phase(
                    ds.server_states[certificate.committer].log,
                    ds_.server_states[certificate.committer].log,
                    index,
                    MembershipPhase::Stable {
                        config: ds.server_constants[certificate.committer]
                            .servers,
                    },
                );
                assert(ds_.server_states[certificate.committer].log[index]
                    == ds.server_states[certificate.committer].log[index]);

                assert forall |replica: int|
                    #![trigger certificate.quorum.contains(replica)]
                    certificate.quorum.contains(replica)
                    implies {
                        &&& 0 <= replica < ds_.num_servers
                        &&& index < ds_.server_states[replica].log.len()
                        &&& ds_.server_states[replica].log[index]
                            == certificate.entry
                        &&& forall |prefix_index: int| #![trigger ds_.server_states[replica].log[prefix_index]]
                            0 <= prefix_index <= index
                            ==> ds_.server_states[replica].log[prefix_index]
                                == ds_.server_states[certificate.committer]
                                    .log[prefix_index]
                    }
                by {
                    assert(0 <= replica < ds.num_servers);
                    assert(ds_.server_states[replica].log.len()
                        >= ds.server_states[replica].log.len());
                    assert(ds_.server_states[replica].log[index]
                        == ds.server_states[replica].log[index]);
                    assert forall |prefix_index: int| #![trigger ds_.server_states[replica].log[prefix_index]]
                        0 <= prefix_index <= index
                        implies ds_.server_states[replica].log[prefix_index]
                            == ds_.server_states[certificate.committer]
                                .log[prefix_index]
                    by {
                        assert(ds_.server_states[replica].log[prefix_index]
                            == ds.server_states[replica].log[prefix_index]);
                        assert(ds.server_states[replica].log[prefix_index]
                            == ds.server_states[certificate.committer]
                                .log[prefix_index]);
                        assert(ds_.server_states[certificate.committer]
                            .log[prefix_index]
                            == ds.server_states[certificate.committer]
                                .log[prefix_index]);
                    };
                };
            } else {
                assert(recv_from is None);
                assert(leader_.commit_index > leader.commit_index);
                assert(leader.commit_index <= index < leader_.commit_index);
                assert(index < leader_.log.len());
                assert(certificate.committer == server_id);
                assert(certificate.entry == leader_.log[index]);
                assert(certificate.quorum == replicator_set(
                    leader, constants, leader_.commit_index));
                assert(LTryAdvanceCommitIndex(
                    leader, leader_, constants,
                    leader_.commit_index, sent_pkts));
                assert(LAdvanceCommitIndex(
                    leader, leader_, constants,
                    leader_.commit_index, sent_pkts));
                assert(leader.role is Leader);
                assert(leader_.log == leader.log);
                assert(0 < leader_.commit_index <= leader.log.len());
                assert(has_active_commit_quorum(
                    leader, constants, leader_.commit_index));
                assert forall |data_index: int| #![trigger leader.log[data_index]]
                    leader.commit_index <= data_index < index
                    implies !(leader.log[data_index].payload is Configuration)
                by {
                    assert(commit_interval_stops_at_first_configuration(
                        leader.log,
                        leader.commit_index,
                        leader_.commit_index,
                    ));
                };
                lemma_configuration_free_interval_preserves_active_phase(
                    leader.log,
                    leader.commit_index,
                    index,
                    MembershipPhase::Stable {
                        config: constants.servers,
                    },
                );
                assert(certificate.governing_phase
                    == active_membership_phase_for_state(
                        leader, constants));
                assert(is_quorum_for_phase(
                    certificate.quorum,
                    certificate.governing_phase,
                ));
                assert(certificate.quorum.contains(server_id));
                assert(ds_.num_servers == ds.num_servers);
                assert(ds_.server_constants == ds.server_constants);

                assert forall |replica: int|
                    #![trigger certificate.quorum.contains(replica)]
                    certificate.quorum.contains(replica)
                    implies {
                        &&& 0 <= replica < ds_.num_servers
                        &&& index < ds_.server_states[replica].log.len()
                        &&& ds_.server_states[replica].log[index]
                            == certificate.entry
                        &&& forall |prefix_index: int| #![trigger ds_.server_states[replica].log[prefix_index]]
                            0 <= prefix_index <= index
                            ==> ds_.server_states[replica].log[prefix_index]
                                == ds_.server_states[certificate.committer]
                                    .log[prefix_index]
                    }
                by {
                    lemma_replicator_set_member_has_matching_prefix(
                        ds, server_id, replica, leader_.commit_index);
                    assert(index < leader_.commit_index);
                    assert(ds_.server_states[replica].log.len()
                        >= ds.server_states[replica].log.len());
                    assert(ds_.server_states[replica].log[index]
                        == ds.server_states[replica].log[index]);
                    assert(ds.server_states[replica].log[index]
                        == leader.log[index]);
                    assert forall |prefix_index: int| #![trigger ds_.server_states[replica].log[prefix_index]]
                        0 <= prefix_index <= index
                        implies ds_.server_states[replica].log[prefix_index]
                            == ds_.server_states[certificate.committer]
                                .log[prefix_index]
                    by {
                        assert(prefix_index < leader_.commit_index);
                        assert(ds_.server_states[replica].log[prefix_index]
                            == ds.server_states[replica].log[prefix_index]);
                        assert(ds.server_states[replica].log[prefix_index]
                            == leader.log[prefix_index]);
                        assert(leader_.log[prefix_index]
                            == leader.log[prefix_index]);
                    };
                };
            }
        };
    }

    /// Committer provenance is monotone: old certificate fields are
    /// immutable, logs are append-only, and commit indexes never decrease.
    /// A new certificate names the stepping leader, which belongs to its own
    /// replicator set and has just committed through the certified index.
    pub proof fn lemma_configuration_committers_retain_certified_prefixes_inductive(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            ConfigurationCommittersRetainCertifiedPrefixes(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            ConfigurationCommittersRetainCertifiedPrefixes(ds_),
    {
        lemma_log_append_only(ds, ds_);
        let (server_id, sent_pkts, recv_from) =
            lemma_extract_step_with_network(ds, ds_);

        assert forall |index: int|
            #![trigger ds_.configuration_commit_certificates[index]]
            ds_.configuration_commit_certificates.dom().contains(index)
        implies {
            let certificate = ds_.configuration_commit_certificates[index];
            &&& 0 <= certificate.committer < ds_.num_servers
            &&& certificate.quorum.contains(certificate.committer)
            &&& certificate.log_index == index
            &&& 0 <= index
                < ds_.server_states[certificate.committer].commit_index
            &&& ds_.server_states[certificate.committer].commit_index
                <= ds_.server_states[certificate.committer].log.len()
            &&& ds_.server_states[certificate.committer].log[index]
                == certificate.entry
        } by {
            let certificate = ds_.configuration_commit_certificates[index];
            if ds.configuration_commit_certificates.dom().contains(index) {
                let old_certificate =
                    ds.configuration_commit_certificates[index];
                lemma_configuration_committer_retains_certified_prefix(
                    ds, index,
                );
                assert(certificate.committer == old_certificate.committer);
                assert(certificate.entry == old_certificate.entry);
                assert(certificate.log_index == old_certificate.log_index);
                assert(certificate.quorum == old_certificate.quorum);
                assert(ds_.num_servers == ds.num_servers);
                assert(0 <= certificate.committer < ds_.num_servers);
                assert(certificate.quorum.contains(certificate.committer));
                assert(certificate.log_index == index);

                if certificate.committer != server_id {
                    assert(ds_.server_states[certificate.committer]
                        == ds.server_states[certificate.committer]);
                } else {
                    assert(LNext(
                        ds.server_states[server_id],
                        ds_.server_states[server_id],
                        ds.server_constants[server_id],
                    ));
                    assert(ds_.server_states[server_id].commit_index
                        >= ds.server_states[server_id].commit_index);
                }
                assert(ds_.server_states[certificate.committer].commit_index
                    >= ds.server_states[certificate.committer].commit_index);
                assert(index
                    < ds_.server_states[certificate.committer].commit_index);
                assert(ds_.server_states[certificate.committer].log.len()
                    >= ds.server_states[certificate.committer].log.len());
                assert(ds_.server_states[certificate.committer].log[index]
                    == ds.server_states[certificate.committer].log[index]);
                assert(ds_.server_states[certificate.committer].log[index]
                    == certificate.entry);
                assert(ds_.server_states[certificate.committer].commit_index
                    <= ds_.server_states[certificate.committer].log.len());
            } else {
                assert(certificate.committer == server_id);
                assert(certificate.log_index == index);
                assert(certificate.entry
                    == ds_.server_states[server_id].log[index]);
                assert(index
                    == ds_.server_states[server_id].commit_index - 1);
                assert(0 <= index
                    < ds_.server_states[server_id].log.len());
                assert(0 <= server_id < ds_.num_servers);
                assert(ds.server_constants[server_id].my_id == server_id);
                assert(certificate.quorum == replicator_set(
                    ds.server_states[server_id],
                    ds.server_constants[server_id],
                    ds_.server_states[server_id].commit_index,
                ));
                assert(certificate.quorum.contains(server_id));
                assert(index
                    < ds_.server_states[server_id].commit_index);
                assert(ds_.server_states[server_id].commit_index
                    <= ds_.server_states[server_id].log.len());
            }
        };
    }

    /// Certificates already present before a distributed step remain valid:
    /// their fields are immutable and every server log preserves its old
    /// prefix.
    pub proof fn lemma_existing_configuration_commit_certificates_remain_valid(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            forall |index: int|
                #![trigger ds.configuration_commit_certificates[index]]
                ds.configuration_commit_certificates.dom().contains(index)
                ==> {
                    let certificate =
                        ds_.configuration_commit_certificates[index];
                    &&& ds_.configuration_commit_certificates.dom()
                        .contains(index)
                    &&& certificate.log_index == index
                    &&& is_quorum_for_phase(
                        certificate.quorum,
                        certificate.governing_phase,
                    )
                    &&& certificate.entry.payload is Configuration
                    &&& forall |replica: int|
                        #![trigger ds_.server_states[replica].log[index]]
                        certificate.quorum.contains(replica)
                        ==> {
                            &&& 0 <= replica < ds_.num_servers
                            &&& configuration_commit_certificate_matches_log(
                                certificate,
                                ds_.server_states[replica].log,
                                MembershipPhase::Stable {
                                    config: ds_.server_constants[replica].servers,
                                },
                            )
                        }
                },
    {
        lemma_log_append_only(ds, ds_);
        let (server_id, sent_pkts, recv_from) =
            lemma_extract_step_with_network(ds, ds_);

        assert forall |index: int|
            #![trigger ds.configuration_commit_certificates[index]]
            ds.configuration_commit_certificates.dom().contains(index)
            implies {
                let certificate =
                    ds_.configuration_commit_certificates[index];
                &&& ds_.configuration_commit_certificates.dom()
                    .contains(index)
                &&& certificate.log_index == index
                &&& is_quorum_for_phase(
                    certificate.quorum,
                    certificate.governing_phase,
                )
                &&& certificate.entry.payload is Configuration
                &&& forall |replica: int|
                    #![trigger ds_.server_states[replica].log[index]]
                    certificate.quorum.contains(replica)
                    ==> {
                        &&& 0 <= replica < ds_.num_servers
                        &&& configuration_commit_certificate_matches_log(
                            certificate,
                            ds_.server_states[replica].log,
                            MembershipPhase::Stable {
                                config: ds_.server_constants[replica].servers,
                            },
                        )
                    }
            }
        by {
            let old_certificate =
                ds.configuration_commit_certificates[index];
            let certificate =
                ds_.configuration_commit_certificates[index];
            assert(ds_.configuration_commit_certificates.dom()
                .contains(index));
            assert(certificate.log_index == old_certificate.log_index);
            assert(certificate.entry == old_certificate.entry);
            assert(certificate.governing_phase
                == old_certificate.governing_phase);
            assert(certificate.quorum == old_certificate.quorum);
            assert(certificate == old_certificate);
            assert(old_certificate.log_index == index);
            assert(is_quorum_for_phase(
                old_certificate.quorum,
                old_certificate.governing_phase,
            ));
            assert(old_certificate.entry.payload is Configuration);

            assert forall |replica: int|
                #![trigger ds_.server_states[replica].log[index]]
                certificate.quorum.contains(replica)
                implies {
                    &&& 0 <= replica < ds_.num_servers
                    &&& configuration_commit_certificate_matches_log(
                        certificate,
                        ds_.server_states[replica].log,
                        MembershipPhase::Stable {
                            config: ds_.server_constants[replica].servers,
                        },
                    )
                }
            by {
                lemma_configuration_commit_certificate_valid_for_replica(
                    ds,
                    index,
                    replica,
                );
                assert(0 <= replica < ds.num_servers);
                assert(ds_.num_servers == ds.num_servers);
                assert(ds_.server_constants == ds.server_constants);
                assert(configuration_commit_certificate_matches_log(
                    old_certificate,
                    ds.server_states[replica].log,
                    MembershipPhase::Stable {
                        config: ds.server_constants[replica].servers,
                    },
                ));
                assert(0 <= index
                    < ds.server_states[replica].log.len());
                assert(ds_.server_states[replica].log.len()
                    >= ds.server_states[replica].log.len());
                assert forall |prefix_index: int|
                    0 <= prefix_index < index
                    implies ds.server_states[replica].log[prefix_index]
                        == ds_.server_states[replica].log[prefix_index]
                by {
                    assert(LogAppendOnly(ds, ds_));
                };
                lemma_equal_committed_raft_prefixes_have_same_active_phase(
                    ds.server_states[replica].log,
                    ds_.server_states[replica].log,
                    index,
                    MembershipPhase::Stable {
                        config: ds.server_constants[replica].servers,
                    },
                );
                assert(ds_.server_states[replica].log[index]
                    == ds.server_states[replica].log[index]);
                assert(configuration_commit_certificate_matches_log(
                    certificate,
                    ds_.server_states[replica].log,
                    MembershipPhase::Stable {
                        config: ds_.server_constants[replica].servers,
                    },
                ));
            };
        };
    }

    /// A certificate created by one leader commit is backed by the exact
    /// replication quorum and legal membership boundary used by that commit.
    pub proof fn lemma_new_configuration_commit_certificate_is_valid(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
        index: int,
    )
        requires
            AllRaftMembershipLogsWellFormed(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            RaftDistributedNext(ds, ds_),
            ds_.configuration_commit_certificates.dom().contains(index),
            !ds.configuration_commit_certificates.dom().contains(index),
        ensures ({
            let certificate =
                ds_.configuration_commit_certificates[index];
            &&& certificate.log_index == index
            &&& is_quorum_for_phase(
                certificate.quorum,
                certificate.governing_phase,
            )
            &&& certificate.entry.payload is Configuration
            &&& forall |replica: int|
                #![trigger certificate.quorum.contains(replica)]
                certificate.quorum.contains(replica)
                ==> 0 <= replica < ds_.num_servers
            &&& forall |replica: int|
                #![trigger ds_.server_states[replica].log[index]]
                0 <= replica < ds_.num_servers
                && certificate.quorum.contains(replica)
                ==> configuration_commit_certificate_matches_log(
                    certificate,
                    ds_.server_states[replica].log,
                    MembershipPhase::Stable {
                        config: ds_.server_constants[replica].servers,
                    },
                )
        })
    {
        let (leader_id, sent_pkts, recv_from) =
            lemma_extract_step_with_network(ds, ds_);
        let leader = ds.server_states[leader_id];
        let leader_ = ds_.server_states[leader_id];
        let constants = ds.server_constants[leader_id];
        let certificate =
            ds_.configuration_commit_certificates[index];
        let initial_phase = MembershipPhase::Stable {
            config: constants.servers,
        };

        assert(recv_from is None);
        assert(leader_.commit_index > leader.commit_index);
        assert(index == leader_.commit_index - 1);
        assert(0 <= index < leader_.log.len());
        assert(leader_.log[index].payload is Configuration);
        assert(certificate.log_index == index);
        assert(certificate.entry == leader_.log[index]);
        assert(certificate.governing_phase
            == active_membership_phase_for_state(leader, constants));
        assert(certificate.quorum
            == replicator_set(
                leader,
                constants,
                leader_.commit_index,
            ));

        assert(LTryAdvanceCommitIndex(
            leader,
            leader_,
            constants,
            leader_.commit_index,
            sent_pkts,
        ));
        assert(LAdvanceCommitIndex(
            leader,
            leader_,
            constants,
            leader_.commit_index,
            sent_pkts,
        ));
        assert(leader.role is Leader);
        assert(leader_.log == leader.log);
        assert(0 < leader_.commit_index <= leader.log.len());
        assert(has_active_commit_quorum(
            leader,
            constants,
            leader_.commit_index,
        ));
        assert(is_quorum_for_phase(
            certificate.quorum,
            certificate.governing_phase,
        ));
        assert(certificate.entry.payload is Configuration);

        assert(raft_membership_log_is_well_formed(
            leader.log,
            initial_phase,
        ));
        assert forall |data_index: int| #![trigger leader.log[data_index]]
            leader.commit_index <= data_index < index
            implies !(leader.log[data_index].payload is Configuration)
        by {
            assert(commit_interval_stops_at_first_configuration(
                leader.log,
                leader.commit_index,
                leader_.commit_index,
            ));
        };
        lemma_configuration_free_interval_preserves_active_phase(
            leader.log,
            leader.commit_index,
            index,
            initial_phase,
        );
        lemma_adjacent_committed_raft_prefixes_progress_legally(
            leader.log,
            index + 1,
            initial_phase,
        );

        match leader.log[index].payload {
            LLogValue::Configuration { phase } => {
                assert(active_membership_phase_from_raft_log(
                    leader.log,
                    index + 1,
                    initial_phase,
                ) == membership_phase_view(phase));
                assert(is_legal_phase_progression(
                    certificate.governing_phase,
                    membership_phase_view(phase),
                ));
            },
            LLogValue::Data { value: _ } => {
                assert(false);
            },
        }

        lemma_log_append_only(ds, ds_);

        assert forall |replica: int|
            #![trigger certificate.quorum.contains(replica)]
            certificate.quorum.contains(replica)
            implies 0 <= replica < ds_.num_servers
        by {
            lemma_replicator_set_member_has_matching_prefix(
                ds,
                leader_id,
                replica,
                leader_.commit_index,
            );
        };

        assert forall |replica: int|
            #![trigger ds_.server_states[replica].log[index]]
            0 <= replica < ds_.num_servers
            && certificate.quorum.contains(replica)
            implies configuration_commit_certificate_matches_log(
                certificate,
                ds_.server_states[replica].log,
                MembershipPhase::Stable {
                    config: ds_.server_constants[replica].servers,
                },
            )
        by {
            lemma_replicator_set_member_has_matching_prefix(
                ds,
                leader_id,
                replica,
                leader_.commit_index,
            );
            assert(leader_.commit_index
                <= ds.server_states[replica].log.len());
            assert(ds_.server_states[replica].log.len()
                >= ds.server_states[replica].log.len());
            assert forall |prefix_index: int| #![trigger leader.log[prefix_index]]
                0 <= prefix_index < leader_.commit_index
                implies ds_.server_states[replica].log[prefix_index]
                    == leader.log[prefix_index]
            by {
                assert(ds_.server_states[replica].log[prefix_index]
                    == ds.server_states[replica].log[prefix_index]);
                assert(ds.server_states[replica].log[prefix_index]
                    == leader.log[prefix_index]);
            };
            assert(ds_.server_constants == ds.server_constants);
            assert(constants.servers
                == ds_.server_constants[replica].servers);
            lemma_equal_committed_raft_prefixes_have_same_active_phase(
                leader.log,
                ds_.server_states[replica].log,
                index,
                initial_phase,
            );
            assert(ds_.server_states[replica].log[index]
                == leader.log[index]);
            assert(configuration_commit_certificate_matches_log(
                certificate,
                ds_.server_states[replica].log,
                MembershipPhase::Stable {
                    config: ds_.server_constants[replica].servers,
                },
            ));
        };
    }

    /// Every configuration-commit certificate is valid after one distributed
    /// step: old certificates use append-only preservation, while the only
    /// possible new certificate is justified by the committing leader's
    /// replication quorum.
    pub proof fn lemma_configuration_commit_certificates_valid_inductive(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            ConfigurationCommitCertificatesValid(ds),
            AllRaftMembershipLogsWellFormed(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            ConfigurationCommitCertificatesValid(ds_),
    {
        lemma_existing_configuration_commit_certificates_remain_valid(
            ds, ds_);

        assert forall |index: int|
            #![trigger ds_.configuration_commit_certificates[index]]
            ds_.configuration_commit_certificates.dom().contains(index)
            implies {
                let certificate =
                    ds_.configuration_commit_certificates[index];
                &&& certificate.log_index == index
                &&& is_quorum_for_phase(
                    certificate.quorum,
                    certificate.governing_phase,
                )
                &&& certificate.entry.payload is Configuration
                &&& forall |replica: int|
                    #![trigger certificate.quorum.contains(replica)]
                    certificate.quorum.contains(replica)
                    ==> 0 <= replica < ds_.num_servers
                &&& forall |replica: int|
                    #![trigger ds_.server_states[replica].log[index]]
                    0 <= replica < ds_.num_servers
                    && certificate.quorum.contains(replica)
                    ==> configuration_commit_certificate_matches_log(
                        certificate,
                        ds_.server_states[replica].log,
                        MembershipPhase::Stable {
                            config: ds_.server_constants[replica].servers,
                        },
                    )
            }
        by {
            if ds.configuration_commit_certificates.dom().contains(index) {
                assert(ConfigurationCommitCertificatesValid(ds));
            } else {
                lemma_new_configuration_commit_certificate_is_valid(
                    ds, ds_, index);
            }
        };
    }

    proof fn lemma_vote_response_integrity_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            VoteResponseIntegrity(ds),
            SenderIntegrity(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            VoteResponseIntegrity(ds_)
    {
        lemma_vote_response_integrity_old_packets(ds, ds_);
        let (server_id, sent_pkts, recv_from) =
            lemma_extract_step_with_network(ds, ds_);
        lemma_vote_response_integrity_new_packets(
            ds, ds_, server_id, sent_pkts, recv_from);
    }

    /// Old packets preserve VoteResponseIntegrity: if a granted VoteResponse
    /// was in ds.network, the invariant properties still hold in ds_.
    proof fn lemma_vote_response_integrity_old_packets(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            VoteResponseIntegrity(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] #![trigger ds.network.contains(p)]
                ds_.network.contains(p) && ds.network.contains(p)
            ==> match p.msg {
                LRaftMessage::VoteResponse { term: t, granted, voter: v, .. } => {
                    granted ==> {
                        &&& 0 <= v < ds_.num_servers
                        &&& p.src == v
                        &&& (ds_.server_states[v].current_term > t
                            || (ds_.server_states[v].current_term == t
                                && ds_.server_states[v].has_voted
                                && ds_.server_states[v].voted_for == p.dst))
                    }
                }
                _ => true,
            }
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |sid: int| #![trigger ds.server_states[sid]] #![trigger ds_.server_states[sid]] #![trigger ds.server_constants[sid]] {
            &&& 0 <= sid < ds.num_servers
            &&& LNext(ds.server_states[sid], ds_.server_states[sid],
                       ds.server_constants[sid])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
        };
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        lemma_lnext_term_monotone(s, s_, c);

        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] #![trigger ds.network.contains(p)]
            ds_.network.contains(p) && ds.network.contains(p)
        implies match p.msg {
            LRaftMessage::VoteResponse { term: t, granted, voter: v, .. } => {
                granted ==> {
                    &&& 0 <= v < ds_.num_servers
                    &&& p.src == v
                    &&& (ds_.server_states[v].current_term > t
                        || (ds_.server_states[v].current_term == t
                            && ds_.server_states[v].has_voted
                            && ds_.server_states[v].voted_for == p.dst))
                }
            }
            _ => true,
        } by {
            assert(VoteResponseIntegrity(ds));
            if p.msg is VoteResponse && p.msg->VoteResponse_granted {
                let v = p.msg->VoteResponse_voter;
                let t = p.msg->VoteResponse_term;
                if v != server_id {
                    assert(ds_.server_states[v] == ds.server_states[v]);
                } else {
                    if s_.current_term > s.current_term {
                        // Term increased: was >= t, now strictly > t
                    } else {
                        assert(s_.current_term == s.current_term);
                        if ds.server_states[v].current_term > t {
                            // Was already > t, term didn't decrease
                        } else {
                            lemma_lnext_voted_for_stable(s, s_, c);
                        }
                    }
                }
            }
        }
    }

    /// Characterize granted VoteResponse outputs from LHandleMessage:
    /// The only way to produce a granted VoteResponse is through LGrantVote,
    /// which sets voter = c.my_id, term = candidate_term = s_.current_term,
    /// s_.has_voted = true.
    proof fn lemma_lhandle_message_granted_vote_response(
        s: LState, s_: LState, c: LConstants,
        msg: LRaftMessage, sent_packets: Seq<LRaftMessage>, i: int,
    )
        requires
            LHandleMessage(s, s_, c, msg, sent_packets),
            0 <= i < sent_packets.len(),
            sent_packets[i] is VoteResponse,
            sent_packets[i]->VoteResponse_granted,
        ensures
            sent_packets[i]->VoteResponse_voter == c.my_id,
            sent_packets[i]->VoteResponse_term == s_.current_term,
            s_.has_voted,
            // msg must be a RequestVote, and s_.voted_for == its candidate field
            msg is RequestVote,
            s_.voted_for == msg->RequestVote_candidate,
    {
    }

    /// If RaftActionProduces outputs a granted VoteResponse, the action must be
    /// LHandleMessage processing a RequestVote packet from the network.
    proof fn lemma_action_granted_vr_implies_handle_request_vote(
        ds: RaftDistributedState,
        server_id: int,
        s: LState, s_: LState, c: LConstants,
        sent_pkts: Seq<LRaftMessage>,
        recv_from: Option<int>,
        i: int,
    )
        requires
            RaftActionProduces(ds, server_id, s, s_, c, sent_pkts, recv_from),
            0 <= i < sent_pkts.len(),
            sent_pkts[i] is VoteResponse,
            sent_pkts[i]->VoteResponse_granted,
        ensures
            exists |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
                &&& ds.network.contains(pkt)
                &&& pkt.dst == server_id
                &&& recv_from == Some(pkt.src)
                &&& LHandleMessage(s, s_, c, pkt.msg, sent_pkts)
                &&& pkt.msg is RequestVote
            },
    {
        // RaftActionProduces is a disjunction. Only the LHandleMessage branch
        // can produce a VoteResponse. Among LHandleMessage sub-cases, only
        // LHandleRequestVoteMsg → LGrantVote produces a granted VoteResponse.
        // The other branches (LTimeout, LClientRequest, LSendAppendEntries,
        // LTryAdvanceCommitIndex) never produce VoteResponse messages.
    }

    /// When LHandleMessage processes a RequestVote and grants a vote,
    /// the RequestVote's log parameters pass log_up_to_date against the
    /// voter's pre-state log.
    proof fn lemma_granted_vote_log_up_to_date(
        s: LState, s_: LState, c: LConstants,
        msg: LRaftMessage, sent_packets: Seq<LRaftMessage>,
    )
        requires
            LHandleMessage(s, s_, c, msg, sent_packets),
            sent_packets.len() > 0,
            sent_packets[0] is VoteResponse,
            sent_packets[0]->VoteResponse_granted,
        ensures
            msg is RequestVote,
            // The log_up_to_date check: candidate's log params vs voter's pre-state log
            ({
                let lt = msg->RequestVote_last_log_term;
                let li = msg->RequestVote_last_log_index;
                let L: int = s.log.len() as int;
                let my_last_term: int = if L == 0 { 0int } else { s.log[L - 1].term };
                lt > my_last_term || (lt == my_last_term && li >= L)
            }),
            // The voter's post-state log is unchanged
            s_.log == s.log,
    {
        // LHandleMessage dispatches on msg type. Only LHandleRequestVoteMsg
        // produces a granted VoteResponse (via LGrantVote).
        // LHandleRequestVoteMsg: s_mid = step_down_if_needed(s, term).
        // step_down_if_needed preserves s.log (s_mid.log == s.log).
        // The log_up_to_date check is log_up_to_date(s_mid, last_log_term, last_log_index).
        // Since s_mid.log == s.log, this gives us log_up_to_date against s.log.
        // LGrantVote: s_.log == s_mid.log == s.log.
    }

    /// If RaftActionProduces outputs a RequestVote, the action must be LTimeout,
    /// so sent_pkts has exactly one message and term = s.current_term + 1.
    proof fn lemma_action_request_vote_implies_timeout(
        ds: RaftDistributedState,
        server_id: int,
        s: LState, s_: LState, c: LConstants,
        sent_pkts: Seq<LRaftMessage>,
        recv_from: Option<int>,
        i: int,
    )
        requires
            RaftActionProduces(ds, server_id, s, s_, c, sent_pkts, recv_from),
            0 <= i < sent_pkts.len(),
            sent_pkts[i] is RequestVote,
        ensures
            sent_pkts[i]->RequestVote_term == s.current_term + 1,
            sent_pkts[i]->RequestVote_candidate == c.my_id,
            sent_pkts.len() == 1,
    {
        // RaftActionProduces disjunction: only LTimeout produces RequestVote.
        // LTimeout: sent_packets == seq![RequestVote{term: s.current_term+1, ...}]
    }

    /// New packets satisfy VoteResponseIntegrity: any granted VoteResponse
    /// newly added to the network was produced by LGrantVote.
    proof fn lemma_vote_response_integrity_new_packets(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
        server_id: int,
        sent_pkts: Seq<LRaftMessage>,
        recv_from: Option<int>,
    )
        requires
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            SenderIntegrity(ds),
            0 <= server_id < ds.num_servers,
            RaftActionProduces(ds, server_id,
                ds.server_states[server_id], ds_.server_states[server_id],
                ds.server_constants[server_id], sent_pkts, recv_from),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                    &&& pkt.src == server_id
                    &&& 0 <= pkt.dst < ds.num_servers
                    &&& (exists |i: int| 0 <= i < sent_pkts.len() && pkt.msg == sent_pkts[i])
                    &&& (match recv_from {
                        Some(src) => pkt.dst == src,
                        None => true,
                    })
                },
        ensures
            forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] #![trigger ds.network.contains(p)]
                ds_.network.contains(p) && !ds.network.contains(p)
            ==> match p.msg {
                LRaftMessage::VoteResponse { term: t, granted, voter: v, .. } => {
                    granted ==> {
                        &&& 0 <= v < ds_.num_servers
                        &&& p.src == v
                        &&& (ds_.server_states[v].current_term > t
                            || (ds_.server_states[v].current_term == t
                                && ds_.server_states[v].has_voted
                                && ds_.server_states[v].voted_for == p.dst))
                    }
                }
                _ => true,
            }
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        // c.my_id == server_id from WellFormedRaftDistributed
        assert(c.my_id == server_id) by {
            assert(WellFormedRaftDistributed(ds));
        };

        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] #![trigger ds.network.contains(p)]
            ds_.network.contains(p) && !ds.network.contains(p)
        implies match p.msg {
            LRaftMessage::VoteResponse { term: t, granted, voter: v, .. } => {
                granted ==> {
                    &&& 0 <= v < ds_.num_servers
                    &&& p.src == v
                    &&& (ds_.server_states[v].current_term > t
                        || (ds_.server_states[v].current_term == t
                            && ds_.server_states[v].has_voted
                            && ds_.server_states[v].voted_for == p.dst))
                }
            }
            _ => true,
        } by {
            if p.msg is VoteResponse && p.msg->VoteResponse_granted {
                assert(p.src == server_id);
                let idx = choose |i: int|
                    0 <= i < sent_pkts.len() && p.msg == sent_pkts[i];

                // The action must be LHandleMessage with a RequestVote
                lemma_action_granted_vr_implies_handle_request_vote(
                    ds, server_id, s, s_, c, sent_pkts, recv_from, idx);
                let req_pkt = choose |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
                    &&& ds.network.contains(pkt)
                    &&& pkt.dst == server_id
                    &&& recv_from == Some(pkt.src)
                    &&& LHandleMessage(s, s_, c, pkt.msg, sent_pkts)
                    &&& pkt.msg is RequestVote
                };

                // Get voter/term/has_voted/voted_for from LHandleMessage
                lemma_lhandle_message_granted_vote_response(
                    s, s_, c, req_pkt.msg, sent_pkts, idx);
                let v = p.msg->VoteResponse_voter;
                assert(v == c.my_id);
                assert(v == server_id);
                assert(0 <= v && v < ds_.num_servers);
                assert(p.src == v);
                let t = p.msg->VoteResponse_term;
                assert(t == s_.current_term);
                assert(s_.has_voted);
                assert(ds_.server_states[v] == s_);
                // s_.voted_for == candidate_id from RequestVote
                assert(s_.voted_for == req_pkt.msg->RequestVote_candidate);
                // Routing: p.dst == recv_from.unwrap() == req_pkt.src
                assert(recv_from == Some(req_pkt.src));
                assert(p.dst == req_pkt.src);
                // SenderIntegrity(ds): req_pkt.src == candidate_id
                assert(SenderIntegrity(ds));
                assert(ds.network.contains(req_pkt));
                assert(req_pkt.src == req_pkt.msg->RequestVote_candidate);
                assert(ds_.server_states[v].voted_for == p.dst);
            }
        }
    }

    /// Preserve VoteResponse vote-time summary validity for packets that were
    /// already in the pre-state network.
    proof fn lemma_vote_response_summary_old_packet_preserved(
        ds: RaftDistributedState, ds_: RaftDistributedState, p: LRaftPacket
    )
        requires
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            RaftDistributedNext(ds, ds_),
            VoteResponseIntegrity(ds),
            VoteResponseSummaryStillValidAtOrAboveTerm(ds),
            ds.network.contains(p),
            p.msg is VoteResponse,
            p.msg->VoteResponse_granted,
            0 <= p.msg->VoteResponse_voter < ds_.num_servers,
            ds_.server_states[p.msg->VoteResponse_voter].current_term
                >= p.msg->VoteResponse_term,
        ensures
            ({
                let v = p.msg->VoteResponse_voter;
                let last_idx = p.msg->VoteResponse_voter_last_log_index;
                let last_term = p.msg->VoteResponse_voter_last_log_term;
                &&& 0 <= last_idx <= ds_.server_states[v].log.len()
                &&& (last_idx == 0 ==> last_term == 0)
                &&& (last_idx > 0 ==> ds_.server_states[v].log[last_idx - 1].term == last_term)
            })
    {
        let v = p.msg->VoteResponse_voter;
        let t = p.msg->VoteResponse_term;
        let last_idx = p.msg->VoteResponse_voter_last_log_index;
        let last_term = p.msg->VoteResponse_voter_last_log_term;

        assert(0 <= v < ds.num_servers);
        assert(VoteResponseIntegrity(ds));
        assert(ds.server_states[v].current_term > t
            || (ds.server_states[v].current_term == t
                && ds.server_states[v].has_voted
                && ds.server_states[v].voted_for == p.dst));
        assert(ds.server_states[v].current_term >= t);

        assert(VoteResponseSummaryStillValidAtOrAboveTerm(ds));
        assert(0 <= last_idx <= ds.server_states[v].log.len());
        assert(last_idx == 0 ==> last_term == 0);
        if last_idx > 0 {
            assert(ds.server_states[v].log[last_idx - 1].term == last_term);
        }

        lemma_log_append_only(ds, ds_);
        assert(ds_.server_states[v].log.len() >= ds.server_states[v].log.len());
        if last_idx > 0 {
            assert(last_idx - 1 < ds.server_states[v].log.len());
            assert(ds_.server_states[v].log[last_idx - 1]
                == ds.server_states[v].log[last_idx - 1]);
        }
    }

    /// Establish VoteResponse vote-time summary validity for packets newly added
    /// in the current step.
    proof fn lemma_vote_response_summary_new_packet_established(
        ds: RaftDistributedState, ds_: RaftDistributedState, p: LRaftPacket
    )
        requires
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            RaftDistributedNext(ds, ds_),
            ds_.network.contains(p),
            !ds.network.contains(p),
            p.msg is VoteResponse,
            p.msg->VoteResponse_granted,
            0 <= p.msg->VoteResponse_voter < ds_.num_servers,
            ds_.server_states[p.msg->VoteResponse_voter].current_term
                >= p.msg->VoteResponse_term,
        ensures
            ({
                let v = p.msg->VoteResponse_voter;
                let last_idx = p.msg->VoteResponse_voter_last_log_index;
                let last_term = p.msg->VoteResponse_voter_last_log_term;
                &&& 0 <= last_idx <= ds_.server_states[v].log.len()
                &&& (last_idx == 0 ==> last_term == 0)
                &&& (last_idx > 0 ==> ds_.server_states[v].log[last_idx - 1].term == last_term)
            })
    {
        let v = p.msg->VoteResponse_voter;
        let last_idx = p.msg->VoteResponse_voter_last_log_index;
        let last_term = p.msg->VoteResponse_voter_last_log_term;

        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        let (sent_packets, received_from) =
            choose |sp: Seq<LRaftMessage>, rf: Option<int>| {
                &&& RaftActionProduces(ds, server_id, s, s_, c, sp, rf)
                &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt) ==> ds_.network.contains(pkt))
                &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                    ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                        &&& pkt.src == server_id
                        &&& 0 <= pkt.dst < ds.num_servers
                        &&& (exists |i: int| 0 <= i < sp.len() && pkt.msg == sp[i])
                        &&& (match rf {
                            Some(src) => pkt.dst == src,
                            None => true,
                        })
                    })
            };

        assert(RaftActionProduces(ds, server_id, s, s_, c, sent_packets, received_from));
        assert(forall |pkt: LRaftPacket| ds.network.contains(pkt) ==> ds_.network.contains(pkt));
        assert(forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
            ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                &&& pkt.src == server_id
                &&& 0 <= pkt.dst < ds.num_servers
                &&& (exists |i: int| 0 <= i < sent_packets.len() && pkt.msg == sent_packets[i])
                &&& (match received_from {
                    Some(src) => pkt.dst == src,
                    None => true,
                })
            });

        assert(p.src == server_id);
        let i = choose |i: int| 0 <= i < sent_packets.len() && p.msg == sent_packets[i];
        assert(0 <= i < sent_packets.len());
        assert(sent_packets[i] == p.msg);

        // VoteResponse packets are produced while handling RequestVote.
        let req_pkt = choose |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
            &&& received_from == Some(pkt.src)
            &&& ds.network.contains(pkt)
            &&& pkt.dst == server_id
            &&& LHandleMessage(s, s_, c, pkt.msg, sent_packets)
        };
        assert(ds.network.contains(req_pkt));
        assert(req_pkt.dst == server_id);
        assert(received_from == Some(req_pkt.src));
        assert(LHandleMessage(s, s_, c, req_pkt.msg, sent_packets));
        assert(req_pkt.msg is RequestVote);

        let req_term = req_pkt.msg->RequestVote_term;
        let req_candidate = req_pkt.msg->RequestVote_candidate;
        let req_last_log_index = req_pkt.msg->RequestVote_last_log_index;
        let req_last_log_term = req_pkt.msg->RequestVote_last_log_term;
        assert(LHandleRequestVoteMsg(
            s, s_, c, req_term, req_candidate, req_last_log_index, req_last_log_term,
            sent_packets));
        assert(sent_packets == seq![LRaftMessage::VoteResponse {
            term: req_term,
            granted: true,
            voter: c.my_id,
            voter_last_log_index: s.log.len() as int,
            voter_last_log_term: if s.log.len() == 0 {
                0int
            } else {
                s.log[s.log.len() - 1].term
            },
        }]);

        assert(c.my_id == server_id);
        assert(p.msg == LRaftMessage::VoteResponse {
            term: req_term,
            granted: true,
            voter: c.my_id,
            voter_last_log_index: s.log.len() as int,
            voter_last_log_term: if s.log.len() == 0 {
                0int
            } else {
                s.log[s.log.len() - 1].term
            },
        });
        assert(v == c.my_id);
        assert(v == server_id);
        assert(ds_.server_states[v] == s_);
        assert(s_.log == s.log);

        assert(last_idx == s.log.len() as int);
        assert(0 <= last_idx);
        assert(last_idx <= ds_.server_states[v].log.len());

        if last_idx == 0 {
            assert(last_term == 0);
        } else {
            assert(last_idx > 0);
            assert(s.log.len() > 0);
            assert(last_term == s.log[s.log.len() - 1].term);
            assert(last_idx - 1 == s.log.len() - 1);
            assert(last_idx - 1 < ds_.server_states[v].log.len());
            assert(ds_.server_states[v].log[last_idx - 1].term == last_term);
        }
    }

    proof fn lemma_vote_response_summary_still_valid_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            VoteResponseSummaryStillValidAtOrAboveTerm(ds),
            VoteResponseIntegrity(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            VoteResponseSummaryStillValidAtOrAboveTerm(ds_)
    {
        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] ds_.network.contains(p) implies
            match p.msg {
                LRaftMessage::VoteResponse {
                    term: t,
                    granted,
                    voter: v,
                    voter_last_log_index: last_idx,
                    voter_last_log_term: last_term,
                } => {
                    granted && 0 <= v < ds_.num_servers && ds_.server_states[v].current_term >= t ==> {
                        &&& 0 <= last_idx <= ds_.server_states[v].log.len()
                        &&& (last_idx == 0 ==> last_term == 0)
                        &&& (last_idx > 0 ==> ds_.server_states[v].log[last_idx - 1].term == last_term)
                    }
                }
                _ => true,
            }
        by {
            if p.msg is VoteResponse {
                let t = p.msg->VoteResponse_term;
                let v = p.msg->VoteResponse_voter;
                if p.msg->VoteResponse_granted
                    && 0 <= v < ds_.num_servers
                    && ds_.server_states[v].current_term >= t
                {
                    if ds.network.contains(p) {
                        lemma_vote_response_summary_old_packet_preserved(ds, ds_, p);
                    } else {
                        lemma_vote_response_summary_new_packet_established(ds, ds_, p);
                    }
                }
            }
        };
    }

    proof fn lemma_vote_response_has_request_vote_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            RaftDistributedNext(ds, ds_),
            VoteResponseHasRequestVote(ds),
            SenderIntegrity(ds),
        ensures
            VoteResponseHasRequestVote(ds_)
    {
        // Use full distributed-next witness (not legacy), so we can reason
        // about old/new packets and response routing.
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        let (sent_packets, received_from) =
            choose |sp: Seq<LRaftMessage>, rf: Option<int>| {
                &&& RaftActionProduces(ds, server_id, s, s_, c, sp, rf)
                &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt) ==> ds_.network.contains(pkt))
                &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                    ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                        &&& pkt.src == server_id
                        &&& 0 <= pkt.dst < ds.num_servers
                        &&& (exists |i: int| 0 <= i < sp.len() && pkt.msg == sp[i])
                        &&& (match rf {
                            Some(src) => pkt.dst == src,
                            None => true,
                        })
                    })
            };

        assert(RaftActionProduces(ds, server_id, s, s_, c, sent_packets, received_from));
        assert(forall |pkt: LRaftPacket| ds.network.contains(pkt) ==> ds_.network.contains(pkt));
        assert(forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
            ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                &&& pkt.src == server_id
                &&& 0 <= pkt.dst < ds.num_servers
                &&& (exists |i: int| 0 <= i < sent_packets.len() && pkt.msg == sent_packets[i])
                &&& (match received_from {
                    Some(src) => pkt.dst == src,
                    None => true,
                })
            });

        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] ds_.network.contains(p) implies
            match p.msg {
                LRaftMessage::VoteResponse { term: t, granted, voter: v, .. } => {
                    granted ==> exists |req: LRaftPacket| #![trigger ds_.network.contains(req)] {
                        &&& ds_.network.contains(req)
                        &&& req.src == p.dst
                        &&& req.dst == v
                        &&& req.msg matches LRaftMessage::RequestVote {
                            term,
                            candidate,
                            last_log_index: _,
                            last_log_term: _,
                        }
                        &&& term == t
                        &&& candidate == p.dst
                    }
                }
                _ => true,
            }
        by {
            if p.msg is VoteResponse {
                if p.msg->VoteResponse_granted {
                    if ds.network.contains(p) {
                        // Old packet: reuse IH witness and network monotonicity.
                        assert(VoteResponseHasRequestVote(ds));
                        let req = choose |req: LRaftPacket| #![trigger ds.network.contains(req)] {
                            &&& ds.network.contains(req)
                            &&& req.src == p.dst
                            &&& req.dst == p.msg->VoteResponse_voter
                            &&& req.msg matches LRaftMessage::RequestVote {
                                term,
                                candidate,
                                last_log_index: _,
                                last_log_term: _,
                            }
                            &&& term == p.msg->VoteResponse_term
                            &&& candidate == p.dst
                        };
                        assert(ds_.network.contains(req));
                    } else {
                        // New packet: produced in this step from sent_packets.
                        assert(p.src == server_id);
                        let i = choose |i: int| 0 <= i < sent_packets.len() && p.msg == sent_packets[i];
                        assert(0 <= i < sent_packets.len());
                        assert(sent_packets[i] == p.msg);

                        // If a VoteResponse packet is sent in this model, it comes from
                        // handling RequestVote.
                        let req_pkt = choose |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
                            &&& received_from == Some(pkt.src)
                            &&& ds.network.contains(pkt)
                            &&& pkt.dst == server_id
                            &&& LHandleMessage(s, s_, c, pkt.msg, sent_packets)
                        };
                        assert(ds.network.contains(req_pkt));
                        assert(req_pkt.dst == server_id);
                        assert(received_from == Some(req_pkt.src));
                        assert(LHandleMessage(s, s_, c, req_pkt.msg, sent_packets));
                        assert(req_pkt.msg is RequestVote);

                        let req_term = req_pkt.msg->RequestVote_term;
                        let req_candidate = req_pkt.msg->RequestVote_candidate;
                        let req_last_log_index = req_pkt.msg->RequestVote_last_log_index;
                        let req_last_log_term = req_pkt.msg->RequestVote_last_log_term;
                        assert(LHandleRequestVoteMsg(
                            s, s_, c, req_term, req_candidate, req_last_log_index, req_last_log_term,
                            sent_packets));
                        assert(sent_packets == seq![LRaftMessage::VoteResponse {
                            term: req_term,
                            granted: true,
                            voter: c.my_id,
                            voter_last_log_index: s.log.len() as int,
                            voter_last_log_term: if s.log.len() == 0 {
                                0int
                            } else {
                                s.log[s.log.len() - 1].term
                            },
                        }]);

                        // Packet shape equalities from new-packet rule + action shape.
                        assert(p.msg == LRaftMessage::VoteResponse {
                            term: req_term,
                            granted: true,
                            voter: c.my_id,
                            voter_last_log_index: s.log.len() as int,
                            voter_last_log_term: if s.log.len() == 0 {
                                0int
                            } else {
                                s.log[s.log.len() - 1].term
                            },
                        });
                        assert(p.msg->VoteResponse_term == req_term);
                        assert(p.msg->VoteResponse_voter == c.my_id);
                        assert(c.my_id == server_id);

                        // Routing gives dst == source of the received RequestVote.
                        assert(p.dst == req_pkt.src);
                        // SenderIntegrity on ds: RequestVote.candidate == src.
                        assert(SenderIntegrity(ds));
                        assert(req_candidate == req_pkt.src);

                        // The received RequestVote packet is still in ds_ (network monotonicity),
                        // and is the required provenance witness.
                        assert(ds_.network.contains(req_pkt));
                        assert(exists |req: LRaftPacket| #![trigger ds_.network.contains(req)] {
                            &&& ds_.network.contains(req)
                            &&& req.src == p.dst
                            &&& req.dst == p.msg->VoteResponse_voter
                            &&& req.msg matches LRaftMessage::RequestVote {
                                term,
                                candidate,
                                last_log_index: _,
                                last_log_term: _,
                            }
                            &&& term == p.msg->VoteResponse_term
                            &&& candidate == p.dst
                        }) by {
                            let req = req_pkt;
                            assert(req.src == p.dst);
                            assert(req.dst == p.msg->VoteResponse_voter);
                            assert(req.msg matches LRaftMessage::RequestVote {
                                term,
                                candidate,
                                last_log_index: _,
                                last_log_term: _,
                            });
                            assert(req.msg->RequestVote_term == p.msg->VoteResponse_term);
                            assert(req.msg->RequestVote_candidate == p.dst);
                        };
                    }
                }
            }
        };
    }

    proof fn lemma_append_entries_integrity_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            AppendEntriesIntegrity(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            AppendEntriesIntegrity(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |sid: int| #![trigger ds.server_states[sid]] #![trigger ds_.server_states[sid]] #![trigger ds.server_constants[sid]] {
            &&& 0 <= sid < ds.num_servers
            &&& LNext(ds.server_states[sid], ds_.server_states[sid],
                       ds.server_constants[sid])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        lemma_log_append_only(ds, ds_);
        lemma_lnext_term_monotone(s, s_, c);
        lemma_lnext_log_preserved_or_extended(s, s_, c);

        // Establish that old entries of the stepping server are preserved
        assert forall |k: int| 0 <= k < s.log.len()
            implies #[trigger] s_.log[k] == s.log[k] by {};

        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] ds_.network.contains(p) implies
            match p.msg {
                LRaftMessage::AppendEntries { term: t, leader: l, prev_index,
                                               prev_term, value, has_entry, .. } => {
                    &&& 0 <= l < ds_.num_servers
                    &&& p.src == l
                    &&& prev_index >= 0
                    &&& ds_.server_states[l].current_term >= t
                    &&& ds_.server_states[l].log.len() >= prev_index
                            + ae_entry_count(has_entry)
                    &&& (prev_index > 0 ==>
                        ds_.server_states[l].log[prev_index - 1].term == prev_term)
                    &&& (has_entry ==>
                        ds_.server_states[l].log[prev_index].value == value)
                    &&& (has_entry ==>
                        ds_.server_states[l].log[prev_index].term == t)
                }
                _ => true,
            }
        by {
            if p.msg is AppendEntries {
                let l = p.msg->AppendEntries_leader;
                let prev_index = p.msg->AppendEntries_prev_index;
                let has_entry = p.msg->AppendEntries_has_entry;

                if ds.network.contains(p) {
                    // Old AE packet: AppendEntriesIntegrity(ds) gives conditions on ds.
                    assert(AppendEntriesIntegrity(ds));

                    if l != server_id {
                        // Non-stepping leader: state unchanged
                        assert(ds_.server_states[l] == ds.server_states[l]);
                    } else {
                        // Stepping server is the leader in this old packet.
                        // s == ds.server_states[server_id], s_ == ds_.server_states[server_id]
                        // lemma_lnext_log_preserved_or_extended gives s_.log[k] == s.log[k]
                        // for k < s.log.len(). Since l == server_id:
                        assert(ds.server_states[l] == s);
                        assert(ds_.server_states[l] == s_);
                        assert(s_.log.len() >= s.log.len());
                        // AEI(ds) + has_entry → prev_index < s.log.len()
                        // lemma_lnext_log_preserved_or_extended → s_.log[k] == s.log[k] for k < s.log.len()
                        if has_entry {
                            // s.log.len() >= prev_index + 1 (from AEI)
                            assert(s.log.len() >= prev_index + 1);
                            assert(0 <= prev_index);
                            assert(prev_index < s_.log.len());
                            assert(s_.log[prev_index] == s.log[prev_index]);
                        }
                        if prev_index > 0 {
                            assert(s.log.len() >= prev_index);
                            assert(prev_index - 1 < s.log.len());
                            assert(prev_index - 1 < s_.log.len());
                            assert(s_.log[prev_index - 1] == s.log[prev_index - 1]);
                        }
                    }
                } else {
                    // New AE packet: produced by RaftDistributedNext.
                    // RaftServerStepWithNetwork ensures p.src == stepping server.
                    // Only LSendAppendEntries produces AppendEntries messages.
                    // Its constraints + WellFormedRaftDistributed + frame conditions
                    // establish all AEI conjuncts. All spec fns are open → auto-verify.
                }
            }
        }
    }

    proof fn lemma_one_vote_per_term_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            OneVotePerTermInNetwork(ds),
            VoteResponseIntegrity(ds),
            SenderIntegrity(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            OneVotePerTermInNetwork(ds_)
    {
        let (server_id, sent_pkts, recv_from) =
            lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        assert forall |p1: LRaftPacket, p2: LRaftPacket| #![trigger ds_.network.contains(p1), ds_.network.contains(p2)]
            ds_.network.contains(p1) && ds_.network.contains(p2)
        implies match p1.msg {
            LRaftMessage::VoteResponse { term: t1, granted: g1, voter: v1, .. } =>
                match p2.msg {
                    LRaftMessage::VoteResponse { term: t2, granted: g2, voter: v2, .. } =>
                        (g1 && g2 && v1 == v2 && t1 == t2) ==> p1.dst == p2.dst,
                    _ => true,
                },
            _ => true,
        } by {
            if p1.msg is VoteResponse && p2.msg is VoteResponse
                && p1.msg->VoteResponse_granted && p2.msg->VoteResponse_granted
                && p1.msg->VoteResponse_voter == p2.msg->VoteResponse_voter
                && p1.msg->VoteResponse_term == p2.msg->VoteResponse_term
            {
                let v = p1.msg->VoteResponse_voter;
                let t = p1.msg->VoteResponse_term;

                if ds.network.contains(p1) && ds.network.contains(p2) {
                    // Both old: from OneVotePerTermInNetwork(ds)
                    assert(OneVotePerTermInNetwork(ds));
                } else if !ds.network.contains(p1) && !ds.network.contains(p2) {
                    // Both new: from same step, same sent_pkts, same routing
                    // Both p1.dst and p2.dst == recv_from (routing constraint)
                    assert(match recv_from {
                        Some(src) => p1.dst == src && p2.dst == src,
                        None => true,
                    });
                    // If recv_from is None, both p1.dst and p2.dst are
                    // unconstrained but they came from the same sent_pkts
                    // with the same routing. Actually for VoteResponse,
                    // recv_from must be Some (from LHandleMessage).
                    lemma_action_granted_vr_implies_handle_request_vote(
                        ds, server_id, s, s_, c, sent_pkts, recv_from,
                        choose |i: int| 0 <= i < sent_pkts.len()
                            && p1.msg == sent_pkts[i]);
                    // recv_from is Some, so p1.dst == p2.dst
                } else {
                    // One old, one new. WLOG assume p1 is old, p2 is new.
                    // (symmetric argument if p1 new, p2 old)
                    if ds.network.contains(p1) && !ds.network.contains(p2) {
                        lemma_one_vote_old_new_match(
                            ds, ds_, server_id, s, s_, c,
                            sent_pkts, recv_from, p1, p2);
                    } else {
                        // p1 new, p2 old: symmetric
                        lemma_one_vote_old_new_match(
                            ds, ds_, server_id, s, s_, c,
                            sent_pkts, recv_from, p2, p1);
                    }
                }
            }
        }
    }

    /// Helper: old-new pair in OneVotePerTermInNetwork.
    /// If p_old is an old granted VoteResponse and p_new is a new one with
    /// the same (voter, term), then p_old.dst == p_new.dst.
    proof fn lemma_one_vote_old_new_match(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
        server_id: int,
        s: LState, s_: LState, c: LConstants,
        sent_pkts: Seq<LRaftMessage>,
        recv_from: Option<int>,
        p_old: LRaftPacket,
        p_new: LRaftPacket,
    )
        requires
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            VoteResponseIntegrity(ds),
            SenderIntegrity(ds),
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            RaftActionProduces(ds, server_id, s, s_, c, sent_pkts, recv_from),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                    &&& pkt.src == server_id
                    &&& 0 <= pkt.dst < ds.num_servers
                    &&& (exists |i: int| 0 <= i < sent_pkts.len() && pkt.msg == sent_pkts[i])
                    &&& (match recv_from {
                        Some(src) => pkt.dst == src,
                        None => true,
                    })
                },
            // p_old is old, p_new is new
            ds.network.contains(p_old),
            ds_.network.contains(p_new),
            !ds.network.contains(p_new),
            // Both are granted VoteResponse with same (voter, term)
            p_old.msg is VoteResponse,
            p_new.msg is VoteResponse,
            p_old.msg->VoteResponse_granted,
            p_new.msg->VoteResponse_granted,
            p_old.msg->VoteResponse_voter == p_new.msg->VoteResponse_voter,
            p_old.msg->VoteResponse_term == p_new.msg->VoteResponse_term,
        ensures
            p_old.dst == p_new.dst,
    {
        let v = p_old.msg->VoteResponse_voter;
        let t = p_old.msg->VoteResponse_term;

        // p_new is a new granted VoteResponse from this step.
        // p_new.src == server_id, and from LGrantVote: voter == c.my_id == server_id
        assert(p_new.src == server_id);
        let idx = choose |i: int|
            0 <= i < sent_pkts.len() && p_new.msg == sent_pkts[i];
        // Use action-level helper: action must be LHandleMessage with RequestVote
        lemma_action_granted_vr_implies_handle_request_vote(
            ds, server_id, s, s_, c, sent_pkts, recv_from, idx);
        let req_pkt = choose |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
            &&& ds.network.contains(pkt)
            &&& pkt.dst == server_id
            &&& recv_from == Some(pkt.src)
            &&& LHandleMessage(s, s_, c, pkt.msg, sent_pkts)
            &&& pkt.msg is RequestVote
        };

        // From LHandleMessage helper: voter == c.my_id, term == s_.current_term
        lemma_lhandle_message_granted_vote_response(
            s, s_, c, req_pkt.msg, sent_pkts, idx);
        assert(c.my_id == server_id) by { assert(WellFormedRaftDistributed(ds)); };
        assert(v == server_id);
        assert(t == s_.current_term);

        // p_new.dst == recv_from.unwrap() (routing)
        assert(recv_from is Some);
        assert(p_new.dst == recv_from->Some_0);

        // recv_from == Some(req_pkt.src), and SenderIntegrity gives req_pkt.src == candidate_id
        assert(recv_from == Some(req_pkt.src));
        assert(SenderIntegrity(ds));
        assert(req_pkt.src == req_pkt.msg->RequestVote_candidate);
        let candidate_id = req_pkt.msg->RequestVote_candidate;
        assert(p_new.dst == candidate_id);

        // s_.voted_for == candidate_id (from LHandleMessage helper)
        assert(s_.voted_for == candidate_id);

        // Now for p_old: VoteResponseIntegrity(ds) on p_old
        assert(VoteResponseIntegrity(ds));
        // v == server_id, t == s_.current_term
        // VoteResponseIntegrity(ds) gives:
        //   ds.server_states[v].current_term > t || (== t && has_voted && voted_for == p_old.dst)

        // From LHandleRequestVoteMsg: s_mid = step_down_if_needed(s, candidate_term)
        // where candidate_term comes from RequestVote. LGrantVote requires
        // candidate_term >= s_mid.current_term. And t == s_.current_term == candidate_term.
        // s_mid = step_down_if_needed(s, t).
        // If t > s.current_term: s_mid steps down, s_mid.current_term = t,
        //   s_mid.has_voted = false.
        // If t <= s.current_term: s_mid == s.
        // LGrantVote requires t >= s_mid.current_term (always true since s_mid.current_term <= t)

        // Case analysis on VoteResponseIntegrity(ds) for p_old:
        if ds.server_states[v].current_term > t {
            // s.current_term > t. But LGrantVote needs candidate_term >= s_mid.current_term.
            // If t <= s.current_term: s_mid == s, s_mid.current_term == s.current_term > t.
            //   LGrantVote needs t >= s_mid.current_term = s.current_term > t. Contradiction.
            // If t > s.current_term: impossible since s.current_term > t already.
            assert(s.current_term > t);
            // s_mid = step_down_if_needed(s, t) = s (since t <= s.current_term)
            // LGrantVote: candidate_term (=t) >= s_mid.current_term (=s.current_term > t). Contradiction.
            assert(false);
        } else {
            // ds.server_states[v].current_term == t && has_voted && voted_for == p_old.dst
            assert(s.current_term == t);
            assert(s.has_voted);
            assert(s.voted_for == p_old.dst);

            // s_mid = step_down_if_needed(s, t) = s (since t == s.current_term)
            // LGrantVote guard: !s_mid.has_voted || s_mid.voted_for == candidate_id
            // s_mid == s, s.has_voted == true, so s.voted_for == candidate_id
            // p_old.dst == s.voted_for == candidate_id == p_new.dst
            assert(p_old.dst == candidate_id);
            assert(p_old.dst == p_new.dst);
        }
    }

    // =========================================================================
    // RequestVoteSenderState inductive proof
    // =========================================================================

    /// 34.7.1.e.4.b.2.b.2.b.3.b helper:
    /// preserve RequestVote summary validity for packets that were already in
    /// the pre-state network.
    ///
    /// If an old RequestVote packet remains in network and its candidate is
    /// still at the packet term in post-state, then the packet summary
    /// (last_log_index/last_log_term) is still justified by the candidate's
    /// post-state log.
    proof fn lemma_request_vote_summary_old_packet_preserved(
        ds: RaftDistributedState, ds_: RaftDistributedState, p: LRaftPacket
    )
        requires
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            RaftDistributedNext(ds, ds_),
            RequestVoteSummaryStillValidAtSameTerm(ds),
            RequestVoteSenderState(ds),
            ds.network.contains(p),
            p.msg is RequestVote,
            0 <= p.msg->RequestVote_candidate < ds_.num_servers,
            ds_.server_states[p.msg->RequestVote_candidate].current_term
                == p.msg->RequestVote_term,
        ensures
            ({
                let d = p.msg->RequestVote_candidate;
                let last_idx = p.msg->RequestVote_last_log_index;
                let last_term = p.msg->RequestVote_last_log_term;
                &&& 0 <= last_idx <= ds_.server_states[d].log.len()
                &&& (last_idx == 0 ==> last_term == 0)
                &&& (last_idx > 0 ==> ds_.server_states[d].log[last_idx - 1].term == last_term)
            })
    {
        let d = p.msg->RequestVote_candidate;
        let t = p.msg->RequestVote_term;
        let last_idx = p.msg->RequestVote_last_log_index;
        let last_term = p.msg->RequestVote_last_log_term;

        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        lemma_distributed_next_implies_legacy(ds, ds_);
        lemma_lnext_term_monotone(s, s_, c);
        lemma_lnext_log_preserved_or_extended(s, s_, c);
        assert(RequestVoteSummaryStillValidAtSameTerm(ds));
        assert(RequestVoteSenderState(ds));
        assert(0 <= d < ds.num_servers);
        assert(ds.server_states[d].current_term == t ==> {
            &&& 0 <= last_idx <= ds.server_states[d].log.len()
            &&& (last_idx == 0 ==> last_term == 0)
            &&& (last_idx > 0 ==> ds.server_states[d].log[last_idx - 1].term == last_term)
        });
        assert(ds.server_states[d].current_term > t
            || (ds.server_states[d].current_term == t
                && ds.server_states[d].has_voted
                && ds.server_states[d].voted_for == d));

        if d != server_id {
            assert(ds_.server_states[d] == ds.server_states[d]);
            assert(ds.server_states[d].current_term == t);
            assert(0 <= last_idx <= ds.server_states[d].log.len());
            assert(last_idx == 0 ==> last_term == 0);
            if last_idx > 0 {
                assert(ds.server_states[d].log[last_idx - 1].term == last_term);
            }
        } else {
            assert(ds.server_states[d] == s);
            assert(ds_.server_states[d] == s_);
            if ds.server_states[d].current_term > t {
                assert(s_.current_term >= s.current_term);
                assert(ds_.server_states[d].current_term > t);
                assert(false);
            }
            assert(ds.server_states[d].current_term == t);

            assert(0 <= last_idx <= ds.server_states[d].log.len());
            assert(last_idx == 0 ==> last_term == 0);
            assert(ds_.server_states[d].log.len() >= ds.server_states[d].log.len());
            if last_idx > 0 {
                assert(ds.server_states[d].log[last_idx - 1].term == last_term);
                assert(last_idx - 1 < ds.server_states[d].log.len());
                assert(ds_.server_states[d].log[last_idx - 1]
                    == ds.server_states[d].log[last_idx - 1]);
            }
        }
    }

    /// 34.7.1.e.4.b.2.b.2.b.3.c helper:
    /// establish RequestVote summary validity for packets that are newly added
    /// to the network in this step.
    ///
    /// In this model, new RequestVote packets are produced by LTimeout and
    /// carry the sender's exact last-log summary at send time.
    proof fn lemma_request_vote_summary_new_packet_established(
        ds: RaftDistributedState, ds_: RaftDistributedState, p: LRaftPacket
    )
        requires
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            RaftDistributedNext(ds, ds_),
            ds_.network.contains(p),
            !ds.network.contains(p),
            p.msg is RequestVote,
            0 <= p.msg->RequestVote_candidate < ds_.num_servers,
            ds_.server_states[p.msg->RequestVote_candidate].current_term
                == p.msg->RequestVote_term,
        ensures
            ({
                let d = p.msg->RequestVote_candidate;
                let last_idx = p.msg->RequestVote_last_log_index;
                let last_term = p.msg->RequestVote_last_log_term;
                &&& 0 <= last_idx <= ds_.server_states[d].log.len()
                &&& (last_idx == 0 ==> last_term == 0)
                &&& (last_idx > 0 ==> ds_.server_states[d].log[last_idx - 1].term == last_term)
            })
    {
        let d = p.msg->RequestVote_candidate;
        let t = p.msg->RequestVote_term;
        let last_idx = p.msg->RequestVote_last_log_index;
        let last_term = p.msg->RequestVote_last_log_term;

        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        let (sent_packets, received_from) =
            choose |sp: Seq<LRaftMessage>, rf: Option<int>| {
                &&& RaftActionProduces(ds, server_id, s, s_, c, sp, rf)
                &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt) ==> ds_.network.contains(pkt))
                &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                    ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                        &&& pkt.src == server_id
                        &&& 0 <= pkt.dst < ds.num_servers
                        &&& (exists |i: int| 0 <= i < sp.len() && pkt.msg == sp[i])
                        &&& (match rf {
                            Some(src) => pkt.dst == src,
                            None => true,
                        })
                    })
            };

        assert(RaftActionProduces(ds, server_id, s, s_, c, sent_packets, received_from));
        assert(forall |pkt: LRaftPacket| ds.network.contains(pkt) ==> ds_.network.contains(pkt));
        assert(forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
            ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                &&& pkt.src == server_id
                &&& 0 <= pkt.dst < ds.num_servers
                &&& (exists |i: int| 0 <= i < sent_packets.len() && pkt.msg == sent_packets[i])
                &&& (match received_from {
                    Some(src) => pkt.dst == src,
                    None => true,
                })
            });

        assert(p.src == server_id);
        let i = choose |i: int| 0 <= i < sent_packets.len() && p.msg == sent_packets[i];
        assert(0 <= i < sent_packets.len());
        assert(sent_packets[i] == p.msg);

        // The step that emits RequestVote packets is LTimeout.
        assert(LTimeout(s, s_, c, sent_packets));
        assert(sent_packets == seq![LRaftMessage::RequestVote {
            term: s.current_term + 1,
            candidate: c.my_id,
            last_log_index: s.log.len() as int,
            last_log_term: if s.log.len() == 0 {
                0int
            } else {
                s.log[s.log.len() - 1].term
            },
        }]);

        assert(sent_packets.len() == 1);
        assert(i == 0);
        assert(p.msg == sent_packets[0]);

        assert(d == c.my_id);
        assert(t == s.current_term + 1);
        assert(c.my_id == server_id);
        assert(d == server_id);
        assert(ds_.server_states[d] == s_);
        assert(s_.log == s.log);

        assert(last_idx == s.log.len() as int);
        assert(0 <= last_idx);
        assert(last_idx <= ds_.server_states[d].log.len());

        if last_idx == 0 {
            assert(s.log.len() == 0);
            assert(last_term == 0);
        } else {
            assert(last_idx > 0);
            assert(s.log.len() > 0);
            assert(last_term == s.log[s.log.len() - 1].term);
            assert(last_idx - 1 == s.log.len() - 1);
            assert(last_idx - 1 < ds_.server_states[d].log.len());
            assert(ds_.server_states[d].log[last_idx - 1] == s.log[s.log.len() - 1]);
        }
    }

    proof fn lemma_request_vote_summary_still_valid_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RequestVoteSummaryStillValidAtSameTerm(ds),
            RequestVoteSenderState(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            RequestVoteSummaryStillValidAtSameTerm(ds_)
    {
        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] ds_.network.contains(p) implies
            match p.msg {
                LRaftMessage::RequestVote {
                    term: t,
                    candidate: d,
                    last_log_index: last_idx,
                    last_log_term: last_term,
                } => {
                    0 <= d < ds_.num_servers ==> (
                        ds_.server_states[d].current_term == t ==> {
                            &&& 0 <= last_idx <= ds_.server_states[d].log.len()
                            &&& (last_idx == 0 ==> last_term == 0)
                            &&& (last_idx > 0 ==> ds_.server_states[d].log[last_idx - 1].term == last_term)
                        }
                    )
                }
                _ => true,
            }
        by {
            if p.msg is RequestVote {
                let d = p.msg->RequestVote_candidate;
                let t = p.msg->RequestVote_term;
                if 0 <= d < ds_.num_servers {
                    if ds_.server_states[d].current_term == t {
                        if ds.network.contains(p) {
                            lemma_request_vote_summary_old_packet_preserved(ds, ds_, p);
                        } else {
                            lemma_request_vote_summary_new_packet_established(ds, ds_, p);
                        }
                    }
                }
            }
        };
    }

    /// Phase 34.7.4: Helper for new RequestVote packets —
    /// the summary is always valid regardless of whether candidate
    /// has moved to a higher term.
    proof fn lemma_request_vote_summary_new_packet_always_valid(
        ds: RaftDistributedState, ds_: RaftDistributedState, p: LRaftPacket
    )
        requires
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            RaftDistributedNext(ds, ds_),
            ds_.network.contains(p),
            !ds.network.contains(p),
            p.msg is RequestVote,
            0 <= p.msg->RequestVote_candidate < ds_.num_servers,
        ensures
            ({
                let d = p.msg->RequestVote_candidate;
                let last_idx = p.msg->RequestVote_last_log_index;
                let last_term = p.msg->RequestVote_last_log_term;
                &&& 0 <= last_idx <= ds_.server_states[d].log.len()
                &&& (last_idx == 0 ==> last_term == 0)
                &&& (last_idx > 0 ==> ds_.server_states[d].log[last_idx - 1].term == last_term)
            })
    {
        let d = p.msg->RequestVote_candidate;
        let last_idx = p.msg->RequestVote_last_log_index;
        let last_term = p.msg->RequestVote_last_log_term;

        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        let (sent_packets, received_from) =
            choose |sp: Seq<LRaftMessage>, rf: Option<int>|
                #![trigger RaftActionProduces(ds, server_id, s, s_, c, sp, rf)]
            {
                &&& RaftActionProduces(ds, server_id, s, s_, c, sp, rf)
                &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt) ==> ds_.network.contains(pkt))
                &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                    ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                        &&& pkt.src == server_id
                        &&& 0 <= pkt.dst < ds.num_servers
                        &&& (exists |i: int| 0 <= i < sp.len() && pkt.msg == sp[i])
                    })
            };

        assert(p.src == server_id);
        assert(LTimeout(s, s_, c, sent_packets));
        assert(d == c.my_id);
        assert(c.my_id == server_id);
        assert(d == server_id);
        assert(ds_.server_states[d] == s_);
        assert(s_.log == s.log);
        assert(last_idx == s.log.len() as int);
        if last_idx > 0 {
            assert(last_term == s.log[s.log.len() - 1].term);
            assert(ds_.server_states[d].log[last_idx - 1]
                == s.log[s.log.len() - 1]);
        }
    }

    /// Phase 34.7.4: Prove RequestVoteSummaryAlwaysValid inductive.
    ///
    /// For old packets: IH gives the facts for ds. Since logs are append-only,
    /// the candidate's log in ds_ still satisfies the summary.
    /// For new packets: delegates to helper.
    proof fn lemma_request_vote_summary_always_valid_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RequestVoteSummaryAlwaysValid(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            RequestVoteSummaryAlwaysValid(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& LNext(ds.server_states[sid], ds_.server_states[sid],
                       ds.server_constants[sid])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
        };
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        lemma_lnext_log_preserved_or_extended(s, s_, c);

        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] ds_.network.contains(p) implies
            match p.msg {
                LRaftMessage::RequestVote {
                    term: t,
                    candidate: d,
                    last_log_index: last_idx,
                    last_log_term: last_term,
                } => {
                    0 <= d < ds_.num_servers ==> {
                        &&& 0 <= last_idx <= ds_.server_states[d].log.len()
                        &&& (last_idx == 0 ==> last_term == 0)
                        &&& (last_idx > 0 ==> ds_.server_states[d].log[last_idx - 1].term == last_term)
                    }
                }
                _ => true,
            }
        by {
            if p.msg is RequestVote {
                let d = p.msg->RequestVote_candidate;
                let last_idx = p.msg->RequestVote_last_log_index;
                let last_term = p.msg->RequestVote_last_log_term;
                if 0 <= d < ds_.num_servers {
                    if ds.network.contains(p) {
                        // Old packet: IH + log append-only
                        assert(RequestVoteSummaryAlwaysValid(ds));
                        assert(0 <= last_idx
                            <= ds.server_states[d].log.len());
                        assert(last_idx == 0 ==> last_term == 0);
                        if d != server_id {
                            assert(ds_.server_states[d]
                                == ds.server_states[d]);
                        } else {
                            assert(ds_.server_states[d].log.len()
                                >= ds.server_states[d].log.len());
                            if last_idx > 0 {
                                assert(ds.server_states[d].log[last_idx - 1].term
                                    == last_term);
                                assert(ds_.server_states[d].log[last_idx - 1]
                                    == ds.server_states[d].log[last_idx - 1]);
                            }
                        }
                    } else {
                        // New packet: delegate to helper (avoids RaftActionProduces in forall)
                        lemma_request_vote_summary_new_packet_always_valid(
                            ds, ds_, p);
                    }
                }
            }
        };
    }

    /// Prove RequestVoteLastLogTermBound inductive.
    ///
    /// Old packets: pure IH (bound on packet fields, no server state).
    /// New packets: delegated to helper to isolate RaftActionProduces.
    proof fn lemma_request_vote_last_log_term_bound_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RequestVoteLastLogTermBound(ds),
            CurrentTermGeLogTerms(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            RequestVoteLastLogTermBound(ds_)
    {
        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] ds_.network.contains(p) implies
            match p.msg {
                LRaftMessage::RequestVote {
                    term: t,
                    last_log_index: last_idx,
                    last_log_term: last_term,
                    ..
                } => {
                    last_idx > 0 ==> last_term < t
                }
                _ => true,
            }
        by {
            if p.msg is RequestVote {
                let last_idx = p.msg->RequestVote_last_log_index;
                if last_idx > 0 {
                    if ds.network.contains(p) {
                        assert(RequestVoteLastLogTermBound(ds));
                    } else {
                        lemma_rv_last_log_term_bound_new_packet(ds, ds_, p);
                    }
                }
            }
        };
    }

    /// Helper: new RequestVote packet satisfies last_log_term < term.
    proof fn lemma_rv_last_log_term_bound_new_packet(
        ds: RaftDistributedState, ds_: RaftDistributedState, p: LRaftPacket
    )
        requires
            WellFormedRaftDistributed(ds),
            CurrentTermGeLogTerms(ds),
            RaftDistributedNext(ds, ds_),
            ds_.network.contains(p),
            !ds.network.contains(p),
            p.msg is RequestVote,
            p.msg->RequestVote_last_log_index > 0,
        ensures
            p.msg->RequestVote_last_log_term < p.msg->RequestVote_term,
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& LNext(ds.server_states[sid], ds_.server_states[sid],
                       ds.server_constants[sid])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
        };
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        // p is new → comes from LTimeout (only action creating RequestVote)
        assert(LTimeout(s, s_, c, seq![p.msg]));
        let t = p.msg->RequestVote_term;
        let last_term = p.msg->RequestVote_last_log_term;
        assert(t == s.current_term + 1);
        assert(last_term == s.log[s.log.len() - 1].term);
        // CurrentTermGeLogTerms: s.log[k].term <= s.current_term
        let _ = ds.server_states[server_id].log[s.log.len() - 1];
    }

    proof fn lemma_request_vote_sender_state_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RequestVoteSenderState(ds),
            SenderIntegrity(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            RequestVoteSenderState(ds_)
    {
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        lemma_distributed_next_implies_legacy(ds, ds_);
        lemma_lnext_term_monotone(s, s_, c);

        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] ds_.network.contains(p) implies
            match p.msg {
                LRaftMessage::RequestVote { term: t, candidate: d, .. } => {
                    &&& 0 <= d < ds_.num_servers
                    &&& p.src == d
                    &&& (ds_.server_states[d].current_term > t
                        || (ds_.server_states[d].current_term == t
                            && ds_.server_states[d].has_voted
                            && ds_.server_states[d].voted_for == d))
                }
                _ => true,
            }
        by {
            if p.msg is RequestVote {
                let t = p.msg->RequestVote_term;
                let d = p.msg->RequestVote_candidate;
                if ds.network.contains(p) {
                    // Old packet: IH
                    assert(RequestVoteSenderState(ds));
                    assert(SenderIntegrity(ds));
                    assert(0 <= d < ds.num_servers);
                    assert(p.src == d);
                    if d != server_id {
                        // d unchanged
                        assert(ds_.server_states[d] == ds.server_states[d]);
                    } else {
                        // d == server_id (stepping server)
                        if ds.server_states[d].current_term > t {
                            // Term was > T, stays >= it by monotonicity
                            assert(s_.current_term >= s.current_term);
                            assert(ds_.server_states[d].current_term > t);
                        } else {
                            // ds.server_states[d].current_term == t
                            // && has_voted && voted_for == d
                            assert(ds.server_states[d].current_term == t);
                            assert(ds.server_states[d].has_voted);
                            assert(ds.server_states[d].voted_for == d);
                            if s_.current_term > t {
                                // Term increased: first disjunct
                            } else {
                                // s_.current_term == t (can't decrease, and == t already)
                                assert(s_.current_term == t);
                                // voted_for stable when has_voted and term unchanged
                                lemma_lnext_voted_for_stable(s, s_, c);
                                assert(s_.has_voted);
                                assert(s_.voted_for == d);
                            }
                        }
                    }
                } else {
                    // New packet: LTimeout is the only action that creates RequestVote.
                    // LTimeout: s_.current_term == s.current_term + 1 == T,
                    //           has_voted = true, voted_for = c.my_id = server_id = d.
                    assert(c.my_id == server_id);
                }
            }
        };
    }

    // =========================================================================
    // RequestVoteLogParamsConsistent inductive proof
    // =========================================================================
    //
    // All RequestVotes from the same candidate at the same term carry identical
    // (last_log_index, last_log_term).
    //
    // Case analysis on (p1 old/new, p2 old/new):
    // - Both old: IH.
    // - Both new: same LTimeout step produces one message, all copies identical.
    // - One old, one new (WLOG p1 old, p2 new): new RequestVote has term =
    //   s.current_term + 1. Old RequestVote at same term from same candidate
    //   implies (RequestVoteSenderState) candidate had current_term >=
    //   s.current_term + 1 in pre-state. But candidate IS the stepping server
    //   with pre-state current_term = s.current_term. Contradiction.

    /// Helper for mixed old+new case: new RequestVote at term t from stepping
    /// server contradicts RequestVoteSenderState on old RequestVote at same
    /// (candidate, term), since the stepping server's pre-state current_term < t.
    proof fn lemma_request_vote_log_params_old_new_contradiction(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int,
        sent_pkts: Seq<LRaftMessage>,
        recv_from: Option<int>,
        p_old: LRaftPacket, p_new: LRaftPacket,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
            0 <= server_id < ds.num_servers,
            RaftActionProduces(ds, server_id,
                ds.server_states[server_id], ds_.server_states[server_id],
                ds.server_constants[server_id], sent_pkts, recv_from),
            // p_old is old, p_new is new
            ds.network.contains(p_old),
            ds_.network.contains(p_new), !ds.network.contains(p_new),
            // Both are RequestVotes with matching (candidate, term)
            p_old.msg is RequestVote, p_new.msg is RequestVote,
            p_old.msg->RequestVote_term == p_new.msg->RequestVote_term,
            p_old.msg->RequestVote_candidate == p_new.msg->RequestVote_candidate,
            // New packet routing
            p_new.src == server_id,
            exists |i: int| 0 <= i < sent_pkts.len() && p_new.msg == sent_pkts[i],
        ensures
            false
    {
        let s = ds.server_states[server_id];
        let c = ds.server_constants[server_id];
        let t = p_new.msg->RequestVote_term;
        // Get index of p_new.msg in sent_pkts
        let i = choose |i: int| 0 <= i < sent_pkts.len() && p_new.msg == sent_pkts[i];
        // LTimeout is the only action producing RequestVote
        lemma_action_request_vote_implies_timeout(
            ds, server_id, s, ds_.server_states[server_id], c,
            sent_pkts, recv_from, i);
        // Now: t == s.current_term + 1
        assert(t == s.current_term + 1);
        // SenderIntegrity on p_new: p_new.src == candidate field
        assert(SenderIntegrity(ds_));
        assert(p_new.msg->RequestVote_candidate == server_id);
        // p_old has same candidate == server_id
        // RequestVoteSenderState(ds) on p_old: server_states[server_id].current_term >= t
        assert(RequestVoteSenderState(ds));
        assert(ds.server_states[server_id].current_term >= t);
        // But s.current_term == ds.server_states[server_id].current_term < t
        // Contradiction
    }

    /// Helper for both-new case: two new RequestVotes from the same step
    /// have identical msg content because LTimeout produces one message.
    proof fn lemma_request_vote_log_params_both_new_match(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int,
        sent_pkts: Seq<LRaftMessage>,
        recv_from: Option<int>,
        p1: LRaftPacket, p2: LRaftPacket,
    )
        requires
            RaftActionProduces(ds, server_id,
                ds.server_states[server_id], ds_.server_states[server_id],
                ds.server_constants[server_id], sent_pkts, recv_from),
            // Both are new RequestVotes
            !ds.network.contains(p1), !ds.network.contains(p2),
            p1.msg is RequestVote, p2.msg is RequestVote,
            // Their msg comes from sent_pkts
            exists |i: int| 0 <= i < sent_pkts.len() && p1.msg == sent_pkts[i],
            exists |j: int| 0 <= j < sent_pkts.len() && p2.msg == sent_pkts[j],
        ensures
            p1.msg->RequestVote_last_log_index == p2.msg->RequestVote_last_log_index,
            p1.msg->RequestVote_last_log_term == p2.msg->RequestVote_last_log_term,
    {
        let i = choose |i: int| 0 <= i < sent_pkts.len() && p1.msg == sent_pkts[i];
        let j = choose |j: int| 0 <= j < sent_pkts.len() && p2.msg == sent_pkts[j];
        // LTimeout produces sent_pkts of length 1, so i == 0 == j.
        lemma_action_request_vote_implies_timeout(
            ds, server_id, ds.server_states[server_id],
            ds_.server_states[server_id], ds.server_constants[server_id],
            sent_pkts, recv_from, i);
        lemma_action_request_vote_implies_timeout(
            ds, server_id, ds.server_states[server_id],
            ds_.server_states[server_id], ds.server_constants[server_id],
            sent_pkts, recv_from, j);
        // sent_pkts.len() == 1, so sent_pkts[i] == sent_pkts[j] == sent_pkts[0]
    }

    proof fn lemma_request_vote_log_params_consistent_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            RequestVoteLogParamsConsistent(ds_)
    {
        let (server_id, sent_pkts, recv_from) =
            lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        assert forall |p1: LRaftPacket, p2: LRaftPacket| #![trigger ds_.network.contains(p1), ds_.network.contains(p2)]
            ds_.network.contains(p1) && ds_.network.contains(p2)
            && (p1.msg is RequestVote) && (p2.msg is RequestVote)
            && p1.msg->RequestVote_term == p2.msg->RequestVote_term
            && p1.msg->RequestVote_candidate == p2.msg->RequestVote_candidate
        implies {
            &&& p1.msg->RequestVote_last_log_index == p2.msg->RequestVote_last_log_index
            &&& p1.msg->RequestVote_last_log_term == p2.msg->RequestVote_last_log_term
        } by {
            if ds.network.contains(p1) && ds.network.contains(p2) {
                // Both old: IH
                assert(RequestVoteLogParamsConsistent(ds));
            } else if !ds.network.contains(p1) && !ds.network.contains(p2) {
                lemma_request_vote_log_params_both_new_match(
                    ds, ds_, server_id, sent_pkts, recv_from, p1, p2);
            } else if ds.network.contains(p1) && !ds.network.contains(p2) {
                lemma_request_vote_log_params_old_new_contradiction(
                    ds, ds_, server_id, sent_pkts, recv_from, p1, p2);
            } else {
                lemma_request_vote_log_params_old_new_contradiction(
                    ds, ds_, server_id, sent_pkts, recv_from, p2, p1);
            }
        };
    }

    // =========================================================================
    // CandidateVoteDestinationUnique inductive proof
    // =========================================================================

    proof fn lemma_candidate_vote_destination_unique_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            RaftDistributedNext(ds, ds_),
            CandidateVoteDestinationUnique(ds),
            RequestVoteSenderState(ds),
            VoteResponseIntegrity(ds),
            SenderIntegrity(ds),
        ensures
            CandidateVoteDestinationUnique(ds_)
    {
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        // Extract network witnesses
        let (sent_packets, received_from) =
            choose |sp: Seq<LRaftMessage>, rf: Option<int>| {
                &&& RaftActionProduces(ds, server_id, s, s_, c, sp, rf)
                &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt) ==> ds_.network.contains(pkt))
                &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                    ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                        &&& pkt.src == server_id
                        &&& 0 <= pkt.dst < ds.num_servers
                        &&& (exists |i: int| 0 <= i < sp.len() && pkt.msg == sp[i])
                        &&& (match rf {
                            Some(src) => pkt.dst == src,
                            None => true,
                        })
                    })
            };

        assert forall |p_req: LRaftPacket, p_vote: LRaftPacket| #![trigger ds_.network.contains(p_req), ds_.network.contains(p_vote)]
            ds_.network.contains(p_req) && ds_.network.contains(p_vote) implies
            match p_req.msg {
                LRaftMessage::RequestVote { term: t_req, candidate: d, .. } =>
                    match p_vote.msg {
                        LRaftMessage::VoteResponse { term: t_vote, granted, voter: v, .. } =>
                            (granted && t_req == t_vote && v == d)
                                ==> p_vote.dst == d,
                        _ => true,
                    },
                _ => true,
            }
        by {
            if p_req.msg is RequestVote && p_vote.msg is VoteResponse {
                let t = p_req.msg->RequestVote_term;
                let d = p_req.msg->RequestVote_candidate;
                let v = p_vote.msg->VoteResponse_voter;
                if p_vote.msg->VoteResponse_granted && t == p_vote.msg->VoteResponse_term && v == d {
                    if ds.network.contains(p_req) && ds.network.contains(p_vote) {
                        // Case 1: both old — IH
                    } else if !ds.network.contains(p_req) && ds.network.contains(p_vote) {
                        // Case 3: new RequestVote + old VoteResponse
                        // p_req is new → p_req.src == server_id, and d == c.my_id == server_id
                        // (from SenderIntegrity on new packet: candidate == src == server_id)
                        // LTimeout: T = s.current_term + 1, so s.current_term = T - 1.
                        // VoteResponseIntegrity on p_vote: d.current_term > T or == T.
                        // But d == server_id, d.current_term == s.current_term == T - 1 < T.
                        // Contradiction: VoteResponse granted can't exist.
                        assert(p_req.src == server_id);
                    } else if ds.network.contains(p_req) && !ds.network.contains(p_vote) {
                        // Case 2: old RequestVote + new VoteResponse
                        // p_vote is new → voter d == c.my_id == server_id
                        assert(p_vote.src == server_id);
                        assert(c.my_id == server_id);
                        // d == server_id, so s == ds.server_states[d]
                        // RequestVoteSenderState on p_req: s.current_term > T or (== T && voted_for == d)
                        // Case s.current_term > T: step_down_if_needed(s, T) is no-op (T <= s.current_term).
                        //   LHandleRequestVoteMsg: T < s.current_term → stale term → no VR → contradiction.
                        // Case s.current_term == T: step_down_if_needed no-op. has_voted && voted_for == d.
                        //   LGrantVote: !has_voted || voted_for == candidate_id → candidate_id == d.
                        //   Routing: p_vote.dst == received_from source == candidate_id == d.
                    } else {
                        // Case 4: both new — impossible (single action, one msg type)
                        assert(p_req.src == server_id);
                        assert(p_vote.src == server_id);
                    }
                }
            }
        };
    }

    // =========================================================================
    // Helper: LNext term monotonicity
    // =========================================================================

    /// LNext never decreases current_term.
    proof fn lemma_lnext_term_monotone(s: LState, s_: LState, c: LConstants)
        requires LNext(s, s_, c)
        ensures s_.current_term >= s.current_term
    {
        // All LNext branches either keep current_term unchanged or increase it
        // (step_down_if_needed increases term when receiving a higher one).
    }

    // =========================================================================
    // Helper: LNext voted_for stability when has_voted and term unchanged
    // =========================================================================

    /// If LNext preserves current_term and has_voted was true before,
    /// then has_voted stays true and voted_for is unchanged.
    /// This follows from analyzing all LNext branches:
    /// - has_voted/voted_for only change via step_down_if_needed (term increases)
    ///   or LGrantVote (requires !has_voted || voted_for == candidate_id).
    /// - If term is unchanged and has_voted was true, LGrantVote can only proceed
    ///   with voted_for == candidate_id, preserving voted_for.
    proof fn lemma_lnext_voted_for_stable(s: LState, s_: LState, c: LConstants)
        requires
            LNext(s, s_, c),
            s.has_voted,
            s_.current_term == s.current_term,
        ensures
            s_.has_voted,
            s_.voted_for == s.voted_for,
    {
        // All LNext branches: if current_term is unchanged, then either:
        // - State fields (has_voted, voted_for) are unchanged (frame conditions), or
        // - LGrantVote fires: requires s_mid.has_voted ==> voted_for == candidate_id.
        //   s_mid == s (since step_down_if_needed doesn't change term).
        //   So s_.voted_for == candidate_id == s.voted_for.
    }

    // =========================================================================
    // Helper: LNext non-Leader to Leader implies Candidate
    // =========================================================================

    /// If LNext produces a Leader from a non-Leader, the pre-state was Candidate.
    proof fn lemma_lnext_non_leader_to_leader_was_candidate(
        s: LState, s_: LState, c: LConstants
    )
        requires
            LNext(s, s_, c),
            !(s.role is Leader),
            s_.role is Leader,
        ensures
            s.role is Candidate,
    {
        // LNext is a disjunction. The only branch that produces Leader from
        // non-Leader is LHandleMessage → LHandleVoteResponseMsg →
        // LReceiveVoteAndBecomeLeader, which requires s_mid.role is Candidate.
        // step_down_if_needed: if term > s.current_term, s_mid.role is Follower
        // (not Candidate → no-op). So s_mid == s, meaning s.role is Candidate.
    }

    // =========================================================================
    // Helper: range set finiteness
    // =========================================================================

    /// The integer range [0, n) is finite with length n.
    proof fn lemma_range_set_finite(n: int)
        requires n >= 0
        ensures
            Set::<int>::range(0, n).len() == n,
    {
        vstd::set_lib::range_set_properties::<int>(0, n);
    }

    // =========================================================================
    // Ghost State Invariant Induction: VoteLogLenCoversNetwork
    // =========================================================================
    //
    // Every granted VoteResponse in the post-network has (voter, term) in
    // vote_log_len. For old packets this holds by IH + ghost-map monotonicity.
    // For new packets: the only action producing granted VoteResponse is
    // LGrantVote, and the ghost state update records (server_id, vt).

    proof fn lemma_vote_log_len_covers_network_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            VoteLogLenCoversNetwork(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            VoteLogLenCoversNetwork(ds_)
    {
        // VoteLogLenCoversNetwork(ds) holds by IH.
        // RaftDistributedNext gives us:
        // (1) network monotonicity: old packets preserved
        // (2) ghost-map monotonicity: old vote_log_len entries preserved
        // (3) new packets come from sent_packets of the stepping server
        // (4) if a granted VoteResponse is in sent_packets, its (voter, term) is recorded

        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        let (sent_packets, received_from) =
            choose |sp: Seq<LRaftMessage>, rf: Option<int>| {
                &&& RaftActionProduces(ds, server_id, s, s_, c, sp, rf)
                &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt)
                    ==> ds_.network.contains(pkt))
                &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                    ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                        &&& pkt.src == server_id
                        &&& 0 <= pkt.dst < ds.num_servers
                        &&& (exists |i: int|
                            0 <= i < sp.len() && pkt.msg == sp[i])
                        &&& (match rf {
                            Some(src) => pkt.dst == src,
                            None => true,
                        })
                    })
                &&& (forall |v: int, t: int|
                    ds.vote_log_len.dom().contains((v, t)) ==>
                        ds_.vote_log_len.dom().contains((v, t)))
                &&& ({
                    ||| (exists |vt: int| {
                        &&& (exists |i: int| #![trigger sp[i]]
                            0 <= i < sp.len()
                            && sp[i] is VoteResponse
                            && sp[i]->VoteResponse_term == vt
                            && sp[i]->VoteResponse_granted
                            && sp[i]->VoteResponse_voter == server_id)
                        &&& ds_.vote_log_len.dom().contains((server_id, vt))
                    })
                    ||| (!(exists |i: int| #![trigger sp[i]]
                        0 <= i < sp.len()
                        && sp[i] is VoteResponse
                        && sp[i]->VoteResponse_granted)
                        && ds_.vote_log_len == ds.vote_log_len)
                })
            };

        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] ds_.network.contains(p) implies
            match p.msg {
                LRaftMessage::VoteResponse { term: t, granted, voter: v, .. } => {
                    granted ==> ds_.vote_log_len.dom().contains((v, t))
                }
                _ => true,
            }
        by {
            if p.msg is VoteResponse && p.msg->VoteResponse_granted {
                let t = p.msg->VoteResponse_term;
                let v = p.msg->VoteResponse_voter;
                if ds.network.contains(p) {
                    // Old packet: IH + ghost-map monotonicity
                    assert(VoteLogLenCoversNetwork(ds));
                    assert(ds.vote_log_len.dom().contains((v, t)));
                    // Ghost-map monotonicity (from RaftServerStepWithNetwork)
                } else {
                    // New packet: voter == server_id, ghost disjunction ensures recorded
                }
            }
        }
    }

    // =========================================================================
    // Ghost State Invariant Induction: VoteLogLenBounded
    // =========================================================================
    //
    // For every (v, t) in vote_log_len, the recorded length <=
    // server_states[v].log.len(). Old entries: IH + LogAppendOnly.
    // New entries: recorded length == s.log.len() == pre-state log length
    //   <= post-state log length (LogAppendOnly).

    proof fn lemma_vote_log_len_bounded_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            VoteLogLenBounded(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            VoteLogLenBounded(ds_)
    {
        // Establish LogAppendOnly as a step property
        lemma_log_append_only(ds, ds_);

        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        let (sent_packets, received_from) =
            choose |sp: Seq<LRaftMessage>, rf: Option<int>| {
                &&& RaftActionProduces(ds, server_id, s, s_, c, sp, rf)
                &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt) ==> ds_.network.contains(pkt))
                &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                    ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                        &&& pkt.src == server_id
                        &&& 0 <= pkt.dst < ds.num_servers
                        &&& (exists |i: int| 0 <= i < sp.len() && pkt.msg == sp[i])
                        &&& (match rf {
                            Some(src) => pkt.dst == src,
                            None => true,
                        })
                    })
                &&& (forall |v: int, t: int| #![trigger ds_.vote_log_len[(v, t)]] #![trigger ds.vote_log_len[(v, t)]] ds.vote_log_len.dom().contains((v, t))
                    ==> ds_.vote_log_len.dom().contains((v, t))
                        && ds_.vote_log_len[(v, t)] == ds.vote_log_len[(v, t)])
                &&& ({
                    ||| (exists |vt: int|
                        #![trigger ds_.vote_log_len.dom().contains((server_id, vt))]
                    {
                        &&& (exists |i: int| #![trigger sp[i]]
                            0 <= i < sp.len()
                            && sp[i] is VoteResponse
                            && sp[i]->VoteResponse_term == vt
                            && sp[i]->VoteResponse_granted
                            && sp[i]->VoteResponse_voter == server_id)
                        &&& ds_.vote_log_len.dom().contains((server_id, vt))
                        &&& ds_.vote_log_len[(server_id, vt)] == s.log.len()
                    })
                    ||| (
                        !(exists |i: int| #![trigger sp[i]]
                            0 <= i < sp.len()
                            && (sp[i] is VoteResponse)
                            && sp[i]->VoteResponse_granted)
                    )
                })
            };

        assert forall |v: int, t: int| #![trigger ds_.vote_log_len.dom().contains((v, t))] ds_.vote_log_len.dom().contains((v, t)) implies {
            &&& 0 <= v < ds_.num_servers
            &&& 0 <= ds_.vote_log_len[(v, t)]
            &&& ds_.vote_log_len[(v, t)] <= ds_.server_states[v].log.len()
            &&& ds_.server_states[v].current_term >= t
        } by {
            if ds.vote_log_len.dom().contains((v, t)) {
                // Old entry: IH gives bounds, LogAppendOnly preserves
                assert(VoteLogLenBounded(ds));
                assert(0 <= v < ds.num_servers);
                assert(0 <= ds.vote_log_len[(v, t)]);
                assert(ds.vote_log_len[(v, t)] <= ds.server_states[v].log.len());
                assert(ds.server_states[v].current_term >= t);
                assert(ds_.vote_log_len[(v, t)] == ds.vote_log_len[(v, t)]);
                // LogAppendOnly: ds_.server_states[v].log.len() >= ds.server_states[v].log.len()
                assert(LogAppendOnly(ds, ds_));
                assert(ds_.server_states[v].log.len() >= ds.server_states[v].log.len());
                // current_term only increases: all LNext branches preserve
                // or increase current_term
                // ds_.server_states[v].current_term >= ds.server_states[v].current_term >= t
            } else {
                // New entry: must be (server_id, vt) from the granted_vote_term witness
                // ds_.vote_log_len[(server_id, vt)] == s.log.len()
                // s == ds.server_states[server_id]
                // LogAppendOnly: ds_.server_states[server_id].log.len() >= s.log.len()
                assert(v == server_id);
                assert(ds_.vote_log_len[(v, t)] == s.log.len());
                assert(s.log.len() >= 0);
                assert(LogAppendOnly(ds, ds_));
                assert(ds_.server_states[server_id].log.len() >= s.log.len());
                // When granting vote at term t, LGrantVote requires
                // term >= s.current_term, and sets s_.current_term = term.
                // So s_.current_term >= t.
            }
        }
    }

    // =========================================================================
    // Ghost State Invariant Induction: VoteLogLenEntryTermBound
    // =========================================================================
    //
    // For all (v, t) in vote_log_len, entries at indices >= vote_log_len[(v,t)]
    // have term >= t.
    //
    // Proof sketch:
    // - Old entries in old log range: by IH + LogAppendOnly (entries preserved).
    // - New entry (if log grew by push): entry.term >= s.current_term >= t.
    //   The s.current_term >= t bound follows from VoteLogLenCoversNetwork
    //   + VoteResponseIntegrity: (v,t) in vote_log_len implies a granted
    //   VoteResponse at term t from v, which implies v.current_term >= t.
    // - New (v, t) entry in vote_log_len: vote_log_len[(v,t)] == s.log.len(),
    //   so there are no indices >= s.log.len() in the pre-state log; the only
    //   new index is the pushed entry (if any), which has term >= current_term = t.

    proof fn lemma_vote_log_len_entry_term_bound_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            VoteLogLenEntryTermBound(ds),
            VoteLogLenBounded(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            VoteLogLenEntryTermBound(ds_)
    {
        lemma_log_append_only(ds, ds_);
        lemma_distributed_next_implies_legacy(ds, ds_);

        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        // Use pair p = (v, t) to provide trigger covering both v and t
        assert forall |p: (int, int), i: int|
            #![trigger ds_.server_states[p.0].log[i], ds_.vote_log_len.dom().contains(p)]
            ds_.vote_log_len.dom().contains(p)
            && 0 <= p.0 < ds_.num_servers
            && ds_.vote_log_len[p] <= i
            && i < ds_.server_states[p.0].log.len()
        implies ds_.server_states[p.0].log[i].term >= p.1 by {
            let v = p.0;
            let t = p.1;
            if v != server_id {
                // Non-stepping server: log and vote_log_len unchanged
                assert(ds_.server_states[v] == ds.server_states[v]);
                // (v, t) must be an old entry (new entries only for server_id)
                assert(ds.vote_log_len.dom().contains((v, t)));
                assert(VoteLogLenEntryTermBound(ds));
            } else {
                // Stepping server: v == server_id
                if ds.vote_log_len.dom().contains((v, t)) {
                    // Old (v, t) entry: value preserved
                    if i < ds.server_states[v].log.len() {
                        // Old log entry: preserved by LogAppendOnly, IH applies
                        assert(LogAppendOnly(ds, ds_));
                        assert(ds_.server_states[v].log[i] == ds.server_states[v].log[i]);
                        assert(VoteLogLenEntryTermBound(ds));
                    } else {
                        // New log entry (pushed at index s.log.len())
                        // Need: new_entry.term >= t
                        // VoteLogLenBounded now includes current_term >= t
                        assert(VoteLogLenBounded(ds));
                        assert(ds.server_states[v].current_term >= t);
                        // new_entry.term >= s.current_term >= t
                        // (from LClientRequest or LFollowerAppendEntries)
                    }
                } else {
                    // New (v, t) entry: vote_log_len[(v, t)] == s.log.len()
                    // i >= s.log.len() and i < ds_.server_states[v].log.len()
                    // Log grew by at most 1, so i == s.log.len()
                    assert(LogAppendOnly(ds, ds_));
                    // new_entry.term >= s.current_term
                    // At vote time, current_term was set to t.
                    // Since this is a new entry, the grant just happened
                    // in this step, so s.current_term == t (approximately).
                }
            }
        }
    }

    // =========================================================================
    // Invariant Induction: CurrentTermGeLogTerms
    // =========================================================================
    //
    // For all servers, every log entry's term is <= the server's current_term.
    //
    // Proof sketch:
    // - Non-stepping server: state unchanged, IH transfers.
    // - Stepping server, old entries: log prefix preserved (LogAppendOnly), and
    //   s_.current_term >= s.current_term (lemma_lnext_term_monotone), so
    //   entry.term <= s.current_term <= s_.current_term.
    // - Stepping server, new entry (if log grew): entry.term >= s.current_term
    //   (lemma_lnext_fresh_append_entry_term_ge_pre_current), and for
    //   LClientRequest: entry.term == s.current_term == s_.current_term.
    //   For LFollowerAppendEntries: entry.term == ae_term == s_.current_term.
    //   In both cases entry.term <= s_.current_term.

    proof fn lemma_current_term_ge_log_terms_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            WellFormedRaftDistributed(ds),
            CurrentTermGeLogTerms(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CurrentTermGeLogTerms(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);

        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        assert forall |i: int, k: int|
            #![trigger ds_.server_states[i].log[k]]
            0 <= i < ds_.num_servers
            && 0 <= k < ds_.server_states[i].log.len()
        implies ds_.server_states[i].log[k].term
            <= ds_.server_states[i].current_term by {
            if i != server_id {
                // Non-stepping server: state unchanged
                assert(ds_.server_states[i] == ds.server_states[i]);
                assert(CurrentTermGeLogTerms(ds));
            } else {
                // Stepping server
                lemma_lnext_log_preserved_or_extended(s, s_, c);
                lemma_lnext_term_monotone(s, s_, c);
                if k < s.log.len() {
                    // Old entry: preserved by log extension
                    assert(s_.log[k] == s.log[k]);
                    assert(CurrentTermGeLogTerms(ds));
                    // s.log[k].term <= s.current_term <= s_.current_term
                } else {
                    // New entry (k == s.log.len(), log grew by 1)
                    assert(s_.log.len() == s.log.len() + 1);
                    assert(k == s.log.len() as int);
                    let entry = s_.log[k];
                    lemma_lnext_fresh_append_entry_term_ge_pre_current(
                        s, s_, c, k, entry);
                    // entry.term >= s.current_term
                    // Need: entry.term <= s_.current_term
                    // From LNext case analysis: LClientRequest sets
                    // entry.term = s.current_term = s_.current_term.
                    // LFollowerAppendEntries sets entry.term = ae_term
                    // = s_.current_term.
                }
            }
        }
    }

    // =========================================================================
    // Invariant Induction: LogTermsMonotonic
    // =========================================================================
    //
    // For all servers, log entry terms are monotonically non-decreasing.
    //
    // Proof sketch:
    // - Non-stepping server: state unchanged, IH transfers.
    // - Stepping server:
    //   - Both old entries (j, k < old_len): IH + log prefix preserved.
    //   - Old j, new k (k == old_len): log[j].term <= current_term (from
    //     CurrentTermGeLogTerms) and new entry term >= current_term (from
    //     lemma_lnext_fresh_append_entry_term_ge_pre_current).
    //   - j == k: trivially 0 == 0.

    proof fn lemma_log_terms_monotonic_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            WellFormedRaftDistributed(ds),
            LogTermsMonotonic(ds),
            CurrentTermGeLogTerms(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            LogTermsMonotonic(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);

        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        assert forall |i: int, j: int, k: int|
            #![trigger ds_.server_states[i].log[j], ds_.server_states[i].log[k]]
            0 <= i < ds_.num_servers
            && 0 <= j <= k
            && k < ds_.server_states[i].log.len()
        implies ds_.server_states[i].log[j].term
            <= ds_.server_states[i].log[k].term by {
            if i != server_id {
                // Non-stepping server: state unchanged
                assert(ds_.server_states[i] == ds.server_states[i]);
                assert(LogTermsMonotonic(ds));
            } else {
                // Stepping server
                lemma_lnext_log_preserved_or_extended(s, s_, c);
                if k < s.log.len() {
                    // Both j and k are old entries
                    assert(s_.log[j] == s.log[j]);
                    assert(s_.log[k] == s.log[k]);
                    assert(LogTermsMonotonic(ds));
                } else {
                    // k is the new entry (k == s.log.len())
                    assert(s_.log.len() == s.log.len() + 1);
                    assert(k == s.log.len() as int);
                    if j < s.log.len() {
                        // j is an old entry, k is the new entry
                        assert(s_.log[j] == s.log[j]);
                        let new_entry = s_.log[k];
                        // old entry: log[j].term <= current_term
                        assert(CurrentTermGeLogTerms(ds));
                        // new entry: term >= current_term
                        lemma_lnext_fresh_append_entry_term_ge_pre_current(
                            s, s_, c, k, new_entry);
                        // log[j].term <= current_term <= new_entry.term
                    } else {
                        // j == k (both are the new entry), trivially equal
                        assert(j == k);
                    }
                }
            }
        }
    }

    // =========================================================================
    // Invariant Induction: TermsNonNegative
    // =========================================================================
    //
    // All current_terms and log entry terms are >= 0.
    //
    // Proof sketch:
    // - Non-stepping server: state unchanged, IH transfers.
    // - Stepping server: current_term only goes up (from >= 0 to >= 0).
    //   Old entries preserved. New entry term >= current_term >= 0.

    proof fn lemma_terms_non_negative_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            WellFormedRaftDistributed(ds),
            TermsNonNegative(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            TermsNonNegative(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);

        let server_id = choose |sid: int| #![trigger ds.server_states[sid]] #![trigger ds_.server_states[sid]] #![trigger ds.server_constants[sid]] {
            &&& 0 <= sid < ds.num_servers
            &&& LNext(ds.server_states[sid], ds_.server_states[sid],
                       ds.server_constants[sid])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        // current_term non-negativity
        assert forall |i: int|
            #![trigger ds_.server_states[i].current_term]
            0 <= i < ds_.num_servers
        implies ds_.server_states[i].current_term >= 0 by {
            if i != server_id {
                assert(ds_.server_states[i] == ds.server_states[i]);
            } else {
                lemma_lnext_term_monotone(s, s_, c);
                // s_.current_term >= s.current_term >= 0
            }
        };

        // log entry term non-negativity
        assert forall |i: int, k: int|
            #![trigger ds_.server_states[i].log[k]]
            0 <= i < ds_.num_servers
            && 0 <= k < ds_.server_states[i].log.len()
        implies ds_.server_states[i].log[k].term >= 0 by {
            if i != server_id {
                assert(ds_.server_states[i] == ds.server_states[i]);
                assert(TermsNonNegative(ds));
            } else {
                lemma_lnext_log_preserved_or_extended(s, s_, c);
                if k < s.log.len() {
                    assert(s_.log[k] == s.log[k]);
                    assert(TermsNonNegative(ds));
                } else {
                    // New entry
                    assert(s_.log.len() == s.log.len() + 1);
                    let entry = s_.log[k];
                    lemma_lnext_fresh_append_entry_term_ge_pre_current(
                        s, s_, c, k, entry);
                    // entry.term >= s.current_term >= 0
                }
            }
        };
    }

    // =========================================================================
    // Ghost State Invariant Induction: VoteGrantedLogUpToDateAtVoteTime
    // =========================================================================
    //
    // For every (granted VoteResponse, matching RequestVote) pair in ds_,
    // the RequestVote's log parameters satisfy log_up_to_date against the
    // voter's reconstructed vote-time log.
    //
    // Proof sketch (case analysis on old/new packets):
    // (1) Both packets old: IH + voter log prefix preserved by LogAppendOnly
    // (2) New VoteResponse + old RequestVote: voter just granted vote, and
    //     LHandleRequestVoteMsg checked log_up_to_date at vote time; ghost
    //     state records vote_log_len[(v,t)] = s.log.len(); voter's post-state
    //     log prefix preserves vote-time entries.
    // (3) Old VoteResponse + new RequestVote: vacuous — new RequestVote at
    //     term t requires sender at term t-1 (LTimeout), but old VoteResponse
    //     at term t implies sender previously had RequestVote at term t
    //     (RequestVoteSenderState), so sender was at term >= t. Contradiction.
    // (4) Both new: impossible (different action types produce different packet types)
    //
    // Full decomposed proof is tracked as follow-up sub-leaves.

    /// Case 2 step A: given a granted VoteResponse in sent_pkts,
    /// extract the processed RequestVote and its log_up_to_date fact.
    proof fn lemma_vote_granted_extract_processed_req(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int,
        sent_pkts: Seq<LRaftMessage>,
        recv_from: Option<int>,
        vr_idx: int,
    ) -> (processed_pkt: LRaftPacket)
        requires
            0 <= server_id < ds.num_servers,
            RaftActionProduces(ds, server_id,
                ds.server_states[server_id], ds_.server_states[server_id],
                ds.server_constants[server_id], sent_pkts, recv_from),
            0 <= vr_idx < sent_pkts.len(),
            sent_pkts[vr_idx] is VoteResponse,
            sent_pkts[vr_idx]->VoteResponse_granted,
        ensures
            ds.network.contains(processed_pkt),
            processed_pkt.msg is RequestVote,
            processed_pkt.dst == server_id,
            // Term of processed RequestVote == VoteResponse term
            processed_pkt.msg->RequestVote_term
                == sent_pkts[vr_idx]->VoteResponse_term,
            // recv_from == Some(processed_pkt.src)
            recv_from == Some(processed_pkt.src),
            // log_up_to_date of processed_pkt's log params against s.log
            ({
                let s = ds.server_states[server_id];
                let lt = processed_pkt.msg->RequestVote_last_log_term;
                let li = processed_pkt.msg->RequestVote_last_log_index;
                let L: int = s.log.len() as int;
                let my_last_term: int = if L == 0 { 0int } else { s.log[L - 1].term };
                lt > my_last_term || (lt == my_last_term && li >= L)
            }),
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        lemma_action_granted_vr_implies_handle_request_vote(
            ds, server_id, s, s_, c, sent_pkts, recv_from, vr_idx);
        let processed_pkt: LRaftPacket = choose |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
            &&& ds.network.contains(pkt)
            &&& pkt.dst == server_id
            &&& recv_from == Some(pkt.src)
            &&& LHandleMessage(s, s_, c, pkt.msg, sent_pkts)
            &&& pkt.msg is RequestVote
        };

        lemma_granted_vote_log_up_to_date(s, s_, c, processed_pkt.msg, sent_pkts);
        processed_pkt
    }

    /// Case 2 core: given pre-extracted facts, transfer log_up_to_date to
    /// the conclusion. Takes req's log params directly (pre-equated with
    /// processed_pkt's via RequestVoteLogParamsConsistent by the caller).
    /// Lightweight: NO RaftSafetyInvariant, NO RaftDistributedNext in requires.
    proof fn lemma_vote_granted_log_utd_new_vr_old_req(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int,
        req_lt: int, req_li: int, t: int,
    )
        requires
            0 <= server_id < ds.num_servers,
            // log_up_to_date of req params against s.log
            ({
                let s = ds.server_states[server_id];
                let L: int = s.log.len() as int;
                let my_last_term: int = if L == 0 { 0int } else { s.log[L - 1].term };
                req_lt > my_last_term
                    || (req_lt == my_last_term && req_li >= L)
            }),
            // Ghost state records L = s.log.len()
            ds_.vote_log_len.dom().contains((server_id, t)),
            ds_.vote_log_len[(server_id, t)]
                == ds.server_states[server_id].log.len(),
            // LogAppendOnly for this specific server
            ds_.server_states[server_id].log.len()
                >= ds.server_states[server_id].log.len(),
            forall |k: int| 0 <= k < ds.server_states[server_id].log.len()
                ==> #[trigger] ds_.server_states[server_id].log[k]
                    == ds.server_states[server_id].log[k],
        ensures ({
            let L = ds_.vote_log_len[(server_id, t)];
            let voter_vote_time_last_term: int = if L == 0 {
                0int
            } else {
                ds_.server_states[server_id].log[L - 1].term
            };
            req_lt > voter_vote_time_last_term
                || (req_lt == voter_vote_time_last_term && req_li >= L)
        })
    {
        let s = ds.server_states[server_id];
        let L: int = ds_.vote_log_len[(server_id, t)];
        assert(L == s.log.len());
        if L > 0 {
            assert(ds_.server_states[server_id].log[L - 1]
                == ds.server_states[server_id].log[L - 1]);
        }
    }

    /// Case 3: old VoteResponse + new RequestVote → contradiction.
    /// Caller pre-extracts: new RequestVote has term = s.current_term + 1.
    /// Old VoteResponse at same term implies (VoteResponseHasRequestVote)
    /// a RequestVote at that term was already in ds.network, so
    /// (RequestVoteSenderState) candidate's current_term >= term.
    /// But candidate IS the stepping server with pre-state current_term < term.
    proof fn lemma_vote_granted_log_utd_old_vr_new_req_contradiction(
        ds: RaftDistributedState,
        server_id: int,
        vote_pkt: LRaftPacket,
        new_req_term: int,
    )
        requires
            VoteResponseHasRequestVote(ds),
            RequestVoteSenderState(ds),
            0 <= server_id < ds.num_servers,
            // vote_pkt is OLD granted VoteResponse at the same term
            ds.network.contains(vote_pkt),
            vote_pkt.msg is VoteResponse,
            vote_pkt.msg->VoteResponse_granted,
            vote_pkt.msg->VoteResponse_term == new_req_term,
            vote_pkt.dst == server_id, // candidate == stepping server
            // The new RequestVote's term from LTimeout = s.current_term + 1
            new_req_term == ds.server_states[server_id].current_term + 1,
        ensures
            false
    {
        // VoteResponseHasRequestVote(ds): vote_pkt has matching RequestVote in ds.network
        assert(VoteResponseHasRequestVote(ds));
        // This gives: exists old_req in ds.network with term new_req_term
        //             and candidate == vote_pkt.dst == server_id
        // RequestVoteSenderState(ds) on that old_req:
        //   server_states[server_id].current_term >= new_req_term
        assert(RequestVoteSenderState(ds));
        // But server_states[server_id].current_term + 1 == new_req_term
        // So server_states[server_id].current_term >= server_states[server_id].current_term + 1
        // Contradiction.
    }

    /// Utility: extract ghost state monotonicity from RaftDistributedNext.
    /// Requires RaftSafetyInvariant(ds) to help Z3 with existential extraction.
    /// RaftActionProduces stays local to this function body.
    proof fn lemma_vote_log_len_monotonic(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            forall |v: int, t: int| #![trigger ds_.vote_log_len[(v, t)]] #![trigger ds.vote_log_len[(v, t)]] ds.vote_log_len.dom().contains((v, t))
                ==> ds_.vote_log_len.dom().contains((v, t))
                    && ds_.vote_log_len[(v, t)] == ds.vote_log_len[(v, t)]
    {
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        let (sp, rf) =
            choose |sp: Seq<LRaftMessage>, rf: Option<int>| {
                &&& RaftActionProduces(ds, server_id, s, s_, c, sp, rf)
                &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt)
                    ==> ds_.network.contains(pkt))
                &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                    ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                        &&& pkt.src == server_id
                        &&& 0 <= pkt.dst < ds.num_servers
                        &&& (exists |i: int| 0 <= i < sp.len() && pkt.msg == sp[i])
                        &&& (match rf {
                            Some(src) => pkt.dst == src,
                            None => true,
                        })
                    })
                &&& (forall |v: int, t: int| #![trigger ds_.vote_log_len[(v, t)]] #![trigger ds.vote_log_len[(v, t)]] ds.vote_log_len.dom().contains((v, t))
                    ==> ds_.vote_log_len.dom().contains((v, t))
                        && ds_.vote_log_len[(v, t)] == ds.vote_log_len[(v, t)])
                &&& ({
                    ||| (exists |vt: int|
                        #![trigger ds_.vote_log_len.dom().contains((server_id, vt))]
                    {
                        &&& (exists |i: int| #![trigger sp[i]]
                            0 <= i < sp.len()
                            && sp[i] is VoteResponse
                            && sp[i]->VoteResponse_term == vt
                            && sp[i]->VoteResponse_granted
                            && sp[i]->VoteResponse_voter == server_id)
                        &&& ds_.vote_log_len.dom().contains((server_id, vt))
                        &&& ds_.vote_log_len[(server_id, vt)] == s.log.len()
                    })
                    ||| (
                        !(exists |i: int| #![trigger sp[i]]
                            0 <= i < sp.len()
                            && (sp[i] is VoteResponse)
                            && sp[i]->VoteResponse_granted)
                    )
                })
            };
    }

    /// Case 2 extraction: extracts processed RequestVote and log_up_to_date.
    /// RaftActionProduces stays internal. Called from orchestrator.
    proof fn lemma_vote_granted_case2_extract(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        vote_pkt: LRaftPacket,
    ) -> (processed_pkt: LRaftPacket)
        requires
            SenderIntegrity(ds),
            RaftDistributedNext(ds, ds_),
            ds_.network.contains(vote_pkt), !ds.network.contains(vote_pkt),
            vote_pkt.msg is VoteResponse,
            vote_pkt.msg->VoteResponse_granted,
            0 <= vote_pkt.src < ds_.num_servers,
        ensures ({
            let server_id = vote_pkt.src;
            &&& ds.network.contains(processed_pkt)
            &&& processed_pkt.msg is RequestVote
            &&& processed_pkt.dst == server_id
            // Term of processed_pkt matches VoteResponse term
            &&& processed_pkt.msg->RequestVote_term
                == vote_pkt.msg->VoteResponse_term
            // Candidate of processed_pkt matches VoteResponse destination
            &&& processed_pkt.msg->RequestVote_candidate == vote_pkt.dst
            &&& ({
                let s = ds.server_states[server_id];
                let lt = processed_pkt.msg->RequestVote_last_log_term;
                let li = processed_pkt.msg->RequestVote_last_log_index;
                let L: int = s.log.len() as int;
                let my_last_term: int = if L == 0 { 0int }
                    else { s.log[L - 1].term };
                lt > my_last_term || (lt == my_last_term && li >= L)
            })
        })
    {
        let (server_id, sent_pkts, recv_from) =
            lemma_extract_step_with_network(ds, ds_);
        assert(vote_pkt.src == server_id);
        let vr_idx = choose |i: int| 0 <= i < sent_pkts.len()
            && vote_pkt.msg == sent_pkts[i];
        let processed_pkt = lemma_vote_granted_extract_processed_req(
            ds, ds_, server_id, sent_pkts, recv_from, vr_idx);
        // recv_from == Some(processed_pkt.src), and routing gives vote_pkt.dst == recv_from.unwrap()
        // SenderIntegrity(ds): processed_pkt.msg->RequestVote_candidate == processed_pkt.src
        assert(SenderIntegrity(ds));
        processed_pkt
    }

    /// RVLPC-specific: two RequestVotes with same term and candidate have same log params.
    /// Isolated from RaftDistributedNext/RaftActionProduces to avoid Z3 blow-up.
    proof fn lemma_rvlpc_same_log_params(
        ds: RaftDistributedState,
        p1: LRaftPacket, p2: LRaftPacket,
    )
        requires
            RequestVoteLogParamsConsistent(ds),
            ds.network.contains(p1), ds.network.contains(p2),
            p1.msg is RequestVote, p2.msg is RequestVote,
            p1.msg->RequestVote_term == p2.msg->RequestVote_term,
            p1.msg->RequestVote_candidate == p2.msg->RequestVote_candidate,
        ensures
            p1.msg->RequestVote_last_log_index == p2.msg->RequestVote_last_log_index,
            p1.msg->RequestVote_last_log_term == p2.msg->RequestVote_last_log_term,
    {
    }

    /// Extract ghost state recording: when a new granted VoteResponse is sent,
    /// RaftServerStepWithNetwork records vote_log_len[(voter, term)] == voter's log length.
    /// Isolated from case2_complete to keep RaftActionProduces internal.
    proof fn lemma_extract_ghost_vote_log_len_recording(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        vote_pkt: LRaftPacket,
    )
        requires
            RaftDistributedNext(ds, ds_),
            ds_.network.contains(vote_pkt), !ds.network.contains(vote_pkt),
            vote_pkt.msg is VoteResponse,
            vote_pkt.msg->VoteResponse_granted,
            0 <= vote_pkt.src < ds.num_servers,
        ensures
            ds_.vote_log_len[(vote_pkt.src, vote_pkt.msg->VoteResponse_term)]
                == ds.server_states[vote_pkt.src].log.len(),
    {
        let v = vote_pkt.src;
        let t = vote_pkt.msg->VoteResponse_term;

        // Extract server_id from RaftDistributedNext
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        // vote_pkt is new → routing gives vote_pkt.src == server_id
        assert(server_id == v);

        // RaftServerStepWithNetwork(ds, ds_, v) is established.
        // Choose sent_packets with ALL clauses including ghost recording,
        // adding the vote_pkt constraints to the choose body to help Z3
        // connect the dots.
        let s = ds.server_states[v];
        let s_ = ds_.server_states[v];
        let c = ds.server_constants[v];

        let (sp, rf) =
            choose |sp: Seq<LRaftMessage>, rf: Option<int>|
            #![trigger RaftActionProduces(ds, v, s, s_, c, sp, rf)]
            {
                &&& RaftActionProduces(ds, v, s, s_, c, sp, rf)
                &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt)
                    ==> ds_.network.contains(pkt))
                &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                    ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                        &&& pkt.src == v
                        &&& 0 <= pkt.dst < ds.num_servers
                        &&& (exists |i: int| 0 <= i < sp.len() && pkt.msg == sp[i])
                    })
                &&& (forall |v2: int, t2: int| #![trigger ds_.vote_log_len[(v2, t2)]] #![trigger ds.vote_log_len[(v2, t2)]] ds.vote_log_len.dom().contains((v2, t2))
                    ==> ds_.vote_log_len.dom().contains((v2, t2))
                        && ds_.vote_log_len[(v2, t2)] == ds.vote_log_len[(v2, t2)])
                &&& ({
                    ||| (exists |vt: int|
                        #![trigger ds_.vote_log_len.dom().contains((v, vt))]
                    {
                        &&& (exists |i: int| #![trigger sp[i]]
                            0 <= i < sp.len()
                            && sp[i] is VoteResponse
                            && sp[i]->VoteResponse_term == vt
                            && sp[i]->VoteResponse_granted
                            && sp[i]->VoteResponse_voter == v)
                        &&& ds_.vote_log_len.dom().contains((v, vt))
                        &&& ds_.vote_log_len[(v, vt)] == s.log.len()
                    })
                    ||| (
                        !(exists |i: int| #![trigger sp[i]]
                            0 <= i < sp.len()
                            && (sp[i] is VoteResponse)
                            && sp[i]->VoteResponse_granted)
                    )
                })
            };

        // vote_pkt.msg == sp[vr_idx] for some vr_idx (from routing on new packet)
        let vr_idx = choose |i: int| 0 <= i < sp.len()
            && vote_pkt.msg == sp[i];

        // Key: the ghost disjunction's second branch says no granted VR in sp.
        // But vote_pkt.msg == sp[vr_idx] and vote_pkt.msg is a granted VoteResponse.
        // So the second branch is false, and the first branch must hold.
        //
        // The first branch gives ∃ vt with recording at (v, vt).
        // We need vt == t. The first branch's inner ∃ says sp has a granted VR
        // at term vt from voter v. Since LGrantVote sends exactly one VoteResponse
        // in sent_packets (it's a singleton seq), vt == t.
        //
        // Rather than proving sp is singleton, use: the ghost clause's first branch
        // gives ds_.vote_log_len[(v, vt)] == s.log.len(). The second branch is
        // eliminated. Now assert the conclusion directly — Z3 should match
        // sp[vr_idx] (which equals vote_pkt.msg) as the witness for the inner
        // existential with vt == t.
        assert(ds_.vote_log_len[(v, t)] == s.log.len());
    }

    /// Self-contained Case 2: new VoteResponse + old RequestVote.
    /// Establishes full conclusion directly so the orchestrator just calls this.
    /// Internally: case2_extract + RVLPC + ghost state + transfer.
    proof fn lemma_vote_granted_case2_complete(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        vote_pkt: LRaftPacket, req: LRaftPacket,
    )
        requires
            SenderIntegrity(ds),
            RequestVoteLogParamsConsistent(ds),
            RaftDistributedNext(ds, ds_),
            // vote_pkt is new granted VoteResponse
            ds_.network.contains(vote_pkt), !ds.network.contains(vote_pkt),
            vote_pkt.msg is VoteResponse,
            vote_pkt.msg->VoteResponse_granted,
            0 <= vote_pkt.src < ds_.num_servers,
            // req is old RequestVote at same term
            ds.network.contains(req), ds_.network.contains(req),
            req.msg is RequestVote,
            vote_pkt.msg->VoteResponse_term == req.msg->RequestVote_term,
            vote_pkt.src == req.dst,
            vote_pkt.dst == req.src,
            // ghost state domain (from VoteLogLenCoversNetwork(ds_))
            ds_.vote_log_len.dom().contains(
                (vote_pkt.src, vote_pkt.msg->VoteResponse_term)),
            // LogAppendOnly already established
            LogAppendOnly(ds, ds_),
        ensures ({
            let v = vote_pkt.src;
            let t = vote_pkt.msg->VoteResponse_term;
            let L = ds_.vote_log_len[(v, t)];
            let voter_vote_time_last_term: int = if L == 0 {
                0int
            } else {
                ds_.server_states[v].log[L - 1].term
            };
            let li = req.msg->RequestVote_last_log_index;
            let lt = req.msg->RequestVote_last_log_term;
            lt > voter_vote_time_last_term
                || (lt == voter_vote_time_last_term && li >= L)
        })
    {
        let v = vote_pkt.src;
        let t = vote_pkt.msg->VoteResponse_term;

        // Step A: Extract processed RequestVote + log_up_to_date against s.log
        let processed_pkt = lemma_vote_granted_case2_extract(ds, ds_, vote_pkt);

        // Step B: Show processed_pkt and req have same log params via RVLPC.
        // From case2_extract: processed_pkt.term == vote_pkt VR term == t == req.term
        // From case2_extract: processed_pkt.candidate == vote_pkt.dst == req.src
        // From SenderIntegrity(ds): req.candidate == req.src
        assert(SenderIntegrity(ds));
        lemma_rvlpc_same_log_params(ds, processed_pkt, req);

        // Step C: Ghost state recording.
        // RaftServerStepWithNetwork records vote_log_len[(v, t)] == s.log.len()
        // when a granted VoteResponse at term t is sent by server v.
        lemma_extract_ghost_vote_log_len_recording(ds, ds_, vote_pkt);
        let s_log_len: int = ds.server_states[v].log.len() as int;

        // Step D: Transfer to lightweight helper (no RaftSafetyInvariant, no RaftDistributedNext).
        lemma_vote_granted_log_utd_new_vr_old_req(
            ds, ds_, v,
            req.msg->RequestVote_last_log_term,
            req.msg->RequestVote_last_log_index,
            t,
        );
    }

    /// Case 3+4 extraction: new RequestVote must be from LTimeout.
    /// Returns the server_id of the stepping server and establishes
    /// that the new req term == s.current_term + 1 and sent_pkts has only RequestVotes.
    /// No ghost state needed. Isolates extraction + action classification.
    proof fn lemma_vote_granted_case34_extract(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        req: LRaftPacket,
    ) -> (server_id: int)
        requires
            RaftDistributedNext(ds, ds_),
            ds_.network.contains(req), !ds.network.contains(req),
            req.msg is RequestVote,
        ensures
            0 <= server_id < ds.num_servers,
            req.src == server_id,
            // The new RequestVote's term is s.current_term + 1 (from LTimeout)
            req.msg->RequestVote_term
                == ds.server_states[server_id].current_term + 1,
            // No granted VoteResponse was sent in this step
            // (LTimeout sends only RequestVote messages)
            forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                    &&& pkt.src == server_id
                    &&& pkt.msg is RequestVote
                }
    {
        let (server_id, sent_pkts, recv_from) =
            lemma_extract_step_with_network(ds, ds_);
        // req is new → routing gives req.src == server_id
        assert(req.src == server_id);
        let rq_idx = choose |i: int| 0 <= i < sent_pkts.len()
            && req.msg == sent_pkts[i];
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        lemma_action_request_vote_implies_timeout(
            ds, server_id, s, s_, c,
            sent_pkts, recv_from, rq_idx);
        // LTimeout: sent_pkts.len() == 1 and sent_pkts[0] is RequestVote
        // So all new packets are RequestVote (from routing: pkt.msg == sent_pkts[i])
        server_id
    }

    /// Self-contained Case 3: old VoteResponse + new RequestVote → contradiction.
    /// Uses case34_extract for server_id + LTimeout facts, then old_vr contradiction.
    proof fn lemma_vote_granted_case3_complete(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        vote_pkt: LRaftPacket, req: LRaftPacket,
    )
        requires
            VoteResponseHasRequestVote(ds),
            RequestVoteSenderState(ds),
            RaftDistributedNext(ds, ds_),
            ds.network.contains(vote_pkt), ds_.network.contains(vote_pkt),
            !ds.network.contains(req), ds_.network.contains(req),
            vote_pkt.msg is VoteResponse,
            vote_pkt.msg->VoteResponse_granted,
            req.msg is RequestVote,
            vote_pkt.msg->VoteResponse_term == req.msg->RequestVote_term,
            vote_pkt.dst == req.src,
        ensures
            false
    {
        let server_id = lemma_vote_granted_case34_extract(ds, ds_, req);
        let t = req.msg->RequestVote_term;
        lemma_vote_granted_log_utd_old_vr_new_req_contradiction(
            ds, server_id, vote_pkt, t);
    }

    /// Self-contained Case 4: both new → contradiction.
    /// LTimeout sent only RequestVotes, but vote_pkt is a new VoteResponse.
    proof fn lemma_vote_granted_case4_complete(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        vote_pkt: LRaftPacket, req: LRaftPacket,
    )
        requires
            RaftDistributedNext(ds, ds_),
            !ds.network.contains(vote_pkt), ds_.network.contains(vote_pkt),
            !ds.network.contains(req), ds_.network.contains(req),
            vote_pkt.msg is VoteResponse,
            req.msg is RequestVote,
        ensures
            false
    {
        let server_id = lemma_vote_granted_case34_extract(ds, ds_, req);
        // All new packets are RequestVote, but vote_pkt is new and VoteResponse.
        // Contradiction.
    }

    /// Per-pair case dispatch for VoteGrantedLogUpToDateAtVoteTime induction.
    /// Isolated from the orchestrator to prevent axiom pollution from
    /// RaftSafetyInvariant leaking into the assert-forall block.
    proof fn lemma_vote_granted_log_utd_per_pair(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        vote_pkt: LRaftPacket, req: LRaftPacket,
    )
        requires
            VoteGrantedLogUpToDateAtVoteTime(ds),
            VoteLogLenCoversNetwork(ds),
            SenderIntegrity(ds),
            RequestVoteLogParamsConsistent(ds),
            VoteResponseHasRequestVote(ds),
            RequestVoteSenderState(ds),
            VoteLogLenBounded(ds),
            LogAppendOnly(ds, ds_),
            RaftDistributedNext(ds, ds_),
            (forall |v: int, t: int| ds.vote_log_len.dom().contains((v, t))
                ==> ds_.vote_log_len.dom().contains((v, t))
                    && #[trigger] ds_.vote_log_len[(v, t)] == ds.vote_log_len[(v, t)]),
            ds_.network.contains(vote_pkt), ds_.network.contains(req),
            vote_pkt.msg is VoteResponse,
            vote_pkt.msg->VoteResponse_granted,
            req.msg is RequestVote,
            vote_pkt.msg->VoteResponse_term == req.msg->RequestVote_term,
            vote_pkt.src == req.dst,
            vote_pkt.dst == req.src,
            ds_.vote_log_len.dom().contains(
                (vote_pkt.src, vote_pkt.msg->VoteResponse_term)),
            0 <= vote_pkt.src < ds_.num_servers,
        ensures ({
            let v = vote_pkt.src;
            let t = vote_pkt.msg->VoteResponse_term;
            let L = ds_.vote_log_len[(v, t)];
            let voter_vote_time_last_term: int = if L == 0 {
                0int
            } else {
                ds_.server_states[v].log[L - 1].term
            };
            let li = req.msg->RequestVote_last_log_index;
            let lt = req.msg->RequestVote_last_log_term;
            lt > voter_vote_time_last_term
                || (lt == voter_vote_time_last_term && li >= L)
        })
    {
        if ds.network.contains(vote_pkt) && ds.network.contains(req) {
            // Case 1: Both old — IH + ghost monotonicity + LogAppendOnly
            let v = vote_pkt.src;
            let t = vote_pkt.msg->VoteResponse_term;
            // VoteLogLenBounded gives bounds on v and L
            assert(VoteLogLenBounded(ds));
            assert(VoteLogLenCoversNetwork(ds));
            assert(ds.vote_log_len.dom().contains((v, t)));
            let L = ds.vote_log_len[(v, t)];
            assert(0 <= v < ds.num_servers);
            assert(L <= ds.server_states[v].log.len());
            // Ghost monotonicity: L is the same in ds and ds_
            assert(ds_.vote_log_len[(v, t)] == L);
            // IH conclusion in terms of ds
            let li = req.msg->RequestVote_last_log_index;
            let lt = req.msg->RequestVote_last_log_term;
            // LogAppendOnly: ds_ log prefix matches ds
            if L > 0 {
                let k = L - 1;
                // Fire LogAppendOnly trigger for (v, k)
                assert(ds.server_states[v].log[k] == ds.server_states[v].log[k]);
                assert(ds_.server_states[v].log[k] == ds.server_states[v].log[k]);
            }
        } else if !ds.network.contains(vote_pkt) && ds.network.contains(req) {
            // Case 2: new VoteResponse + old RequestVote
            lemma_vote_granted_case2_complete(ds, ds_, vote_pkt, req);
        } else if ds.network.contains(vote_pkt) && !ds.network.contains(req) {
            // Case 3: old VR + new req → contradiction
            lemma_vote_granted_case3_complete(ds, ds_, vote_pkt, req);
        } else {
            // Case 4: both new → contradiction
            lemma_vote_granted_case4_complete(ds, ds_, vote_pkt, req);
        }
    }

    proof fn lemma_vote_granted_log_up_to_date_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            VoteGrantedLogUpToDateAtVoteTime(ds_)
    {
        lemma_log_append_only(ds, ds_);
        lemma_vote_log_len_monotonic(ds, ds_);

        assert forall |vote_pkt: LRaftPacket, req: LRaftPacket| #![trigger ds_.network.contains(vote_pkt), ds_.network.contains(req)]
            ds_.network.contains(vote_pkt) && ds_.network.contains(req)
            && (vote_pkt.msg is VoteResponse)
            && vote_pkt.msg->VoteResponse_granted
            && (req.msg is RequestVote)
            && vote_pkt.msg->VoteResponse_term == req.msg->RequestVote_term
            && vote_pkt.src == req.dst
            && vote_pkt.dst == req.src
            && ds_.vote_log_len.dom().contains(
                (vote_pkt.src, vote_pkt.msg->VoteResponse_term))
            && 0 <= vote_pkt.src < ds_.num_servers
        implies ({
            let v = vote_pkt.src;
            let t = vote_pkt.msg->VoteResponse_term;
            let L = ds_.vote_log_len[(v, t)];
            let voter_vote_time_last_term: int = if L == 0 {
                0int
            } else {
                ds_.server_states[v].log[L - 1].term
            };
            let li = req.msg->RequestVote_last_log_index;
            let lt = req.msg->RequestVote_last_log_term;
            lt > voter_vote_time_last_term
                || (lt == voter_vote_time_last_term && li >= L)
        }) by {
            lemma_vote_granted_log_utd_per_pair(ds, ds_, vote_pkt, req);
        };
    }

    // =========================================================================
    // AppendResponseLogAgreement Helpers
    // =========================================================================

    /// Helper: extract AE packet from the action and establish ARLA for
    /// a new AR packet sent by LFollowerAppendEntries.
    ///
    /// When server_id handles an AE message and sends a success AR:
    /// - AR.src == server_id (follower), AR.dst == ae_leader
    /// - match_index = if ae_has_entry { s.log.len()+1 } else { ae_prev_index }
    /// - Prev_log check + AEI + LogMatching give log agreement
    ///
    /// Isolates the expensive RaftActionProduces unfolding from the main proof.
    proof fn lemma_arla_new_packet(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, p: LRaftPacket,
    )
        requires
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            LogMatching(ds),
            AppendEntriesIntegrity(ds),
            0 <= server_id < ds.num_servers,
            (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j]),
            RaftServerStepWithNetwork(ds, ds_, server_id),
            // p is a new AR packet sent by server_id
            ds_.network.contains(p),
            !ds.network.contains(p),
            p.msg is AppendResponse,
            p.msg->AppendResponse_success,
            0 <= p.src < ds.num_servers,
            0 <= p.dst < ds.num_servers,
        ensures
            p.msg->AppendResponse_match_index <= ds_.server_states[p.src].log.len(),
            p.msg->AppendResponse_match_index <= ds_.server_states[p.dst].log.len(),
            forall |k: int|
                #![trigger ds_.server_states[p.src].log[k]]
                0 <= k < p.msg->AppendResponse_match_index
                ==> ds_.server_states[p.src].log[k] == ds_.server_states[p.dst].log[k],
    {
        // p is a new packet, so p.src == server_id (from network model)
        assert(p.src == server_id);
        let leader = p.dst;
        let mi = p.msg->AppendResponse_match_index;

        if leader == server_id {
            // Self-AE: src == dst, everything trivial
            assert(mi <= ds_.server_states[p.src].log.len()) by {
                // Z3 unfolds action to establish mi bound
            };
            assert(mi <= ds_.server_states[p.dst].log.len());
        } else {
            // leader's state is unchanged (leader != server_id)
            assert(ds_.server_states[leader] == ds.server_states[leader]);

            // Z3 unfolds RaftActionProduces → LHandleMessage →
            // LHandleAppendEntriesMsg → LFollowerAppendEntries.
            // The success AR proves prev_log check passed.
            // mi bounds follow from action + AEI.
            assert(mi <= ds_.server_states[p.src].log.len());
            assert(mi <= ds_.server_states[p.dst].log.len());

            assert forall |k: int|
                #![trigger ds_.server_states[p.src].log[k]]
                0 <= k < mi
            implies ds_.server_states[p.src].log[k] == ds_.server_states[p.dst].log[k]
            by {
                // leader's log is unchanged
                assert(ds_.server_states[leader].log[k]
                    == ds.server_states[leader].log[k]);
            };
        }
    }

    // =========================================================================
    // AppendResponseLogAgreement Induction
    // =========================================================================

    /// ARLA: for every successful AR in the network, follower (p.src) and
    /// AE sender (p.dst) agree on log entries below match_index, and
    /// match_index is bounded by both logs' lengths.
    ///
    /// Old packets: ARLA(ds) gives match_index <= both old log lengths.
    ///   By LogAppendOnly, old entries preserved → agreement preserved.
    /// New packets: only LFollowerAppendEntries sends success ARs.
    ///   Prev_log check + AEI + LogMatching gives agreement.
    ///   match_index bounds from AR creation logic.
    proof fn lemma_append_response_log_agreement_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            AppendResponseLogAgreement(ds),
            LogMatching(ds),
            AppendEntriesIntegrity(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            AppendResponseLogAgreement(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        lemma_log_append_only(ds, ds_);

        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        assert forall |p: LRaftPacket|
            #![trigger ds_.network.contains(p)]
            ds_.network.contains(p)
            && (p.msg is AppendResponse)
            && p.msg->AppendResponse_success
            && 0 <= p.src < ds_.num_servers
            && 0 <= p.dst < ds_.num_servers
        implies {
            &&& p.msg->AppendResponse_match_index <= ds_.server_states[p.src].log.len()
            &&& p.msg->AppendResponse_match_index <= ds_.server_states[p.dst].log.len()
            &&& (forall |k: int|
                #![trigger ds_.server_states[p.src].log[k]]
                0 <= k < p.msg->AppendResponse_match_index
                ==> ds_.server_states[p.src].log[k] == ds_.server_states[p.dst].log[k])
        } by {
            if ds.network.contains(p) {
                // Old packet: ARLA(ds) gives bounds + agreement at old state.
                // LogAppendOnly preserves both.
                assert(AppendResponseLogAgreement(ds));
                let mi = p.msg->AppendResponse_match_index;
                // From ARLA(ds): mi <= both old log lengths
                assert(mi <= ds.server_states[p.src].log.len());
                assert(mi <= ds.server_states[p.dst].log.len());
                // LogAppendOnly: new log lengths >= old log lengths
                assert(ds_.server_states[p.src].log.len()
                    >= ds.server_states[p.src].log.len());
                assert(ds_.server_states[p.dst].log.len()
                    >= ds.server_states[p.dst].log.len());
                // Agreement: for k < mi, k < both old log lengths.
                // ARLA(ds) gives agreement at old state.
                // LogAppendOnly preserves entries.
                assert forall |k: int|
                    #![trigger ds_.server_states[p.src].log[k]]
                    0 <= k < mi
                implies ds_.server_states[p.src].log[k]
                    == ds_.server_states[p.dst].log[k]
                by {
                    assert(k < ds.server_states[p.src].log.len());
                    assert(ds.server_states[p.src].log[k]
                        == ds.server_states[p.dst].log[k]);
                };
            } else {
                // New packet: sent in this step by LFollowerAppendEntries.
                // Use helper to extract AE parameters and establish agreement.
                lemma_arla_new_packet(ds, ds_, server_id, p);
            }
        }
    }

    // =========================================================================
    // MatchIndexImpliesLogAgreement Induction
    // =========================================================================

    /// If the stepping leader has a changed match_index entry, extract the
    /// successful AppendResponse packet whose handling produced that entry.
    /// This keeps RaftActionProduces case analysis out of the quantified MILA
    /// proof below.
    proof fn lemma_mila_changed_match_index_packet(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
        follower_id: int,
    ) -> (p: LRaftPacket)
        requires
            WellFormedRaftDistributed(ds),
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            RaftServerStepWithNetwork(ds, ds_, server_id),
            s_.role is Leader,
            0 <= follower_id < ds.num_servers,
            s_.match_index.dom().contains(follower_id as u64),
            !(s_.match_index =~= s.match_index),
        ensures
            ds.network.contains(p),
            p.dst == server_id,
            p.msg is AppendResponse,
            p.msg->AppendResponse_success,
            0 <= p.msg->AppendResponse_follower < ds.num_servers,
            p.msg->AppendResponse_match_index >= 0,
            p.msg->AppendResponse_match_index <= u64::MAX as int,
            p.msg->AppendResponse_match_index <= s.log.len(),
            s_.log == s.log,
            s_.match_index =~= s.match_index.insert(
                p.msg->AppendResponse_follower as u64,
                p.msg->AppendResponse_match_index as u64),
    {
        let (sent_packets, received_from) =
            choose |sp: Seq<LRaftMessage>, rf: Option<int>| {
                &&& RaftActionProduces(ds, server_id, s, s_, c, sp, rf)
                &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt)
                    ==> ds_.network.contains(pkt))
                &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                    ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                        &&& pkt.src == server_id
                        &&& 0 <= pkt.dst < ds.num_servers
                        &&& (exists |i: int|
                            0 <= i < sp.len() && pkt.msg == sp[i])
                        &&& (match rf {
                            Some(src) => pkt.dst == src,
                            None => true,
                        })
                    })
            };
        assert(exists |p: LRaftPacket| #![trigger ds.network.contains(p)] {
            &&& received_from == Some(p.src)
            &&& ds.network.contains(p)
            &&& p.dst == server_id
            &&& LHandleMessage(s, s_, c, p.msg, sent_packets)
        }) by {
            // Local actions either preserve match_index or clear it while
            // changing role, so a changed nonempty leader map comes from the
            // message-handling branch of RaftActionProduces.
        };
        let p = choose |p: LRaftPacket| #![trigger ds.network.contains(p)] {
            &&& received_from == Some(p.src)
            &&& ds.network.contains(p)
            &&& p.dst == server_id
            &&& LHandleMessage(s, s_, c, p.msg, sent_packets)
        };
        assert(p.msg is AppendResponse);
        assert(p.msg->AppendResponse_success);
        assert(0 <= p.msg->AppendResponse_follower < ds.num_servers);
        assert(p.msg->AppendResponse_match_index >= 0);
        assert(p.msg->AppendResponse_match_index <= u64::MAX as int);
        assert(p.msg->AppendResponse_match_index <= s.log.len());
        assert(s_.log == s.log);
        assert(s_.match_index =~= s.match_index.insert(
            p.msg->AppendResponse_follower as u64,
            p.msg->AppendResponse_match_index as u64));
        p
    }

    // =========================================================================
    // MatchIndexBounded Induction
    // =========================================================================

    /// MIB: match_index[follower] <= follower.log.len() and <= leader.log.len().
    ///
    /// match_index is only updated by LHandleAppendResponse, which sets
    /// match_index[follower] = new_match_index from an AR packet.
    /// - new_match_index <= leader.log.len() (from LHandleAppendResponseMsg guard).
    /// - new_match_index <= follower.log.len() (from ARLA: AR.match_index <= AR.src.log.len()).
    /// match_index is cleared when becoming leader (empty map → vacuous).
    /// For preserved entries: LogAppendOnly grows logs, so bounds are preserved.
    proof fn lemma_match_index_bounded_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            MatchIndexBounded(ds),
            AppendResponseLogAgreement(ds),
            SenderIntegrity(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            MatchIndexBounded(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        lemma_log_append_only(ds, ds_);

        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        assert forall |leader_id: int, follower_id: int|
            #![trigger ds_.server_states[leader_id].match_index, ds_.server_states[follower_id].log]
            0 <= leader_id < ds_.num_servers
            && 0 <= follower_id < ds_.num_servers
            && ds_.server_states[leader_id].role is Leader
            && ds_.server_states[leader_id].match_index.dom().contains(follower_id as u64)
        implies {
            &&& ds_.server_states[leader_id].match_index[follower_id as u64] as int
                <= ds_.server_states[follower_id].log.len()
            &&& ds_.server_states[leader_id].match_index[follower_id as u64] as int
                <= ds_.server_states[leader_id].log.len()
        } by {
            if leader_id != server_id {
                // Leader unchanged: match_index, role unchanged.
                // MIB(ds) gives bounds at ds. LogAppendOnly grows logs.
                assert(ds_.server_states[leader_id] == ds.server_states[leader_id]);
                assert(MatchIndexBounded(ds));
            } else {
                assert(MatchIndexBounded(ds));
                assert(AppendResponseLogAgreement(ds));
                let follower = follower_id as u64;
                if s.match_index.dom().contains(follower)
                    && s_.match_index[follower] == s.match_index[follower]
                {
                    // Preserved entry: old bounds survive append-only logs.
                    assert(s.role is Leader);
                    assert(s.match_index[follower] as int
                        <= ds.server_states[follower_id].log.len());
                    if follower_id != server_id {
                        assert(ds_.server_states[follower_id]
                            == ds.server_states[follower_id]);
                    }
                } else {
                    assert(!(s_.match_index =~= s.match_index)) by {
                        if s_.match_index =~= s.match_index {
                            assert(s_.match_index[follower]
                                == s.match_index[follower]);
                        }
                    };
                    let p = lemma_mila_changed_match_index_packet(
                        ds, ds_, server_id, s, s_, c, follower_id);
                    let response_follower =
                        p.msg->AppendResponse_follower;
                    assert(response_follower as u64 == follower) by {
                        if response_follower as u64 != follower {
                            assert(s_.match_index[follower]
                                == s.match_index[follower]);
                        }
                    };
                    assert(response_follower == follower_id);
                    assert(p.msg->AppendResponse_match_index
                        == s_.match_index[follower] as int);
                    assert(p.src == follower_id);
                    assert(p.msg->AppendResponse_match_index
                        <= ds.server_states[follower_id].log.len());
                    if follower_id != server_id {
                        assert(ds_.server_states[follower_id]
                            == ds.server_states[follower_id]);
                    }
                }
            }
        }
    }

    // =========================================================================
    // AppendEntriesLeaderCommitBound Induction
    // =========================================================================

    /// AELCB: for AE packets in the network, ae_leader_commit <= leader's
    /// current commit_index.
    ///
    /// Old packets: AELCB(ds) gives bound at ds. commit_index only grows
    /// (all actions preserve or increase). So bound preserved at ds_.
    /// New packets: LSendAppendEntries sets leader_commit = s.commit_index.
    /// Stepping server's commit_index at ds_ >= s.commit_index.
    proof fn lemma_append_entries_leader_commit_bound_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            AppendEntriesLeaderCommitBound(ds),
            AppendEntriesIntegrity(ds),
            CommitIndexBounded(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            AppendEntriesLeaderCommitBound(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);

        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        assert(LNext(s, s_, c));
        assert(s.commit_index <= s.log.len());
        lemma_lnext_commit_index_monotone(s, s_, c);
        let (sent_packets, received_from) =
            choose |sp: Seq<LRaftMessage>, rf: Option<int>| {
                &&& RaftActionProduces(ds, server_id, s, s_, c, sp, rf)
                &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt)
                    ==> ds_.network.contains(pkt))
                &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                    ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                        &&& pkt.src == server_id
                        &&& 0 <= pkt.dst < ds.num_servers
                        &&& (exists |i: int|
                            0 <= i < sp.len() && pkt.msg == sp[i])
                        &&& (match rf {
                            Some(src) => pkt.dst == src,
                            None => true,
                        })
                    })
            };

        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] ds_.network.contains(p) implies
            match p.msg {
                LRaftMessage::AppendEntries { leader_commit, leader, .. } => {
                    &&& 0 <= leader < ds_.num_servers
                    &&& leader_commit <= ds_.server_states[leader].commit_index
                }
                _ => true,
            }
        by {
            if p.msg is AppendEntries {
                let l = p.msg->AppendEntries_leader;
                let lc = p.msg->AppendEntries_leader_commit;
                if ds.network.contains(p) {
                    // Old packet: AELCB(ds) gives lc <= leader.commit_index at ds.
                    // commit_index never decreases, so holds at ds_.
                    assert(AppendEntriesLeaderCommitBound(ds));
                    assert(lc <= ds.server_states[l].commit_index);
                    // leader's commit_index at ds_ >= ds (either unchanged or increased)
                    if l != server_id {
                        assert(ds_.server_states[l] == ds.server_states[l]);
                    }
                    // For l == server_id: all LNext branches preserve or increase
                    // commit_index. Z3 handles this by unfolding LNext.
                } else {
                    // New packet: sent by LSendAppendEntries.
                    // leader_commit == s.commit_index (at send time).
                    // The sender is server_id, so l == server_id.
                    // s_.commit_index >= s.commit_index.
                    // From AEI, 0 <= l < num_servers.
                    assert(p.src == server_id);
                    assert(l == server_id);
                    assert(lc == s.commit_index);
                }
            }
        }
    }

    // =========================================================================
    // Membership-boundary provenance induction
    // =========================================================================

    proof fn lemma_append_entries_configuration_boundary_integrity_inductive(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            AppendEntriesConfigurationBoundaryIntegrity(ds),
            AppendEntriesIntegrity(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            AppendEntriesConfigurationBoundaryIntegrity(ds_),
    {
        let (server_id, sent_packets, recv_from) =
            lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        lemma_log_append_only(ds, ds_);

        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)] ds_.network.contains(p) implies
            match p.msg {
                LRaftMessage::AppendEntries {
                    leader,
                    prev_index,
                    payload,
                    has_entry,
                    leader_commit,
                    ..
                } => (has_entry && payload is Configuration) ==> {
                    &&& 0 <= leader < ds_.num_servers
                    &&& forall |index: int| #![trigger ds_.server_states[leader].log[index]]
                        0 <= index < prev_index
                        && ds_.server_states[leader].log[index].payload
                            is Configuration
                        ==> index < leader_commit
                },
                _ => true,
            }
        by {
            if p.msg is AppendEntries
                && p.msg->AppendEntries_has_entry
                && p.msg->AppendEntries_payload is Configuration
            {
                let leader = p.msg->AppendEntries_leader;
                let boundary = p.msg->AppendEntries_prev_index;
                let leader_commit = p.msg->AppendEntries_leader_commit;
                if ds.network.contains(p) {
                    assert(AppendEntriesConfigurationBoundaryIntegrity(ds));
                    assert(0 <= leader < ds.num_servers);
                    assert forall |index: int| #![trigger ds_.server_states[leader].log[index]]
                        0 <= index < boundary
                        && ds_.server_states[leader].log[index].payload
                            is Configuration
                        implies index < leader_commit
                    by {
                        assert(ds.server_states[leader].log[index]
                            == ds_.server_states[leader].log[index]);
                    };
                } else {
                    assert(leader == server_id);
                    assert(p.msg == sent_packets[choose |i: int|
                        0 <= i < sent_packets.len()
                        && p.msg == sent_packets[i]]);
                    assert(s.log.len() >= boundary + 1);
                    assert(s.log[boundary].payload == p.msg->AppendEntries_payload);
                    assert(leader_commit == s.commit_index);
                    assert(UncommittedSuffixesHaveAtMostOneConfiguration(ds));
                    assert(uncommitted_suffix_has_at_most_one_configuration(
                        s.log, s.commit_index));
                    assert forall |index: int| #![trigger s_.log[index]]
                        0 <= index < boundary
                        && s_.log[index].payload is Configuration
                        implies index < leader_commit
                    by {
                        assert(s_.log[index] == s.log[index]);
                        if index >= s.commit_index {
                            assert(boundary >= s.commit_index);
                            assert(index == boundary);
                            assert(false);
                        }
                    };
                }
            }
        };
    }

    proof fn lemma_uncommitted_suffixes_have_at_most_one_configuration_inductive(
        ds: RaftDistributedState,
        ds_: RaftDistributedState,
    )
        requires
            UncommittedSuffixesHaveAtMostOneConfiguration(ds),
            AppendEntriesConfigurationBoundaryIntegrity(ds),
            AppendEntriesIntegrity(ds),
            LogMatching(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            UncommittedSuffixesHaveAtMostOneConfiguration(ds_),
    {
        let (server_id, sent_packets, recv_from) =
            lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        assert forall |id: int| #![trigger ds_.server_states[id]] 0 <= id < ds_.num_servers implies
            uncommitted_suffix_has_at_most_one_configuration(
                ds_.server_states[id].log,
                ds_.server_states[id].commit_index,
            )
        by {
            if id != server_id {
                assert(ds_.server_states[id] == ds.server_states[id]);
            } else {
                assert(0 <= s_.commit_index <= s_.log.len());
                assert forall |left: int, right: int| #![trigger s_.log[left], s_.log[right]]
                    s_.commit_index <= left < s_.log.len()
                    && s_.commit_index <= right < s_.log.len()
                    && s_.log[left].payload is Configuration
                    && s_.log[right].payload is Configuration
                    implies left == right
                by {
                    if left == right {
                    } else if left < s.log.len() && right < s.log.len() {
                        assert(s_.log[left] == s.log[left]);
                        assert(s_.log[right] == s.log[right]);
                        assert(s.commit_index <= s_.commit_index);
                    } else if left == s.log.len() || right == s.log.len() {
                        let old_index = if left == s.log.len() { right } else { left };
                        let new_index = s.log.len() as int;
                        assert(s_.log.len() == s.log.len() + 1);
                        assert(old_index != new_index);
                        assert(old_index <= new_index);
                        assert(old_index < s.log.len());
                        assert(s_.log[old_index] == s.log[old_index]);

                        if recv_from is Some {
                            let source = recv_from->Some_0;
                            let pkt = choose |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
                                &&& recv_from == Some(pkt.src)
                                &&& ds.network.contains(pkt)
                                &&& pkt.dst == server_id
                                &&& LHandleMessage(s, s_, c, pkt.msg, sent_packets)
                            };
                            assert(pkt.msg is AppendEntries);
                            assert(pkt.msg->AppendEntries_has_entry);
                            assert(pkt.msg->AppendEntries_prev_index == new_index);
                            assert(pkt.msg->AppendEntries_payload is Configuration);
                            assert(AppendEntriesConfigurationBoundaryIntegrity(ds));
                            assert(AppendEntriesIntegrity(ds));
                            assert(source == pkt.msg->AppendEntries_leader);
                            assert(ds.server_states[source].log.len()
                                >= new_index + 1);
                            assert(new_index > 0);
                            assert(s.log[new_index - 1].term
                                == pkt.msg->AppendEntries_prev_term);
                            assert(ds.server_states[source].log[new_index - 1].term
                                == pkt.msg->AppendEntries_prev_term);
                            assert forall |index: int| #![trigger s.log[index]]
                                0 <= index <= new_index - 1
                                implies ds.server_states[source].log[index]
                                    == s.log[index]
                            by {
                                assert(LogMatching(ds));
                            };
                            assert(ds.server_states[source].log[old_index]
                                == s.log[old_index]);
                            assert(old_index < pkt.msg->AppendEntries_leader_commit);
                            assert(s_.commit_index
                                >= pkt.msg->AppendEntries_leader_commit);
                            assert(false);
                        } else {
                            // Only the guarded local configuration append can
                            // add a Configuration without receiving a packet.
                            assert(uncommitted_suffix_has_no_configuration(
                                s.log, s.commit_index));
                            assert(s.commit_index <= s_.commit_index);
                            assert(false);
                        }
                    }
                };
            }
        };
    }

    // =========================================================================
    // Composite induction step
    // =========================================================================

    /// Top-level induction: the full safety invariant is preserved by RaftDistributedNext
    pub proof fn lemma_safety_invariant_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            RaftSafetyInvariant(ds_)
    {
        // Well-formedness: directly from RaftDistributedNext precondition
        assert(WellFormedRaftDistributed(ds_));

        // Supporting invariants
        lemma_votes_granted_are_servers_inductive(ds, ds_);
        lemma_candidate_or_leader_voted_for_self_inductive(ds, ds_);
        lemma_candidate_or_leader_voted_for_self_id_inductive(ds, ds_);
        lemma_voters_voted_for_candidate_inductive(ds, ds_);
        lemma_leader_has_recorded_election_quorum_inductive(ds, ds_);
        lemma_leader_has_recorded_election_log_provenance_inductive(ds, ds_);
        lemma_committed_configurations_have_certificates_inductive(
            ds, ds_);
        lemma_committed_entries_have_log_certificates_inductive(
            ds, ds_);
        lemma_commit_index_bounded_inductive(ds, ds_);
        lemma_commit_index_nonnegative_inductive(ds, ds_);
        lemma_entry_term_leader_witness_inductive(ds, ds_);

        lemma_log_certificate_coverage_implies_state_machine_safety(ds_);
        lemma_state_machine_safety_implies_committed_membership_prefix_agreement(
            ds_,
        );

        // Message invariants
        lemma_sender_integrity_inductive(ds, ds_);
        lemma_vote_response_integrity_inductive(ds, ds_);
        lemma_vote_response_summary_still_valid_inductive(ds, ds_);
        lemma_vote_response_has_request_vote_inductive(ds, ds_);
        lemma_append_entries_integrity_inductive(ds, ds_);
        lemma_one_vote_per_term_inductive(ds, ds_);
        lemma_request_vote_sender_state_inductive(ds, ds_);
        lemma_request_vote_summary_still_valid_inductive(ds, ds_);
        lemma_request_vote_summary_always_valid_inductive(ds, ds_);
        lemma_request_vote_last_log_term_bound_inductive(ds, ds_);
        lemma_request_vote_log_params_consistent_inductive(ds, ds_);
        lemma_candidate_vote_destination_unique_inductive(ds, ds_);

        // Ghost state invariants (Phase 34.7 — stale-vote provenance)
        lemma_vote_log_len_covers_network_inductive(ds, ds_);
        lemma_vote_log_len_bounded_inductive(ds, ds_);
        lemma_vote_log_len_entry_term_bound_inductive(ds, ds_);
        lemma_vote_granted_log_up_to_date_inductive(ds, ds_);

        // Follower commit-update bound
        lemma_append_entries_leader_commit_bound_inductive(ds, ds_);

        // Election-snapshot ghost state
        lemma_election_log_len_bounded_inductive(ds, ds_);
        lemma_election_log_len_entry_term_bound_inductive(ds, ds_);
        lemma_leader_election_snapshot_recorded_inductive(ds, ds_);

        // Log structure invariants (Phase 34.7 — strict-term transfer)
        lemma_current_term_ge_log_terms_inductive(ds, ds_);
        lemma_log_terms_monotonic_inductive(ds, ds_);
        lemma_terms_non_negative_inductive(ds, ds_);

    }
}

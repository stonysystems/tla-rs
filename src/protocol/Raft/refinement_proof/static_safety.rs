//! Raft safety for executions without membership changes.
//!
//! In these executions no server ever appends a Configuration entry, so every
//! membership phase is the initial one (a majority of all servers) and the
//! classic fixed-majority Raft argument applies. This module restates that
//! argument's invariants (election safety, log matching, leader completeness)
//! for the current protocol, including reboots.
use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::membership::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::invariants::*;
use crate::protocol::Raft::refinement_proof::message_invariants::*;
use crate::protocol::Raft::refinement_proof::reconfiguration::*;
use vstd::prelude::*;
use crate::common::collections::sets::*;
use vstd::set_lib::*;

verus! {

    // =========================================================================
    // Scope: executions without membership changes
    // =========================================================================

    /// No server's log holds a Configuration entry.
    pub open spec fn NoConfigurationEntries(ds: RaftDistributedState) -> bool {
        forall |i: int, k: int| #![trigger ds.server_states[i].log[k]]
            0 <= i < ds.num_servers && 0 <= k < ds.server_states[i].log.len()
            ==> !(ds.server_states[i].log[k].payload is Configuration)
    }

    /// No server appends a Configuration entry in this step.
    pub open spec fn NoNewConfigurationEntries(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    ) -> bool {
        forall |i: int, k: int| #![trigger ds_.server_states[i].log[k]]
            0 <= i < ds.num_servers
            && ds.server_states[i].log.len() <= k < ds_.server_states[i].log.len()
            ==> !(ds_.server_states[i].log[k].payload is Configuration)
    }

    /// A step of an execution without membership changes.
    pub open spec fn RaftDistributedStaticNext(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    ) -> bool {
        &&& RaftDistributedNext(ds, ds_)
        &&& NoNewConfigurationEntries(ds, ds_)
    }

    pub proof fn lemma_static_next_preserves_no_configuration_entries(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            NoConfigurationEntries(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            NoConfigurationEntries(ds_),
    {
        if RaftDistributedNormalNext(ds, ds_) {
            lemma_log_append_only(ds, ds_);
            assert forall |i: int, k: int|
                0 <= i < ds_.num_servers && 0 <= k < ds_.server_states[i].log.len()
                implies !(#[trigger] ds_.server_states[i].log[k].payload is Configuration) by {
                if k < ds.server_states[i].log.len() {
                    assert(ds_.server_states[i].log[k] == ds.server_states[i].log[k]);
                }
            }
        } else {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |i: int, k: int|
                0 <= i < ds_.num_servers && 0 <= k < ds_.server_states[i].log.len()
                implies !(#[trigger] ds_.server_states[i].log[k].payload is Configuration) by {
                assert(ds_.server_states[i].log == ds.server_states[i].log);
            }
        }
    }

    // =========================================================================
    // Without Configuration entries every phase is the initial one
    // =========================================================================

    pub proof fn lemma_configuration_free_log_has_initial_phase(
        log: Seq<LLogEntry>, len: int, initial_phase: MembershipPhase,
    )
        requires
            forall |k: int| #![trigger log[k]] 0 <= k < log.len()
                ==> !(log[k].payload is Configuration),
        ensures
            active_membership_phase_from_raft_log(log, len, initial_phase) == initial_phase,
        decreases len
    {
        if len <= 0 || len > log.len() {
        } else {
            assert(!(log[len - 1].payload is Configuration));
            lemma_configuration_free_log_has_initial_phase(log, len - 1, initial_phase);
        }
    }

    /// A quorum for the initial phase is a majority of all servers.
    pub proof fn lemma_initial_phase_quorum_is_majority(
        ds: RaftDistributedState, i: int, quorum: Set<int>,
    )
        requires
            WellFormedRaftDistributed(ds),
            0 <= i < ds.num_servers,
            is_quorum_for_phase(
                quorum,
                MembershipPhase::Stable { config: ds.server_constants[i].servers },
            ),
        ensures
            quorum.subset_of(Set::<int>::range(0, ds.num_servers)),
            quorum.len() >= ds.server_constants[i].quorum_size,
    {
        lemma_int_range(0, ds.num_servers);
    }

    /// Fixed-majority election quorums follow from the recorded election
    /// quorum when no Configuration entry exists.
    pub proof fn lemma_static_leader_has_quorum(ds: RaftDistributedState)
        requires
            WellFormedRaftDistributed(ds),
            LeaderHasRecordedElectionQuorum(ds),
            LeaderHasRecordedElectionLogProvenance(ds),
            NoConfigurationEntries(ds),
        ensures
            LeaderHasQuorum(ds),
    {
        assert forall |i: int| #![trigger ds.server_states[i]] #![trigger ds.server_constants[i]]
            0 <= i < ds.num_servers && ds.server_states[i].role is Leader
            implies ds.server_states[i].votes_granted.len() >= ds.server_constants[i].quorum_size by {
            let s = ds.server_states[i];
            let c = ds.server_constants[i];
            let initial = MembershipPhase::Stable { config: c.servers };
            assert(has_recorded_election_log_provenance(s, c));
            assert(has_recorded_election_quorum(s));
            let len = choose |len: int| #![trigger active_membership_phase_from_raft_log(s.log, len, initial)] {
                &&& 0 <= len <= s.log.len()
                &&& s.election_membership_phase == Some(
                    active_membership_phase_from_raft_log(s.log, len, initial))
            };
            assert forall |k: int| #![trigger s.log[k]] 0 <= k < s.log.len()
                implies !(s.log[k].payload is Configuration) by {
                assert(!(ds.server_states[i].log[k].payload is Configuration));
            }
            lemma_configuration_free_log_has_initial_phase(s.log, len, initial);
            lemma_initial_phase_quorum_is_majority(ds, i, s.votes_granted);
        }
    }

    // =========================================================================
    // Election safety
    // =========================================================================

    /// A Candidate that becomes Leader cannot meet another Leader of its
    /// term: both hold a majority of votes, and the vote sets are disjoint
    /// because every server votes at most once per term.
    proof fn lemma_static_candidate_to_leader_is_alone(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        stepping: int, other: int,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftSafetyInvariant(ds_),
            NoConfigurationEntries(ds),
            NoConfigurationEntries(ds_),
            RaftDistributedNormalNext(ds, ds_),
            0 <= stepping < ds.num_servers,
            0 <= other < ds.num_servers,
            stepping != other,
            LNext(ds.server_states[stepping], ds_.server_states[stepping],
                  ds.server_constants[stepping]),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != stepping ==>
                ds_.server_states[j] == ds.server_states[j],
            ds_.server_states[stepping].role is Leader,
            ds_.server_states[other].role is Leader,
            ds_.server_states[stepping].current_term == ds_.server_states[other].current_term,
            !(ds.server_states[stepping].role is Leader),
        ensures
            false,
    {
        broadcast use vstd::set_lib::group_set_properties;
        let term = ds_.server_states[stepping].current_term;
        let other_votes = ds.server_states[other].votes_granted;
        let stepping_votes = ds_.server_states[stepping].votes_granted;
        let n = ds.num_servers;
        let quorum_size = ds.server_constants[other].quorum_size;

        lemma_lnext_non_leader_to_leader_was_candidate(
            ds.server_states[stepping], ds_.server_states[stepping],
            ds.server_constants[stepping]);
        lemma_static_leader_has_quorum(ds);
        lemma_static_leader_has_quorum(ds_);
        assert(ds_.server_states[other] == ds.server_states[other]);

        let universe = Set::<int>::range(0, n);
        lemma_range_set_finite(n);
        assert(other_votes.subset_of(universe)) by {
            assert forall |v: int| other_votes.contains(v) implies universe.contains(v) by {
                assert(VotesGrantedAreServers(ds));
            }
        };
        assert(stepping_votes.subset_of(universe)) by {
            assert forall |v: int| stepping_votes.contains(v) implies universe.contains(v) by {
                assert(VotesGrantedAreServers(ds_));
            }
        };
        lemma_len_subset(other_votes, universe);
        lemma_len_subset(stepping_votes, universe);
        assert(other_votes.len() >= quorum_size);
        assert(stepping_votes.len() >= quorum_size);

        lemma_vote_sets_disjoint(ds, ds_, stepping, other, term, n);
        assert((other_votes + stepping_votes).subset_of(universe));
        lemma_len_subset(other_votes + stepping_votes, universe);
        assert(other_votes.len() + stepping_votes.len() > universe.len());
    }

    /// A Leader that stays Leader keeps its term.
    proof fn lemma_leader_stays_in_term(s: LState, s_: LState, c: LConstants)
        requires
            LNext(s, s_, c),
            s.role is Leader,
            s_.role is Leader,
        ensures
            s_.current_term == s.current_term,
    {
    }

    pub proof fn lemma_static_election_safety_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftSafetyInvariant(ds_),
            NoConfigurationEntries(ds),
            ElectionSafety(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            ElectionSafety(ds_),
    {
        if RaftDistributedNormalNext(ds, ds_) {
            lemma_static_next_preserves_no_configuration_entries(ds, ds_);
            lemma_normal_next_implies_legacy(ds, ds_);
            let stepping = choose |sid: int| #![trigger ds.server_states[sid]] #![trigger ds_.server_states[sid]] #![trigger ds.server_constants[sid]] {
                &&& 0 <= sid < ds.num_servers
                &&& LNext(ds.server_states[sid], ds_.server_states[sid], ds.server_constants[sid])
                &&& (forall |j: int| #![trigger ds_.server_states[j]]
                    0 <= j < ds.num_servers && j != sid ==>
                    ds_.server_states[j] == ds.server_states[j])
            };
            assert forall |i: int, j: int| #![trigger ds_.server_states[i], ds_.server_states[j]]
                0 <= i < ds_.num_servers && 0 <= j < ds_.num_servers
                && ds_.server_states[i].role is Leader
                && ds_.server_states[j].role is Leader
                && ds_.server_states[i].current_term == ds_.server_states[j].current_term
                implies i == j by {
                if i != stepping && j != stepping {
                    assert(ds_.server_states[i] == ds.server_states[i]);
                    assert(ds_.server_states[j] == ds.server_states[j]);
                } else if i != j {
                    let other = if i == stepping { j } else { i };
                    assert(ds_.server_states[other] == ds.server_states[other]);
                    if ds.server_states[stepping].role is Leader {
                        lemma_leader_stays_in_term(ds.server_states[stepping],
                            ds_.server_states[stepping], ds.server_constants[stepping]);
                        assert(ds.server_states[stepping].current_term
                            == ds.server_states[other].current_term);
                    } else {
                        lemma_static_candidate_to_leader_is_alone(ds, ds_, stepping, other);
                    }
                }
            }
        } else {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |i: int, j: int| #![trigger ds_.server_states[i], ds_.server_states[j]]
                0 <= i < ds_.num_servers && 0 <= j < ds_.num_servers
                && ds_.server_states[i].role is Leader
                && ds_.server_states[j].role is Leader
                && ds_.server_states[i].current_term == ds_.server_states[j].current_term
                implies i == j by {
                assert(i != sid && j != sid);
                assert(ds_.server_states[i] == ds.server_states[i]);
                assert(ds_.server_states[j] == ds.server_states[j]);
            }
        }
    }

    // =========================================================================
    // Leader logs are long enough; log matching
    // =========================================================================

    pub proof fn lemma_static_leader_log_long_enough_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftSafetyInvariant(ds_),
            NoConfigurationEntries(ds),
            ElectionSafety(ds),
            LeaderLogLongEnough(ds),
            EntryTermHasVoteQuorum(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            LeaderLogLongEnough(ds_),
    {
        if RaftDistributedNormalNext(ds, ds_) {
            lemma_static_next_preserves_no_configuration_entries(ds, ds_);
            lemma_static_leader_has_quorum(ds_);
            let (server_id, s, s_, c) = lemma_lllong_extract_step(ds, ds_);
            lemma_lllong_body_i_ne_sid_light(ds, ds_, server_id, s, s_, c);
            lemma_lllong_body_i_ne_sid_heavy(ds, ds_, server_id, s, s_);
            lemma_lllong_body_i_eq_sid(ds, ds_, server_id, s, s_, c);
            assert forall |i: int, k: int, l: int| #![trigger ds_.server_states[l], ds_.server_states[i].log[k]]
                0 <= i < ds_.num_servers
                && 0 <= k < ds_.server_states[i].log.len()
                && 0 <= l < ds_.num_servers
                && ds_.server_states[l].role is Leader
                && ds_.server_states[l].current_term == ds_.server_states[i].log[k].term
                implies ds_.server_states[l].log.len() > k by {
                if i == server_id && l == server_id {
                    assert(ds_.server_states[l].log.len() > k);
                }
            }
        } else {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |i: int, k: int, l: int| #![trigger ds_.server_states[l], ds_.server_states[i].log[k]]
                0 <= i < ds_.num_servers
                && 0 <= k < ds_.server_states[i].log.len()
                && 0 <= l < ds_.num_servers
                && ds_.server_states[l].role is Leader
                && ds_.server_states[l].current_term == ds_.server_states[i].log[k].term
                implies ds_.server_states[l].log.len() > k by {
                assert(l != sid);
                assert(ds_.server_states[l] == ds.server_states[l]);
                assert(ds_.server_states[i].log == ds.server_states[i].log);
                assert(ds.server_states[i].log[k] == ds_.server_states[i].log[k]);
            }
        }
    }

    pub proof fn lemma_static_log_matching_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            LogMatching(ds),
            LeaderLogLongEnough(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            LogMatching(ds_),
    {
        if RaftDistributedNormalNext(ds, ds_) {
            let (server_id, sent, recv) = lemma_extract_step_with_network(ds, ds_);
            let s = ds.server_states[server_id];
            let s_ = ds_.server_states[server_id];
            let c = ds.server_constants[server_id];
            assert(RaftServerStepWithNetwork(ds, ds_, server_id));
            lemma_lnext_log_preserved_or_extended(s, s_, c);
            lemma_log_append_only(ds, ds_);
            assert forall |k: int| 0 <= k < s.log.len()
                implies #[trigger] s_.log[k] == s.log[k] by {};
            lemma_log_matching_inner(ds, ds_, server_id, s, s_, c);
        } else {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |i: int| #![trigger ds_.server_states[i]] 0 <= i < ds_.num_servers
                implies ds_.server_states[i].log == ds.server_states[i].log by {};
        }
    }

    // =========================================================================
    // Every log entry's term has a leader elected by a majority
    // =========================================================================

    /// A leader appending an entry: the voters that elected it in this term
    /// are the majority behind the new entry's term.
    proof fn lemma_static_ethvq_leader_append(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, k: int,
    )
        requires
            RaftSafetyInvariant(ds),
            LeaderHasQuorum(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= server_id < ds.num_servers,
            ds.server_states[server_id].role is Leader,
            k == ds.server_states[server_id].log.len(),
            k < ds_.server_states[server_id].log.len(),
            ds_.server_states[server_id].log[k].term
                == ds.server_states[server_id].current_term,
            forall |pkt: LRaftPacket| ds.network.contains(pkt)
                ==> ds_.network.contains(pkt),
        ensures
            exists |d: int, voters: Seq<int>|
                #![trigger ds_.server_states[d].log[k], voters.len()]
            {
                &&& 0 <= d < ds_.num_servers
                &&& ds_.server_states[d].log.len() > k
                &&& ds_.server_states[d].log[k]
                    == ds_.server_states[server_id].log[k]
                &&& voters.len() >= ds_.num_servers / 2
                &&& (forall |a: int| #![trigger voters[a]] 0 <= a < voters.len() ==> {
                    &&& 0 <= voters[a] < ds_.num_servers
                    &&& voters[a] != d
                    &&& ExistsGrantedVoteResponse(ds_, voters[a], d,
                            ds_.server_states[server_id].log[k].term)
                })
                &&& (forall |a: int, b: int|
                    #![trigger voters[a], voters[b]]
                    0 <= a < voters.len() && 0 <= b < voters.len() && a != b
                    ==> voters[a] != voters[b])
            }
    {
        let s = ds.server_states[server_id];
        let c = ds.server_constants[server_id];
        let term = s.current_term;
        let voters = lemma_votes_granted_to_voter_seq(ds, server_id, term);
        assert(s.votes_granted.len() >= c.quorum_size);
        assert forall |a: int| #![trigger voters[a]]
            0 <= a < voters.len()
        implies {
            &&& 0 <= voters[a] < ds_.num_servers
            &&& voters[a] != server_id
            &&& ExistsGrantedVoteResponse(ds_, voters[a], server_id, term)
        } by {
            assert(ExistsGrantedVoteResponse(ds, voters[a], server_id, term));
            lemma_vote_response_transfers(ds, ds_, voters[a], server_id, term);
        };
    }

    #[verifier::rlimit(200)]
    pub proof fn lemma_static_ethvq_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            NoConfigurationEntries(ds),
            EntryTermHasVoteQuorum(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            EntryTermHasVoteQuorum(ds_),
    {
        if !RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            lemma_static_ethvq_reboot(ds, ds_, sid);
            return;
        }
        lemma_static_leader_has_quorum(ds);
        lemma_log_append_only(ds, ds_);
        let (server_id, _sp, _rf) = lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        let n = ds.num_servers;
        let quorum_size = n / 2 + 1;
        assert(RaftServerStepWithNetwork(ds, ds_, server_id));
        lemma_lnext_log_preserved_or_extended(s, s_, c);

        assert forall |src: int, dst: int, term: int|
            ExistsGrantedVoteResponse(ds, src, dst, term)
        implies ExistsGrantedVoteResponse(ds_, src, dst, term) by {
            lemma_vote_response_transfers(ds, ds_, src, dst, term);
        };
        assert forall |j: int, m: int|
            #![trigger ds.server_states[j].log[m]]
            0 <= j < n && 0 <= m < ds.server_states[j].log.len()
        implies ds_.server_states[j].log[m] == ds.server_states[j].log[m] by {};
        assert forall |j: int|
            #![trigger ds.server_states[j].log.len()]
            0 <= j < n
        implies ds_.server_states[j].log.len() >= ds.server_states[j].log.len() by {};

        if s_.log.len() > s.log.len() {
            let new_k: int = s.log.len() as int;
            if s_.role is Leader {
                assert(s.role is Leader);
                assert(s_.log[new_k].term == s.current_term);
                lemma_static_ethvq_leader_append(ds, ds_, server_id, new_k);
            } else {
                assert(s_.role is Follower);
                let ae_leader = lemma_follower_find_ae_leader(ds, ds_, server_id, new_k);
                lemma_entry_term_has_vote_quorum_trigger(ds, ae_leader, new_k);
                assert(ds.server_states[ae_leader].log[new_k] == s_.log[new_k]);
            }
        }

        assert forall |i: int, k: int|
            #![trigger entry_term_has_vote_quorum_trigger(ds_, i, k)]
            0 <= i < ds_.num_servers
            && 0 <= k < ds_.server_states[i].log.len()
            && entry_term_has_vote_quorum_trigger(ds_, i, k)
        implies exists |d: int, voters: Seq<int>|
            #![trigger ds_.server_states[d].log[k], voters.len()]
        {
            &&& 0 <= d < ds_.num_servers
            &&& ds_.server_states[d].log.len() > k
            &&& ds_.server_states[d].log[k] == ds_.server_states[i].log[k]
            &&& voters.len() >= quorum_size - 1
            &&& (forall |a: int| #![trigger voters[a]] 0 <= a < voters.len() ==> {
                &&& 0 <= voters[a] < ds_.num_servers
                &&& voters[a] != d
                &&& ExistsGrantedVoteResponse(ds_, voters[a], d,
                        ds_.server_states[i].log[k].term)
            })
            &&& (forall |a: int, b: int|
                #![trigger voters[a], voters[b]]
                0 <= a < voters.len() && 0 <= b < voters.len() && a != b
                ==> voters[a] != voters[b])
        } by {
            if i != server_id || k < s.log.len() {
                if i != server_id {
                    assert(ds_.server_states[i] == ds.server_states[i]);
                }
                assert(0 <= k < ds.server_states[i].log.len());
                lemma_entry_term_has_vote_quorum_trigger(ds, i, k);
            }
        }
    }

    /// A reboot changes neither logs nor the network.
    proof fn lemma_static_ethvq_reboot(
        ds: RaftDistributedState, ds_: RaftDistributedState, sid: int,
    )
        requires
            EntryTermHasVoteQuorum(ds),
            RaftDistributedReboot(ds, ds_, sid),
        ensures
            EntryTermHasVoteQuorum(ds_),
    {
        assert(ds_.network == ds.network);
        assert forall |i: int| #![trigger ds_.server_states[i]] 0 <= i < ds_.num_servers
            implies ds_.server_states[i].log == ds.server_states[i].log by {};
        assert forall |src: int, dst: int, term: int|
            ExistsGrantedVoteResponse(ds, src, dst, term)
            == ExistsGrantedVoteResponse(ds_, src, dst, term) by {};
        assert forall |i: int, k: int|
            #![trigger entry_term_has_vote_quorum_trigger(ds_, i, k)]
            0 <= i < ds_.num_servers
            && 0 <= k < ds_.server_states[i].log.len()
            && entry_term_has_vote_quorum_trigger(ds_, i, k)
        implies exists |d: int, voters: Seq<int>|
            #![trigger ds_.server_states[d].log[k], voters.len()]
        {
            &&& 0 <= d < ds_.num_servers
            &&& ds_.server_states[d].log.len() > k
            &&& ds_.server_states[d].log[k] == ds_.server_states[i].log[k]
            &&& voters.len() >= ds_.num_servers / 2 + 1 - 1
            &&& (forall |a: int| #![trigger voters[a]] 0 <= a < voters.len() ==> {
                &&& 0 <= voters[a] < ds_.num_servers
                &&& voters[a] != d
                &&& ExistsGrantedVoteResponse(ds_, voters[a], d,
                        ds_.server_states[i].log[k].term)
            })
            &&& (forall |a: int, b: int|
                #![trigger voters[a], voters[b]]
                0 <= a < voters.len() && 0 <= b < voters.len() && a != b
                ==> voters[a] != voters[b])
        } by {
            lemma_entry_term_has_vote_quorum_trigger(ds, i, k);
            assert(ds.server_states[i].log[k] == ds_.server_states[i].log[k]);
            let (d, voters) = choose |d: int, voters: Seq<int>|
                #![trigger ds.server_states[d].log[k], voters.len()]
            {
                &&& 0 <= d < ds.num_servers
                &&& ds.server_states[d].log.len() > k
                &&& ds.server_states[d].log[k] == ds.server_states[i].log[k]
                &&& voters.len() >= ds.num_servers / 2 + 1 - 1
                &&& (forall |a: int| #![trigger voters[a]] 0 <= a < voters.len() ==> {
                    &&& 0 <= voters[a] < ds.num_servers
                    &&& voters[a] != d
                    &&& ExistsGrantedVoteResponse(ds, voters[a], d,
                            ds.server_states[i].log[k].term)
                })
                &&& (forall |a: int, b: int|
                    #![trigger voters[a], voters[b]]
                    0 <= a < voters.len() && 0 <= b < voters.len() && a != b
                    ==> voters[a] != voters[b])
            };
            assert(ds_.server_states[d].log[k] == ds.server_states[d].log[k]);
        }
    }

    // =========================================================================
    // Leader completeness
    // =========================================================================

    /// Leader completeness follows from the state alone: a committed entry's
    /// majority and a leader's vote majority share a server, and an entry
    /// that server holds reaches the leader through its vote (the
    /// term-indexed transfer argument of `lemma_overlap_voter_entry_transfer`).
    pub proof fn lemma_static_leader_completeness_from_state(ds: RaftDistributedState)
        requires
            RaftSafetyInvariant(ds),
            NoConfigurationEntries(ds),
            LogMatching(ds),
            EntryTermHasVoteQuorum(ds),
        ensures
            LeaderCompleteness(ds),
    {
        lemma_static_leader_has_quorum(ds);
        let n = ds.num_servers;
        let universe = Set::<int>::range(0, n);
        lemma_range_set_finite(n);
        assert forall |k: int, entry: LLogEntry, leader_id: int| #![trigger EntryCommittedAt(ds, k, entry), ds.server_states[leader_id]]
            0 <= k
            && EntryCommittedAt(ds, k, entry)
            && 0 <= leader_id < n
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term > entry.term
        implies {
            &&& ds.server_states[leader_id].log.len() > k
            &&& ds.server_states[leader_id].log[k] == entry
        } by {
            let quorum = choose |quorum: Set<int>| {
                &&& quorum.len() >= n / 2 + 1
                &&& (forall |id: int| #![trigger quorum.contains(id)] quorum.contains(id) ==> {
                    &&& 0 <= id < n
                    &&& ds.server_states[id].log.len() > k
                    &&& ds.server_states[id].log[k] == entry
                })
            };
            let votes = ds.server_states[leader_id].votes_granted;
            assert(quorum.subset_of(universe));
            assert(votes.subset_of(universe)) by {
                assert forall |v: int| votes.contains(v) implies universe.contains(v) by {
                    assert(VotesGrantedAreServers(ds));
                }
            };
            assert(votes.len() >= ds.server_constants[leader_id].quorum_size);
            lemma_quorum_intersection(quorum, votes, universe);
            let w = choose |w: int| quorum.contains(w) && votes.contains(w);
            if w != leader_id {
                lemma_vote_witness_from_votes_granted(ds, leader_id, w);
                lemma_overlap_voter_entry_transfer(ds, leader_id, w, k, entry);
            }
        }
    }

    // =========================================================================
    // The static safety core
    // =========================================================================

    /// The inductive core of the fixed-majority Raft argument.
    pub open spec fn StaticCore(ds: RaftDistributedState) -> bool {
        &&& NoConfigurationEntries(ds)
        &&& ElectionSafety(ds)
        &&& LogMatching(ds)
        &&& LeaderLogLongEnough(ds)
        &&& EntryTermHasVoteQuorum(ds)
    }

    pub proof fn lemma_static_core_init(ds: RaftDistributedState)
        requires
            RaftDistributedInit(ds),
        ensures
            StaticCore(ds),
    {
        assert forall |i: int| #![trigger ds.server_states[i]] 0 <= i < ds.num_servers
            implies ds.server_states[i].log.len() == 0 && !(ds.server_states[i].role is Leader) by {
            assert(LInit(ds.server_states[i], ds.server_constants[i]));
        }
        lemma_entry_term_has_vote_quorum_trigger(ds, 0, 0);
    }

    pub proof fn lemma_static_core_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftSafetyInvariant(ds_),
            StaticCore(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            StaticCore(ds_),
    {
        lemma_static_next_preserves_no_configuration_entries(ds, ds_);
        lemma_static_election_safety_inductive(ds, ds_);
        lemma_static_log_matching_inductive(ds, ds_);
        lemma_static_leader_log_long_enough_inductive(ds, ds_);
        lemma_static_ethvq_inductive(ds, ds_);
    }

    // =========================================================================
    // Leader match indexes agree with follower logs
    // =========================================================================

    pub proof fn lemma_static_arla_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            LogMatching(ds),
            AppendResponseLogAgreement(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            AppendResponseLogAgreement(ds_),
    {
        if RaftDistributedNormalNext(ds, ds_) {
            lemma_append_response_log_agreement_inductive(ds, ds_);
        } else {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |i: int| #![trigger ds_.server_states[i]] 0 <= i < ds_.num_servers
                implies ds_.server_states[i].log == ds.server_states[i].log by {};
        }
    }

    pub proof fn lemma_static_mib_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            MatchIndexBounded(ds),
            AppendResponseLogAgreement(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            MatchIndexBounded(ds_),
    {
        if RaftDistributedNormalNext(ds, ds_) {
            lemma_match_index_bounded_inductive(ds, ds_);
        } else {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |i: int| #![trigger ds_.server_states[i]] 0 <= i < ds_.num_servers
                implies ds_.server_states[i].log == ds.server_states[i].log by {};
        }
    }

    pub proof fn lemma_static_mila_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            MatchIndexImpliesLogAgreement(ds),
            AppendResponseLogAgreement(ds),
            MatchIndexBounded(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            MatchIndexImpliesLogAgreement(ds_),
    {
        if !RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |i: int| #![trigger ds_.server_states[i]] 0 <= i < ds_.num_servers
                implies ds_.server_states[i].log == ds.server_states[i].log by {};
            assert forall |leader_id: int, follower_id: int, k: int|
                #![trigger ds_.server_states[leader_id].log[k], ds_.server_states[follower_id].log[k], ds_.server_states[leader_id].match_index]
                0 <= leader_id < ds_.num_servers
                && 0 <= follower_id < ds_.num_servers
                && ds_.server_states[leader_id].role is Leader
                && ds_.server_states[leader_id].match_index.dom().contains(follower_id as u64)
                && 0 <= k < ds_.server_states[leader_id].match_index[follower_id as u64] as int
                && k < ds_.server_states[leader_id].log.len()
                && k < ds_.server_states[follower_id].log.len()
            implies ds_.server_states[leader_id].log[k] == ds_.server_states[follower_id].log[k] by {
                assert(leader_id != sid);
                assert(ds_.server_states[leader_id] == ds.server_states[leader_id]);
                assert(ds.server_states[leader_id].log[k] == ds.server_states[follower_id].log[k]);
            }
            return;
        }
        lemma_log_append_only(ds, ds_);
        let (server_id, _sp, _rf) = lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        assert(RaftServerStepWithNetwork(ds, ds_, server_id));
        assert forall |leader_id: int, follower_id: int, k: int|
            #![trigger ds_.server_states[leader_id].log[k], ds_.server_states[follower_id].log[k], ds_.server_states[leader_id].match_index]
            0 <= leader_id < ds_.num_servers
            && 0 <= follower_id < ds_.num_servers
            && ds_.server_states[leader_id].role is Leader
            && ds_.server_states[leader_id].match_index.dom().contains(follower_id as u64)
            && 0 <= k < ds_.server_states[leader_id].match_index[follower_id as u64] as int
            && k < ds_.server_states[leader_id].log.len()
            && k < ds_.server_states[follower_id].log.len()
        implies ds_.server_states[leader_id].log[k] == ds_.server_states[follower_id].log[k]
        by {
            if leader_id != server_id {
                assert(ds_.server_states[leader_id] == ds.server_states[leader_id]);
                assert(ds.server_states[leader_id].match_index.dom().contains(follower_id as u64));
                assert(k < ds.server_states[leader_id].match_index[follower_id as u64] as int);
                assert(ds.server_states[leader_id].log[k]
                    == ds.server_states[follower_id].log[k]);
            } else {
                let follower = follower_id as u64;
                if s.match_index.dom().contains(follower)
                    && s_.match_index[follower] == s.match_index[follower]
                    && s.role is Leader
                {
                    assert(k < s.match_index[follower] as int);
                    assert(k < ds.server_states[follower_id].log.len());
                    assert(s.log[k] == ds.server_states[follower_id].log[k]);
                    if follower_id != server_id {
                        assert(ds_.server_states[follower_id] == ds.server_states[follower_id]);
                    }
                } else {
                    assert(!(s_.match_index =~= s.match_index)) by {
                        if s_.match_index =~= s.match_index {
                            if s.role is Leader {
                                assert(s_.match_index[follower] == s.match_index[follower]);
                                assert(s.match_index.dom().contains(follower));
                            } else {
                                lemma_lnext_non_leader_to_leader_was_candidate(s, s_, c);
                            }
                        }
                    };
                    let p = lemma_mila_changed_match_index_packet(
                        ds, ds_, server_id, s, s_, c, follower_id);
                    let response_follower = p.msg->AppendResponse_follower;
                    assert(response_follower as u64 == follower);
                    assert(response_follower == follower_id);
                    assert(p.msg->AppendResponse_match_index == s_.match_index[follower] as int);
                    assert(p.src == follower_id);
                    assert(p.dst == leader_id);
                    assert(ds.server_states[p.src].log[k] == ds.server_states[p.dst].log[k]);
                    if follower_id != server_id {
                        assert(ds_.server_states[follower_id] == ds.server_states[follower_id]);
                    }
                }
            }
        }
    }

    // =========================================================================
    // Certificates: held by a majority, and carried by AppendEntries
    // =========================================================================

    /// Every log certificate's entry is held by a majority of all servers.
    pub open spec fn CertificatesHeldByMajority(ds: RaftDistributedState) -> bool {
        forall |index: int| #![trigger ds.log_commit_certificates[index]]
            ds.log_commit_certificates.dom().contains(index) ==> {
                &&& 0 <= index
                &&& ds.log_commit_certificates[index].log_index == index
                &&& EntryCommittedAt(ds, index, ds.log_commit_certificates[index].entry)
            }
    }

    /// Without Configuration entries no configuration certificate exists.
    pub open spec fn NoConfigurationCertificates(ds: RaftDistributedState) -> bool {
        ds.configuration_commit_certificates.dom() =~= Set::<int>::empty()
    }

    /// An AppendEntries carries its sender's certified commit point: below
    /// leader_commit the sender's log matches the certificates.
    pub open spec fn AppendEntriesCommitCertified(ds: RaftDistributedState) -> bool {
        forall |p: LRaftPacket| #![trigger ds.network.contains(p)]
            ds.network.contains(p) && p.msg is AppendEntries ==> {
                let l = p.msg->AppendEntries_leader;
                let lc = p.msg->AppendEntries_leader_commit;
                &&& 0 <= l < ds.num_servers
                &&& lc <= ds.server_states[l].log.len()
                &&& forall |k: int| #![trigger ds.server_states[l].log[k]]
                    0 <= k < lc ==> {
                        &&& ds.log_commit_certificates.dom().contains(k)
                        &&& ds.log_commit_certificates[k].entry == ds.server_states[l].log[k]
                    }
            }
    }

    /// Commitment by a majority survives log growth.
    proof fn lemma_entry_committed_at_monotone(
        ds: RaftDistributedState, ds_: RaftDistributedState, k: int, entry: LLogEntry,
    )
        requires
            0 <= k,
            ds_.num_servers == ds.num_servers,
            LogAppendOnly(ds, ds_),
            EntryCommittedAt(ds, k, entry),
        ensures
            EntryCommittedAt(ds_, k, entry),
    {
        let quorum = choose |quorum: Set<int>| {
            &&& quorum.len() >= ds.num_servers / 2 + 1
            &&& (forall |id: int| #![trigger quorum.contains(id)] quorum.contains(id) ==> {
                &&& 0 <= id < ds.num_servers
                &&& ds.server_states[id].log.len() > k
                &&& ds.server_states[id].log[k] == entry
            })
        };
        assert forall |id: int| #![trigger quorum.contains(id)] quorum.contains(id) implies {
            &&& 0 <= id < ds_.num_servers
            &&& ds_.server_states[id].log.len() > k
            &&& ds_.server_states[id].log[k] == entry
        } by {
            let si = ds.server_states[id];
            let si_ = ds_.server_states[id];
            assert(si_.log.len() >= si.log.len());
            assert(si.log[k] == entry);
            assert(si_.log[k] == si.log[k]);
        };
    }

    /// A local step that raises the commit index is a leader commit backed
    /// by a majority of replicators that agree with the leader's log.
    proof fn lemma_local_commit_is_majority_backed(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, sp: Seq<LRaftMessage>, rf: Option<int>,
    )
        requires
            RaftSafetyInvariant(ds),
            NoConfigurationEntries(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            0 <= server_id < ds.num_servers,
            RaftActionProduces(ds, server_id, ds.server_states[server_id],
                ds_.server_states[server_id], ds.server_constants[server_id], sp, rf),
            rf is None,
            ds_.server_states[server_id].commit_index > ds.server_states[server_id].commit_index,
        ensures ({
            let s = ds.server_states[server_id];
            let s_ = ds_.server_states[server_id];
            let c = ds.server_constants[server_id];
            let quorum = replicator_set(s, c, s_.commit_index);
            &&& s.role is Leader
            &&& s_.log == s.log
            &&& s_.commit_index <= s.log.len()
            &&& quorum.subset_of(Set::<int>::range(0, ds.num_servers))
            &&& quorum.len() >= ds.num_servers / 2 + 1
            &&& forall |id: int, k: int| #![trigger quorum.contains(id), s.log[k]]
                quorum.contains(id) && 0 <= k < s_.commit_index ==> {
                    &&& ds.server_states[id].log.len() > k
                    &&& ds.server_states[id].log[k] == s.log[k]
                }
        }),
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        let n = s_.commit_index;
        assert(exists |nci: int| LTryAdvanceCommitIndex(s, s_, c, nci, sp));
        let nci = choose |nci: int| LTryAdvanceCommitIndex(s, s_, c, nci, sp);
        assert(s.role is Leader && has_active_commit_quorum(s, c, nci) && nci == n);
        let initial = MembershipPhase::Stable { config: c.servers };
        assert forall |k: int| #![trigger s.log[k]] 0 <= k < s.log.len()
            implies !(s.log[k].payload is Configuration) by {
            assert(!(ds.server_states[server_id].log[k].payload is Configuration));
        }
        lemma_configuration_free_log_has_initial_phase(s.log, s.commit_index, initial);
        let quorum = replicator_set(s, c, n);
        lemma_initial_phase_quorum_is_majority(ds, server_id, quorum);
        assert forall |id: int, k: int| #![trigger quorum.contains(id), s.log[k]]
            quorum.contains(id) && 0 <= k < n implies {
                &&& ds.server_states[id].log.len() > k
                &&& ds.server_states[id].log[k] == s.log[k]
            } by {
            if id != server_id {
                assert(s.match_index.contains_key(id as u64) && s.match_index[id as u64] as int >= n);
                assert(MatchIndexBounded(ds));
                assert(s.match_index[id as u64] as int <= ds.server_states[id].log.len());
                assert(s.log[k] == ds.server_states[id].log[k]);
            }
        }
    }

    pub proof fn lemma_static_certificates_held_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            NoConfigurationEntries(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            CertificatesHeldByMajority(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            CertificatesHeldByMajority(ds_),
    {
        if !RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |i: int| #![trigger ds_.server_states[i]] 0 <= i < ds_.num_servers
                implies ds_.server_states[i].log == ds.server_states[i].log by {};
            assert(LogAppendOnly(ds, ds_));
            assert forall |index: int| #![trigger ds_.log_commit_certificates[index]]
                ds_.log_commit_certificates.dom().contains(index) implies {
                    &&& 0 <= index
                    &&& ds_.log_commit_certificates[index].log_index == index
                    &&& EntryCommittedAt(ds_, index, ds_.log_commit_certificates[index].entry)
                } by {
                lemma_entry_committed_at_monotone(ds, ds_, index, ds.log_commit_certificates[index].entry);
            }
            return;
        }
        lemma_log_append_only(ds, ds_);
        let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        assert(ds_.log_commit_certificates
            == next_log_commit_certificates(ds, server_id, s, s_, c, rf));
        let fresh = rf is None && s_.commit_index > s.commit_index;
        if fresh {
            lemma_local_commit_is_majority_backed(ds, ds_, server_id, sp, rf);
        }
        assert forall |index: int| #![trigger ds_.log_commit_certificates[index]]
            ds_.log_commit_certificates.dom().contains(index) implies {
                &&& 0 <= index
                &&& ds_.log_commit_certificates[index].log_index == index
                &&& EntryCommittedAt(ds_, index, ds_.log_commit_certificates[index].entry)
            } by {
            if ds.log_commit_certificates.dom().contains(index) {
                assert(ds_.log_commit_certificates[index] == ds.log_commit_certificates[index]);
                lemma_entry_committed_at_monotone(ds, ds_, index, ds.log_commit_certificates[index].entry);
            } else {
                assert(fresh);
                assert(s.commit_index <= index < s_.commit_index && index < s_.log.len());
                let quorum = replicator_set(s, c, s_.commit_index);
                let entry = s_.log[index];
                assert(ds_.log_commit_certificates[index]
                    == new_log_commit_certificate(server_id, s, s_, c, index));
                lemma_int_range(0, ds.num_servers);
                vstd::set_lib::lemma_len_subset(quorum, Set::<int>::range(0, ds.num_servers));
                assert forall |id: int| #![trigger quorum.contains(id)] quorum.contains(id) implies {
                    &&& 0 <= id < ds_.num_servers
                    &&& ds_.server_states[id].log.len() > index
                    &&& ds_.server_states[id].log[index] == entry
                } by {
                    assert(ds.server_states[id].log.len() > index);
                    assert(ds.server_states[id].log[index] == s.log[index]);
                    assert(ds_.server_states[id].log[index] == ds.server_states[id].log[index]);
                };
            }
        }
    }

    pub proof fn lemma_static_no_configuration_certificates_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            NoConfigurationEntries(ds),
            NoConfigurationCertificates(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            NoConfigurationCertificates(ds_),
    {
        lemma_static_next_preserves_no_configuration_entries(ds, ds_);
        if RaftDistributedNormalNext(ds, ds_) {
            let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
            let s = ds.server_states[server_id];
            let s_ = ds_.server_states[server_id];
            let c = ds.server_constants[server_id];
            assert(ds_.configuration_commit_certificates
                == next_configuration_commit_certificates(ds, server_id, s, s_, c, rf));
            let index = s_.commit_index - 1;
            if 0 <= index < s_.log.len() {
                assert(!(ds_.server_states[server_id].log[index].payload is Configuration));
            }
        }
    }

    pub proof fn lemma_static_append_entries_commit_certified_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            WellFormedRaftDistributed(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CommitIndexBounded(ds),
            AppendEntriesCommitCertified(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            AppendEntriesCommitCertified(ds_),
    {
        if !RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |i: int| #![trigger ds_.server_states[i]] 0 <= i < ds_.num_servers
                implies ds_.server_states[i].log == ds.server_states[i].log by {};
            return;
        }
        lemma_log_append_only(ds, ds_);
        let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        assert(ds_.log_commit_certificates
            == next_log_commit_certificates(ds, server_id, s, s_, c, rf));
        // Certificates only grow; existing ones keep their entries.
        assert forall |k: int| ds.log_commit_certificates.dom().contains(k)
            implies #[trigger] ds_.log_commit_certificates.dom().contains(k)
                && ds_.log_commit_certificates[k] == ds.log_commit_certificates[k] by {};
        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)]
            ds_.network.contains(p) && p.msg is AppendEntries implies {
                let l = p.msg->AppendEntries_leader;
                let lc = p.msg->AppendEntries_leader_commit;
                &&& 0 <= l < ds_.num_servers
                &&& lc <= ds_.server_states[l].log.len()
                &&& forall |k: int| #![trigger ds_.server_states[l].log[k]]
                    0 <= k < lc ==> {
                        &&& ds_.log_commit_certificates.dom().contains(k)
                        &&& ds_.log_commit_certificates[k].entry == ds_.server_states[l].log[k]
                    }
            } by {
            let l = p.msg->AppendEntries_leader;
            let lc = p.msg->AppendEntries_leader_commit;
            if ds.network.contains(p) {
                assert forall |k: int| #![trigger ds_.server_states[l].log[k]] 0 <= k < lc implies {
                    &&& ds_.log_commit_certificates.dom().contains(k)
                    &&& ds_.log_commit_certificates[k].entry == ds_.server_states[l].log[k]
                } by {
                    assert(ds.server_states[l].log[k] == ds_.server_states[l].log[k]);
                }
            } else {
                let i = choose |i: int| 0 <= i < sp.len() && p.msg == sp[i];
                assert(RaftActionProduces(ds, server_id, s, s_, c, sp, rf));
                assert(l == server_id);
                assert(lc == s.commit_index);
                assert(s_ == s);
                assert(CommittedEntriesHaveLogCertificates(ds));
                assert forall |k: int| #![trigger ds_.server_states[l].log[k]] 0 <= k < lc implies {
                    &&& ds_.log_commit_certificates.dom().contains(k)
                    &&& ds_.log_commit_certificates[k].entry == ds_.server_states[l].log[k]
                } by {
                    assert(ds.server_states[server_id].log[k] == s.log[k]);
                }
            }
        }
    }

    /// A follower only raises its commit index on an accepted AppendEntries,
    /// and never past the leader's advertised commit index nor past the
    /// prefix it now shares with that leader. The advertisement is certified,
    /// so every newly committed entry already has a matching certificate.
    proof fn lemma_follower_commit_is_certified(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, sp: Seq<LRaftMessage>, rf: Option<int>,
    )
        requires
            WellFormedRaftDistributed(ds),
            AppendEntriesIntegrity(ds),
            LogMatching(ds),
            AppendEntriesCommitCertified(ds),
            0 <= server_id < ds.num_servers,
            RaftActionProduces(ds, server_id, ds.server_states[server_id],
                ds_.server_states[server_id], ds.server_constants[server_id], sp, rf),
            rf is Some,
            ds_.server_states[server_id].commit_index > ds.server_states[server_id].commit_index,
            ds_.log_commit_certificates == ds.log_commit_certificates,
        ensures
            ds_.server_states[server_id].log.len() >= ds.server_states[server_id].log.len(),
            forall |k: int| #![trigger ds_.server_states[server_id].log[k]]
                0 <= k < ds.server_states[server_id].log.len()
                ==> ds_.server_states[server_id].log[k] == ds.server_states[server_id].log[k],
            forall |k: int| #![trigger ds_.server_states[server_id].log[k]]
                0 <= k < ds_.server_states[server_id].commit_index
                && k < ds_.server_states[server_id].log.len()
                && ds.server_states[server_id].commit_index <= k
                ==> {
                    &&& ds_.log_commit_certificates.dom().contains(k)
                    &&& ds_.log_commit_certificates[k].entry == ds_.server_states[server_id].log[k]
                },
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        let pkt = choose |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
            &&& rf == Some(pkt.src)
            &&& ds.network.contains(pkt)
            &&& pkt.dst == server_id
            &&& LHandleMessage(s, s_, c, pkt.msg, sp)
        };
        assert(pkt.msg is AppendEntries);
        let l = pkt.msg->AppendEntries_leader;
        let prev = pkt.msg->AppendEntries_prev_index;
        let lc = pkt.msg->AppendEntries_leader_commit;
        let he = pkt.msg->AppendEntries_has_entry;
        let t = pkt.msg->AppendEntries_term;
        let s_mid = step_down_if_needed(s, t);
        assert(s_mid.log == s.log && s_mid.commit_index == s.commit_index);
        assert(LFollowerAppendEntries(s_mid, s_, c, t, l,
            prev, pkt.msg->AppendEntries_prev_term,
            pkt.msg->AppendEntries_value, pkt.msg->AppendEntries_payload, he, lc, sp));
        let ll = ds.server_states[l].log;
        assert(0 <= l < ds.num_servers && prev >= 0 && ll.len() >= prev + ae_entry_count(he));
        assert(lc <= ll.len());
        assert(s_.commit_index <= lc);
        assert(s_.commit_index <= prev + ae_entry_count(he));
        if prev > 0 {
            assert(s.log[prev - 1].term == ll[prev - 1].term);
            assert(ds.server_states[server_id].log[prev - 1].term
                == ds.server_states[l].log[prev - 1].term);
        }
        assert forall |k: int| #![trigger ds_.server_states[server_id].log[k]]
            0 <= k < ds_.server_states[server_id].commit_index
            && k < ds_.server_states[server_id].log.len()
            && ds.server_states[server_id].commit_index <= k
            implies {
                &&& ds_.log_commit_certificates.dom().contains(k)
                &&& ds_.log_commit_certificates[k].entry == ds_.server_states[server_id].log[k]
            } by {
            assert(ds.server_states[l].log[k] == ll[k]);
            if k < prev {
                assert(ds.server_states[server_id].log[k] == ds.server_states[l].log[k]);
            } else {
                assert(he && k == prev && prev == s.log.len());
                assert(s_.log[k] == ll[k]);
            }
        }
    }

    /// A leader's fresh commit is covered: an index without a certificate
    /// receives one for the leader's own entry, and an existing certificate
    /// is majority-held, so it meets the leader's replicator majority on the
    /// leader's entry.
    proof fn lemma_leader_commit_is_certified(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, sp: Seq<LRaftMessage>, rf: Option<int>,
    )
        requires
            RaftSafetyInvariant(ds),
            NoConfigurationEntries(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            CertificatesHeldByMajority(ds),
            0 <= server_id < ds.num_servers,
            RaftActionProduces(ds, server_id, ds.server_states[server_id],
                ds_.server_states[server_id], ds.server_constants[server_id], sp, rf),
            rf is None,
            ds_.server_states[server_id].commit_index > ds.server_states[server_id].commit_index,
            ds_.log_commit_certificates == next_log_commit_certificates(ds, server_id,
                ds.server_states[server_id], ds_.server_states[server_id],
                ds.server_constants[server_id], rf),
        ensures
            ds_.server_states[server_id].log == ds.server_states[server_id].log,
            forall |k: int| #![trigger ds_.server_states[server_id].log[k]]
                ds.server_states[server_id].commit_index <= k
                && k < ds_.server_states[server_id].commit_index
                && k < ds_.server_states[server_id].log.len()
                ==> {
                    &&& ds_.log_commit_certificates.dom().contains(k)
                    &&& ds_.log_commit_certificates[k].entry == ds_.server_states[server_id].log[k]
                },
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        lemma_local_commit_is_majority_backed(ds, ds_, server_id, sp, rf);
        let n = ds.num_servers;
        let universe = Set::<int>::range(0, n);
        let quorum = replicator_set(s, c, s_.commit_index);
        lemma_int_range(0, n);
        assert forall |k: int| #![trigger ds_.server_states[server_id].log[k]]
            s.commit_index <= k && k < s_.commit_index && k < s_.log.len()
            implies {
                &&& ds_.log_commit_certificates.dom().contains(k)
                &&& ds_.log_commit_certificates[k].entry == ds_.server_states[server_id].log[k]
            } by {
            if !ds.log_commit_certificates.dom().contains(k) {
                assert(ds_.log_commit_certificates[k]
                    == new_log_commit_certificate(server_id, s, s_, c, k));
            } else {
                let cert = ds.log_commit_certificates[k];
                assert(ds_.log_commit_certificates[k] == cert);
                assert(EntryCommittedAt(ds, k, cert.entry));
                let held = choose |held: Set<int>| {
                    &&& held.len() >= n / 2 + 1
                    &&& (forall |id: int| #![trigger held.contains(id)] held.contains(id) ==> {
                        &&& 0 <= id < n
                        &&& ds.server_states[id].log.len() > k
                        &&& ds.server_states[id].log[k] == cert.entry
                    })
                };
                assert(held.subset_of(universe));
                lemma_quorum_intersection(held, quorum, universe);
                let w = choose |w: int| held.contains(w) && quorum.contains(w);
                assert(ds.server_states[w].log[k] == s.log[k]);
            }
        }
    }

    proof fn lemma_static_log_certificates_cover_reboot(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
            !RaftDistributedNormalNext(ds, ds_),
        ensures
            CommittedEntriesHaveLogCertificates(ds_),
    {
        let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
        assert(CommittedEntriesHaveLogCertificates(ds));
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
            assert(ds_.server_states[server].log[index] == ds.server_states[server].log[index]);
        }
    }

    /// Coverage after one server step, from coverage before it, unchanged
    /// other servers, a preserved prefix, and covered newly committed indices.
    proof fn lemma_log_certificates_cover_after_step(
        ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int,
    )
        requires
            CommittedEntriesHaveLogCertificates(ds),
            CertificatesHeldByMajority(ds_),
            0 <= server_id < ds.num_servers,
            ds_.num_servers == ds.num_servers,
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            forall |k: int| #![trigger ds.log_commit_certificates[k]]
                ds.log_commit_certificates.dom().contains(k) ==>
                ds_.log_commit_certificates.dom().contains(k)
                && ds_.log_commit_certificates[k] == ds.log_commit_certificates[k],
            ds.server_states[server_id].commit_index <= ds.server_states[server_id].log.len(),
            ds_.server_states[server_id].log.len() >= ds.server_states[server_id].log.len(),
            forall |k: int| #![trigger ds_.server_states[server_id].log[k]]
                0 <= k < ds.server_states[server_id].log.len()
                ==> ds_.server_states[server_id].log[k] == ds.server_states[server_id].log[k],
            forall |k: int| #![trigger ds_.server_states[server_id].log[k]]
                ds.server_states[server_id].commit_index <= k
                && k < ds_.server_states[server_id].commit_index
                && k < ds_.server_states[server_id].log.len()
                ==> {
                    &&& ds_.log_commit_certificates.dom().contains(k)
                    &&& ds_.log_commit_certificates[k].entry == ds_.server_states[server_id].log[k]
                },
        ensures
            CommittedEntriesHaveLogCertificates(ds_),
    {
        let s = ds.server_states[server_id];
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
            if server != server_id {
                assert(ds_.server_states[server] == ds.server_states[server]);
                assert(ds.server_states[server].log[index] == ds_.server_states[server].log[index]);
                assert(ds.log_commit_certificates.dom().contains(index));
            } else if index < s.commit_index {
                assert(ds.server_states[server_id].log[index] == ds_.server_states[server_id].log[index]);
                assert(ds.log_commit_certificates.dom().contains(index));
            }
            assert(ds_.log_commit_certificates.dom().contains(index));
        }
    }

    /// The recorded certificates only grow; existing ones never change.
    proof fn lemma_next_log_commit_certificates_extend(
        ds: RaftDistributedState, server_id: int,
        s: LState, s_: LState, c: LConstants, rf: Option<int>,
    )
        ensures ({
            let certs_ = next_log_commit_certificates(ds, server_id, s, s_, c, rf);
            forall |k: int| #![trigger ds.log_commit_certificates[k]]
                ds.log_commit_certificates.dom().contains(k)
                ==> certs_.dom().contains(k)
                    && certs_[k] == ds.log_commit_certificates[k]
        }),
    {
    }

    proof fn lemma_static_log_certificates_cover_normal(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            NoConfigurationEntries(ds),
            LogMatching(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            CertificatesHeldByMajority(ds),
            CertificatesHeldByMajority(ds_),
            AppendEntriesCommitCertified(ds),
            RaftDistributedNormalNext(ds, ds_),
        ensures
            CommittedEntriesHaveLogCertificates(ds_),
    {
        let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        assert(ds_.log_commit_certificates
            == next_log_commit_certificates(ds, server_id, s, s_, c, rf));
        lemma_next_log_commit_certificates_extend(ds, server_id, s, s_, c, rf);
        assert(s.commit_index <= s.log.len());
        lemma_lnext_log_preserved_or_extended(s, s_, c);
        if s_.commit_index > s.commit_index {
            if rf is None {
                lemma_leader_commit_is_certified(ds, ds_, server_id, sp, rf);
            } else {
                assert(ds_.log_commit_certificates == ds.log_commit_certificates);
                lemma_follower_commit_is_certified(ds, ds_, server_id, sp, rf);
            }
        }
        lemma_log_certificates_cover_after_step(ds, ds_, server_id);
    }

    /// Certificate coverage is preserved by every static step.
    pub proof fn lemma_static_log_certificates_cover_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            NoConfigurationEntries(ds),
            LogMatching(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            CertificatesHeldByMajority(ds),
            AppendEntriesCommitCertified(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            CommittedEntriesHaveLogCertificates(ds_),
    {
        if !RaftDistributedNormalNext(ds, ds_) {
            lemma_static_log_certificates_cover_reboot(ds, ds_);
        } else {
            lemma_static_certificates_held_inductive(ds, ds_);
            lemma_static_log_certificates_cover_normal(ds, ds_);
        }
    }

    // =========================================================================
    // The whole fixed-membership invariant
    // =========================================================================

    /// Everything the fixed-membership argument carries from state to state:
    /// the generic invariant, the static safety core, match-index agreement,
    /// and the certificate layer that makes commit certificates honest.
    pub open spec fn StaticInvariant(ds: RaftDistributedState) -> bool {
        &&& RaftSafetyInvariant(ds)
        &&& StaticCore(ds)
        &&& AppendResponseLogAgreement(ds)
        &&& MatchIndexBounded(ds)
        &&& MatchIndexImpliesLogAgreement(ds)
        &&& NoConfigurationCertificates(ds)
        &&& CertificatesHeldByMajority(ds)
        &&& AppendEntriesCommitCertified(ds)
    }

    pub proof fn lemma_static_invariant_init(ds: RaftDistributedState)
        requires
            RaftDistributedInit(ds),
        ensures
            StaticInvariant(ds),
    {
        lemma_init_establishes_invariant(ds);
        lemma_static_core_init(ds);
        assert forall |i: int| #![trigger ds.server_states[i]] 0 <= i < ds.num_servers
            implies ds.server_states[i].match_index == Map::<u64, u64>::empty() by {
            assert(LInit(ds.server_states[i], ds.server_constants[i]));
        }
        assert(ds.configuration_commit_certificates.dom() =~= Set::<int>::empty());
    }

    /// Under a static step, no configuration entry is ever committed, so
    /// configuration-certificate coverage holds vacuously.
    proof fn lemma_static_configuration_coverage(ds: RaftDistributedState)
        requires
            NoConfigurationEntries(ds),
        ensures
            CommittedConfigurationsHaveCertificates(ds),
    {
    }

    #[verifier::spinoff_prover]
    pub proof fn lemma_static_invariant_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            StaticInvariant(ds),
            RaftDistributedStaticNext(ds, ds_),
        ensures
            StaticInvariant(ds_),
    {
        lemma_static_next_preserves_no_configuration_entries(ds, ds_);
        lemma_static_configuration_coverage(ds_);
        lemma_static_log_certificates_cover_inductive(ds, ds_);
        if RaftDistributedNormalNext(ds, ds_) {
            lemma_safety_invariant_inductive(ds, ds_);
        } else {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            crate::protocol::Raft::refinement_proof::recovery::lemma_reboot_preserves_invariant(
                ds, ds_, sid);
        }
        lemma_static_core_inductive(ds, ds_);
        lemma_static_arla_inductive(ds, ds_);
        lemma_static_mib_inductive(ds, ds_);
        lemma_static_mila_inductive(ds, ds_);
        lemma_static_no_configuration_certificates_inductive(ds, ds_);
        lemma_static_certificates_held_inductive(ds, ds_);
        lemma_static_append_entries_commit_certified_inductive(ds, ds_);
    }

    /// A behavior of the protocol in which no configuration change is ever
    /// proposed: every step is a protocol step or a reboot, and none of them
    /// introduces a Configuration log entry.
    pub open spec fn IsValidStaticRaftBehavior(b: RaftBehavior) -> bool {
        &&& b.len() > 0
        &&& RaftDistributedInit(b[0])
        &&& (forall |i: int| #![trigger b[i]] 0 <= i < b.len() - 1
            ==> RaftDistributedStaticNext(b[i], b[i + 1]))
    }

    pub proof fn lemma_static_behavior_is_valid(b: RaftBehavior)
        requires
            IsValidStaticRaftBehavior(b),
        ensures
            IsValidRaftBehavior(b),
    {
    }

    pub proof fn lemma_static_invariant_holds_throughout_behavior(b: RaftBehavior, i: int)
        requires
            IsValidStaticRaftBehavior(b),
            0 <= i < b.len(),
        ensures
            StaticInvariant(b[i]),
        decreases i
    {
        if i == 0 {
            lemma_static_invariant_init(b[0]);
        } else {
            lemma_static_invariant_holds_throughout_behavior(b, i - 1);
            lemma_static_invariant_inductive(b[i - 1], b[i]);
        }
    }

} // verus!

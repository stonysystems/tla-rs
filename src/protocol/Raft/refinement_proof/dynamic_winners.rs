//! Winners of terms under membership changes: every elected leader leaves a
//! record of the quorum that elected it, and every log entry is held by the
//! winner of its term.
//!
//! See docs/raft-joint-consensus-proof-plan.md, section 2.

use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::membership::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::invariants::*;
use crate::protocol::Raft::refinement_proof::message_invariants::*;
use crate::protocol::Raft::refinement_proof::reconfiguration::*;
use crate::protocol::Raft::refinement_proof::static_safety::*;
use crate::protocol::Raft::refinement_proof::dynamic_safety::*;
use crate::protocol::Raft::refinement_proof::dynamic_logs::*;
use vstd::prelude::*;

verus! {

    // =========================================================================
    // A candidate's log lies strictly below its term
    // =========================================================================

    pub open spec fn CandidateLogBelowTerm(ds: RaftDistributedState) -> bool {
        forall |i: int, m: int| #![trigger ds.server_states[i].log[m]]
            0 <= i < ds.num_servers
            && ds.server_states[i].role is Candidate
            && 0 <= m < ds.server_states[i].log.len()
            ==> ds.server_states[i].log[m].term < ds.server_states[i].current_term
    }

    proof fn lemma_lnext_candidate_log_below(s: LState, s_: LState, c: LConstants)
        requires
            LNext(s, s_, c),
            forall |m: int| #![trigger s.log[m]] 0 <= m < s.log.len() ==> s.log[m].term <= s.current_term,
            s.role is Candidate ==> forall |m: int| #![trigger s.log[m]]
                0 <= m < s.log.len() ==> s.log[m].term < s.current_term,
        ensures
            s_.role is Candidate ==> forall |m: int| #![trigger s_.log[m]]
                0 <= m < s_.log.len() ==> s_.log[m].term < s_.current_term,
    {
    }

    pub proof fn lemma_candidate_log_below_init(ds: RaftDistributedState)
        requires RaftDistributedInit(ds),
        ensures CandidateLogBelowTerm(ds),
    {
        assert forall |i: int| #![trigger ds.server_states[i]] 0 <= i < ds.num_servers
            implies ds.server_states[i].log.len() == 0 by {
            assert(LInit(ds.server_states[i], ds.server_constants[i]));
        }
    }

    pub proof fn lemma_candidate_log_below_inductive(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            CandidateLogBelowTerm(ds),
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CandidateLogBelowTerm(ds_),
    {
        if !RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |i: int, m: int| #![trigger ds_.server_states[i].log[m]]
                0 <= i < ds_.num_servers
                && ds_.server_states[i].role is Candidate
                && 0 <= m < ds_.server_states[i].log.len()
                implies ds_.server_states[i].log[m].term < ds_.server_states[i].current_term by {
                assert(i != sid);
                assert(ds_.server_states[i] == ds.server_states[i]);
            }
            return;
        }
        let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        assert(CurrentTermGeLogTerms(ds));
        assert forall |m: int| #![trigger s.log[m]] 0 <= m < s.log.len()
            implies s.log[m].term <= s.current_term by {
            assert(ds.server_states[server_id].log[m].term <= ds.server_states[server_id].current_term);
        }
        if s.role is Candidate {
            assert forall |m: int| #![trigger s.log[m]] 0 <= m < s.log.len()
                implies s.log[m].term < s.current_term by {
                assert(ds.server_states[server_id].log[m].term < ds.server_states[server_id].current_term);
            }
        }
        lemma_lnext_candidate_log_below(s, s_, ds.server_constants[server_id]);
        assert forall |i: int, m: int| #![trigger ds_.server_states[i].log[m]]
            0 <= i < ds_.num_servers
            && ds_.server_states[i].role is Candidate
            && 0 <= m < ds_.server_states[i].log.len()
            implies ds_.server_states[i].log[m].term < ds_.server_states[i].current_term by {
            if i != server_id {
                assert(ds_.server_states[i] == ds.server_states[i]);
            } else {
                assert(s_.log[m].term < s_.current_term);
            }
        }
    }

    // =========================================================================
    // Votes inside one step
    // =========================================================================

    /// A step that keeps a server's term keeps any vote it already cast.
    proof fn lemma_lnext_same_term_keeps_vote(s: LState, s_: LState, c: LConstants)
        requires
            LNext(s, s_, c),
            s_.current_term == s.current_term,
            s.has_voted,
        ensures
            s_.has_voted,
            s_.voted_for == s.voted_for,
    {
    }

    /// A granted VoteResponse sent in a step comes from the stepping server,
    /// at its new term, for the candidate it now votes for; and before the
    /// step it either had a lower term or had not voted for anyone else.
    pub proof fn lemma_new_granted_vote_facts(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, sp: Seq<LRaftMessage>, rf: Option<int>,
    )
        requires
            WellFormedRaftDistributed(ds),
            SenderIntegrity(ds),
            0 <= server_id < ds.num_servers,
            RaftServerStepWitness(ds, ds_, server_id, sp, rf),
        ensures
            forall |p: LRaftPacket| #![trigger ds_.network.contains(p)]
                ds_.network.contains(p) && !ds.network.contains(p)
                && p.msg is VoteResponse && p.msg->VoteResponse_granted
                ==> {
                    let s = ds.server_states[server_id];
                    let s_ = ds_.server_states[server_id];
                    let t = p.msg->VoteResponse_term;
                    &&& p.msg->VoteResponse_voter == server_id
                    &&& s_.current_term == t
                    &&& s_.has_voted
                    &&& s_.voted_for == p.dst
                    &&& (s.current_term < t
                        || (s.current_term == t && (!s.has_voted || s.voted_for == p.dst)))
                },
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)]
            ds_.network.contains(p) && !ds.network.contains(p)
            && p.msg is VoteResponse && p.msg->VoteResponse_granted
            implies {
                let t = p.msg->VoteResponse_term;
                &&& p.msg->VoteResponse_voter == server_id
                &&& s_.current_term == t
                &&& s_.has_voted
                &&& s_.voted_for == p.dst
                &&& (s.current_term < t
                    || (s.current_term == t && (!s.has_voted || s.voted_for == p.dst)))
            } by {
            let i = choose |i: int| 0 <= i < sp.len() && p.msg == sp[i];
            assert(p.src == server_id);
            let pkt = choose |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
                &&& rf == Some(pkt.src)
                &&& ds.network.contains(pkt)
                &&& pkt.dst == server_id
                &&& LHandleMessage(s, s_, c, pkt.msg, sp)
            };
            assert(pkt.msg is RequestVote);
            assert(p.dst == pkt.src);
        }
    }

    // =========================================================================
    // Winner records
    // =========================================================================

    /// The voters that elected `d` in term `t`: `d` itself and servers that
    /// sent `d` a granted VoteResponse for `t`, forming a quorum of the phase
    /// of `d`'s log at election time.
    pub open spec fn winner_votes(ds: RaftDistributedState, d: int, t: int, votes: Set<int>) -> bool {
        &&& votes.contains(d)
        &&& is_quorum_for_phase(votes, active_membership_phase_from_raft_log(
            ds.server_states[d].log, ds.election_log_len[(d, t)], initial_membership_phase(ds)))
        &&& forall |v: int| #![trigger votes.contains(v)]
            votes.contains(v) && v != d ==> ExistsGrantedVoteResponse(ds, v, d, t)
    }

    /// What winning term `t` leaves behind for server `d`.
    pub open spec fn winner_record(ds: RaftDistributedState, d: int, t: int) -> bool {
        let ell = ds.election_log_len[(d, t)];
        let dl = ds.server_states[d].log;
        &&& 0 <= d < ds.num_servers
        &&& 0 <= ell <= dl.len()
        &&& forall |m: int| #![trigger dl[m]] 0 <= m < ell ==> dl[m].term < t
        &&& exists |votes: Set<int>| #![trigger winner_votes(ds, d, t, votes)] winner_votes(ds, d, t, votes)
        &&& (ds.server_states[d].current_term == t ==> {
            &&& ds.server_states[d].has_voted
            &&& ds.server_states[d].voted_for == d
        })
        &&& forall |p: LRaftPacket| #![trigger ds.network.contains(p)]
            ds.network.contains(p)
            && p.msg is VoteResponse && p.msg->VoteResponse_granted
            && p.msg->VoteResponse_voter == d && p.msg->VoteResponse_term == t
            ==> p.dst == d
    }

    pub open spec fn WinnerRecords(ds: RaftDistributedState) -> bool {
        forall |d: int, t: int| #![trigger ds.election_log_len.dom().contains((d, t))]
            ds.election_log_len.dom().contains((d, t)) ==> winner_record(ds, d, t)
    }

    pub proof fn lemma_winner_records_init(ds: RaftDistributedState)
        requires RaftDistributedInit(ds),
        ensures WinnerRecords(ds),
    {
    }

    /// Granted VoteResponses persist in the network.
    proof fn lemma_granted_vote_persists(
        ds: RaftDistributedState, ds_: RaftDistributedState, v: int, d: int, t: int,
    )
        requires
            ExistsGrantedVoteResponse(ds, v, d, t),
            forall |pkt: LRaftPacket| ds.network.contains(pkt) ==> ds_.network.contains(pkt),
        ensures
            ExistsGrantedVoteResponse(ds_, v, d, t),
    {
        let (li, lt) = choose |li: int, lt: int| #![trigger ds.network.contains(LRaftPacket {
            src: v, dst: d,
            msg: LRaftMessage::VoteResponse {
                term: t, granted: true, voter: v,
                voter_last_log_index: li, voter_last_log_term: lt,
            },
        })] ds.network.contains(LRaftPacket {
            src: v, dst: d,
            msg: LRaftMessage::VoteResponse {
                term: t, granted: true, voter: v,
                voter_last_log_index: li, voter_last_log_term: lt,
            },
        });
        assert(ds_.network.contains(LRaftPacket {
            src: v, dst: d,
            msg: LRaftMessage::VoteResponse {
                term: t, granted: true, voter: v,
                voter_last_log_index: li, voter_last_log_term: lt,
            },
        }));
    }

    /// An existing record survives a step.
    proof fn lemma_old_winner_record_persists(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, sp: Seq<LRaftMessage>, rf: Option<int>, d: int, t: int,
    )
        requires
            winner_record(ds, d, t),
            ds.election_log_len.dom().contains((d, t)),
            ElectionLogLenBounded(ds),
            RaftSafetyInvariant(ds),
            RaftDistributedNormalNext(ds, ds_),
            0 <= server_id < ds.num_servers,
            RaftServerStepWitness(ds, ds_, server_id, sp, rf),
            LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id]),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==> ds_.server_states[j] == ds.server_states[j],
            LogAppendOnly(ds, ds_),
        ensures
            winner_record(ds_, d, t),
    {
        let ell = ds.election_log_len[(d, t)];
        let dl = ds.server_states[d].log;
        let dl_ = ds_.server_states[d].log;
        assert(ds_.election_log_len[(d, t)] == ell);
        assert forall |m: int| 0 <= m < ell implies #[trigger] dl_[m] == dl[m] by {}
        let initial = initial_membership_phase(ds);
        lemma_equal_committed_raft_prefixes_have_same_active_phase(dl_, dl, ell, initial);
        let votes = choose |votes: Set<int>| #![trigger winner_votes(ds, d, t, votes)] winner_votes(ds, d, t, votes);
        assert forall |v: int| #![trigger votes.contains(v)]
            votes.contains(v) && v != d implies ExistsGrantedVoteResponse(ds_, v, d, t) by {
            lemma_granted_vote_persists(ds, ds_, v, d, t);
        }
        assert(winner_votes(ds_, d, t, votes));
        if d == server_id {
            let s = ds.server_states[d];
            let s_ = ds_.server_states[d];
            lemma_lnext_term_monotone(s, s_, ds.server_constants[d]);
            if s_.current_term == t {
                assert(s.current_term >= t);
                lemma_lnext_same_term_keeps_vote(s, s_, ds.server_constants[d]);
            }
        }
        lemma_new_granted_vote_facts(ds, ds_, server_id, sp, rf);
        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)]
            ds_.network.contains(p)
            && p.msg is VoteResponse && p.msg->VoteResponse_granted
            && p.msg->VoteResponse_voter == d && p.msg->VoteResponse_term == t
            implies p.dst == d by {
            if !ds.network.contains(p) {
                assert(d == server_id);
                assert(ds.server_states[d].current_term >= t);
            }
        }
    }

    /// The record a promotion creates.
    proof fn lemma_new_winner_record(
        ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftSafetyInvariant(ds_),
            CandidateLogBelowTerm(ds),
            RaftDistributedNormalNext(ds, ds_),
            0 <= server_id < ds.num_servers,
            LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id]),
            !(ds.server_states[server_id].role is Leader),
            ds_.server_states[server_id].role is Leader,
            ds_.election_log_len.dom().contains((server_id, ds_.server_states[server_id].current_term)),
            ds_.election_log_len[(server_id, ds_.server_states[server_id].current_term)]
                == ds.server_states[server_id].log.len(),
            LogAppendOnly(ds, ds_),
        ensures
            winner_record(ds_, server_id, ds_.server_states[server_id].current_term),
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        let t = s_.current_term;
        lemma_lnext_non_leader_to_leader_was_candidate(s, s_, c);
        lemma_lnext_term_monotone(s, s_, c);
        assert(s_.current_term == s.current_term && s_.log == s.log);
        let ell = s.log.len() as int;
        assert forall |m: int| #![trigger s_.log[m]] 0 <= m < ell implies s_.log[m].term < t by {
            assert(ds.server_states[server_id].log[m].term < ds.server_states[server_id].current_term);
        }
        assert(LeaderElectionSnapshotRecorded(ds_));
        assert(LeaderHasRecordedElectionQuorum(ds_));
        assert(c.servers =~= Set::<int>::range(0, ds.num_servers));
        let votes = s_.votes_granted;
        assert(CandidateOrLeaderVotedForSelf(ds_));
        assert forall |v: int| #![trigger votes.contains(v)]
            votes.contains(v) && v != server_id implies ExistsGrantedVoteResponse(ds_, v, server_id, t) by {
            assert(VotesGrantedAreServers(ds_));
            assert(VotersVotedForCandidate(ds_));
            let p = choose |p: LRaftPacket| #![trigger ds_.network.contains(p)] {
                &&& ds_.network.contains(p)
                &&& p.dst == server_id
                &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter, .. }
                &&& term == ds_.server_states[server_id].current_term
                &&& granted
                &&& voter == v
            };
            assert(VoteResponseIntegrity(ds_));
            assert(p.src == v);
            assert(ds_.network.contains(LRaftPacket {
                src: v, dst: server_id,
                msg: LRaftMessage::VoteResponse {
                    term: t, granted: true, voter: v,
                    voter_last_log_index: p.msg->VoteResponse_voter_last_log_index,
                    voter_last_log_term: p.msg->VoteResponse_voter_last_log_term,
                },
            }));
        }
        assert(winner_votes(ds_, server_id, t, votes));
        assert(CandidateOrLeaderVotedForSelfId(ds_));
        assert forall |p: LRaftPacket| #![trigger ds_.network.contains(p)]
            ds_.network.contains(p)
            && p.msg is VoteResponse && p.msg->VoteResponse_granted
            && p.msg->VoteResponse_voter == server_id && p.msg->VoteResponse_term == t
            implies p.dst == server_id by {
            assert(VoteResponseIntegrity(ds_));
        }
    }

    proof fn lemma_winner_records_reboot(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            WinnerRecords(ds),
            RaftDistributedNext(ds, ds_),
            !RaftDistributedNormalNext(ds, ds_),
        ensures
            WinnerRecords(ds_),
    {
        let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
        assert forall |d: int, t: int| #![trigger ds_.election_log_len.dom().contains((d, t))]
            ds_.election_log_len.dom().contains((d, t)) implies winner_record(ds_, d, t) by {
            assert(winner_record(ds, d, t));
            let votes = choose |votes: Set<int>| #![trigger winner_votes(ds, d, t, votes)] winner_votes(ds, d, t, votes);
            assert(ds_.server_states[d].log == ds.server_states[d].log);
            assert(ds_.network == ds.network);
            assert forall |v: int| #![trigger votes.contains(v)]
                votes.contains(v) && v != d implies ExistsGrantedVoteResponse(ds_, v, d, t) by {
                lemma_granted_vote_persists(ds, ds_, v, d, t);
            }
            assert(winner_votes(ds_, d, t, votes));
            if d == sid {
                assert(ds_.server_states[d].current_term == ds.server_states[d].current_term);
            }
        }
    }

    proof fn lemma_winner_records_normal(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            WinnerRecords(ds),
            CandidateLogBelowTerm(ds),
            RaftSafetyInvariant(ds),
            RaftSafetyInvariant(ds_),
            RaftDistributedNormalNext(ds, ds_),
        ensures
            WinnerRecords(ds_),
    {
        lemma_log_append_only(ds, ds_);
        let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
        assert(ElectionLogLenBounded(ds));
        assert forall |d: int, t: int| #![trigger ds_.election_log_len.dom().contains((d, t))]
            ds_.election_log_len.dom().contains((d, t)) implies winner_record(ds_, d, t) by {
            if ds.election_log_len.dom().contains((d, t)) {
                lemma_old_winner_record_persists(ds, ds_, server_id, sp, rf, d, t);
            } else {
                lemma_new_winner_record(ds, ds_, server_id);
            }
        }
    }

    pub proof fn lemma_winner_records_inductive(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            WinnerRecords(ds),
            CandidateLogBelowTerm(ds),
            RaftSafetyInvariant(ds),
            RaftSafetyInvariant(ds_),
            RaftDistributedNext(ds, ds_),
        ensures
            WinnerRecords(ds_),
    {
        if RaftDistributedNormalNext(ds, ds_) {
            lemma_winner_records_normal(ds, ds_);
        } else {
            lemma_winner_records_reboot(ds, ds_);
        }
    }

    // =========================================================================
    // Entry provenance and unique winners
    // =========================================================================

    /// The entry at `(i, j)` is held, at index `j`, by a winner of its term.
    pub closed spec fn entry_has_winner(ds: RaftDistributedState, i: int, j: int) -> bool {
        exists |d: int| #![trigger ds.election_log_len.dom().contains((d, ds.server_states[i].log[j].term))] {
            &&& ds.election_log_len.dom().contains((d, ds.server_states[i].log[j].term))
            &&& 0 <= d < ds.num_servers
            &&& ds.server_states[d].log.len() > j
            &&& ds.server_states[d].log[j] == ds.server_states[i].log[j]
        }
    }

    /// Every entry is held, at its index, by a winner of its term.
    pub open spec fn EntryHeldByWinner(ds: RaftDistributedState) -> bool {
        forall |i: int, j: int| #![trigger ds.server_states[i].log[j]]
            0 <= i < ds.num_servers && 0 <= j < ds.server_states[i].log.len()
            ==> entry_has_winner(ds, i, j)
    }

    pub proof fn lemma_entry_winner(ds: RaftDistributedState, i: int, j: int) -> (d: int)
        requires
            EntryHeldByWinner(ds),
            0 <= i < ds.num_servers,
            0 <= j < ds.server_states[i].log.len(),
        ensures
            ds.election_log_len.dom().contains((d, ds.server_states[i].log[j].term)),
            0 <= d < ds.num_servers,
            ds.server_states[d].log.len() > j,
            ds.server_states[d].log[j] == ds.server_states[i].log[j],
    {
        assert(entry_has_winner(ds, i, j));
        reveal(entry_has_winner);
        choose |d: int| #![trigger ds.election_log_len.dom().contains((d, ds.server_states[i].log[j].term))] {
            &&& ds.election_log_len.dom().contains((d, ds.server_states[i].log[j].term))
            &&& 0 <= d < ds.num_servers
            &&& ds.server_states[d].log.len() > j
            &&& ds.server_states[d].log[j] == ds.server_states[i].log[j]
        }
    }

    pub proof fn lemma_entry_has_winner_intro(ds: RaftDistributedState, i: int, j: int, d: int)
        requires
            0 <= i < ds.num_servers,
            0 <= j < ds.server_states[i].log.len(),
            ds.election_log_len.dom().contains((d, ds.server_states[i].log[j].term)),
            0 <= d < ds.num_servers,
            ds.server_states[d].log.len() > j,
            ds.server_states[d].log[j] == ds.server_states[i].log[j],
        ensures
            entry_has_winner(ds, i, j),
    {
        reveal(entry_has_winner);
    }

    /// No term below `bound` has two winners.
    pub open spec fn UniqueWinnersBelow(ds: RaftDistributedState, bound: int) -> bool {
        forall |a: int, b: int, t: int|
            #![trigger ds.election_log_len.dom().contains((a, t)), ds.election_log_len.dom().contains((b, t))]
            t < bound
            && ds.election_log_len.dom().contains((a, t))
            && ds.election_log_len.dom().contains((b, t))
            ==> a == b
    }

    pub open spec fn UniqueWinners(ds: RaftDistributedState) -> bool {
        forall |a: int, b: int, t: int|
            #![trigger ds.election_log_len.dom().contains((a, t)), ds.election_log_len.dom().contains((b, t))]
            ds.election_log_len.dom().contains((a, t))
            && ds.election_log_len.dom().contains((b, t))
            ==> a == b
    }

    // =========================================================================
    // Preservation: entry provenance
    // =========================================================================

    pub proof fn lemma_entry_held_by_winner_init(ds: RaftDistributedState)
        requires RaftDistributedInit(ds),
        ensures EntryHeldByWinner(ds),
    {
        assert forall |i: int| #![trigger ds.server_states[i]] 0 <= i < ds.num_servers
            implies ds.server_states[i].log.len() == 0 by {
            assert(LInit(ds.server_states[i], ds.server_constants[i]));
        }
    }

    /// An old entry keeps its winner: the winner's log only grows and
    /// election records are never removed.
    proof fn lemma_old_entry_keeps_winner(ds: RaftDistributedState, ds_: RaftDistributedState, i: int, j: int)
        requires
            EntryHeldByWinner(ds),
            LogAppendOnly(ds, ds_),
            ds_.num_servers == ds.num_servers,
            forall |v: int, t: int| #![trigger ds.election_log_len.dom().contains((v, t))]
                ds.election_log_len.dom().contains((v, t)) ==> ds_.election_log_len.dom().contains((v, t)),
            0 <= i < ds.num_servers,
            0 <= j < ds.server_states[i].log.len(),
        ensures
            entry_has_winner(ds_, i, j),
    {
        let d = lemma_entry_winner(ds, i, j);
        assert(ds_.server_states[i].log[j] == ds.server_states[i].log[j]);
        assert(ds_.server_states[d].log[j] == ds.server_states[d].log[j]);
        lemma_entry_has_winner_intro(ds_, i, j, d);
    }

    /// What a normal step does to logs, stated without the step relation.
    #[verifier::opaque]
    pub open spec fn log_step_facts(ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int) -> bool {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        &&& 0 <= server_id < ds.num_servers
        &&& ds_.num_servers == ds.num_servers
        &&& LogAppendOnly(ds, ds_)
        &&& forall |j: int| #![trigger ds_.server_states[j]]
            0 <= j < ds.num_servers && j != server_id ==> ds_.server_states[j] == ds.server_states[j]
        &&& forall |v: int, t: int| #![trigger ds.election_log_len.dom().contains((v, t))]
            ds.election_log_len.dom().contains((v, t)) ==> ds_.election_log_len.dom().contains((v, t))
        &&& s_.log.len() <= s.log.len() + 1
        &&& (s_.log.len() == s.log.len() + 1 ==> appended_entry_source(ds, ds_, server_id))
        &&& (s.role is Leader ==> ds.election_log_len.dom().contains((server_id, s.current_term)))
    }

    pub proof fn lemma_log_step_facts(ds: RaftDistributedState, ds_: RaftDistributedState) -> (server_id: int)
        requires
            RaftSafetyInvariant(ds),
            LogMatching(ds),
            RaftDistributedNormalNext(ds, ds_),
        ensures
            log_step_facts(ds, ds_, server_id),
    {
        reveal(log_step_facts);
        lemma_log_append_only(ds, ds_);
        let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        lemma_lnext_log_preserved_or_extended(s, s_, ds.server_constants[server_id]);
        if s_.log.len() == s.log.len() + 1 {
            lemma_appended_entry_source(ds, ds_, server_id);
        }
        assert(LeaderElectionSnapshotRecorded(ds));
        assert forall |v: int, t: int| #![trigger ds.election_log_len.dom().contains((v, t))]
            ds.election_log_len.dom().contains((v, t)) implies ds_.election_log_len.dom().contains((v, t)) by {
            assert(ds_.election_log_len.dom().contains((v, t)) && ds_.election_log_len[(v, t)] == ds.election_log_len[(v, t)]);
        }
        server_id
    }

    proof fn lemma_entry_held_by_winner_step(ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int)
        requires
            EntryHeldByWinner(ds),
            log_step_facts(ds, ds_, server_id),
        ensures
            EntryHeldByWinner(ds_),
    {
        reveal(log_step_facts);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        assert forall |i: int, j: int| #![trigger ds_.server_states[i].log[j]]
            0 <= i < ds_.num_servers && 0 <= j < ds_.server_states[i].log.len()
            implies entry_has_winner(ds_, i, j) by {
            if j < ds.server_states[i].log.len() {
                lemma_old_entry_keeps_winner(ds, ds_, i, j);
            } else {
                assert(i == server_id && j == s.log.len());
                let at = j;
                if s.role is Leader && s_.log[at].term == s.current_term {
                    lemma_entry_has_winner_intro(ds_, i, j, server_id);
                } else {
                    let source = choose |source: int| #![trigger ds.server_states[source]] {
                        &&& 0 <= source < ds.num_servers
                        &&& ds.server_states[source].log.len() > at
                        &&& ds.server_states[source].log[at] == s_.log[at]
                        &&& forall |m: int| #![trigger s.log[m]]
                            0 <= m < at ==> ds.server_states[source].log[m] == s.log[m]
                    };
                    let d = lemma_entry_winner(ds, source, at);
                    assert(ds_.server_states[d].log[at] == ds.server_states[d].log[at]);
                    lemma_entry_has_winner_intro(ds_, i, j, d);
                }
            }
        }
    }

    pub proof fn lemma_entry_held_by_winner_inductive(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            EntryHeldByWinner(ds),
            RaftSafetyInvariant(ds),
            LogMatching(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            EntryHeldByWinner(ds_),
    {
        if !RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert(LogAppendOnly(ds, ds_)) by {
                assert forall |i: int| #![trigger ds_.server_states[i]] 0 <= i < ds_.num_servers
                    implies ds_.server_states[i].log == ds.server_states[i].log by {};
            }
            assert forall |i: int, j: int| #![trigger ds_.server_states[i].log[j]]
                0 <= i < ds_.num_servers && 0 <= j < ds_.server_states[i].log.len()
                implies entry_has_winner(ds_, i, j) by {
                lemma_old_entry_keeps_winner(ds, ds_, i, j);
            }
            return;
        }
        let server_id = lemma_log_step_facts(ds, ds_);
        lemma_entry_held_by_winner_step(ds, ds_, server_id);
    }

    // =========================================================================
    // Preservation: log matching with membership changes
    // =========================================================================

    /// The new entry of a step matches every other log that has an entry of
    /// the same term at that index, on the whole prefix through it. A
    /// leader's own entry has no such match: the winner of its term would be
    /// the leader itself, whose log is too short.
    proof fn lemma_new_entry_matches(
        ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int, other: int,
    )
        requires
            log_matching_premises(ds),
            log_step_facts(ds, ds_, server_id),
            0 <= other < ds.num_servers,
            other != server_id,
            ds_.server_states[server_id].log.len() == ds.server_states[server_id].log.len() + 1,
            ds.server_states[other].log.len() > ds.server_states[server_id].log.len(),
            ds.server_states[other].log[ds.server_states[server_id].log.len() as int].term
                == ds_.server_states[server_id].log[ds.server_states[server_id].log.len() as int].term,
        ensures
            forall |m: int| #![trigger ds.server_states[other].log[m]]
                0 <= m <= ds.server_states[server_id].log.len()
                ==> ds_.server_states[server_id].log[m] == ds.server_states[other].log[m],
    {
        reveal(log_matching_premises);
        reveal(log_step_facts);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let at = s.log.len() as int;
        assert(appended_entry_source(ds, ds_, server_id));
        if s.role is Leader && s_.log[at].term == s.current_term {
            lemma_leader_entry_is_fresh(ds, server_id, other, at);
        } else {
            let source = choose |source: int| #![trigger ds.server_states[source]] {
                &&& 0 <= source < ds.num_servers
                &&& ds.server_states[source].log.len() > at
                &&& ds.server_states[source].log[at] == s_.log[at]
                &&& forall |m: int| #![trigger s.log[m]]
                    0 <= m < at ==> ds.server_states[source].log[m] == s.log[m]
            };
            lemma_copied_entry_matches(ds, s.log, s_.log, source, other, at);
        }
    }

    /// No other log has an entry of the leader's term at the leader's log
    /// end: the winner of that term is the leader.
    proof fn lemma_leader_entry_is_fresh(ds: RaftDistributedState, server_id: int, other: int, at: int)
        requires
            EntryHeldByWinner(ds),
            UniqueWinners(ds),
            0 <= server_id < ds.num_servers,
            0 <= other < ds.num_servers,
            ds.election_log_len.dom().contains((server_id, ds.server_states[server_id].current_term)),
            at == ds.server_states[server_id].log.len(),
            ds.server_states[other].log.len() > at,
            ds.server_states[other].log[at].term == ds.server_states[server_id].current_term,
        ensures
            false,
    {
        let d = lemma_entry_winner(ds, other, at);
        assert(d == server_id);
    }

    /// A copied entry matches any log with the same term at that index.
    proof fn lemma_copied_entry_matches(
        ds: RaftDistributedState, old_log: Seq<LLogEntry>, new_log: Seq<LLogEntry>,
        source: int, other: int, at: int,
    )
        requires
            LogMatching(ds),
            0 <= source < ds.num_servers,
            0 <= other < ds.num_servers,
            at == old_log.len(),
            new_log.len() == at + 1,
            forall |m: int| #![trigger new_log[m]] 0 <= m < at ==> new_log[m] == old_log[m],
            ds.server_states[source].log.len() > at,
            ds.server_states[source].log[at] == new_log[at],
            forall |m: int| #![trigger old_log[m]] 0 <= m < at ==> ds.server_states[source].log[m] == old_log[m],
            ds.server_states[other].log.len() > at,
            ds.server_states[other].log[at].term == new_log[at].term,
        ensures
            forall |m: int| #![trigger ds.server_states[other].log[m]]
                0 <= m <= at ==> new_log[m] == ds.server_states[other].log[m],
    {
        let sl = ds.server_states[source].log;
        let ol = ds.server_states[other].log;
        assert(sl[at].term == ol[at].term);
        assert forall |m: int| #![trigger ds.server_states[other].log[m]]
            0 <= m <= at implies new_log[m] == ds.server_states[other].log[m] by {
            assert(sl[m] == ol[m]);
            if m < at {
                assert(new_log[m] == old_log[m]);
                assert(sl[m] == old_log[m]);
            }
        }
    }

    /// What log matching after a step needs from the state before it.
    #[verifier::opaque]
    pub open spec fn log_matching_premises(ds: RaftDistributedState) -> bool {
        &&& LogMatching(ds)
        &&& EntryHeldByWinner(ds)
        &&& UniqueWinners(ds)
    }

    /// Servers other than the stepping one keep their state; logs only grow.
    proof fn lemma_log_step_frame(ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int, i: int)
        requires
            log_step_facts(ds, ds_, server_id),
            0 <= i < ds_.num_servers,
        ensures
            ds_.num_servers == ds.num_servers,
            0 <= server_id < ds.num_servers,
            i != server_id ==> ds_.server_states[i] == ds.server_states[i],
    {
        reveal(log_step_facts);
    }

    /// Two logs that both had index `k` before the step still match.
    proof fn lemma_log_matching_pair_old(
        ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int, i: int, j: int, k: int,
    )
        requires
            log_matching_premises(ds),
            log_step_facts(ds, ds_, server_id),
            0 <= i < ds.num_servers && 0 <= j < ds.num_servers,
            0 <= k < ds.server_states[i].log.len(),
            0 <= k < ds.server_states[j].log.len(),
            ds_.server_states[i].log[k].term == ds_.server_states[j].log[k].term,
        ensures
            forall |m: int| 0 <= m <= k
                && m < ds_.server_states[i].log.len()
                && m < ds_.server_states[j].log.len()
                ==> ds_.server_states[i].log[m] == ds_.server_states[j].log[m],
    {
        reveal(log_matching_premises);
        reveal(log_step_facts);
        let li = ds.server_states[i].log;
        let lj = ds.server_states[j].log;
        let li_ = ds_.server_states[i].log;
        let lj_ = ds_.server_states[j].log;
        assert(li_[k] == li[k]);
        assert(lj_[k] == lj[k]);
        assert forall |m: int| 0 <= m <= k && m < li_.len() && m < lj_.len()
            implies li_[m] == lj_[m] by {
            assert(li_[m] == li[m]);
            assert(lj_[m] == lj[m]);
            assert(li[m] == lj[m]);
        }
    }

    /// The stepping server's new entry against an unchanged log.
    proof fn lemma_log_matching_pair_new(
        ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int, other: int, k: int,
    )
        requires
            log_matching_premises(ds),
            log_step_facts(ds, ds_, server_id),
            0 <= other < ds.num_servers,
            other != server_id,
            k >= ds.server_states[server_id].log.len(),
            k < ds_.server_states[server_id].log.len(),
            k < ds_.server_states[other].log.len(),
            ds_.server_states[server_id].log[k].term == ds_.server_states[other].log[k].term,
        ensures
            forall |m: int| 0 <= m <= k
                && m < ds_.server_states[server_id].log.len()
                && m < ds_.server_states[other].log.len()
                ==> ds_.server_states[server_id].log[m] == ds_.server_states[other].log[m],
    {
        reveal(log_step_facts);
        assert(ds_.server_states[other] == ds.server_states[other]);
        lemma_new_entry_matches(ds, ds_, server_id, other);
        assert forall |m: int| 0 <= m <= k
            && m < ds_.server_states[server_id].log.len()
            && m < ds_.server_states[other].log.len()
            implies ds_.server_states[server_id].log[m] == ds_.server_states[other].log[m] by {
            assert(ds_.server_states[server_id].log[m] == ds.server_states[other].log[m]);
        }
    }

    /// Log matching for one pair of logs at one index after a step.
    proof fn lemma_log_matching_pair(
        ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int, i: int, j: int, k: int,
    )
        requires
            log_matching_premises(ds),
            log_step_facts(ds, ds_, server_id),
            0 <= i < ds_.num_servers && 0 <= j < ds_.num_servers,
            0 <= k < ds_.server_states[i].log.len(),
            0 <= k < ds_.server_states[j].log.len(),
            ds_.server_states[i].log[k].term == ds_.server_states[j].log[k].term,
        ensures
            forall |m: int| 0 <= m <= k
                && m < ds_.server_states[i].log.len()
                && m < ds_.server_states[j].log.len()
                ==> ds_.server_states[i].log[m] == ds_.server_states[j].log[m],
    {
        if i == j {
            return;
        }
        lemma_log_step_frame(ds, ds_, server_id, i);
        lemma_log_step_frame(ds, ds_, server_id, j);
        let li = ds.server_states[i].log;
        let lj = ds.server_states[j].log;
        if k < li.len() && k < lj.len() {
            lemma_log_matching_pair_old(ds, ds_, server_id, i, j, k);
        } else if k >= li.len() {
            assert(i == server_id);
            lemma_log_matching_pair_new(ds, ds_, server_id, j, k);
        } else {
            assert(j == server_id);
            lemma_log_matching_pair_new(ds, ds_, server_id, i, k);
        }
    }

    proof fn lemma_dynamic_log_matching_step(ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int)
        requires
            log_matching_premises(ds),
            log_step_facts(ds, ds_, server_id),
        ensures
            LogMatching(ds_),
    {
        assert forall |i: int, j: int, k: int|
            #![trigger ds_.server_states[i], ds_.server_states[j].log[k]]
            #![trigger ds_.server_states[i].log[k], ds_.server_states[j]]
            0 <= i < ds_.num_servers && 0 <= j < ds_.num_servers
            && 0 <= k < ds_.server_states[i].log.len()
            && 0 <= k < ds_.server_states[j].log.len()
            && ds_.server_states[i].log[k].term == ds_.server_states[j].log[k].term
            implies (forall |m: int| 0 <= m <= k
                && m < ds_.server_states[i].log.len()
                && m < ds_.server_states[j].log.len()
                ==> ds_.server_states[i].log[m] == ds_.server_states[j].log[m]) by {
            lemma_log_matching_pair(ds, ds_, server_id, i, j, k);
        }
    }

    pub proof fn lemma_dynamic_log_matching_inductive(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            RaftSafetyInvariant(ds),
            LogMatching(ds),
            EntryHeldByWinner(ds),
            UniqueWinners(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            LogMatching(ds_),
    {
        if !RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |i: int| #![trigger ds_.server_states[i]] 0 <= i < ds_.num_servers
                implies ds_.server_states[i].log == ds.server_states[i].log by {};
            return;
        }
        let server_id = lemma_log_step_facts(ds, ds_);
        reveal(log_matching_premises);
        lemma_dynamic_log_matching_step(ds, ds_, server_id);
    }

} // verus!

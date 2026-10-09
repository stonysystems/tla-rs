//! Election safety under membership changes: two winners of one term share
//! a voter, so a term has one winner.
//!
//! See docs/raft-joint-consensus-proof-plan.md, section 2.

use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::membership::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::invariants::*;
use crate::protocol::Raft::refinement_proof::message_invariants::*;
use crate::protocol::Raft::refinement_proof::reconfiguration::*;
use crate::protocol::Raft::refinement_proof::dynamic_safety::*;
use crate::protocol::Raft::refinement_proof::dynamic_logs::*;
use crate::protocol::Raft::refinement_proof::dynamic_winners::*;
use crate::protocol::Raft::refinement_proof::dynamic_completeness::*;
use vstd::prelude::*;

verus! {

    // =========================================================================
    // The committed entries below a term form a prefix of the history
    // =========================================================================

    /// The largest `n' <= n` whose entry `h[n' - 1]` lies below term `t`.
    pub open spec fn history_cut(h: Seq<LLogEntry>, t: int, n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 } else if h[n - 1].term < t { n } else { history_cut(h, t, n - 1) }
    }

    pub proof fn lemma_history_cut(h: Seq<LLogEntry>, t: int, n: int)
        requires
            0 <= n <= h.len(),
            forall |a: int, b: int| #![trigger h[a], h[b]]
                0 <= a <= b < h.len() ==> h[a].term <= h[b].term,
        ensures
            0 <= history_cut(h, t, n) <= n,
            forall |k: int| #![trigger h[k]] 0 <= k < history_cut(h, t, n) ==> h[k].term < t,
            forall |k: int| #![trigger h[k]] history_cut(h, t, n) <= k < n ==> h[k].term >= t,
        decreases n,
    {
        if n > 0 {
            lemma_history_cut(h, t, n - 1);
            if h[n - 1].term < t {
                assert forall |k: int| #![trigger h[k]] 0 <= k < n implies h[k].term < t by {
                    assert(h[k].term <= h[n - 1].term);
                }
            }
        }
    }

    // =========================================================================
    // Two winners of a term
    // =========================================================================

    /// A vote-backed log of term `t` agrees with the history exactly on the
    /// committed entries below `t`, so its election phase is the history
    /// phase at that cut, or one legal step past it.
    pub proof fn lemma_vote_backed_phase_near_cut(
        ds: RaftDistributedState, d: int, t: int, ell: int, votes: Set<int>,
    )
        requires
            CompletenessCore(ds),
            UniqueWinnersBelow(ds, t),
            vote_backed(ds, d, t, ell, votes),
            votes.contains(d),
        ensures ({
            let h = ds.committed_history;
            let cut = history_cut(h, t, h.len() as int);
            is_legal_phase_progression(
                history_phase_at(ds, cut),
                active_membership_phase_from_raft_log(
                    ds.server_states[d].log, ell, initial_membership_phase(ds)))
        }),
    {
        let h = ds.committed_history;
        let dl = ds.server_states[d].log;
        lemma_history_terms_monotone(ds);
        lemma_history_cut(h, t, h.len() as int);
        let cut = history_cut(h, t, h.len() as int);
        assert forall |m: int| #![trigger ds.committed_history[m]]
            0 <= m < cut implies ds.server_states[d].log[m] == ds.committed_history[m] by {
            lemma_completeness_at(ds, d, t, ell, votes, m);
        }
        if cut > 0 {
            lemma_completeness_at(ds, d, t, ell, votes, cut - 1);
        }
        if cut < ell && cut < h.len() && dl[cut] == h[cut] {
            assert(h[cut].term >= t);
            assert(dl[cut].term < t);
        }
        lemma_election_phase_near(ds, d, ell, cut);
    }

    /// Two vote-backed logs of one term have intersecting voter sets.
    pub proof fn lemma_vote_backed_votes_intersect(
        ds: RaftDistributedState, t: int,
        d1: int, ell1: int, votes1: Set<int>,
        d2: int, ell2: int, votes2: Set<int>,
    )
        requires
            CompletenessCore(ds),
            UniqueWinnersBelow(ds, t),
            vote_backed(ds, d1, t, ell1, votes1),
            votes1.contains(d1),
            vote_backed(ds, d2, t, ell2, votes2),
            votes2.contains(d2),
        ensures
            exists |v: int| votes1.contains(v) && votes2.contains(v),
    {
        let h = ds.committed_history;
        let cut = history_cut(h, t, h.len() as int);
        lemma_vote_backed_phase_near_cut(ds, d1, t, ell1, votes1);
        lemma_vote_backed_phase_near_cut(ds, d2, t, ell2, votes2);
        let initial = initial_membership_phase(ds);
        lemma_sibling_progressions_intersect(
            history_phase_at(ds, cut),
            active_membership_phase_from_raft_log(ds.server_states[d1].log, ell1, initial),
            active_membership_phase_from_raft_log(ds.server_states[d2].log, ell2, initial),
            votes1, votes2);
    }

    /// Two winners of one term are the same server: a common voter would
    /// have granted its vote for that term twice, or a winner would have
    /// voted for someone other than itself.
    pub proof fn lemma_two_winners_coincide(ds: RaftDistributedState, a: int, b: int, t: int)
        requires
            CompletenessCore(ds),
            OneVotePerTermInNetwork(ds),
            UniqueWinnersBelow(ds, t),
            ds.election_log_len.dom().contains((a, t)),
            ds.election_log_len.dom().contains((b, t)),
        ensures
            a == b,
    {
        let va = lemma_winner_is_vote_backed(ds, a, t);
        let vb = lemma_winner_is_vote_backed(ds, b, t);
        lemma_vote_backed_votes_intersect(
            ds, t, a, ds.election_log_len[(a, t)], va, b, ds.election_log_len[(b, t)], vb);
        let v = choose |v: int| va.contains(v) && vb.contains(v);
        if a != b {
            assert(winner_record(ds, a, t));
            assert(winner_record(ds, b, t));
            if v == a {
                lemma_granted_vote_packet(ds, a, b, t);
            } else if v == b {
                lemma_granted_vote_packet(ds, b, a, t);
            } else {
                let pa = lemma_granted_vote_packet(ds, v, a, t);
                let pb = lemma_granted_vote_packet(ds, v, b, t);
                assert(ds.network.contains(pa) && ds.network.contains(pb));
            }
        }
    }

    /// Name the packet behind `ExistsGrantedVoteResponse`.
    pub proof fn lemma_granted_vote_packet(ds: RaftDistributedState, v: int, d: int, t: int) -> (p: LRaftPacket)
        requires
            ExistsGrantedVoteResponse(ds, v, d, t),
        ensures
            ds.network.contains(p),
            p.src == v,
            p.dst == d,
            p.msg is VoteResponse,
            p.msg->VoteResponse_granted,
            p.msg->VoteResponse_voter == v,
            p.msg->VoteResponse_term == t,
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
        LRaftPacket {
            src: v, dst: d,
            msg: LRaftMessage::VoteResponse {
                term: t, granted: true, voter: v,
                voter_last_log_index: li, voter_last_log_term: lt,
            },
        }
    }

} // verus!

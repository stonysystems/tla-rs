//! Winner completeness under membership changes: the winner of a term holds
//! every committed entry of a lower term. Proved in a single state by
//! induction on terms, so it needs no preservation argument of its own.
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
use vstd::prelude::*;

verus! {

    // =========================================================================
    // Phases
    // =========================================================================

    /// Two legal successors of one phase have intersecting quorums: both keep
    /// a majority of the configuration every successor shares.
    pub proof fn lemma_sibling_progressions_intersect(
        phase: MembershipPhase, left: MembershipPhase, right: MembershipPhase,
        left_quorum: Set<int>, right_quorum: Set<int>,
    )
        requires
            is_legal_phase_progression(phase, left),
            is_legal_phase_progression(phase, right),
            is_quorum_for_phase(left_quorum, left),
            is_quorum_for_phase(right_quorum, right),
        ensures
            exists |server: int| left_quorum.contains(server) && right_quorum.contains(server),
    {
        let shared = match phase {
            MembershipPhase::Stable { config } => config,
            MembershipPhase::Joint { old_config: _, new_config } => new_config,
        };
        let l = match left {
            MembershipPhase::Stable { config: _ } => left_quorum,
            MembershipPhase::Joint { old_config, new_config } =>
                if old_config == shared { left_quorum.intersect(old_config) }
                else { left_quorum.intersect(new_config) },
        };
        let r = match right {
            MembershipPhase::Stable { config: _ } => right_quorum,
            MembershipPhase::Joint { old_config, new_config } =>
                if old_config == shared { right_quorum.intersect(old_config) }
                else { right_quorum.intersect(new_config) },
        };
        assert(is_majority_of(l, shared));
        assert(is_majority_of(r, shared));
        lemma_majorities_intersect(l, r, shared);
        let w = choose |w: int| l.contains(w) && r.contains(w);
        assert(left_quorum.contains(w) && right_quorum.contains(w));
    }

    // =========================================================================
    // The committed history
    // =========================================================================

    pub proof fn lemma_history_terms_monotone(ds: RaftDistributedState)
        requires
            HistoryHeld(ds),
            LogTermsMonotonic(ds),
        ensures
            forall |a: int, b: int| #![trigger ds.committed_history[a], ds.committed_history[b]]
                0 <= a <= b < ds.committed_history.len()
                ==> ds.committed_history[a].term <= ds.committed_history[b].term,
    {
        let h = choose |h: int| #![trigger log_holds_history(ds, h)] log_holds_history(ds, h);
        assert forall |a: int, b: int| #![trigger ds.committed_history[a], ds.committed_history[b]]
            0 <= a <= b < ds.committed_history.len()
            implies ds.committed_history[a].term <= ds.committed_history[b].term by {
            assert(ds.server_states[h].log[a].term <= ds.server_states[h].log[b].term);
        }
    }

    /// The first index where `d`'s log stops agreeing with the history,
    /// below some index where it does not agree (or ends). Agreement is
    /// downward closed, so everything below that index agrees.
    pub proof fn lemma_first_disagreement(ds: RaftDistributedState, d: int, ell: int, k: int) -> (m0: int)
        requires
            LogMatching(ds),
            HistoryHeld(ds),
            0 <= d < ds.num_servers,
            0 <= ell <= ds.server_states[d].log.len(),
            0 <= k < ds.committed_history.len(),
            !(k < ell && ds.server_states[d].log[k] == ds.committed_history[k]),
        ensures
            0 <= m0 <= k,
            m0 <= ell,
            !(m0 < ell && ds.server_states[d].log[m0] == ds.committed_history[m0]),
            forall |m: int| #![trigger ds.committed_history[m]]
                0 <= m < m0 ==> ds.server_states[d].log[m] == ds.committed_history[m],
        decreases k,
    {
        if k == 0 {
            0
        } else if !(k - 1 < ell && ds.server_states[d].log[k - 1] == ds.committed_history[k - 1]) {
            lemma_first_disagreement(ds, d, ell, k - 1)
        } else {
            lemma_agreement_below(ds, d, ell, k);
            k
        }
    }

    /// Agreement with the history at `k - 1` extends to every index below.
    proof fn lemma_agreement_below(ds: RaftDistributedState, d: int, ell: int, k: int)
        requires
            0 <= d < ds.num_servers,
            0 < k <= ds.committed_history.len(),
            k <= ell <= ds.server_states[d].log.len(),
            ds.server_states[d].log[k - 1] == ds.committed_history[k - 1],
            LogMatching(ds),
            HistoryHeld(ds),
        ensures
            forall |m: int| #![trigger ds.committed_history[m]]
                0 <= m < k ==> ds.server_states[d].log[m] == ds.committed_history[m],
    {
        lemma_history_prefix_closed(ds, d, k - 1);
    }

    // =========================================================================
    // A log's own phase is at most one step past the history's
    // =========================================================================

    /// With at most one configuration in `[from, len)`, each legal from the
    /// phase before it, the phase at `len` is a legal progression of the
    /// phase at `from`.
    pub proof fn lemma_phase_progression_from(
        log: Seq<LLogEntry>, from: int, len: int, initial: MembershipPhase,
    )
        requires
            0 <= from <= len <= log.len(),
            forall |y: int| #![trigger log[y]] from <= y < len
                ==> configuration_entry_legal(log, y, initial),
            forall |y1: int, y2: int| #![trigger log[y1], log[y2]]
                from <= y1 < y2 < len
                ==> !(log[y1].payload is Configuration && log[y2].payload is Configuration),
        ensures
            is_legal_phase_progression(
                active_membership_phase_from_raft_log(log, from, initial),
                active_membership_phase_from_raft_log(log, len, initial)),
        decreases len - from,
    {
        let z = active_membership_phase_from_raft_log(log, from, initial);
        if len == from {
            lemma_phase_progression_reflexive(z);
        } else if !(log[len - 1].payload is Configuration) {
            lemma_phase_progression_from(log, from, len - 1, initial);
        } else {
            assert forall |y: int| #![trigger log[y]] from <= y < len - 1
                implies !(log[y].payload is Configuration) by {
                assert(!(log[y].payload is Configuration && log[len - 1].payload is Configuration));
            }
            lemma_configuration_free_interval_preserves_active_phase(log, from, len - 1, initial);
            assert(configuration_entry_legal(log, len - 1, initial));
        }
    }

    /// The phase a log reaches at `ell` is a legal progression of the history
    /// phase where the log stops agreeing with the history: any earlier
    /// configuration past that point would be committed (I4), so at most one
    /// configuration lies past it.
    pub proof fn lemma_election_phase_near(ds: RaftDistributedState, d: int, ell: int, m0: int)
        requires
            ConfigurationFollowedIsCommitted(ds),
            ConfigurationEntriesLegal(ds),
            LogMatching(ds),
            HistoryHeld(ds),
            0 <= d < ds.num_servers,
            0 <= m0 <= ell <= ds.server_states[d].log.len(),
            m0 <= ds.committed_history.len(),
            forall |m: int| #![trigger ds.committed_history[m]]
                0 <= m < m0 ==> ds.server_states[d].log[m] == ds.committed_history[m],
            !(m0 < ell && m0 < ds.committed_history.len()
                && ds.server_states[d].log[m0] == ds.committed_history[m0]),
        ensures
            is_legal_phase_progression(
                history_phase_at(ds, m0),
                active_membership_phase_from_raft_log(
                    ds.server_states[d].log, ell, initial_membership_phase(ds))),
    {
        let log = ds.server_states[d].log;
        let initial = initial_membership_phase(ds);
        assert forall |m: int| 0 <= m < m0 implies #[trigger] log[m] == ds.committed_history[m] by {}
        lemma_equal_committed_raft_prefixes_have_same_active_phase(log, ds.committed_history, m0, initial);
        assert forall |y1: int, y2: int| #![trigger log[y1], log[y2]]
            m0 <= y1 < y2 < ell
            implies !(log[y1].payload is Configuration && log[y2].payload is Configuration) by {
            if log[y1].payload is Configuration && log[y2].payload is Configuration {
                assert(ds.server_states[d].log[y1] == ds.committed_history[y1]);
                lemma_history_prefix_closed(ds, d, y1);
                assert(ds.server_states[d].log[m0] == ds.committed_history[m0]);
            }
        }
        lemma_phase_progression_from(log, m0, ell, initial);
    }

    // =========================================================================
    // Term induction
    // =========================================================================

    /// `d`'s log below `ell` lies below term `t`, the rest at or above it, and
    /// `votes` is a quorum of the phase at `ell` whose other members granted
    /// `d` their vote for `t`.
    pub open spec fn vote_backed(ds: RaftDistributedState, d: int, t: int, ell: int, votes: Set<int>) -> bool {
        let dl = ds.server_states[d].log;
        &&& 0 <= d < ds.num_servers
        &&& 0 <= ell <= dl.len()
        &&& forall |m: int| #![trigger dl[m]] 0 <= m < ell ==> dl[m].term < t
        &&& forall |m: int| #![trigger dl[m]] ell <= m < dl.len() ==> dl[m].term >= t
        &&& is_quorum_for_phase(votes, active_membership_phase_from_raft_log(dl, ell, initial_membership_phase(ds)))
        &&& forall |v: int| #![trigger votes.contains(v)]
            votes.contains(v) && v != d ==> ExistsGrantedVoteResponse(ds, v, d, t)
    }

    /// The invariants the term induction reads.
    pub open spec fn CompletenessCore(ds: RaftDistributedState) -> bool {
        &&& WellFormedRaftDistributed(ds)
        &&& CommitHistoryValid(ds)
        &&& LogTermsMonotonic(ds)
        &&& TermsNonNegative(ds)
        &&& VoteResponseIntegrity(ds)
        &&& VoteResponseHasRequestVote(ds)
        &&& VoteLogLenCoversNetwork(ds)
        &&& VoteLogLenBounded(ds)
        &&& VoteLogLenEntryTermBound(ds)
        &&& VoteGrantedLogUpToDateAtVoteTime(ds)
        &&& RequestVoteSummaryAlwaysValid(ds)
        &&& RequestVoteLastLogTermBound(ds)
        &&& SenderIntegrity(ds)
        &&& ElectionLogLenBounded(ds)
        &&& ElectionLogLenEntryTermBound(ds)
        &&& LogMatching(ds)
        &&& HistoryHeld(ds)
        &&& ConfigurationFollowedIsCommitted(ds)
        &&& ConfigurationEntriesLegal(ds)
        &&& CertificatesHeldByPhaseQuorum(ds)
        &&& WinnerRecords(ds)
        &&& EntryHeldByWinner(ds)
    }

    /// A winner record is vote-backed.
    pub proof fn lemma_winner_is_vote_backed(ds: RaftDistributedState, d: int, t: int) -> (votes: Set<int>)
        requires
            CompletenessCore(ds),
            ds.election_log_len.dom().contains((d, t)),
        ensures
            vote_backed(ds, d, t, ds.election_log_len[(d, t)], votes),
            votes.contains(d),
    {
        assert(winner_record(ds, d, t));
        let votes = choose |votes: Set<int>| #![trigger winner_votes(ds, d, t, votes)] winner_votes(ds, d, t, votes);
        let dl = ds.server_states[d].log;
        let ell = ds.election_log_len[(d, t)];
        assert forall |m: int| #![trigger dl[m]] ell <= m < dl.len() implies dl[m].term >= t by {
            assert(ds.server_states[(d, t).0].log[m].term >= (d, t).1);
        }
        votes
    }

    /// Strong log matching: entries of one term agree on the prefix through
    /// the lower index, because one winner holds both.
    pub proof fn lemma_strong_log_matching(ds: RaftDistributedState, i: int, j: int, i2: int, j2: int)
        requires
            LogMatching(ds),
            EntryHeldByWinner(ds),
            0 <= i < ds.num_servers,
            0 <= i2 < ds.num_servers,
            0 <= j <= j2,
            j < ds.server_states[i].log.len(),
            j2 < ds.server_states[i2].log.len(),
            ds.server_states[i].log[j].term == ds.server_states[i2].log[j2].term,
            UniqueWinnersBelow(ds, ds.server_states[i].log[j].term + 1),
        ensures
            forall |m: int| #![trigger ds.server_states[i].log[m]]
                0 <= m <= j ==> ds.server_states[i].log[m] == ds.server_states[i2].log[m],
    {
        let e1 = lemma_entry_winner(ds, i, j);
        let e2 = lemma_entry_winner(ds, i2, j2);
        assert(e1 == e2);
        let el = ds.server_states[e1].log;
        let li = ds.server_states[i].log;
        let li2 = ds.server_states[i2].log;
        assert(li[j].term == el[j].term);
        assert(li2[j2].term == el[j2].term);
        assert forall |m: int| #![trigger ds.server_states[i].log[m]]
            0 <= m <= j implies ds.server_states[i].log[m] == ds.server_states[i2].log[m] by {
            assert(li[m] == el[m]);
            assert(li2[m] == el[m]);
        }
    }

    /// What a granted vote from `w` to `d` in term `t` says. `w`'s log had
    /// length `L` when it voted, every entry of `w` below term `t` lies below
    /// `L`, and `d`'s RequestVote summary `(li, lt)` was at least as up to
    /// date as `w`'s log then. The summary describes a real prefix of `d`'s
    /// log below its election length.
    pub proof fn lemma_vote_summary(
        ds: RaftDistributedState, w: int, d: int, t: int, ell: int, x: int,
    ) -> (res: (int, int))
        requires
            WellFormedRaftDistributed(ds),
            VoteLogLenCoversNetwork(ds),
            VoteLogLenBounded(ds),
            VoteLogLenEntryTermBound(ds),
            VoteResponseHasRequestVote(ds),
            VoteGrantedLogUpToDateAtVoteTime(ds),
            RequestVoteSummaryAlwaysValid(ds),
            RequestVoteLastLogTermBound(ds),
            TermsNonNegative(ds),
            SenderIntegrity(ds),
            0 <= w < ds.num_servers,
            0 <= d < ds.num_servers,
            ExistsGrantedVoteResponse(ds, w, d, t),
            0 <= ell <= ds.server_states[d].log.len(),
            forall |m: int| #![trigger ds.server_states[d].log[m]]
                ell <= m < ds.server_states[d].log.len() ==> ds.server_states[d].log[m].term >= t,
            0 <= x < ds.server_states[w].log.len(),
            ds.server_states[w].log[x].term < t,
        ensures ({
            let (li, lt) = res;
            let wl = ds.server_states[w].log;
            let dl = ds.server_states[d].log;
            let big_l = ds.vote_log_len[(w, t)];
            &&& x < big_l <= wl.len()
            &&& 1 <= li <= ell
            &&& dl[li - 1].term == lt
            &&& lt < t
            &&& (lt > wl[big_l - 1].term || (lt == wl[big_l - 1].term && li >= big_l))
        }),
    {
        let wl = ds.server_states[w].log;
        let dl = ds.server_states[d].log;
        let (li0, lt0) = choose |li0: int, lt0: int| #![trigger ds.network.contains(LRaftPacket {
            src: w, dst: d,
            msg: LRaftMessage::VoteResponse {
                term: t, granted: true, voter: w,
                voter_last_log_index: li0, voter_last_log_term: lt0,
            },
        })] ds.network.contains(LRaftPacket {
            src: w, dst: d,
            msg: LRaftMessage::VoteResponse {
                term: t, granted: true, voter: w,
                voter_last_log_index: li0, voter_last_log_term: lt0,
            },
        });
        let vp = LRaftPacket {
            src: w, dst: d,
            msg: LRaftMessage::VoteResponse {
                term: t, granted: true, voter: w,
                voter_last_log_index: li0, voter_last_log_term: lt0,
            },
        };
        assert(ds.network.contains(vp));
        assert(ds.vote_log_len.dom().contains((w, t)));
        let big_l = ds.vote_log_len[(w, t)];
        assert(0 <= big_l <= wl.len());
        if x >= big_l {
            assert(ds.server_states[(w, t).0].log[x].term >= (w, t).1);
        }
        let req = choose |req: LRaftPacket| #![trigger ds.network.contains(req)] {
            &&& ds.network.contains(req)
            &&& req.src == vp.dst
            &&& req.dst == w
            &&& req.msg matches LRaftMessage::RequestVote { term, candidate, last_log_index: _, last_log_term: _ }
            &&& term == t
            &&& candidate == vp.dst
        };
        let li = req.msg->RequestVote_last_log_index;
        let lt = req.msg->RequestVote_last_log_term;
        assert(lt > wl[big_l - 1].term || (lt == wl[big_l - 1].term && li >= big_l));
        assert(0 <= li <= dl.len());
        assert(wl[big_l - 1].term >= 0);
        if li == 0 {
            assert(lt == 0);
        }
        assert(dl[li - 1].term == lt && lt < t);
        if li - 1 >= ell {
            assert(dl[li - 1].term >= t);
        }
        (li, lt)
    }

    /// One step of the completeness argument at the first index `m0` where
    /// `d`'s election log leaves the history. The certificate quorum of `m0`
    /// meets `d`'s voters; the common voter's vote shows `d`'s log ends, below
    /// its election length, in an entry of a term strictly between the
    /// history entry's and `t`.
    pub proof fn lemma_completeness_step(
        ds: RaftDistributedState, d: int, t: int, ell: int, votes: Set<int>, m0: int,
    ) -> (li: int)
        requires
            CompletenessCore(ds),
            UniqueWinnersBelow(ds, t),
            vote_backed(ds, d, t, ell, votes),
            votes.contains(d),
            0 <= m0 < ds.committed_history.len(),
            m0 <= ell,
            ds.committed_history[m0].term < t,
            forall |m: int| #![trigger ds.committed_history[m]]
                0 <= m < m0 ==> ds.server_states[d].log[m] == ds.committed_history[m],
            !(m0 < ell && ds.server_states[d].log[m0] == ds.committed_history[m0]),
        ensures
            1 <= li <= ell,
            ds.committed_history[m0].term < ds.server_states[d].log[li - 1].term < t,
    {
        let h = ds.committed_history;
        let dl = ds.server_states[d].log;
        let initial = initial_membership_phase(ds);
        lemma_election_phase_near(ds, d, ell, m0);
        let z = history_phase_at(ds, m0);
        let e = active_membership_phase_from_raft_log(dl, ell, initial);
        assert(ds.log_commit_certificates.dom().contains(m0));
        assert(certificate_held_at(ds, m0));
        reveal(certificate_held_at);
        let cert = ds.log_commit_certificates[m0];
        assert(cert.entry == h[m0]);
        lemma_legal_phase_progression_quorums_intersect(cert.quorum, votes, z, e);
        let w = choose |w: int| #![trigger votes.contains(w)] cert.quorum.contains(w) && votes.contains(w);
        let wl = ds.server_states[w].log;
        assert(0 <= w < ds.num_servers && wl.len() > m0 && wl[m0] == h[m0]);
        if w == d {
            if m0 >= ell {
                assert(dl[m0].term >= t);
            }
            assert(false);
        }
        let (li, lt) = lemma_vote_summary(ds, w, d, t, ell, m0);
        let big_l = ds.vote_log_len[(w, t)];
        assert(wl[m0].term <= wl[big_l - 1].term);
        if lt == wl[big_l - 1].term && li >= big_l {
            assert(UniqueWinnersBelow(ds, lt + 1));
            lemma_strong_log_matching(ds, w, big_l - 1, d, li - 1);
            assert(wl[m0] == dl[m0]);
            assert(false);
        }
        li
    }

    /// Winner completeness: a vote-backed log of term `t` holds, below its
    /// election length, every committed entry of a lower term.
    pub proof fn lemma_completeness_at(
        ds: RaftDistributedState, d: int, t: int, ell: int, votes: Set<int>, k: int,
    )
        requires
            CompletenessCore(ds),
            UniqueWinnersBelow(ds, t),
            vote_backed(ds, d, t, ell, votes),
            votes.contains(d),
            0 <= k < ds.committed_history.len(),
            ds.committed_history[k].term < t,
        ensures
            k < ell,
            ds.server_states[d].log[k] == ds.committed_history[k],
        decreases t,
    {
        let h = ds.committed_history;
        let dl = ds.server_states[d].log;
        if k < ell && dl[k] == h[k] {
            return;
        }
        let m0 = lemma_first_disagreement(ds, d, ell, k);
        lemma_history_terms_monotone(ds);
        assert(h[m0].term <= h[k].term);
        let li = lemma_completeness_step(ds, d, t, ell, votes, m0);
        let lt = dl[li - 1].term;
        let d2 = lemma_entry_winner(ds, d, li - 1);
        let votes2 = lemma_winner_is_vote_backed(ds, d2, lt);
        let ell2 = ds.election_log_len[(d2, lt)];
        assert(lt >= 0) by {
            assert(TermsNonNegative(ds));
            assert(ds.server_states[d].log[li - 1].term >= 0);
        }
        assert(UniqueWinnersBelow(ds, lt));
        lemma_completeness_at(ds, d2, lt, ell2, votes2, m0);
        let dl2 = ds.server_states[d2].log;
        if li - 1 < ell2 {
            assert(dl2[li - 1].term < lt);
        }
        assert(dl2[li - 1].term == dl[li - 1].term);
        assert(dl2[m0] == dl[m0]);
        assert(false);
    }

} // verus!

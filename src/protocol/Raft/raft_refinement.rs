// Refinement proof: composite LNext refines atomic LNext
//
// Shows that every state transition (s, s') in the new 5-branch composite
// LNext corresponds to either:
//   (a) a stutter step (s' == s),
//   (b) a single step of the old 11-branch atomic LNext, or
//   (c) two consecutive steps of the old atomic LNext.
//
// Cases (a) and (c) are standard in TLA+ refinement (stuttering simulation).

use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use vstd::prelude::*;

verus! {

/// The old 11-branch atomic LNext (before Phase 27.4 composite rewrite).
/// Each branch is an individual atomic spec action.
pub open spec fn LNextAtomic(s: LState, s_: LState, c: LConstants) -> bool {
    ||| exists |sent_packets: Seq<LRaftMessage>|
            LTimeout(s, s_, c, sent_packets)
    ||| exists |new_term: int, sent_packets: Seq<LRaftMessage>|
            LStepDown(s, s_, c, new_term, sent_packets)
    ||| exists |ct: int, cllt: int, clli: int, cid: int, sent_packets: Seq<LRaftMessage>|
            LGrantVote(s, s_, c, ct, cllt, clli, cid, sent_packets)
    ||| exists |vt: int, vg: bool, v: int, sent_packets: Seq<LRaftMessage>|
            LReceiveVoteGranted(s, s_, c, vt, vg, v, sent_packets)
    ||| exists |sent_packets: Seq<LRaftMessage>|
            LBecomeLeader(s, s_, c, sent_packets)
    ||| exists |value: int, sent_packets: Seq<LRaftMessage>|
            LClientRequest(s, s_, c, value, sent_packets)
    ||| exists |f: int, ev: int, pli: int, plt: int, he: bool, sent_packets: Seq<LRaftMessage>|
            LSendAppendEntries(s, s_, c, f, ev, pli, plt, he, sent_packets)
    ||| exists |at: int, al: int, api: int, apt: int, av: int, ahe: bool, alc: int,
               sent_packets: Seq<LRaftMessage>|
            LFollowerAppendEntries(s, s_, c, at, al, api, apt, av, ahe, alc, sent_packets)
    ||| exists |rt: int, rs: bool, rmi: int, rf: int, f: u64, nmi: u64,
               sent_packets: Seq<LRaftMessage>|
            LHandleAppendResponse(s, s_, c, rt, rs, rmi, rf, f, nmi, sent_packets)
    ||| exists |rt: int, rs: bool, rmi: int, rf: int, f: u64,
               sent_packets: Seq<LRaftMessage>|
            LHandleAppendReject(s, s_, c, rt, rs, rmi, rf, f, sent_packets)
    ||| exists |nci: int, sent_packets: Seq<LRaftMessage>|
            LAdvanceCommitIndex(s, s_, c, nci, sent_packets)
}

/// Refinement relation: every composite step maps to stutter, one atomic step,
/// or two consecutive atomic steps.
pub open spec fn refines_atomic(s: LState, s_: LState, c: LConstants) -> bool {
    ||| s_ == s  // stutter
    ||| LNextAtomic(s, s_, c)  // single step
    ||| (exists |s_mid: LState|  // two steps
            LNextAtomic(s, s_mid, c) && LNextAtomic(s_mid, s_, c))
}

// ---------------------------------------------------------------
// Per-handler refinement lemmas
// ---------------------------------------------------------------

/// LHandleRequestVoteMsg refines to stutter, LStepDown, LGrantVote,
/// or LStepDown followed by LGrantVote.
proof fn lemma_handle_request_vote_refines(
    s: LState, s_: LState, c: LConstants,
    term: int, candidate_id: int, last_log_index: int, last_log_term: int,
    sent_packets: Seq<LRaftMessage>,
)
requires
    LHandleRequestVoteMsg(s, s_, c, term, candidate_id, last_log_index,
                          last_log_term, sent_packets),
ensures
    refines_atomic(s, s_, c),
{
    let s_mid = step_down_if_needed(s, term);

    let empty = Seq::<LRaftMessage>::empty();
    if term > s.current_term {
        // Step-down occurred: s_mid != s
        if term < s_mid.current_term {
            // Impossible: s_mid.current_term == term
            assert(false);
        } else if s_mid.has_voted && s_mid.voted_for != candidate_id {
            // Guard failure: s_ == s_mid = step_down result
            assert(LStepDown(s, s_, c, term, empty));
            assert(LNextAtomic(s, s_, c));
        } else if !log_up_to_date(s_mid, last_log_term, last_log_index) {
            // Guard failure: s_ == s_mid = step_down result
            assert(LStepDown(s, s_, c, term, empty));
            assert(LNextAtomic(s, s_, c));
        } else {
            // Step-down + grant-vote: two-step refinement
            // Witness: s_mid is the intermediate state
            assert(LStepDown(s, s_mid, c, term, empty));
            assert(LNextAtomic(s, s_mid, c));
            assert(LGrantVote(s_mid, s_, c, term, last_log_term, last_log_index,
                              candidate_id, sent_packets));
            assert(LNextAtomic(s_mid, s_, c));
            assert(LNextAtomic(s, s_mid, c) && LNextAtomic(s_mid, s_, c));
        }
    } else {
        // No step-down: s_mid == s
        if term < s.current_term {
            // s_ == s: stutter
            assert(s_ == s);
        } else if s.has_voted && s.voted_for != candidate_id {
            // s_ == s: stutter
            assert(s_ == s);
        } else if !log_up_to_date(s, last_log_term, last_log_index) {
            // s_ == s: stutter
            assert(s_ == s);
        } else {
            // Direct grant-vote
            assert(LGrantVote(s, s_, c, term, last_log_term, last_log_index,
                              candidate_id, sent_packets));
            assert(LNextAtomic(s, s_, c));
        }
    }
}

/// LHandleAppendEntriesMsg refines to stutter, LStepDown,
/// or LFollowerAppendEntries (which handles step-down internally).
proof fn lemma_handle_append_entries_refines(
    s: LState, s_: LState, c: LConstants,
    ae_term: int, ae_leader: int, ae_prev_index: int, ae_prev_term: int,
    ae_value: int, ae_has_entry: bool, ae_leader_commit: int,
    sent_packets: Seq<LRaftMessage>,
)
requires
    LHandleAppendEntriesMsg(s, s_, c, ae_term, ae_leader, ae_prev_index,
                            ae_prev_term, ae_value, ae_has_entry,
                            ae_leader_commit, sent_packets),
ensures
    refines_atomic(s, s_, c),
{
    let s_mid = step_down_if_needed(s, ae_term);

    if ae_term < s_mid.current_term {
        // Rejection: stale term, s_ == s_mid
        if ae_term > s.current_term {
            // Step-down occurred but term is still stale (impossible:
            // s_mid.current_term == ae_term, so ae_term < ae_term is false)
            assert(false);
        } else {
            // No step-down, s_mid == s, s_ == s: stutter
            assert(s_ == s);
        }
    } else if ae_prev_index > 0 && (
        ae_prev_index > s_mid.log.len()
        || s_mid.log[ae_prev_index - 1].term != ae_prev_term
    ) {
        // Rejection: prev_log consistency check failed, s_ == s_mid
        let empty = Seq::<LRaftMessage>::empty();
        if ae_term > s.current_term {
            // Step-down occurred: s_ == s_mid = step_down_if_needed(s, ae_term)
            // LStepDown's sent_packets is existentially quantified in LNextAtomic,
            // so we witness with empty (the actual rejection packet is irrelevant).
            assert(LStepDown(s, s_, c, ae_term, empty));
            assert(LNextAtomic(s, s_, c));
        } else {
            // No step-down, s_mid == s, s_ == s: stutter
            assert(s_ == s);
        }
    } else if ae_has_entry && ae_prev_index != s_mid.log.len() {
        // Rejection: log index mismatch, s_ == s_mid
        let empty = Seq::<LRaftMessage>::empty();
        if ae_term > s.current_term {
            assert(LStepDown(s, s_, c, ae_term, empty));
            assert(LNextAtomic(s, s_, c));
        } else {
            assert(s_ == s);
        }
    } else {
        // Accepted: LFollowerAppendEntries(s_mid, s_, ...)
        // The atomic LFollowerAppendEntries handles step-down internally,
        // so LFollowerAppendEntries(s, s_, ...) produces the same result.
        assert(LFollowerAppendEntries(s, s_, c, ae_term, ae_leader, ae_prev_index,
                                      ae_prev_term, ae_value, ae_has_entry,
                                      ae_leader_commit, sent_packets));
        assert(LNextAtomic(s, s_, c));
    }
}

/// LHandleVoteResponseMsg refines to stutter, LStepDown,
/// LReceiveVoteGranted, or LReceiveVoteGranted + LBecomeLeader.
proof fn lemma_handle_vote_response_refines(
    s: LState, s_: LState, c: LConstants,
    term: int, granted: bool, voter: int,
    sent_packets: Seq<LRaftMessage>,
)
requires
    LHandleVoteResponseMsg(s, s_, c, term, granted, voter, sent_packets),
ensures
    refines_atomic(s, s_, c),
{
    let s_mid = step_down_if_needed(s, term);
    let empty = Seq::<LRaftMessage>::empty();

    if term > s.current_term {
        // Step-down occurred: s_mid.role is Follower, not Candidate
        // So the guard !(s_mid.role is Candidate) is true → s_ == s_mid
        assert(LStepDown(s, s_, c, term, empty));
        assert(LNextAtomic(s, s_, c));
    } else {
        // No step-down: s_mid == s
        if !(s_mid.role is Candidate) || term < s_mid.current_term
           || !granted || !c.servers.contains(voter) {
            // Guard failure (including stale term): s_ == s: stutter
            assert(s_ == s);
        } else {
            // Add vote
            let s_voted = LState {
                votes_granted: s_mid.votes_granted.insert(voter),
                ..s_mid
            };
            if s_voted.votes_granted.len() >= c.quorum_size {
                // Quorum reached: ReceiveVoteGranted + BecomeLeader (two steps)
                assert(LReceiveVoteGranted(s, s_voted, c, term, granted, voter, empty));
                assert(LNextAtomic(s, s_voted, c));
                assert(LBecomeLeader(s_voted, s_, c, empty));
                assert(LNextAtomic(s_voted, s_, c));
                assert(LNextAtomic(s, s_voted, c) && LNextAtomic(s_voted, s_, c));
            } else {
                // Below quorum: just ReceiveVoteGranted
                assert(LReceiveVoteGranted(s, s_, c, term, granted, voter, empty));
                assert(LNextAtomic(s, s_, c));
            }
        }
    }
}

/// LHandleAppendResponseMsg refines to stutter, LStepDown,
/// LHandleAppendResponse, or LHandleAppendReject.
proof fn lemma_handle_append_response_refines(
    s: LState, s_: LState, c: LConstants,
    term: int, success: bool, match_index: int, follower_id: int,
    sent_packets: Seq<LRaftMessage>,
)
requires
    LHandleAppendResponseMsg(s, s_, c, term, success, match_index,
                              follower_id, sent_packets),
ensures
    refines_atomic(s, s_, c),
{
    let s_mid = step_down_if_needed(s, term);

    let empty = Seq::<LRaftMessage>::empty();
    if term > s.current_term {
        // Step-down: s_mid.role is Follower, not Leader → s_ == s_mid
        assert(LStepDown(s, s_, c, term, empty));
        assert(LNextAtomic(s, s_, c));
    } else {
        // No step-down: s_mid == s
        if !(s_mid.role is Leader) || !c.servers.contains(follower_id) {
            // Guard failure: stutter
            assert(s_ == s);
        } else if success {
            let follower = follower_id as u64;
            let new_match_index = match_index as u64;
            if new_match_index as int > s_mid.log.len() {
                // Out of bounds: stutter
                assert(s_ == s);
            } else {
                // Success: direct match
                assert(LHandleAppendResponse(s, s_, c, term, success, match_index,
                                              follower_id, follower, new_match_index,
                                              sent_packets));
                assert(LNextAtomic(s, s_, c));
            }
        } else {
            // Reject: direct match
            let follower = follower_id as u64;
            assert(LHandleAppendReject(s, s_, c, term, success, match_index,
                                        follower_id, follower, sent_packets));
            assert(LNextAtomic(s, s_, c));
        }
    }
}

/// LTryAdvanceCommitIndex refines to stutter or LAdvanceCommitIndex.
proof fn lemma_try_advance_commit_index_refines(
    s: LState, s_: LState, c: LConstants,
    new_commit_index: int,
    sent_packets: Seq<LRaftMessage>,
)
requires
    LTryAdvanceCommitIndex(s, s_, c, new_commit_index, sent_packets),
ensures
    refines_atomic(s, s_, c),
{
    if !(s.role is Leader) || new_commit_index <= s.commit_index {
        // Guard failure: stutter (s_ == s)
        assert(s_ == s);
    } else {
        // Valid: direct match to LAdvanceCommitIndex
        assert(LAdvanceCommitIndex(s, s_, c, new_commit_index, sent_packets));
        assert(LNextAtomic(s, s_, c));
    }
}

// ---------------------------------------------------------------
// Main refinement theorem
// ---------------------------------------------------------------

/// Every step of the composite LNext refines to stutter or
/// one/two steps of the atomic LNextAtomic.
proof fn lemma_lnext_refines_atomic(s: LState, s_: LState, c: LConstants)
requires
    LNext(s, s_, c),
ensures
    refines_atomic(s, s_, c),
{
    // LNext is a disjunction; Verus should split on which branch holds.
    // Branches 1-3 (LTimeout, LClientRequest, LSendAppendEntries) are
    // unchanged between old and new LNext, so they directly satisfy
    // LNextAtomic.
    //
    // Branch 4 (LHandleMessage) dispatches to per-handler lemmas.
    // Branch 5 (LTryAdvanceCommitIndex) delegates to its lemma.

    // For the existentially quantified branches, we need to instantiate
    // witnesses. Verus should handle this via the choose operator.

    if exists |sent_packets: Seq<LRaftMessage>| LTimeout(s, s_, c, sent_packets) {
        // Direct match to LNextAtomic
    } else if exists |value: int, sent_packets: Seq<LRaftMessage>|
                  LClientRequest(s, s_, c, value, sent_packets) {
        // Direct match to LNextAtomic
    } else if exists |follower: int, entry_value: int, prev_log_index: int,
                      prev_log_term: int, has_entry: bool,
                      sent_packets: Seq<LRaftMessage>|
                  LSendAppendEntries(s, s_, c, follower, entry_value, prev_log_index,
                                     prev_log_term, has_entry, sent_packets) {
        // Direct match to LNextAtomic
    } else if exists |msg: LRaftMessage, sent_packets: Seq<LRaftMessage>|
                  LHandleMessage(s, s_, c, msg, sent_packets) {
        // LHandleMessage dispatches based on message type
        let pair = choose |msg: LRaftMessage, sent_packets: Seq<LRaftMessage>|
                       LHandleMessage(s, s_, c, msg, sent_packets);
        let msg = pair.0;
        let sent_packets = pair.1;
        match msg {
            LRaftMessage::RequestVote { term, candidate, last_log_index, last_log_term } => {
                lemma_handle_request_vote_refines(
                    s, s_, c, term, candidate, last_log_index, last_log_term, sent_packets);
            }
            LRaftMessage::VoteResponse { term, granted, voter, .. } => {
                lemma_handle_vote_response_refines(
                    s, s_, c, term, granted, voter, sent_packets);
            }
            LRaftMessage::AppendEntries { term, leader, prev_index, prev_term,
                                          value, has_entry, leader_commit } => {
                lemma_handle_append_entries_refines(
                    s, s_, c, term, leader, prev_index, prev_term,
                    value, has_entry, leader_commit, sent_packets);
            }
            LRaftMessage::AppendResponse { term, success, match_index, follower } => {
                lemma_handle_append_response_refines(
                    s, s_, c, term, success, match_index, follower, sent_packets);
            }
        }
    } else {
        // LTryAdvanceCommitIndex
        let pair = choose |nci: int, sent_packets: Seq<LRaftMessage>|
                       LTryAdvanceCommitIndex(s, s_, c, nci, sent_packets);
        let new_commit_index = pair.0;
        let sent_packets = pair.1;
        lemma_try_advance_commit_index_refines(
            s, s_, c, new_commit_index, sent_packets);
    }
}

} // verus!

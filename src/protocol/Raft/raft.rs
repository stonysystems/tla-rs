use crate::protocol::Raft::types::*;
use vstd::prelude::*;

verus! {
    /// Helper: increment a u64 by 1 in spec mode, staying in u64
    pub open spec fn u64_inc(x: u64) -> u64 { (x + 1) as u64 }
    /// Helper: decrement a u64 by 1 in spec mode, staying in u64
    pub open spec fn u64_dec(x: u64) -> u64 { (x - 1) as u64 }

    /// Initialize the Raft protocol state
    /// Server starts as Follower with empty log, no votes, term 0
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.current_term == 0int
        &&& s.role is Follower
        &&& s.has_voted == false
        &&& s.voted_for == 0int
        &&& s.log == Seq::<LLogEntry>::empty()
        &&& s.commit_index == 0int
        &&& s.votes_granted == Set::<int>::empty()
        &&& s.match_index == Map::<u64, u64>::empty()
        &&& s.next_index == Map::<u64, u64>::empty()
    }

    /// Timeout: a Follower or Candidate starts a new election
    /// Increments term, becomes Candidate, votes for self, sends RequestVote
    pub open spec fn LTimeout(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LRaftMessage>) -> bool {
        &&& s.role is Follower || s.role is Candidate
        &&& s_.current_term == s.current_term + 1
        &&& s_.role is Candidate
        &&& s_.has_voted == true
        &&& s_.voted_for == c.my_id
        &&& s_.log == s.log
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == Set::<int>::empty().insert(c.my_id)
        &&& s_.match_index == s.match_index
        &&& s_.next_index == s.next_index
        &&& sent_packets == seq![LRaftMessage::RequestVote {
            term: s.current_term + 1,
            candidate: c.my_id,
            last_log_index: 0,
            last_log_term: 0,
        }]
    }

    /// Grant a vote to a candidate and send VoteResponse
    pub open spec fn LGrantVote(
        s: LState, s_: LState, c: LConstants,
        candidate_term: int, candidate_last_log_term: int, candidate_last_log_index: int,
        candidate_id: int, sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        &&& candidate_term >= s.current_term
        &&& !s.has_voted || s.voted_for == candidate_id
        // State updates
        &&& s_.current_term == candidate_term
        &&& s_.role is Follower
        &&& s_.has_voted == true
        &&& s_.voted_for == candidate_id
        &&& s_.log == s.log
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == s.votes_granted
        &&& s_.match_index == s.match_index
        &&& s_.next_index == s.next_index
        &&& sent_packets == seq![LRaftMessage::VoteResponse {
            term: candidate_term,
            granted: true,
            voter: c.my_id,
        }]
    }

    /// Receive a vote granted response
    pub open spec fn LReceiveVoteGranted(
        s: LState, s_: LState, c: LConstants,
        vote_term: int, vote_granted: bool, voter: int, sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        &&& s.role is Candidate
        &&& vote_granted == true
        &&& c.servers.contains(voter)
        &&& s_.current_term == s.current_term
        &&& s_.role == s.role
        &&& s_.has_voted == s.has_voted
        &&& s_.voted_for == s.voted_for
        &&& s_.log == s.log
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == s.votes_granted.insert(voter)
        &&& s_.match_index == s.match_index
        &&& s_.next_index == s.next_index
        &&& sent_packets == Seq::<LRaftMessage>::empty()
    }

    /// Become leader after receiving a quorum of votes
    /// Initializes match_index and next_index. Uses Set::len() for quorum check.
    pub open spec fn LBecomeLeader(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LRaftMessage>) -> bool {
        &&& s.role is Candidate
        &&& s.votes_granted.len() >= c.quorum_size
        &&& s_.current_term == s.current_term
        &&& s_.role is Leader
        &&& s_.has_voted == s.has_voted
        &&& s_.voted_for == s.voted_for
        &&& s_.log == s.log
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == s.votes_granted
        &&& s_.match_index == Map::<u64, u64>::empty()
        &&& s_.next_index == Map::<u64, u64>::empty()
        &&& sent_packets == Seq::<LRaftMessage>::empty()
    }

    /// Client request: leader appends a new entry to its log
    pub open spec fn LClientRequest(
        s: LState, s_: LState, c: LConstants, value: int, sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        &&& s.role is Leader
        &&& s_.current_term == s.current_term
        &&& s_.role == s.role
        &&& s_.has_voted == s.has_voted
        &&& s_.voted_for == s.voted_for
        &&& s_.log == s.log.push(LLogEntry { term: s.current_term, value: value })
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == s.votes_granted
        &&& s_.match_index == s.match_index
        &&& s_.next_index == s.next_index
        &&& sent_packets == Seq::<LRaftMessage>::empty()
    }

    /// Leader sends AppendEntries to a follower
    /// Sends entries starting from the next_index for that follower
    pub open spec fn LSendAppendEntries(
        s: LState, s_: LState, c: LConstants,
        follower: int, entry_value: int, prev_log_index: int, prev_log_term: int,
        has_entry: bool, sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        &&& s.role is Leader
        &&& c.servers.contains(follower)
        // Frame
        &&& s_.current_term == s.current_term
        &&& s_.role == s.role
        &&& s_.has_voted == s.has_voted
        &&& s_.voted_for == s.voted_for
        &&& s_.log == s.log
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == s.votes_granted
        &&& s_.match_index == s.match_index
        &&& s_.next_index == s.next_index
        &&& sent_packets == seq![LRaftMessage::AppendEntries {
            term: s.current_term,
            leader: c.my_id,
            prev_index: prev_log_index,
            prev_term: prev_log_term,
            value: entry_value,
            has_entry: has_entry,
            leader_commit: s.commit_index,
        }]
    }

    /// Follower handles AppendEntries: accepts entries if term >= current_term
    /// Simplified: appends single entry if has_entry, updates commit_index
    pub open spec fn LFollowerAppendEntries(
        s: LState, s_: LState, c: LConstants,
        ae_term: int, ae_leader: int, ae_prev_index: int, ae_prev_term: int,
        ae_value: int, ae_has_entry: bool, ae_leader_commit: int,
        sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        &&& ae_term >= s.current_term
        // Accept: step down to follower if needed, append entry
        &&& s_.current_term == ae_term
        &&& s_.role is Follower
        &&& s_.has_voted == (if ae_term > s.current_term { false } else { s.has_voted })
        &&& s_.voted_for == (if ae_term > s.current_term { 0int } else { s.voted_for })
        &&& s_.log == (if ae_has_entry {
            s.log.push(LLogEntry { term: ae_term, value: ae_value })
        } else { s.log })
        &&& s_.commit_index == (if ae_leader_commit > s.commit_index {
            ae_leader_commit
        } else { s.commit_index })
        &&& s_.votes_granted == (if ae_term > s.current_term {
            Set::<int>::empty()
        } else { s.votes_granted })
        &&& s_.match_index == s.match_index
        &&& s_.next_index == s.next_index
        &&& sent_packets == seq![LRaftMessage::AppendResponse {
            term: ae_term,
            success: true,
            match_index: (if ae_has_entry {
                s.log.len() as int + 1
            } else { s.log.len() as int }),
            follower: c.my_id,
        }]
    }

    /// Handle a successful AppendEntries response from a follower
    /// Updates match_index and next_index for the responding server
    pub open spec fn LHandleAppendResponse(
        s: LState, s_: LState, c: LConstants,
        resp_term: int, resp_success: bool, resp_match_index: int, resp_follower: int,
        follower: u64, new_match_index: u64, sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        &&& s.role is Leader
        &&& resp_success == true
        &&& c.servers.contains(follower as int)
        &&& new_match_index as int >= 0int
        &&& new_match_index as int <= s.log.len()
        &&& s_.current_term == s.current_term
        &&& s_.role == s.role
        &&& s_.has_voted == s.has_voted
        &&& s_.voted_for == s.voted_for
        &&& s_.log == s.log
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == s.votes_granted
        &&& s_.match_index == s.match_index.insert(follower, new_match_index)
        &&& s_.next_index == s.next_index.insert(follower, u64_inc(new_match_index))
        &&& sent_packets == Seq::<LRaftMessage>::empty()
    }

    /// Handle a failed AppendEntries response: backtrack next_index
    pub open spec fn LHandleAppendReject(
        s: LState, s_: LState, c: LConstants,
        resp_term: int, resp_success: bool, resp_match_index: int, resp_follower: int,
        follower: u64, sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        &&& s.role is Leader
        &&& resp_success == false
        &&& c.servers.contains(follower as int)
        // Backtrack next_index for this follower
        &&& s_.next_index == (if s.next_index.dom().contains(follower) && s.next_index[follower] > 0 {
            s.next_index.insert(follower, u64_dec(s.next_index[follower]))
        } else {
            s.next_index
        })
        // Frame
        &&& s_.current_term == s.current_term
        &&& s_.role == s.role
        &&& s_.has_voted == s.has_voted
        &&& s_.voted_for == s.voted_for
        &&& s_.log == s.log
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == s.votes_granted
        &&& s_.match_index == s.match_index
        &&& sent_packets == Seq::<LRaftMessage>::empty()
    }

    /// Advance commit index: leader commits entries replicated on a quorum
    pub open spec fn LAdvanceCommitIndex(
        s: LState, s_: LState, c: LConstants,
        new_commit_index: int, sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        &&& s.role is Leader
        &&& new_commit_index > s.commit_index
        &&& new_commit_index <= s.log.len()
        &&& s.log[new_commit_index - 1].term == s.current_term
        &&& s_.current_term == s.current_term
        &&& s_.role == s.role
        &&& s_.has_voted == s.has_voted
        &&& s_.voted_for == s.voted_for
        &&& s_.log == s.log
        &&& s_.commit_index == new_commit_index
        &&& s_.votes_granted == s.votes_granted
        &&& s_.match_index == s.match_index
        &&& s_.next_index == s.next_index
        &&& sent_packets == Seq::<LRaftMessage>::empty()
    }

    /// Step down: a server discovers a higher term and becomes Follower
    pub open spec fn LStepDown(
        s: LState, s_: LState, c: LConstants, new_term: int, sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        &&& new_term > s.current_term
        &&& s_.current_term == new_term
        &&& s_.role is Follower
        &&& s_.has_voted == false
        &&& s_.voted_for == 0int
        &&& s_.log == s.log
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == Set::<int>::empty()
        &&& s_.match_index == s.match_index
        &&& s_.next_index == s.next_index
        &&& sent_packets == Seq::<LRaftMessage>::empty()
    }

    // ---------------------------------------------------------------
    // Composite message handlers (Phase 27.1)
    //
    // Each incorporates step-down + guard checks + state transition
    // into a single action, matching the host.rs handler logic.
    // Guard failure yields s_ == s_mid && sent_packets == empty.
    // ---------------------------------------------------------------

    /// Spec helper: compute step-down intermediate state.
    /// If new_term > current_term, become Follower and reset voting state.
    /// Otherwise, return s unchanged.
    pub open spec fn step_down_if_needed(s: LState, new_term: int) -> LState {
        if new_term > s.current_term {
            LState {
                current_term: new_term,
                role: LServerRole::Follower,
                has_voted: false,
                voted_for: 0int,
                votes_granted: Set::<int>::empty(),
                ..s
            }
        } else {
            s
        }
    }

    /// Spec helper: check if candidate's log is at least as up-to-date as ours.
    pub open spec fn log_up_to_date(
        s: LState, candidate_last_log_term: int, candidate_last_log_index: int,
    ) -> bool {
        let my_last_log_term: int = if s.log.len() == 0 {
            0int
        } else {
            s.log[s.log.len() - 1].term
        };
        candidate_last_log_term > my_last_log_term
            || (candidate_last_log_term == my_last_log_term
                && candidate_last_log_index >= s.log.len())
    }

    /// Handle RequestVote: step down if higher term, check guards, grant vote or no-op.
    pub open spec fn LHandleRequestVoteMsg(
        s: LState, s_: LState, c: LConstants,
        term: int, candidate_id: int, last_log_index: int, last_log_term: int,
        sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        let s_mid = step_down_if_needed(s, term);
        if term < s_mid.current_term {
            // Stale term after possible step-down: no-op
            &&& s_ == s_mid
            &&& sent_packets == Seq::<LRaftMessage>::empty()
        } else if s_mid.has_voted && s_mid.voted_for != candidate_id {
            // Already voted for different candidate: no-op
            &&& s_ == s_mid
            &&& sent_packets == Seq::<LRaftMessage>::empty()
        } else if !log_up_to_date(s_mid, last_log_term, last_log_index) {
            // Candidate's log not up-to-date: no-op
            &&& s_ == s_mid
            &&& sent_packets == Seq::<LRaftMessage>::empty()
        } else {
            // All guards pass: grant vote
            LGrantVote(s_mid, s_, c, term, last_log_term, last_log_index,
                       candidate_id, sent_packets)
        }
    }

    /// Handle AppendEntries: step down if higher term, check guards, append or reject.
    pub open spec fn LHandleAppendEntriesMsg(
        s: LState, s_: LState, c: LConstants,
        ae_term: int, ae_leader: int, ae_prev_index: int, ae_prev_term: int,
        ae_value: int, ae_has_entry: bool, ae_leader_commit: int,
        sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        let s_mid = step_down_if_needed(s, ae_term);
        if ae_term < s_mid.current_term {
            // Stale term: send failure response
            &&& s_ == s_mid
            &&& sent_packets == seq![LRaftMessage::AppendResponse {
                term: s_mid.current_term,
                success: false,
                match_index: 0int,
                follower: c.my_id,
            }]
        } else {
            // Accept: delegate to atomic follower append entries
            LFollowerAppendEntries(s_mid, s_, c, ae_term, ae_leader, ae_prev_index,
                                   ae_prev_term, ae_value, ae_has_entry,
                                   ae_leader_commit, sent_packets)
        }
    }

    /// Handle VoteResponse: step down if higher term, add vote, check quorum, become leader.
    pub open spec fn LHandleVoteResponseMsg(
        s: LState, s_: LState, c: LConstants,
        term: int, granted: bool, voter: int,
        sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        let s_mid = step_down_if_needed(s, term);
        if !(s_mid.role is Candidate) {
            // Not a candidate (stepped down or was follower/leader): no-op
            &&& s_ == s_mid
            &&& sent_packets == Seq::<LRaftMessage>::empty()
        } else if !granted {
            // Vote denied: no-op
            &&& s_ == s_mid
            &&& sent_packets == Seq::<LRaftMessage>::empty()
        } else if !c.servers.contains(voter) {
            // Unknown voter: no-op
            &&& s_ == s_mid
            &&& sent_packets == Seq::<LRaftMessage>::empty()
        } else {
            // Add vote, then check quorum
            let s_voted = LState {
                votes_granted: s_mid.votes_granted.insert(voter),
                ..s_mid
            };
            if s_voted.votes_granted.len() >= c.quorum_size {
                // Quorum reached: become leader
                &&& s_.current_term == s_voted.current_term
                &&& s_.role is Leader
                &&& s_.has_voted == s_voted.has_voted
                &&& s_.voted_for == s_voted.voted_for
                &&& s_.log == s_voted.log
                &&& s_.commit_index == s_voted.commit_index
                &&& s_.votes_granted == s_voted.votes_granted
                &&& s_.match_index == Map::<u64, u64>::empty()
                &&& s_.next_index == Map::<u64, u64>::empty()
                &&& sent_packets == Seq::<LRaftMessage>::empty()
            } else {
                // Below quorum: stay candidate with updated votes
                &&& s_ == s_voted
                &&& sent_packets == Seq::<LRaftMessage>::empty()
            }
        }
    }

    /// Handle AppendResponse: step down if higher term, update match/next_index or backtrack.
    pub open spec fn LHandleAppendResponseMsg(
        s: LState, s_: LState, c: LConstants,
        term: int, success: bool, match_index: int, follower_id: int,
        sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        let s_mid = step_down_if_needed(s, term);
        if !(s_mid.role is Leader) {
            // Not leader (stepped down): no-op
            &&& s_ == s_mid
            &&& sent_packets == Seq::<LRaftMessage>::empty()
        } else if !c.servers.contains(follower_id) {
            // Unknown follower: no-op
            &&& s_ == s_mid
            &&& sent_packets == Seq::<LRaftMessage>::empty()
        } else if success {
            // Success path: update match_index and next_index
            let follower = follower_id as u64;
            let new_match_index = match_index as u64;
            if new_match_index as int > s_mid.log.len() {
                // match_index out of bounds: no-op
                &&& s_ == s_mid
                &&& sent_packets == Seq::<LRaftMessage>::empty()
            } else {
                LHandleAppendResponse(s_mid, s_, c, term, success, match_index,
                                      follower_id, follower, new_match_index,
                                      sent_packets)
            }
        } else {
            // Failure path: backtrack next_index
            let follower = follower_id as u64;
            LHandleAppendReject(s_mid, s_, c, term, success, match_index,
                                follower_id, follower, sent_packets)
        }
    }

    /// Next-state relation: disjunction of all possible transitions
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| exists |sent_packets: Seq<LRaftMessage>| LTimeout(s, s_, c, sent_packets)
        ||| exists |candidate_term: int, candidate_last_log_term: int,
                    candidate_last_log_index: int, candidate_id: int,
                    sent_packets: Seq<LRaftMessage>|
                LGrantVote(s, s_, c, candidate_term, candidate_last_log_term,
                           candidate_last_log_index, candidate_id, sent_packets)
        ||| exists |vote_term: int, vote_granted: bool, voter: int,
                    sent_packets: Seq<LRaftMessage>|
                LReceiveVoteGranted(s, s_, c, vote_term, vote_granted, voter, sent_packets)
        ||| exists |sent_packets: Seq<LRaftMessage>| LBecomeLeader(s, s_, c, sent_packets)
        ||| exists |value: int, sent_packets: Seq<LRaftMessage>|
                LClientRequest(s, s_, c, value, sent_packets)
        ||| exists |follower: int, entry_value: int, prev_log_index: int, prev_log_term: int,
                    sent_packets: Seq<LRaftMessage>|
                LSendAppendEntries(s, s_, c, follower, entry_value, prev_log_index, prev_log_term, true, sent_packets)
        ||| exists |ae_term: int, ae_leader: int, ae_prev_index: int, ae_prev_term: int,
                    ae_value: int, ae_has_entry: bool, ae_leader_commit: int,
                    sent_packets: Seq<LRaftMessage>|
                LFollowerAppendEntries(s, s_, c, ae_term, ae_leader, ae_prev_index, ae_prev_term,
                                       ae_value, ae_has_entry, ae_leader_commit, sent_packets)
        ||| exists |resp_term: int, resp_success: bool, resp_match_index: int, resp_follower: int,
                    follower: u64, new_match_index: u64,
                    sent_packets: Seq<LRaftMessage>|
                LHandleAppendResponse(s, s_, c, resp_term, resp_success, resp_match_index, resp_follower,
                                      follower, new_match_index, sent_packets)
        ||| exists |resp_term: int, resp_success: bool, resp_match_index: int, resp_follower: int,
                    follower: u64, sent_packets: Seq<LRaftMessage>|
                LHandleAppendReject(s, s_, c, resp_term, resp_success, resp_match_index, resp_follower,
                                    follower, sent_packets)
        ||| exists |new_commit_index: int, sent_packets: Seq<LRaftMessage>|
                LAdvanceCommitIndex(s, s_, c, new_commit_index, sent_packets)
        ||| exists |new_term: int, sent_packets: Seq<LRaftMessage>|
                LStepDown(s, s_, c, new_term, sent_packets)
    }
}

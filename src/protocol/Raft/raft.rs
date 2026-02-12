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
        &&& s.msgs_request_vote == false
        &&& s.msgs_request_vote_term == 0
        &&& s.msgs_request_vote_candidate == 0
        &&& s.msgs_request_vote_last_log_index == 0
        &&& s.msgs_request_vote_last_log_term == 0
        &&& s.msgs_vote_response == false
        &&& s.msgs_vote_response_term == 0
        &&& s.msgs_vote_response_granted == false
        &&& s.msgs_vote_response_voter == 0
        &&& s.msgs_append_entries == false
        &&& s.msgs_append_entries_term == 0
        &&& s.msgs_append_entries_leader == 0
        &&& s.msgs_append_entries_prev_index == 0
        &&& s.msgs_append_entries_prev_term == 0
        &&& s.msgs_append_entries_value == 0
        &&& s.msgs_append_entries_has_entry == false
        &&& s.msgs_append_entries_leader_commit == 0
        &&& s.msgs_append_response == false
        &&& s.msgs_append_response_term == 0
        &&& s.msgs_append_response_success == false
        &&& s.msgs_append_response_match_index == 0
        &&& s.msgs_append_response_follower == 0
    }

    /// Timeout: a Follower or Candidate starts a new election
    /// Increments term, becomes Candidate, votes for self, sends RequestVote
    pub open spec fn LTimeout(s: LState, s_: LState, c: LConstants) -> bool {
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
        // Send RequestVote message
        &&& s_.msgs_request_vote == true
        &&& s_.msgs_request_vote_term == s.current_term + 1
        &&& s_.msgs_request_vote_candidate == c.my_id
        &&& s_.msgs_request_vote_last_log_index == 0
        &&& s_.msgs_request_vote_last_log_term == 0
        // Clear other messages
        &&& s_.msgs_vote_response == false
        &&& s_.msgs_vote_response_term == 0
        &&& s_.msgs_vote_response_granted == false
        &&& s_.msgs_vote_response_voter == 0
        &&& s_.msgs_append_entries == s.msgs_append_entries
        &&& s_.msgs_append_entries_term == s.msgs_append_entries_term
        &&& s_.msgs_append_entries_leader == s.msgs_append_entries_leader
        &&& s_.msgs_append_entries_prev_index == s.msgs_append_entries_prev_index
        &&& s_.msgs_append_entries_prev_term == s.msgs_append_entries_prev_term
        &&& s_.msgs_append_entries_value == s.msgs_append_entries_value
        &&& s_.msgs_append_entries_has_entry == s.msgs_append_entries_has_entry
        &&& s_.msgs_append_entries_leader_commit == s.msgs_append_entries_leader_commit
        &&& s_.msgs_append_response == s.msgs_append_response
        &&& s_.msgs_append_response_term == s.msgs_append_response_term
        &&& s_.msgs_append_response_success == s.msgs_append_response_success
        &&& s_.msgs_append_response_match_index == s.msgs_append_response_match_index
        &&& s_.msgs_append_response_follower == s.msgs_append_response_follower
    }

    /// Grant a vote to a candidate and send VoteResponse
    pub open spec fn LGrantVote(
        s: LState, s_: LState, c: LConstants,
        candidate_term: int, candidate_last_log_term: int, candidate_last_log_index: int,
        candidate_id: int,
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
        // Send VoteResponse (granted)
        &&& s_.msgs_vote_response == true
        &&& s_.msgs_vote_response_term == candidate_term
        &&& s_.msgs_vote_response_granted == true
        &&& s_.msgs_vote_response_voter == c.my_id
        // Frame
        &&& s_.msgs_request_vote == s.msgs_request_vote
        &&& s_.msgs_request_vote_term == s.msgs_request_vote_term
        &&& s_.msgs_request_vote_candidate == s.msgs_request_vote_candidate
        &&& s_.msgs_request_vote_last_log_index == s.msgs_request_vote_last_log_index
        &&& s_.msgs_request_vote_last_log_term == s.msgs_request_vote_last_log_term
        &&& s_.msgs_append_entries == s.msgs_append_entries
        &&& s_.msgs_append_entries_term == s.msgs_append_entries_term
        &&& s_.msgs_append_entries_leader == s.msgs_append_entries_leader
        &&& s_.msgs_append_entries_prev_index == s.msgs_append_entries_prev_index
        &&& s_.msgs_append_entries_prev_term == s.msgs_append_entries_prev_term
        &&& s_.msgs_append_entries_value == s.msgs_append_entries_value
        &&& s_.msgs_append_entries_has_entry == s.msgs_append_entries_has_entry
        &&& s_.msgs_append_entries_leader_commit == s.msgs_append_entries_leader_commit
        &&& s_.msgs_append_response == s.msgs_append_response
        &&& s_.msgs_append_response_term == s.msgs_append_response_term
        &&& s_.msgs_append_response_success == s.msgs_append_response_success
        &&& s_.msgs_append_response_match_index == s.msgs_append_response_match_index
        &&& s_.msgs_append_response_follower == s.msgs_append_response_follower
    }

    /// Receive a vote granted response
    pub open spec fn LReceiveVoteGranted(
        s: LState, s_: LState, c: LConstants, voter: int,
    ) -> bool {
        &&& s.role is Candidate
        &&& s.msgs_vote_response == true
        &&& s.msgs_vote_response_granted == true
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
        // Frame: preserve all messages
        &&& s_.msgs_request_vote == s.msgs_request_vote
        &&& s_.msgs_request_vote_term == s.msgs_request_vote_term
        &&& s_.msgs_request_vote_candidate == s.msgs_request_vote_candidate
        &&& s_.msgs_request_vote_last_log_index == s.msgs_request_vote_last_log_index
        &&& s_.msgs_request_vote_last_log_term == s.msgs_request_vote_last_log_term
        &&& s_.msgs_vote_response == s.msgs_vote_response
        &&& s_.msgs_vote_response_term == s.msgs_vote_response_term
        &&& s_.msgs_vote_response_granted == s.msgs_vote_response_granted
        &&& s_.msgs_vote_response_voter == s.msgs_vote_response_voter
        &&& s_.msgs_append_entries == s.msgs_append_entries
        &&& s_.msgs_append_entries_term == s.msgs_append_entries_term
        &&& s_.msgs_append_entries_leader == s.msgs_append_entries_leader
        &&& s_.msgs_append_entries_prev_index == s.msgs_append_entries_prev_index
        &&& s_.msgs_append_entries_prev_term == s.msgs_append_entries_prev_term
        &&& s_.msgs_append_entries_value == s.msgs_append_entries_value
        &&& s_.msgs_append_entries_has_entry == s.msgs_append_entries_has_entry
        &&& s_.msgs_append_entries_leader_commit == s.msgs_append_entries_leader_commit
        &&& s_.msgs_append_response == s.msgs_append_response
        &&& s_.msgs_append_response_term == s.msgs_append_response_term
        &&& s_.msgs_append_response_success == s.msgs_append_response_success
        &&& s_.msgs_append_response_match_index == s.msgs_append_response_match_index
        &&& s_.msgs_append_response_follower == s.msgs_append_response_follower
    }

    /// Become leader after receiving a quorum of votes
    /// Initializes match_index and next_index. Uses Set::len() for quorum check.
    pub open spec fn LBecomeLeader(s: LState, s_: LState, c: LConstants) -> bool {
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
        // Frame messages
        &&& s_.msgs_request_vote == false
        &&& s_.msgs_request_vote_term == 0
        &&& s_.msgs_request_vote_candidate == 0
        &&& s_.msgs_request_vote_last_log_index == 0
        &&& s_.msgs_request_vote_last_log_term == 0
        &&& s_.msgs_vote_response == false
        &&& s_.msgs_vote_response_term == 0
        &&& s_.msgs_vote_response_granted == false
        &&& s_.msgs_vote_response_voter == 0
        &&& s_.msgs_append_entries == false
        &&& s_.msgs_append_entries_term == 0
        &&& s_.msgs_append_entries_leader == 0
        &&& s_.msgs_append_entries_prev_index == 0
        &&& s_.msgs_append_entries_prev_term == 0
        &&& s_.msgs_append_entries_value == 0
        &&& s_.msgs_append_entries_has_entry == false
        &&& s_.msgs_append_entries_leader_commit == 0
        &&& s_.msgs_append_response == false
        &&& s_.msgs_append_response_term == 0
        &&& s_.msgs_append_response_success == false
        &&& s_.msgs_append_response_match_index == 0
        &&& s_.msgs_append_response_follower == 0
    }

    /// Client request: leader appends a new entry to its log
    pub open spec fn LClientRequest(
        s: LState, s_: LState, c: LConstants, value: int,
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
        // Frame messages
        &&& s_.msgs_request_vote == s.msgs_request_vote
        &&& s_.msgs_request_vote_term == s.msgs_request_vote_term
        &&& s_.msgs_request_vote_candidate == s.msgs_request_vote_candidate
        &&& s_.msgs_request_vote_last_log_index == s.msgs_request_vote_last_log_index
        &&& s_.msgs_request_vote_last_log_term == s.msgs_request_vote_last_log_term
        &&& s_.msgs_vote_response == s.msgs_vote_response
        &&& s_.msgs_vote_response_term == s.msgs_vote_response_term
        &&& s_.msgs_vote_response_granted == s.msgs_vote_response_granted
        &&& s_.msgs_vote_response_voter == s.msgs_vote_response_voter
        &&& s_.msgs_append_entries == s.msgs_append_entries
        &&& s_.msgs_append_entries_term == s.msgs_append_entries_term
        &&& s_.msgs_append_entries_leader == s.msgs_append_entries_leader
        &&& s_.msgs_append_entries_prev_index == s.msgs_append_entries_prev_index
        &&& s_.msgs_append_entries_prev_term == s.msgs_append_entries_prev_term
        &&& s_.msgs_append_entries_value == s.msgs_append_entries_value
        &&& s_.msgs_append_entries_has_entry == s.msgs_append_entries_has_entry
        &&& s_.msgs_append_entries_leader_commit == s.msgs_append_entries_leader_commit
        &&& s_.msgs_append_response == s.msgs_append_response
        &&& s_.msgs_append_response_term == s.msgs_append_response_term
        &&& s_.msgs_append_response_success == s.msgs_append_response_success
        &&& s_.msgs_append_response_match_index == s.msgs_append_response_match_index
        &&& s_.msgs_append_response_follower == s.msgs_append_response_follower
    }

    /// Leader sends AppendEntries to a follower
    /// Sends entries starting from the next_index for that follower
    pub open spec fn LSendAppendEntries(
        s: LState, s_: LState, c: LConstants,
        follower: int, entry_value: int, prev_log_index: int, prev_log_term: int,
        has_entry: bool,
    ) -> bool {
        &&& s.role is Leader
        &&& c.servers.contains(follower)
        // Send AppendEntries message
        &&& s_.msgs_append_entries == true
        &&& s_.msgs_append_entries_term == s.current_term
        &&& s_.msgs_append_entries_leader == c.my_id
        &&& s_.msgs_append_entries_prev_index == prev_log_index
        &&& s_.msgs_append_entries_prev_term == prev_log_term
        &&& s_.msgs_append_entries_value == entry_value
        &&& s_.msgs_append_entries_has_entry == has_entry
        &&& s_.msgs_append_entries_leader_commit == s.commit_index
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
        &&& s_.msgs_request_vote == s.msgs_request_vote
        &&& s_.msgs_request_vote_term == s.msgs_request_vote_term
        &&& s_.msgs_request_vote_candidate == s.msgs_request_vote_candidate
        &&& s_.msgs_request_vote_last_log_index == s.msgs_request_vote_last_log_index
        &&& s_.msgs_request_vote_last_log_term == s.msgs_request_vote_last_log_term
        &&& s_.msgs_vote_response == s.msgs_vote_response
        &&& s_.msgs_vote_response_term == s.msgs_vote_response_term
        &&& s_.msgs_vote_response_granted == s.msgs_vote_response_granted
        &&& s_.msgs_vote_response_voter == s.msgs_vote_response_voter
        &&& s_.msgs_append_response == s.msgs_append_response
        &&& s_.msgs_append_response_term == s.msgs_append_response_term
        &&& s_.msgs_append_response_success == s.msgs_append_response_success
        &&& s_.msgs_append_response_match_index == s.msgs_append_response_match_index
        &&& s_.msgs_append_response_follower == s.msgs_append_response_follower
    }

    /// Follower handles AppendEntries: accepts entries if term >= current_term
    /// Simplified: appends single entry if has_entry, updates commit_index
    pub open spec fn LFollowerAppendEntries(
        s: LState, s_: LState, c: LConstants,
        entry_value: int,
    ) -> bool {
        &&& s.msgs_append_entries == true
        &&& s.msgs_append_entries_term >= s.current_term
        // Accept: step down to follower if needed, append entry
        &&& s_.current_term == s.msgs_append_entries_term
        &&& s_.role is Follower
        &&& s_.has_voted == (if s.msgs_append_entries_term > s.current_term { false } else { s.has_voted })
        &&& s_.voted_for == (if s.msgs_append_entries_term > s.current_term { 0int } else { s.voted_for })
        &&& s_.log == (if s.msgs_append_entries_has_entry {
            s.log.push(LLogEntry { term: s.msgs_append_entries_term, value: entry_value })
        } else { s.log })
        &&& s_.commit_index == (if s.msgs_append_entries_leader_commit > s.commit_index {
            s.msgs_append_entries_leader_commit
        } else { s.commit_index })
        &&& s_.votes_granted == (if s.msgs_append_entries_term > s.current_term {
            Set::<int>::empty()
        } else { s.votes_granted })
        &&& s_.match_index == s.match_index
        &&& s_.next_index == s.next_index
        // Send AppendEntriesResponse (success)
        &&& s_.msgs_append_response == true
        &&& s_.msgs_append_response_term == s.msgs_append_entries_term
        &&& s_.msgs_append_response_success == true
        &&& s_.msgs_append_response_match_index == (if s.msgs_append_entries_has_entry {
            s.log.len() + 1
        } else { s.log.len() })
        &&& s_.msgs_append_response_follower == c.my_id
        // Frame
        &&& s_.msgs_request_vote == s.msgs_request_vote
        &&& s_.msgs_request_vote_term == s.msgs_request_vote_term
        &&& s_.msgs_request_vote_candidate == s.msgs_request_vote_candidate
        &&& s_.msgs_request_vote_last_log_index == s.msgs_request_vote_last_log_index
        &&& s_.msgs_request_vote_last_log_term == s.msgs_request_vote_last_log_term
        &&& s_.msgs_vote_response == s.msgs_vote_response
        &&& s_.msgs_vote_response_term == s.msgs_vote_response_term
        &&& s_.msgs_vote_response_granted == s.msgs_vote_response_granted
        &&& s_.msgs_vote_response_voter == s.msgs_vote_response_voter
        &&& s_.msgs_append_entries == s.msgs_append_entries
        &&& s_.msgs_append_entries_term == s.msgs_append_entries_term
        &&& s_.msgs_append_entries_leader == s.msgs_append_entries_leader
        &&& s_.msgs_append_entries_prev_index == s.msgs_append_entries_prev_index
        &&& s_.msgs_append_entries_prev_term == s.msgs_append_entries_prev_term
        &&& s_.msgs_append_entries_value == s.msgs_append_entries_value
        &&& s_.msgs_append_entries_has_entry == s.msgs_append_entries_has_entry
        &&& s_.msgs_append_entries_leader_commit == s.msgs_append_entries_leader_commit
    }

    /// Handle a successful AppendEntries response from a follower
    /// Updates match_index and next_index for the responding server
    pub open spec fn LHandleAppendResponse(
        s: LState, s_: LState, c: LConstants,
        follower: u64, new_match_index: u64,
    ) -> bool {
        &&& s.role is Leader
        &&& s.msgs_append_response == true
        &&& s.msgs_append_response_success == true
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
        // Frame messages
        &&& s_.msgs_request_vote == s.msgs_request_vote
        &&& s_.msgs_request_vote_term == s.msgs_request_vote_term
        &&& s_.msgs_request_vote_candidate == s.msgs_request_vote_candidate
        &&& s_.msgs_request_vote_last_log_index == s.msgs_request_vote_last_log_index
        &&& s_.msgs_request_vote_last_log_term == s.msgs_request_vote_last_log_term
        &&& s_.msgs_vote_response == s.msgs_vote_response
        &&& s_.msgs_vote_response_term == s.msgs_vote_response_term
        &&& s_.msgs_vote_response_granted == s.msgs_vote_response_granted
        &&& s_.msgs_vote_response_voter == s.msgs_vote_response_voter
        &&& s_.msgs_append_entries == s.msgs_append_entries
        &&& s_.msgs_append_entries_term == s.msgs_append_entries_term
        &&& s_.msgs_append_entries_leader == s.msgs_append_entries_leader
        &&& s_.msgs_append_entries_prev_index == s.msgs_append_entries_prev_index
        &&& s_.msgs_append_entries_prev_term == s.msgs_append_entries_prev_term
        &&& s_.msgs_append_entries_value == s.msgs_append_entries_value
        &&& s_.msgs_append_entries_has_entry == s.msgs_append_entries_has_entry
        &&& s_.msgs_append_entries_leader_commit == s.msgs_append_entries_leader_commit
        &&& s_.msgs_append_response == s.msgs_append_response
        &&& s_.msgs_append_response_term == s.msgs_append_response_term
        &&& s_.msgs_append_response_success == s.msgs_append_response_success
        &&& s_.msgs_append_response_match_index == s.msgs_append_response_match_index
        &&& s_.msgs_append_response_follower == s.msgs_append_response_follower
    }

    /// Handle a failed AppendEntries response: backtrack next_index
    pub open spec fn LHandleAppendReject(
        s: LState, s_: LState, c: LConstants,
        follower: u64,
    ) -> bool {
        &&& s.role is Leader
        &&& s.msgs_append_response == true
        &&& s.msgs_append_response_success == false
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
        &&& s_.msgs_request_vote == s.msgs_request_vote
        &&& s_.msgs_request_vote_term == s.msgs_request_vote_term
        &&& s_.msgs_request_vote_candidate == s.msgs_request_vote_candidate
        &&& s_.msgs_request_vote_last_log_index == s.msgs_request_vote_last_log_index
        &&& s_.msgs_request_vote_last_log_term == s.msgs_request_vote_last_log_term
        &&& s_.msgs_vote_response == s.msgs_vote_response
        &&& s_.msgs_vote_response_term == s.msgs_vote_response_term
        &&& s_.msgs_vote_response_granted == s.msgs_vote_response_granted
        &&& s_.msgs_vote_response_voter == s.msgs_vote_response_voter
        &&& s_.msgs_append_entries == s.msgs_append_entries
        &&& s_.msgs_append_entries_term == s.msgs_append_entries_term
        &&& s_.msgs_append_entries_leader == s.msgs_append_entries_leader
        &&& s_.msgs_append_entries_prev_index == s.msgs_append_entries_prev_index
        &&& s_.msgs_append_entries_prev_term == s.msgs_append_entries_prev_term
        &&& s_.msgs_append_entries_value == s.msgs_append_entries_value
        &&& s_.msgs_append_entries_has_entry == s.msgs_append_entries_has_entry
        &&& s_.msgs_append_entries_leader_commit == s.msgs_append_entries_leader_commit
        &&& s_.msgs_append_response == s.msgs_append_response
        &&& s_.msgs_append_response_term == s.msgs_append_response_term
        &&& s_.msgs_append_response_success == s.msgs_append_response_success
        &&& s_.msgs_append_response_match_index == s.msgs_append_response_match_index
        &&& s_.msgs_append_response_follower == s.msgs_append_response_follower
    }

    /// Advance commit index: leader commits entries replicated on a quorum
    pub open spec fn LAdvanceCommitIndex(
        s: LState, s_: LState, c: LConstants,
        new_commit_index: int,
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
        // Frame messages
        &&& s_.msgs_request_vote == s.msgs_request_vote
        &&& s_.msgs_request_vote_term == s.msgs_request_vote_term
        &&& s_.msgs_request_vote_candidate == s.msgs_request_vote_candidate
        &&& s_.msgs_request_vote_last_log_index == s.msgs_request_vote_last_log_index
        &&& s_.msgs_request_vote_last_log_term == s.msgs_request_vote_last_log_term
        &&& s_.msgs_vote_response == s.msgs_vote_response
        &&& s_.msgs_vote_response_term == s.msgs_vote_response_term
        &&& s_.msgs_vote_response_granted == s.msgs_vote_response_granted
        &&& s_.msgs_vote_response_voter == s.msgs_vote_response_voter
        &&& s_.msgs_append_entries == s.msgs_append_entries
        &&& s_.msgs_append_entries_term == s.msgs_append_entries_term
        &&& s_.msgs_append_entries_leader == s.msgs_append_entries_leader
        &&& s_.msgs_append_entries_prev_index == s.msgs_append_entries_prev_index
        &&& s_.msgs_append_entries_prev_term == s.msgs_append_entries_prev_term
        &&& s_.msgs_append_entries_value == s.msgs_append_entries_value
        &&& s_.msgs_append_entries_has_entry == s.msgs_append_entries_has_entry
        &&& s_.msgs_append_entries_leader_commit == s.msgs_append_entries_leader_commit
        &&& s_.msgs_append_response == s.msgs_append_response
        &&& s_.msgs_append_response_term == s.msgs_append_response_term
        &&& s_.msgs_append_response_success == s.msgs_append_response_success
        &&& s_.msgs_append_response_match_index == s.msgs_append_response_match_index
        &&& s_.msgs_append_response_follower == s.msgs_append_response_follower
    }

    /// Step down: a server discovers a higher term and becomes Follower
    pub open spec fn LStepDown(
        s: LState, s_: LState, c: LConstants, new_term: int,
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
        // Clear election messages
        &&& s_.msgs_request_vote == false
        &&& s_.msgs_request_vote_term == 0
        &&& s_.msgs_request_vote_candidate == 0
        &&& s_.msgs_request_vote_last_log_index == 0
        &&& s_.msgs_request_vote_last_log_term == 0
        &&& s_.msgs_vote_response == false
        &&& s_.msgs_vote_response_term == 0
        &&& s_.msgs_vote_response_granted == false
        &&& s_.msgs_vote_response_voter == 0
        // Frame append messages
        &&& s_.msgs_append_entries == s.msgs_append_entries
        &&& s_.msgs_append_entries_term == s.msgs_append_entries_term
        &&& s_.msgs_append_entries_leader == s.msgs_append_entries_leader
        &&& s_.msgs_append_entries_prev_index == s.msgs_append_entries_prev_index
        &&& s_.msgs_append_entries_prev_term == s.msgs_append_entries_prev_term
        &&& s_.msgs_append_entries_value == s.msgs_append_entries_value
        &&& s_.msgs_append_entries_has_entry == s.msgs_append_entries_has_entry
        &&& s_.msgs_append_entries_leader_commit == s.msgs_append_entries_leader_commit
        &&& s_.msgs_append_response == s.msgs_append_response
        &&& s_.msgs_append_response_term == s.msgs_append_response_term
        &&& s_.msgs_append_response_success == s.msgs_append_response_success
        &&& s_.msgs_append_response_match_index == s.msgs_append_response_match_index
        &&& s_.msgs_append_response_follower == s.msgs_append_response_follower
    }

    /// Next-state relation: disjunction of all possible transitions
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| LTimeout(s, s_, c)
        ||| exists |candidate_term: int, candidate_last_log_term: int,
                    candidate_last_log_index: int, candidate_id: int|
                LGrantVote(s, s_, c, candidate_term, candidate_last_log_term,
                           candidate_last_log_index, candidate_id)
        ||| exists |voter: int| LReceiveVoteGranted(s, s_, c, voter)
        ||| LBecomeLeader(s, s_, c)
        ||| exists |value: int| LClientRequest(s, s_, c, value)
        ||| exists |follower: int, entry_value: int, prev_log_index: int, prev_log_term: int|
                LSendAppendEntries(s, s_, c, follower, entry_value, prev_log_index, prev_log_term, true)
        ||| exists |entry_value: int| LFollowerAppendEntries(s, s_, c, entry_value)
        ||| exists |follower: u64, new_match_index: u64|
                LHandleAppendResponse(s, s_, c, follower, new_match_index)
        ||| exists |follower: u64| LHandleAppendReject(s, s_, c, follower)
        ||| exists |new_commit_index: int| LAdvanceCommitIndex(s, s_, c, new_commit_index)
        ||| exists |new_term: int| LStepDown(s, s_, c, new_term)
    }
}

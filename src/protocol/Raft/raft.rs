use crate::protocol::Raft::types::*;
use vstd::prelude::*;

verus! {
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
    }

    /// Timeout: a Follower or Candidate starts a new election
    /// Increments term, becomes Candidate, votes for self
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
    }

    /// Grant a vote to a candidate
    /// This server grants its vote if it hasn't voted yet in this term
    /// and the candidate's log is at least as up-to-date
    pub open spec fn LGrantVote(
        s: LState, s_: LState, c: LConstants,
        candidate_term: int, candidate_last_log_term: int, candidate_last_log_index: int,
        candidate_id: int,
    ) -> bool {
        let last_log_term = if s.log.len() == 0 { 0int } else { s.log[s.log.len() - 1].term };
        let log_ok =
            candidate_last_log_term > last_log_term
            || (candidate_last_log_term == last_log_term
                && candidate_last_log_index >= s.log.len());
        &&& candidate_term >= s.current_term
        &&& !s.has_voted || s.voted_for == candidate_id
        &&& log_ok
        // State updates
        &&& s_.current_term == candidate_term
        &&& s_.role is Follower
        &&& s_.has_voted == true
        &&& s_.voted_for == candidate_id
        &&& s_.log == s.log
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == s.votes_granted
        &&& s_.match_index == s.match_index
    }

    /// Receive a vote granted response
    /// A candidate records that a server granted its vote
    pub open spec fn LReceiveVoteGranted(
        s: LState, s_: LState, c: LConstants, voter: int,
    ) -> bool {
        &&& s.role is Candidate
        &&& c.servers.contains(voter)
        &&& s_.current_term == s.current_term
        &&& s_.role == s.role
        &&& s_.has_voted == s.has_voted
        &&& s_.voted_for == s.voted_for
        &&& s_.log == s.log
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == s.votes_granted.insert(voter)
        &&& s_.match_index == s.match_index
    }

    /// Become leader after receiving a quorum of votes
    /// Initializes match_index to 0 for all servers
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
    }

    /// Client request: leader appends a new entry to its log
    pub open spec fn LClientRequest(
        s: LState, s_: LState, c: LConstants, value: int,
    ) -> bool {
        let entry = LLogEntry { term: s.current_term, value: value };
        &&& s.role is Leader
        &&& s_.current_term == s.current_term
        &&& s_.role == s.role
        &&& s_.has_voted == s.has_voted
        &&& s_.voted_for == s.voted_for
        &&& s_.log == s.log.push(entry)
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == s.votes_granted
        &&& s_.match_index == s.match_index
    }

    /// Handle a successful AppendEntries response from a follower
    /// Updates match_index for the responding server
    pub open spec fn LHandleAppendResponse(
        s: LState, s_: LState, c: LConstants,
        follower: int, new_match_index: int,
    ) -> bool {
        &&& s.role is Leader
        &&& c.servers.contains(follower)
        &&& new_match_index >= 0int
        &&& new_match_index <= s.log.len()
        &&& s_.current_term == s.current_term
        &&& s_.role == s.role
        &&& s_.has_voted == s.has_voted
        &&& s_.voted_for == s.voted_for
        &&& s_.log == s.log
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == s.votes_granted
        &&& s_.match_index == s.match_index.insert(follower as u64, new_match_index as u64)
    }

    /// Advance commit index: leader commits entries replicated on a quorum
    /// The new commit index is the supplied value if:
    ///   - it is greater than current commit_index
    ///   - the entry at that index has the current term
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
        ||| exists |follower: int, new_match_index: int|
                LHandleAppendResponse(s, s_, c, follower, new_match_index)
        ||| exists |new_commit_index: int| LAdvanceCommitIndex(s, s_, c, new_commit_index)
        ||| exists |new_term: int| LStepDown(s, s_, c, new_term)
    }
}

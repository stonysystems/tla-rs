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
            // RequestVote must carry the candidate's current last-log summary.
            last_log_index: s.log.len() as int,
            last_log_term: if s.log.len() == 0 {
                0int
            } else {
                s.log[s.log.len() - 1].term
            },
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
            voter_last_log_index: s.log.len() as int,
            voter_last_log_term: if s.log.len() == 0 { 0int } else { s.log[s.log.len() - 1].term },
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
        // Log-consistency constraints: message parameters match the leader's log
        &&& prev_log_index >= 0
        &&& s.log.len() >= prev_log_index + ae_entry_count(has_entry)
        &&& (prev_log_index > 0 ==> s.log[prev_log_index - 1].term == prev_log_term)
        &&& (has_entry ==> s.log[prev_log_index].value == entry_value)
        // Entry term must match leader's current term. This ensures
        // replicated entries have the correct term (ae_term == entry's original term),
        // which is needed for LogMatching. In the simplified spec (no log truncation),
        // the leader only replicates entries from its current term.
        &&& (has_entry ==> s.log[prev_log_index].term == s.current_term)
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
        &&& s_.has_voted == step_down_if_needed(s, ae_term).has_voted
        &&& s_.voted_for == step_down_if_needed(s, ae_term).voted_for
        &&& s_.log == (if ae_has_entry {
            s.log.push(LLogEntry { term: ae_term, value: ae_value })
        } else { s.log })
        &&& s_.commit_index == (if ae_leader_commit > s.commit_index {
            if ae_has_entry {
                if ae_leader_commit <= s.log.len() + 1 { ae_leader_commit } else { (s.log.len() + 1) as int }
            } else {
                if ae_leader_commit <= s.log.len() { ae_leader_commit } else { s.log.len() as int }
            }
        } else { s.commit_index })
        &&& s_.votes_granted == step_down_if_needed(s, ae_term).votes_granted
        &&& s_.match_index == s.match_index
        &&& s_.next_index == s.next_index
        &&& sent_packets == seq![LRaftMessage::AppendResponse {
            term: ae_term,
            success: true,
            match_index: (if ae_has_entry {
                s.log.len() as int + 1
            } else { ae_prev_index as int }),
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

    /// Advance commit index: leader commits entries replicated on a quorum.
    /// Requires a quorum of servers to have replicated log up to new_commit_index:
    /// the leader itself counts (it has the entry), and followers are tracked
    /// via match_index.
    pub open spec fn LAdvanceCommitIndex(
        s: LState, s_: LState, c: LConstants,
        new_commit_index: int, sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        &&& s.role is Leader
        &&& new_commit_index > s.commit_index
        &&& new_commit_index <= s.log.len()
        &&& s.log[new_commit_index - 1].term == s.current_term
        // Quorum replication guard: at least quorum_size servers have the entry
        &&& c.servers.finite()
        &&& replicator_count(s, c, new_commit_index) >= c.quorum_size
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

    /// Spec helper: number of entries in an AppendEntries message.
    pub open spec fn ae_entry_count(has_entry: bool) -> int {
        if has_entry { 1int } else { 0int }
    }

    /// Spec helper: count of servers that have replicated log up to `idx`.
    /// The leader itself counts (it has the entry), and followers are tracked
    /// via match_index. Used as a transpiler-friendly replacement for the
    /// existential quorum quantifier in LAdvanceCommitIndex.
    pub open spec fn replicator_count(s: LState, c: LConstants, idx: int) -> int {
        c.servers.filter(|v: int|
            v == c.my_id
            || (s.match_index.contains_key(v as u64)
                && s.match_index[v as u64] as int >= idx)
        ).len() as int
    }

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
        } else if ae_prev_index > 0 && (
            ae_prev_index > s_mid.log.len()
            || s_mid.log[ae_prev_index - 1].term != ae_prev_term
        ) {
            // Prev-log consistency check failed (Raft paper 5.3):
            // follower doesn't have a matching entry at prev_log_index
            &&& s_ == s_mid
            &&& sent_packets == seq![LRaftMessage::AppendResponse {
                term: s_mid.current_term,
                success: false,
                match_index: 0int,
                follower: c.my_id,
            }]
        } else if ae_has_entry && ae_prev_index != s_mid.log.len() {
            // Log index mismatch: entry would go to the wrong index.
            // Without log truncation, the follower can only accept entries that
            // extend its log at the correct position (prev_index == log.len()).
            // This guards LogMatching: entries are always placed at the index
            // matching the leader's log.
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

    /// Receive vote and become leader: add vote, then transition to leader role.
    /// Combines LReceiveVoteGranted + LBecomeLeader into a single atomic action.
    pub open spec fn LReceiveVoteAndBecomeLeader(
        s: LState, s_: LState, c: LConstants,
        vote_term: int, vote_granted: bool, voter: int,
        sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        &&& s.role is Candidate
        &&& vote_granted == true
        &&& c.servers.contains(voter)
        &&& s_.current_term == s.current_term
        &&& s_.role is Leader
        &&& s_.has_voted == s.has_voted
        &&& s_.voted_for == s.voted_for
        &&& s_.log == s.log
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == s.votes_granted.insert(voter)
        &&& s_.match_index == Map::<u64, u64>::empty()
        &&& s_.next_index == Map::<u64, u64>::empty()
        &&& sent_packets == Seq::<LRaftMessage>::empty()
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
        } else if term < s_mid.current_term {
            // Stale term (vote from a previous election): no-op
            // This matches real Raft: candidates ignore VoteResponses from old terms.
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
        } else if s_mid.votes_granted.insert(voter).len() >= c.quorum_size {
            // Quorum reached: add vote and become leader
            LReceiveVoteAndBecomeLeader(s_mid, s_, c, term, granted, voter, sent_packets)
        } else {
            // Below quorum: just receive vote
            LReceiveVoteGranted(s_mid, s_, c, term, granted, voter, sent_packets)
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

    // ---------------------------------------------------------------
    // Commit index advancement (Phase 27.2)
    //
    // Combines guard check + LAdvanceCommitIndex into one composite
    // action. The spec requires quorum replication (via existential
    // quantification over a quorum set); the implementation computes
    // the concrete quorum via match_index scanning in host.rs.
    // ---------------------------------------------------------------

    /// Advance commit index: combines guard check + LAdvanceCommitIndex.
    /// If not leader or new_commit_index is not an advancement, stutter.
    /// LAdvanceCommitIndex requires quorum replication; the exec code
    /// computes the concrete quorum via the match_index scan loop.
    pub open spec fn LTryAdvanceCommitIndex(
        s: LState, s_: LState, c: LConstants,
        new_commit_index: int,
        sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        if !(s.role is Leader) || new_commit_index <= s.commit_index {
            // Not leader or no advancement: stutter
            &&& s_ == s
            &&& sent_packets == Seq::<LRaftMessage>::empty()
        } else {
            // Valid advancement: delegate to LAdvanceCommitIndex
            LAdvanceCommitIndex(s, s_, c, new_commit_index, sent_packets)
        }
    }

    // ---------------------------------------------------------------
    // Message dispatch (Phase 27.3)
    //
    // Top-level dispatch from incoming message to composite handler,
    // analogous to RSL's LReplicaNextProcessPacket.
    // ---------------------------------------------------------------

    /// Dispatch an incoming message to the appropriate composite handler.
    pub open spec fn LHandleMessage(
        s: LState, s_: LState, c: LConstants,
        msg: LRaftMessage,
        sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        match msg {
            LRaftMessage::RequestVote { term, candidate, last_log_index, last_log_term } =>
                LHandleRequestVoteMsg(s, s_, c, term, candidate, last_log_index,
                                      last_log_term, sent_packets),
            LRaftMessage::VoteResponse { term, granted, voter, .. } =>
                LHandleVoteResponseMsg(s, s_, c, term, granted, voter, sent_packets),
            LRaftMessage::AppendEntries { term, leader, prev_index, prev_term,
                                          value, has_entry, leader_commit } =>
                LHandleAppendEntriesMsg(s, s_, c, term, leader, prev_index, prev_term,
                                        value, has_entry, leader_commit, sent_packets),
            LRaftMessage::AppendResponse { term, success, match_index, follower } =>
                LHandleAppendResponseMsg(s, s_, c, term, success, match_index,
                                         follower, sent_packets),
        }
    }

    // ---------------------------------------------------------------
    // Next-state relation (Phase 27.4)
    //
    // Uses composite message handlers and commit advancement instead
    // of individual atomic actions. Timer-driven actions are unchanged.
    // ---------------------------------------------------------------

    /// Next-state relation: disjunction of all possible transitions.
    /// Uses composite message dispatch + commit advancement (Phases 27.2-27.4).
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        // Timer-driven actions (unchanged)
        ||| exists |sent_packets: Seq<LRaftMessage>| LTimeout(s, s_, c, sent_packets)
        ||| exists |value: int, sent_packets: Seq<LRaftMessage>|
                LClientRequest(s, s_, c, value, sent_packets)
        ||| exists |follower: int, entry_value: int, prev_log_index: int, prev_log_term: int,
                    has_entry: bool, sent_packets: Seq<LRaftMessage>|
                LSendAppendEntries(s, s_, c, follower, entry_value, prev_log_index,
                                   prev_log_term, has_entry, sent_packets)
        // Composite message dispatch (replaces individual message handlers)
        ||| exists |msg: LRaftMessage, sent_packets: Seq<LRaftMessage>|
                LHandleMessage(s, s_, c, msg, sent_packets)
        // Composite commit advancement (replaces LAdvanceCommitIndex)
        ||| exists |new_commit_index: int, sent_packets: Seq<LRaftMessage>|
                LTryAdvanceCommitIndex(s, s_, c, new_commit_index, sent_packets)
    }
}

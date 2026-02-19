---- MODULE Raft ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS RaftMessage, Constants, State, u64

u64_inc(x) ==
    x + 1

u64_dec(x) ==
    x - 1

Init(s, c) ==
    /\ s.current_term = 0
    /\ s.role.tag = Follower
    /\ s.has_voted = FALSE
    /\ s.voted_for = 0
    /\ s.log = <<>>
    /\ s.commit_index = 0
    /\ s.votes_granted = {}
    /\ s.match_index = <<>>
    /\ s.next_index = <<>>

Timeout(s, s_, c, sent_packets) ==
    /\ s.role.tag = Follower \/ s.role.tag = Candidate
    /\ s_.current_term = s.current_term + 1
    /\ s_.role.tag = Candidate
    /\ s_.has_voted = TRUE
    /\ s_.voted_for = c.my_id
    /\ s_.log = s.log
    /\ s_.commit_index = s.commit_index
    /\ s_.votes_granted = {} \cup {c.my_id}
    /\ s_.match_index = s.match_index
    /\ s_.next_index = s.next_index
    /\ sent_packets = <<[term |-> s.current_term + 1, candidate |-> c.my_id, last_log_index |-> 0, last_log_term |-> 0]>>

GrantVote(s, s_, c, candidate_term, candidate_last_log_term, candidate_last_log_index, candidate_id, sent_packets) ==
    /\ candidate_term >= s.current_term
    /\ ~s.has_voted \/ s.voted_for = candidate_id
    /\ s_.current_term = candidate_term
    /\ s_.role.tag = Follower
    /\ s_.has_voted = TRUE
    /\ s_.voted_for = candidate_id
    /\ s_.log = s.log
    /\ s_.commit_index = s.commit_index
    /\ s_.votes_granted = s.votes_granted
    /\ s_.match_index = s.match_index
    /\ s_.next_index = s.next_index
    /\ sent_packets = <<[term |-> candidate_term, granted |-> TRUE, voter |-> c.my_id]>>

ReceiveVoteGranted(s, s_, c, vote_term, vote_granted, voter, sent_packets) ==
    /\ s.role.tag = Candidate
    /\ vote_granted = TRUE
    /\ voter \in c.servers
    /\ s_.current_term = s.current_term
    /\ s_.role = s.role
    /\ s_.has_voted = s.has_voted
    /\ s_.voted_for = s.voted_for
    /\ s_.log = s.log
    /\ s_.commit_index = s.commit_index
    /\ s_.votes_granted = s.votes_granted \cup {voter}
    /\ s_.match_index = s.match_index
    /\ s_.next_index = s.next_index
    /\ sent_packets = <<>>

BecomeLeader(s, s_, c, sent_packets) ==
    /\ s.role.tag = Candidate
    /\ Len(s.votes_granted) >= c.quorum_size
    /\ s_.current_term = s.current_term
    /\ s_.role.tag = Leader
    /\ s_.has_voted = s.has_voted
    /\ s_.voted_for = s.voted_for
    /\ s_.log = s.log
    /\ s_.commit_index = s.commit_index
    /\ s_.votes_granted = s.votes_granted
    /\ s_.match_index = <<>>
    /\ s_.next_index = <<>>
    /\ sent_packets = <<>>

ClientRequest(s, s_, c, value, sent_packets) ==
    /\ s.role.tag = Leader
    /\ s_.current_term = s.current_term
    /\ s_.role = s.role
    /\ s_.has_voted = s.has_voted
    /\ s_.voted_for = s.voted_for
    /\ s_.log = Append(s.log, [term |-> s.current_term, value |-> value])
    /\ s_.commit_index = s.commit_index
    /\ s_.votes_granted = s.votes_granted
    /\ s_.match_index = s.match_index
    /\ s_.next_index = s.next_index
    /\ sent_packets = <<>>

SendAppendEntries(s, s_, c, follower, entry_value, prev_log_index, prev_log_term, has_entry, sent_packets) ==
    /\ s.role.tag = Leader
    /\ follower \in c.servers
    /\ s_.current_term = s.current_term
    /\ s_.role = s.role
    /\ s_.has_voted = s.has_voted
    /\ s_.voted_for = s.voted_for
    /\ s_.log = s.log
    /\ s_.commit_index = s.commit_index
    /\ s_.votes_granted = s.votes_granted
    /\ s_.match_index = s.match_index
    /\ s_.next_index = s.next_index
    /\ sent_packets = <<[term |-> s.current_term, leader |-> c.my_id, prev_index |-> prev_log_index, prev_term |-> prev_log_term, value |-> entry_value, has_entry |-> has_entry, leader_commit |-> s.commit_index]>>

FollowerAppendEntries(s, s_, c, ae_term, ae_leader, ae_prev_index, ae_prev_term, ae_value, ae_has_entry, ae_leader_commit, sent_packets) ==
    /\ ae_term >= s.current_term
    /\ s_.current_term = ae_term
    /\ s_.role.tag = Follower
    /\ s_.has_voted = IF ae_term > s.current_term THEN FALSE ELSE s.has_voted
    /\ s_.voted_for = IF ae_term > s.current_term THEN 0 ELSE s.voted_for
    /\ s_.log = IF ae_has_entry THEN Append(s.log, [term |-> ae_term, value |-> ae_value]) ELSE s.log
    /\ s_.commit_index = IF ae_leader_commit > s.commit_index THEN ae_leader_commit ELSE s.commit_index
    /\ s_.votes_granted = IF ae_term > s.current_term THEN {} ELSE s.votes_granted
    /\ s_.match_index = s.match_index
    /\ s_.next_index = s.next_index
    /\ sent_packets = <<[term |-> ae_term, success |-> TRUE, match_index |-> IF ae_has_entry THEN Len(s.log) + 1 ELSE Len(s.log), follower |-> c.my_id]>>

HandleAppendResponse(s, s_, c, resp_term, resp_success, resp_match_index, resp_follower, follower, new_match_index, sent_packets) ==
    /\ s.role.tag = Leader
    /\ resp_success = TRUE
    /\ follower \in c.servers
    /\ new_match_index >= 0
    /\ new_match_index <= Len(s.log)
    /\ s_.current_term = s.current_term
    /\ s_.role = s.role
    /\ s_.has_voted = s.has_voted
    /\ s_.voted_for = s.voted_for
    /\ s_.log = s.log
    /\ s_.commit_index = s.commit_index
    /\ s_.votes_granted = s.votes_granted
    /\ s_.match_index = [s.match_index EXCEPT ![follower] = new_match_index]
    /\ s_.next_index = [s.next_index EXCEPT ![follower] = u64_inc(new_match_index)]
    /\ sent_packets = <<>>

HandleAppendReject(s, s_, c, resp_term, resp_success, resp_match_index, resp_follower, follower, sent_packets) ==
    /\ s.role.tag = Leader
    /\ resp_success = FALSE
    /\ follower \in c.servers
    /\ s_.next_index = IF follower \in DOMAIN s.next_index /\ s.next_index[follower] > 0 THEN [s.next_index EXCEPT ![follower] = u64_dec(s.next_index[follower])] ELSE s.next_index
    /\ s_.current_term = s.current_term
    /\ s_.role = s.role
    /\ s_.has_voted = s.has_voted
    /\ s_.voted_for = s.voted_for
    /\ s_.log = s.log
    /\ s_.commit_index = s.commit_index
    /\ s_.votes_granted = s.votes_granted
    /\ s_.match_index = s.match_index
    /\ sent_packets = <<>>

AdvanceCommitIndex(s, s_, c, new_commit_index, sent_packets) ==
    /\ s.role.tag = Leader
    /\ new_commit_index > s.commit_index
    /\ new_commit_index <= Len(s.log)
    /\ s.log[new_commit_index - 1].term = s.current_term
    /\ s_.current_term = s.current_term
    /\ s_.role = s.role
    /\ s_.has_voted = s.has_voted
    /\ s_.voted_for = s.voted_for
    /\ s_.log = s.log
    /\ s_.commit_index = new_commit_index
    /\ s_.votes_granted = s.votes_granted
    /\ s_.match_index = s.match_index
    /\ s_.next_index = s.next_index
    /\ sent_packets = <<>>

StepDown(s, s_, c, new_term, sent_packets) ==
    /\ new_term > s.current_term
    /\ s_.current_term = new_term
    /\ s_.role.tag = Follower
    /\ s_.has_voted = FALSE
    /\ s_.voted_for = 0
    /\ s_.log = s.log
    /\ s_.commit_index = s.commit_index
    /\ s_.votes_granted = {}
    /\ s_.match_index = s.match_index
    /\ s_.next_index = s.next_index
    /\ sent_packets = <<>>

Next(s, s_, c) ==
    \/ \E sent_packets \in Seq(RaftMessage) : Timeout(s, s_, c, sent_packets)
    \/ \E candidate_term \in Int, candidate_last_log_term \in Int, candidate_last_log_index \in Int, candidate_id \in Int, sent_packets \in Seq(RaftMessage) : GrantVote(s, s_, c, candidate_term, candidate_last_log_term, candidate_last_log_index, candidate_id, sent_packets)
    \/ \E vote_term \in Int, vote_granted \in BOOLEAN, voter \in Int, sent_packets \in Seq(RaftMessage) : ReceiveVoteGranted(s, s_, c, vote_term, vote_granted, voter, sent_packets)
    \/ \E sent_packets \in Seq(RaftMessage) : BecomeLeader(s, s_, c, sent_packets)
    \/ \E value \in Int, sent_packets \in Seq(RaftMessage) : ClientRequest(s, s_, c, value, sent_packets)
    \/ \E follower \in Int, entry_value \in Int, prev_log_index \in Int, prev_log_term \in Int, sent_packets \in Seq(RaftMessage) : SendAppendEntries(s, s_, c, follower, entry_value, prev_log_index, prev_log_term, TRUE, sent_packets)
    \/ \E ae_term \in Int, ae_leader \in Int, ae_prev_index \in Int, ae_prev_term \in Int, ae_value \in Int, ae_has_entry \in BOOLEAN, ae_leader_commit \in Int, sent_packets \in Seq(RaftMessage) : FollowerAppendEntries(s, s_, c, ae_term, ae_leader, ae_prev_index, ae_prev_term, ae_value, ae_has_entry, ae_leader_commit, sent_packets)
    \/ \E resp_term \in Int, resp_success \in BOOLEAN, resp_match_index \in Int, resp_follower \in Int, follower \in u64, new_match_index \in u64, sent_packets \in Seq(RaftMessage) : HandleAppendResponse(s, s_, c, resp_term, resp_success, resp_match_index, resp_follower, follower, new_match_index, sent_packets)
    \/ \E resp_term \in Int, resp_success \in BOOLEAN, resp_match_index \in Int, resp_follower \in Int, follower \in u64, sent_packets \in Seq(RaftMessage) : HandleAppendReject(s, s_, c, resp_term, resp_success, resp_match_index, resp_follower, follower, sent_packets)
    \/ \E new_commit_index \in Int, sent_packets \in Seq(RaftMessage) : AdvanceCommitIndex(s, s_, c, new_commit_index, sent_packets)
    \/ \E new_term \in Int, sent_packets \in Seq(RaftMessage) : StepDown(s, s_, c, new_term, sent_packets)

====

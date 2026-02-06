---- MODULE Raft ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS State, Constants

Init(s, c) ==
    /\ s.current_term = 0
    /\ s.role.tag = Follower
    /\ s.has_voted = FALSE
    /\ s.voted_for = 0
    /\ s.log = <<>>
    /\ s.commit_index = 0
    /\ s.votes_granted = {}
    /\ s.match_index = <<>>

Timeout(s, s_, c) ==
    /\ s.role.tag = Follower \/ s.role.tag = Candidate
    /\ s_.current_term = s.current_term + 1
    /\ s_.role.tag = Candidate
    /\ s_.has_voted = TRUE
    /\ s_.voted_for = c.my_id
    /\ s_.log = s.log
    /\ s_.commit_index = s.commit_index
    /\ s_.votes_granted = {} \cup {c.my_id}
    /\ s_.match_index = s.match_index

GrantVote(s, s_, c, candidate_term, candidate_last_log_term, candidate_last_log_index, candidate_id) ==
    LET last_log_term == IF Len(s.log) = 0 THEN 0 ELSE s.log[Len(s.log) - 1].term
    IN LET log_ok == candidate_last_log_term > last_log_term \/ (candidate_last_log_term = last_log_term /\ candidate_last_log_index >= Len(s.log))
IN candidate_term >= s.current_term /\ (~s.has_voted \/ s.voted_for = candidate_id) /\ log_ok /\ s_.current_term = candidate_term /\ s_.role.tag = Follower /\ s_.has_voted = TRUE /\ s_.voted_for = candidate_id /\ s_.log = s.log /\ s_.commit_index = s.commit_index /\ s_.votes_granted = s.votes_granted /\ s_.match_index = s.match_index

ReceiveVoteGranted(s, s_, c, voter) ==
    /\ s.role.tag = Candidate
    /\ voter \in c.servers
    /\ s_.current_term = s.current_term
    /\ s_.role = s.role
    /\ s_.has_voted = s.has_voted
    /\ s_.voted_for = s.voted_for
    /\ s_.log = s.log
    /\ s_.commit_index = s.commit_index
    /\ s_.votes_granted = s.votes_granted \cup {voter}
    /\ s_.match_index = s.match_index

BecomeLeader(s, s_, c) ==
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

ClientRequest(s, s_, c, value) ==
    LET entry == [term |-> s.current_term, value |-> value]
    IN s.role.tag = Leader /\ s_.current_term = s.current_term /\ s_.role = s.role /\ s_.has_voted = s.has_voted /\ s_.voted_for = s.voted_for /\ s_.log = Append(s.log, entry) /\ s_.commit_index = s.commit_index /\ s_.votes_granted = s.votes_granted /\ s_.match_index = s.match_index

HandleAppendResponse(s, s_, c, follower, new_match_index) ==
    /\ s.role.tag = Leader
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

AdvanceCommitIndex(s, s_, c, new_commit_index) ==
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

StepDown(s, s_, c, new_term) ==
    /\ new_term > s.current_term
    /\ s_.current_term = new_term
    /\ s_.role.tag = Follower
    /\ s_.has_voted = FALSE
    /\ s_.voted_for = 0
    /\ s_.log = s.log
    /\ s_.commit_index = s.commit_index
    /\ s_.votes_granted = {}
    /\ s_.match_index = s.match_index

Next(s, s_, c) ==
    \/ Timeout(s, s_, c)
    \/ \E candidate_term \in Int, candidate_last_log_term \in Int, candidate_last_log_index \in Int, candidate_id \in Int : GrantVote(s, s_, c, candidate_term, candidate_last_log_term, candidate_last_log_index, candidate_id)
    \/ \E voter \in Int : ReceiveVoteGranted(s, s_, c, voter)
    \/ BecomeLeader(s, s_, c)
    \/ \E value \in Int : ClientRequest(s, s_, c, value)
    \/ \E follower \in Int, new_match_index \in Int : HandleAppendResponse(s, s_, c, follower, new_match_index)
    \/ \E new_commit_index \in Int : AdvanceCommitIndex(s, s_, c, new_commit_index)
    \/ \E new_term \in Int : StepDown(s, s_, c, new_term)

====

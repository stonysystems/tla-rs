---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

Constants ==
    [servers |-> SUBSET Int, quorum_size |-> Int, my_id |-> Int]

LogEntry ==
    [term |-> Int, value |-> Int]

State ==
    [current_term |-> Int, role |-> ServerRole, has_voted |-> BOOLEAN, voted_for |-> Int, log |-> Seq(LogEntry), commit_index |-> Int, votes_granted |-> SUBSET Int, match_index |-> [u64 -> u64], next_index |-> [u64 -> u64]]

ServerRole ==
    {Follower, Candidate, Leader}

RaftMessage ==
    {RequestVote, VoteResponse, AppendEntries, AppendResponse}

====

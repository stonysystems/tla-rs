---- MODULE types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

State ==
    [current_term |-> Int, role |-> ServerRole, has_voted |-> BOOLEAN, voted_for |-> Int, log |-> Seq(LogEntry), commit_index |-> Int, votes_granted |-> SUBSET Int, match_index |-> [u64 -> u64]]

LogEntry ==
    [term |-> Int, value |-> Int]

Constants ==
    [servers |-> SUBSET Int, quorum_size |-> Int, my_id |-> Int]

ServerRole ==
    {Follower, Candidate, Leader}

====

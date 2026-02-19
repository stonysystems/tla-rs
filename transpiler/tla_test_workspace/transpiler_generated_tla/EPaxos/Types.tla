---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

Constants ==
    [num_replicas |-> Int, fast_quorum_size |-> Int, quorum_size |-> Int, my_id |-> Int]

State ==
    [ballot |-> Int, phase |-> InstancePhase, cmd |-> Int, seq |-> Int, dep_count |-> Int, is_leader |-> BOOLEAN, committed_count |-> Int, executed_count |-> Int, preaccept_senders |-> SUBSET Int, accept_senders |-> SUBSET Int, has_conflict |-> BOOLEAN, max_resp_seq |-> Int]

InstancePhase ==
    {Empty, PreAccepted, Accepted, Committed, Executed}

EPaxosMessage ==
    {PreAccept, PreAcceptOk, Accept, AcceptOk, Commit}

====

---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

Constants ==
    [acceptors |-> SUBSET Int, quorum_size |-> Int, node_id |-> Int]

State ==
    [promised_bal |-> Int, accepted_bal |-> Int, accepted_val |-> Int, proposer_bal |-> Int, phase |-> Phase, promises_rcvd |-> SUBSET Int, highest_accepted_bal |-> Int, highest_accepted_val |-> Int, proposed_val |-> Int, accepts_rcvd |-> SUBSET Int, decided_val |-> Int]

Phase ==
    {Idle, Phase1, Phase2, Decided}

====

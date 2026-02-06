---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

State ==
    [max_bal |-> SUBSET Int, max_v_bal |-> SUBSET Int, max_val |-> SUBSET Int, msg_count |-> Int]

Constants ==
    [acceptors |-> SUBSET Int, quorum_size |-> Int]

MsgType ==
    {Phase1a, Phase1b, Phase2a, Phase2b}

====

---- MODULE types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

State ==
    [role |-> NodeRole, history |-> Seq(Int), pending_sent |-> SUBSET Int, committed_count |-> Int, obj_value |-> Int]

Constants ==
    [node_id |-> Int, chain_len |-> Int]

NodeRole ==
    {Head, Middle, Tail}

====

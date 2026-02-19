---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

State ==
    [role |-> NodeRole, history |-> Seq(Int), pending_sent |-> SUBSET Int, committed_count |-> Int, obj_value |-> Int, has_predecessor |-> BOOLEAN, predecessor |-> Int, has_successor |-> BOOLEAN, successor |-> Int, alive |-> BOOLEAN]

Constants ==
    [node_id |-> Int, chain_len |-> Int]

CRMessage ==
    {Forward, Ack}

NodeRole ==
    {Head, Middle, Tail}

====

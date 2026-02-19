---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

State ==
    [config_num |-> Int, max_bal |-> Int, max_v_bal |-> Int, max_val |-> Int, has_voted |-> BOOLEAN, is_active |-> BOOLEAN, promises_rcvd |-> SUBSET Int, accepts_rcvd |-> SUBSET Int, committed |-> BOOLEAN, committed_val |-> Int, witness_val |-> Int, has_witness |-> BOOLEAN]

Constants ==
    [quorum_size |-> Int, num_nodes |-> Int, node_id |-> Int]

VPMessage ==
    {Prepare, Promise, Accept}

====

---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

State ==
    [config_num |-> Int, max_bal |-> Int, max_v_bal |-> Int, max_val |-> Int, has_voted |-> BOOLEAN, is_active |-> BOOLEAN]

Constants ==
    [quorum_size |-> Int, num_nodes |-> Int]

====

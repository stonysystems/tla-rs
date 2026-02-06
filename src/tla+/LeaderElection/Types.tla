---- MODULE types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

State ==
    [electing |-> SUBSET Int, has_leader |-> BOOLEAN, leader |-> Int, alive |-> SUBSET Int, has_highest |-> BOOLEAN, highest_heard |-> Int]

Constants ==
    [nodes |-> SUBSET Int, num_nodes |-> Int]

NodeState ==
    {Normal, Election, Leader}

====

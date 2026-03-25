---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

Constants ==
    [nodes |-> SUBSET Int, num_nodes |-> Int]

State ==
    [electing |-> SUBSET Int, has_leader |-> BOOLEAN, leader |-> Int, alive |-> SUBSET Int, has_highest |-> BOOLEAN, highest_heard |-> Int, waiting_answer |-> BOOLEAN, waiting_node |-> Int]

ElectionMessage ==
    {Election, Answer, Coordinator}

NodeState ==
    {Normal, Election, Leader}

====

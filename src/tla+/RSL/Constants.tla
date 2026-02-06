---- MODULE constants ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ReplicaConstants

ReplicaConstants ==
    [my_index |-> Int, all |-> Constants]

Constants ==
    [config |-> Configuration, params |-> Parameters]

ReplicaConstantsValid(c) ==
    0 <= c.my_index /\ c.my_index < Len(c.all.config.replica_ids)

====

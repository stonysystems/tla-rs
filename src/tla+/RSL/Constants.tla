---- MODULE Constants ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ReplicaConstants

Constants ==
    [config |-> Configuration, params |-> Parameters]

ReplicaConstants ==
    [my_index |-> Int, all |-> Constants]

ReplicaConstantsValid(c) ==
    0 <= c.my_index /\ c.my_index < Len(c.all.config.replica_ids)

====

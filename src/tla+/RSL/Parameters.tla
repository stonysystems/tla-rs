---- MODULE parameters ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Parameters

Parameters ==
    [max_log_length |-> Int, baseline_view_timeout_period |-> Int, heartbeat_period |-> Int, max_integer_val |-> UpperBound, max_batch_size |-> Int, max_batch_delay |-> Int]

WFLParameters(p) ==
    /\ p.max_log_length > 0
    /\ p.baseline_view_timeout_period > 0
    /\ p.heartbeat_period > 0
    /\ p.max_batch_size > 0
    /\ p.max_batch_delay >= 0

====

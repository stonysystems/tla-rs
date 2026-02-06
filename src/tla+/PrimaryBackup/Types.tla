---- MODULE types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

State ==
    [role |-> NodeRole, log_length |-> Int, last_value |-> Int, has_pending |-> BOOLEAN, pending_value |-> Int, acked |-> BOOLEAN]

Constants ==
    [max_log_len |-> Int]

NodeRole ==
    {Primary, Backup}

====

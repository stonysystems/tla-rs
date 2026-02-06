---- MODULE types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

Constants ==
    [f |-> Int, n |-> Int]

State ==
    [view |-> Int, phase |-> Phase, prepare_count |-> Int, commit_count |-> Int, seq_num |-> Int, is_primary |-> BOOLEAN]

Phase ==
    {PrePrepare, Prepare, Commit, Replied}

====

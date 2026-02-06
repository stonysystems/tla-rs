---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

State ==
    [view |-> Int, phase |-> Phase, prepare_count |-> Int, commit_count |-> Int, seq_num |-> Int, is_primary |-> BOOLEAN]

Constants ==
    [f |-> Int, n |-> Int]

Phase ==
    {PrePrepare, Prepare, Commit, Replied}

====

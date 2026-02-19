---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

State ==
    [view |-> Int, phase |-> Phase, prepare_senders |-> SUBSET Int, commit_senders |-> SUBSET Int, seq_num |-> Int, is_primary |-> BOOLEAN, request_digest |-> Int, checkpoint_seq |-> Int, checkpoint_digest |-> Int, low_watermark |-> Int, high_watermark |-> Int]

Constants ==
    [f |-> Int, n |-> Int, node_id |-> Int, checkpoint_interval |-> Int]

PBFTMessage ==
    {PrePrepare}

Phase ==
    {PrePrepare, Prepare, Commit, Replied}

====

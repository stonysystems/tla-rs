---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

State ==
    [tm_state |-> TMState, tm_prepared |-> SUBSET Int, rm_prepared |-> SUBSET Int, rm_committed |-> SUBSET Int, rm_aborted |-> SUBSET Int]

Constants ==
    [rm |-> SUBSET Int]

TMState ==
    {Init, Committed, Aborted}

RMState ==
    {Working, Prepared, Committed, Aborted}

TPCMessage ==
    {Prepare, PreparedVote, Commit, Abort}

====

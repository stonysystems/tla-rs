---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

Constants ==
    [rm |-> SUBSET Int]

State ==
    [tm_state |-> TMState, tm_prepared |-> SUBSET Int, rm_prepared |-> SUBSET Int, rm_committed |-> SUBSET Int, rm_aborted |-> SUBSET Int]

TMState ==
    {Init, Committed, Aborted}

RMState ==
    {Working, Prepared, Committed, Aborted}

TPCMessage ==
    {Prepare, PreparedVote, Commit, Abort}

====

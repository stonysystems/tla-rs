---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

Constants ==
    [rm |-> SUBSET Int]

State ==
    [rm_state |-> SUBSET Int, tm_state |-> TMState, tm_prepared |-> SUBSET Int]

TMState ==
    {Init, Committed, Aborted}

====

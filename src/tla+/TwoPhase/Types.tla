---- MODULE types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

State ==
    [rm_state |-> SUBSET Int, tm_state |-> TMState, tm_prepared |-> SUBSET Int]

Constants ==
    [rm |-> SUBSET Int]

TMState ==
    {Init, Committed, Aborted}

====

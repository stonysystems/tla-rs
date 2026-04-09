------------------------------ MODULE TwoPhase ------------------------------
\* Small Two-Phase Commit model for DPOR protocol case 13.

EXTENDS Naturals

CONSTANT NumRM

VARIABLE rmState, tmState, tmPrepared

RM == 1..NumRM

Init ==
    /\ rmState = {}
    /\ tmState = "init"
    /\ tmPrepared = {}

TMRcvPrepared(r) ==
    /\ tmState = "init"
    /\ r \in RM
    /\ r \notin tmPrepared
    /\ tmPrepared' = tmPrepared \cup {r}
    /\ rmState' = rmState \cup {r}
    /\ tmState' = tmState

TMCommit ==
    /\ tmState = "init"
    /\ tmPrepared = RM
    /\ tmState' = "committed"
    /\ rmState' = rmState
    /\ tmPrepared' = tmPrepared

TMAbort ==
    /\ tmState = "init"
    /\ tmState' = "aborted"
    /\ rmState' = rmState
    /\ tmPrepared' = tmPrepared

Next ==
    \/ \E r \in RM : TMRcvPrepared(r)
    \/ TMCommit
    \/ TMAbort

PreparedWithinRM ==
    \A r \in tmPrepared : r \in RM

TCConsistent ==
    /\ rmState = tmPrepared
    /\ PreparedWithinRM
    /\ tmState = "committed" => tmPrepared = RM

================================================================================

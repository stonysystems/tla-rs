---- MODULE TwoPhaseCommit ----
\* LLM-generated Two-Phase Commit protocol specification.
\* Models a Transaction Manager coordinating Resource Managers.

EXTENDS Naturals, FiniteSets

CONSTANT NumRM

VARIABLE tmState, rmState, prepared, msgs

TMInit == "init"
TMCommitted == "committed"
TMAborted == "aborted"

RMWorking == "working"
RMPrepared == "prepared"
RMCommitted == "committed"
RMAborted == "aborted"

RMs == 1..NumRM

TypeOK ==
    /\ tmState \in {TMInit, TMCommitted, TMAborted}
    /\ rmState \in [RMs -> {RMWorking, RMPrepared, RMCommitted, RMAborted}]
    /\ prepared \subseteq RMs
    /\ msgs \subseteq {"Prepare", "Commit", "Abort"} \cup {<<"Prepared", r>> : r \in RMs}

Init ==
    /\ tmState = TMInit
    /\ rmState = [r \in RMs |-> RMWorking]
    /\ prepared = {}
    /\ msgs = {}

TMSendPrepare ==
    /\ tmState = TMInit
    /\ msgs' = msgs \cup {"Prepare"}
    /\ UNCHANGED <<tmState, rmState, prepared>>

RMPrepare(r) ==
    /\ rmState[r] = RMWorking
    /\ "Prepare" \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = RMPrepared]
    /\ prepared' = prepared \cup {r}
    /\ msgs' = msgs \cup {<<"Prepared", r>>}
    /\ UNCHANGED tmState

TMReceivePrepared(r) ==
    /\ tmState = TMInit
    /\ <<"Prepared", r>> \in msgs
    /\ prepared' = prepared \cup {r}
    /\ UNCHANGED <<tmState, rmState, msgs>>

TMCommit ==
    /\ tmState = TMInit
    /\ prepared = RMs
    /\ tmState' = TMCommitted
    /\ msgs' = msgs \cup {"Commit"}
    /\ UNCHANGED <<rmState, prepared>>

TMAbort ==
    /\ tmState = TMInit
    /\ tmState' = TMAborted
    /\ msgs' = msgs \cup {"Abort"}
    /\ UNCHANGED <<rmState, prepared>>

RMCommit(r) ==
    /\ rmState[r] = RMPrepared
    /\ "Commit" \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = RMCommitted]
    /\ UNCHANGED <<tmState, prepared, msgs>>

RMAbort(r) ==
    /\ rmState[r] \in {RMWorking, RMPrepared}
    /\ "Abort" \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = RMAborted]
    /\ UNCHANGED <<tmState, prepared, msgs>>

Next ==
    \/ TMSendPrepare
    \/ TMCommit
    \/ TMAbort
    \/ \E r \in RMs : RMPrepare(r)
    \/ \E r \in RMs : TMReceivePrepared(r)
    \/ \E r \in RMs : RMCommit(r)
    \/ \E r \in RMs : RMAbort(r)

Spec == Init /\ [][Next]_<<tmState, rmState, prepared, msgs>>

Consistency ==
    \A r1, r2 \in RMs :
        ~ (rmState[r1] = RMCommitted /\ rmState[r2] = RMAborted)

====

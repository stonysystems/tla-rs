------------------------------ MODULE TwoPhase ------------------------------
(* A simplified Two-Phase Commit protocol.
   This version uses simpler syntax for parser compatibility. *)

EXTENDS Naturals

CONSTANT RM

VARIABLE rmState, tmState, tmPrepared

Init == rmState = {} /\ tmState = "init" /\ tmPrepared = {}

TMRcvPrepared(r) == tmState = "init" /\ tmPrepared' = tmPrepared \cup {r} /\ rmState' = rmState /\ tmState' = tmState

TMCommit == tmState = "init" /\ tmPrepared = RM /\ tmState' = "committed" /\ rmState' = rmState /\ tmPrepared' = tmPrepared

TMAbort == tmState = "init" /\ tmState' = "aborted" /\ rmState' = rmState /\ tmPrepared' = tmPrepared

Next == TMCommit \/ TMAbort

================================================================================

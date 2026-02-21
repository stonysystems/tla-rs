---- MODULE Primarybackup_MC ----
\* Auto-generated model-check wrapper for relational spec pattern.
\* Source module: Primarybackup

EXTENDS Primarybackup

VARIABLE state, constants

StateInit ==
    /\ state \in State
    /\ constants \in Constants
    /\ Init(state, constants)

StateNext ==
    /\ \E state_ \in State :
        /\ Next(state, state_, constants)
        /\ state' = state_
    /\ UNCHANGED constants

vars == <<state, constants>>

Spec == StateInit /\ [][StateNext]_vars

====

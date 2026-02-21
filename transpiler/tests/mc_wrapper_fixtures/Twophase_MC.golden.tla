---- MODULE Twophase_MC ----
\* Auto-generated model-check wrapper for relational spec pattern.
\* Source module: Twophase

EXTENDS Twophase

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

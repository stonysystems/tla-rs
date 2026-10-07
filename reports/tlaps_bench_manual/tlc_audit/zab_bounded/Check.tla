---- MODULE Check ----
EXTENDS ZabDefs
Bound == /\ \A i \in Server: /\ acceptedEpoch[i] <= 2 /\ currentEpoch[i] <= 2 /\ Len(history[i]) <= 3
         /\ \A i,j \in Server: Len(msgs[i][j]) <= 2
====

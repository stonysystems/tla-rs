---- MODULE CounterIncDec ----
\* Tiny shared-state model: two processes can independently increment or decrement.

CONSTANT NumProcs
VARIABLE counter, pc

Procs == 1..NumProcs

Init == counter = 0 /\ pc = [p \in Procs |-> "ready"]

Increment(p) ==
    /\ pc[p] = "ready"
    /\ counter' = counter + 1
    /\ pc' = [pc EXCEPT ![p] = "done"]

Decrement(p) ==
    /\ pc[p] = "ready"
    /\ counter >= 1
    /\ counter' = counter - 1
    /\ pc' = [pc EXCEPT ![p] = "done"]

Next == \E p \in Procs : Increment(p) \/ Decrement(p)

TypeOK == counter >= 0

====

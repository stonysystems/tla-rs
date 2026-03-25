---- MODULE CounterRaceBug ----
\* Negative case: two processes read-then-write a shared counter.
\* The interleaving causes a lost update — invariant TotalCorrect is violated.

CONSTANT NumProcs
VARIABLE counter, local, pc

Procs == 1..NumProcs

Init ==
    /\ counter = 0
    /\ local = [p \in Procs |-> 0]
    /\ pc = [p \in Procs |-> "read"]

Read(p) ==
    /\ pc[p] = "read"
    /\ local' = [local EXCEPT ![p] = counter]
    /\ pc' = [pc EXCEPT ![p] = "write"]
    /\ UNCHANGED counter

Write(p) ==
    /\ pc[p] = "write"
    /\ counter' = local[p] + 1
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED local

Next == \E p \in Procs : Read(p) \/ Write(p)

\* This invariant is VIOLATED: after all procs finish, counter should equal
\* NumProcs, but lost updates cause counter < NumProcs.
AllDone == \A p \in Procs : pc[p] = "done"
TotalCorrect == AllDone => counter = NumProcs

====

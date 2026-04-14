---- MODULE BrokenLockBug ----
EXTENDS Naturals
\* Negative case: a broken lock that doesn't check the lock variable before entering.
\* MutualExclusion invariant is VIOLATED.

CONSTANT NumProcs
VARIABLE lock, pc

Procs == 1..NumProcs

Init == lock = 0 /\ pc = [p \in Procs |-> "idle"]

\* BUG: no check on lock — both processes can enter critical section
Acquire(p) ==
    /\ pc[p] = "idle"
    /\ lock' = p
    /\ pc' = [pc EXCEPT ![p] = "critical"]

Release(p) ==
    /\ pc[p] = "critical"
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![p] = "idle"]

Next == \E p \in Procs : Acquire(p) \/ Release(p)

MutualExclusion ==
    \A p1, p2 \in Procs :
        (pc[p1] = "critical" /\ pc[p2] = "critical") => p1 = p2

====

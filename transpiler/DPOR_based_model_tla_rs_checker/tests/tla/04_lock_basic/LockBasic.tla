---- MODULE LockBasic ----
EXTENDS Naturals
\* Basic mutual exclusion with a single lock variable.
\* Two processes acquire/release; invariant: at most one in critical section.

CONSTANT NumProcs
VARIABLE lock, pc

Procs == 1..NumProcs

Init == lock = 0 /\ pc = [p \in Procs |-> "idle"]

Acquire(p) ==
    /\ pc[p] = "idle"
    /\ lock = 0
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

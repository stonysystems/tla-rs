---- MODULE DiningPhilosophers ----
\* Dining philosophers with 3 philosophers. Deadlock is expected.

CONSTANT NumPhil
VARIABLE fork, pc

Phil == 1..NumPhil

\* Fork i is between philosopher i and philosopher (i % N) + 1
LeftFork(p) == p
RightFork(p) == (p % NumPhil) + 1

Init ==
    /\ fork = [f \in Phil |-> 0]  \* 0 = free, p = held by philosopher p
    /\ pc = [p \in Phil |-> "thinking"]

PickLeftFork(p) ==
    /\ pc[p] = "thinking"
    /\ fork[LeftFork(p)] = 0
    /\ fork' = [fork EXCEPT ![LeftFork(p)] = p]
    /\ pc' = [pc EXCEPT ![p] = "has_left"]

PickRightFork(p) ==
    /\ pc[p] = "has_left"
    /\ fork[RightFork(p)] = 0
    /\ fork' = [fork EXCEPT ![RightFork(p)] = p]
    /\ pc' = [pc EXCEPT ![p] = "eating"]

PutForks(p) ==
    /\ pc[p] = "eating"
    /\ fork' = [fork EXCEPT ![LeftFork(p)] = 0, ![RightFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "thinking"]

Next == \E p \in Phil : PickLeftFork(p) \/ PickRightFork(p) \/ PutForks(p)

\* This invariant is checked, but the real test is DEADLOCK detection:
\* all philosophers hold their left fork and wait for the right fork.
NoStarvation == \E p \in Phil : pc[p] # "has_left"

====

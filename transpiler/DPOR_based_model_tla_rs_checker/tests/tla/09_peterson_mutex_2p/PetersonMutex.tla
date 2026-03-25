---- MODULE PetersonMutex ----
\* Peterson's mutual exclusion algorithm for 2 processes.

VARIABLE flag, turn, pc

P == {0, 1}

Init ==
    /\ flag = [p \in P |-> FALSE]
    /\ turn = 0
    /\ pc = [p \in P |-> "idle"]

Other(p) == 1 - p

SetFlag(p) ==
    /\ pc[p] = "idle"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ turn' = Other(p)
    /\ pc' = [pc EXCEPT ![p] = "waiting"]

Enter(p) ==
    /\ pc[p] = "waiting"
    /\ (~flag[Other(p)] \/ turn = p)
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<flag, turn>>

Exit(p) ==
    /\ pc[p] = "critical"
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED turn

Next == \E p \in P : SetFlag(p) \/ Enter(p) \/ Exit(p)

MutualExclusion ==
    ~(pc[0] = "critical" /\ pc[1] = "critical")

====

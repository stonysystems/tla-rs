---- MODULE BakeryMutexBug ----
EXTENDS Naturals
\* NEGATIVE variant: Bakery algorithm with broken priority check.
\* Omits the process-ID tiebreaker, allowing two processes with
\* the same number to both enter the critical section.

CONSTANT NumProcs
VARIABLE choosing, number, pc

Procs == 1..NumProcs

Init ==
    /\ choosing = [p \in Procs |-> FALSE]
    /\ number = [p \in Procs |-> 0]
    /\ pc = [p \in Procs |-> "idle"]

MaxNumber == LET S == {number[q] : q \in Procs}
             IN CHOOSE m \in S : \A n \in S : n <= m

StartChoosing(p) ==
    /\ pc[p] = "idle"
    /\ choosing' = [choosing EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED number

PickNumber(p) ==
    /\ pc[p] = "choosing"
    /\ number' = [number EXCEPT ![p] = MaxNumber + 1]
    /\ choosing' = [choosing EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "waiting"]

\* BUG: missing tiebreaker (p < q) — two processes with same number both enter
Enter(p) ==
    /\ pc[p] = "waiting"
    /\ \A q \in Procs \ {p} :
        /\ ~choosing[q]
        /\ (number[q] = 0 \/ number[p] < number[q])
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<choosing, number>>

Exit(p) ==
    /\ pc[p] = "critical"
    /\ number' = [number EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED choosing

Next == \E p \in Procs : StartChoosing(p) \/ PickNumber(p) \/ Enter(p) \/ Exit(p)

\* VIOLATED: two processes with equal numbers can both enter
MutualExclusion ==
    \A p1, p2 \in Procs :
        (pc[p1] = "critical" /\ pc[p2] = "critical") => p1 = p2

====

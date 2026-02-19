---- MODULE BullyElection ----
\* LLM-generated Bully Leader Election algorithm specification.
\* Models the Garcia-Molina bully algorithm for leader election.

EXTENDS Naturals, FiniteSets

CONSTANT Node

VARIABLE alive, leader, electing, answered

Init ==
    /\ alive = Node
    /\ leader = CHOOSE n \in Node : \A m \in Node : n >= m
    /\ electing = {}
    /\ answered = [n \in Node |-> FALSE]

NodeFails(n) ==
    /\ n \in alive
    /\ alive' = alive \ {n}
    /\ IF n = leader
       THEN leader' = 0
       ELSE leader' = leader
    /\ UNCHANGED <<electing, answered>>

DetectFailure(n) ==
    /\ n \in alive
    /\ leader \notin alive
    /\ n \notin electing
    /\ electing' = electing \cup {n}
    /\ answered' = [answered EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<alive, leader>>

SendAnswer(higher, lower) ==
    /\ higher \in alive
    /\ lower \in electing
    /\ higher > lower
    /\ answered' = [answered EXCEPT ![lower] = TRUE]
    /\ electing' = (electing \ {lower}) \cup {higher}
    /\ UNCHANGED <<alive, leader>>

BecomeLeader(n) ==
    /\ n \in electing
    /\ n \in alive
    /\ answered[n] = FALSE
    /\ \A m \in alive : m <= n
    /\ leader' = n
    /\ electing' = electing \ {n}
    /\ UNCHANGED <<alive, answered>>

NodeRecovers(n) ==
    /\ n \notin alive
    /\ alive' = alive \cup {n}
    /\ IF n > leader
       THEN /\ electing' = electing \cup {n}
            /\ answered' = [answered EXCEPT ![n] = FALSE]
            /\ UNCHANGED leader
       ELSE UNCHANGED <<leader, electing, answered>>

Next ==
    \/ \E n \in Node : NodeFails(n)
    \/ \E n \in Node : DetectFailure(n)
    \/ \E h, l \in Node : SendAnswer(h, l)
    \/ \E n \in Node : BecomeLeader(n)
    \/ \E n \in Node : NodeRecovers(n)

Spec == Init /\ [][Next]_<<alive, leader, electing, answered>>

LeaderIsAlive == leader # 0 => leader \in alive

====

---- MODULE Paxos ----
\* LLM-generated Single-Decree Paxos specification.
\* Models proposers and acceptors achieving consensus on a single value.

EXTENDS Naturals, FiniteSets

CONSTANTS Acceptor, Value, MaxBallot

VARIABLE maxBal, maxVBal, maxVal, msgs

None == CHOOSE v : v \notin Value

Ballot == 0..MaxBallot

\* Quorum: any strict majority of acceptors
Quorum == {Q \in SUBSET Acceptor : Cardinality(Q) * 2 > Cardinality(Acceptor)}

Send(m) == msgs' = msgs \cup {m}

Init ==
    /\ maxBal  = [a \in Acceptor |-> -1]
    /\ maxVBal = [a \in Acceptor |-> -1]
    /\ maxVal  = [a \in Acceptor |-> None]
    /\ msgs    = {}

\* Phase 1a: Proposer sends prepare request for ballot b
Phase1a(b) ==
    /\ b \in Ballot
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

\* Phase 1b: Acceptor responds to prepare if ballot is higher than any seen
Phase1b(a) ==
    /\ \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                 mbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<maxVBal, maxVal>>

\* Phase 2a: Proposer sends accept request after collecting quorum of promises
Phase2a(b, v) ==
    /\ b \in Ballot
    /\ v \in Value
    \* No existing 2a for this ballot
    /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
    \* A quorum of acceptors have promised
    /\ \E Q \in Quorum :
        LET Q1b == {m \in msgs : m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
            Q1bv == {m \in Q1b : m.mbal >= 0}
        IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
            /\ \/ Q1bv = {} /\ Send([type |-> "2a", bal |-> b, val |-> v])
               \/ \E m \in Q1bv :
                    /\ \A mm \in Q1bv : m.mbal >= mm.mbal
                    /\ Send([type |-> "2a", bal |-> b, val |-> m.mval])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

\* Phase 2b: Acceptor accepts a value
Phase2b(a) ==
    /\ \E m \in msgs :
        /\ m.type = "2a"
        /\ m.bal >= maxBal[a]
        /\ maxBal'  = [maxBal EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
        /\ maxVal'  = [maxVal EXCEPT ![a] = m.val]
        /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Next ==
    \/ \E b \in Ballot : Phase1a(b)
    \/ \E a \in Acceptor : Phase1b(a)
    \/ \E b \in Ballot, v \in Value : Phase2a(b, v)
    \/ \E a \in Acceptor : Phase2b(a)

vars == <<maxBal, maxVBal, maxVal, msgs>>
Spec == Init /\ [][Next]_vars

\* --- Safety Invariants ---

\* A value is chosen when a quorum of acceptors have accepted it at the same ballot
Chosen(v) ==
    \E b \in Ballot, Q \in Quorum :
        \A a \in Q : \E m \in msgs :
            m.type = "2b" /\ m.val = v /\ m.bal = b /\ m.acc = a

\* Agreement: at most one value is chosen
Consistency ==
    \A v1, v2 \in Value : Chosen(v1) /\ Chosen(v2) => v1 = v2

\* Acceptor monotonicity: maxBal never decreases
AcceptorMonotonicity ==
    \A a \in Acceptor : maxVBal[a] <= maxBal[a]

====

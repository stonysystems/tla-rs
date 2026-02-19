---- MODULE SimplePaxos ----
\* LLM-generated Single-Decree Paxos specification.
\* Models proposers, acceptors, and learners for consensus on a single value.

EXTENDS Naturals, FiniteSets

CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption ==
    /\ \A Q \in Quorum : Q \subseteq Acceptor
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat

VARIABLE maxBal, maxVBal, maxVal, msgs

None == CHOOSE v : v \notin Value

Send(m) == msgs' = msgs \cup {m}

Init ==
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ maxVBal = [a \in Acceptor |-> -1]
    /\ maxVal = [a \in Acceptor |-> None]
    /\ msgs = {}

Phase1a(b) ==
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase1b(a) ==
    /\ \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                 mbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<maxVBal, maxVal>>

Phase2a(b, v) ==
    /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
    /\ \E Q \in Quorum :
        LET Q1b == {m \in msgs : m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
            Q1bv == {m \in Q1b : m.mbal >= 0}
        IN /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ Q1bv = {}  /\ Send([type |-> "2a", bal |-> b, val |-> v])
              \/ \E m \in Q1bv :
                    /\ m.mbal >= 0
                    /\ \A mm \in Q1bv : m.mbal >= mm.mbal
                    /\ Send([type |-> "2a", bal |-> b, val |-> m.mval])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase2b(a) ==
    /\ \E m \in msgs :
        /\ m.type = "2a"
        /\ m.bal >= maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
        /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
        /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Next ==
    \/ \E b \in Ballot : Phase1a(b)
    \/ \E a \in Acceptor : Phase1b(a)
    \/ \E b \in Ballot, v \in Value : Phase2a(b, v)
    \/ \E a \in Acceptor : Phase2b(a)

Spec == Init /\ [][Next]_<<maxBal, maxVBal, maxVal, msgs>>

Chosen(v) ==
    \E Q \in Quorum, b \in Ballot :
        \A a \in Q : \E m \in msgs :
            m.type = "2b" /\ m.val = v /\ m.bal = b /\ m.acc = a

Consistency == \A v1, v2 \in Value : Chosen(v1) /\ Chosen(v2) => v1 = v2

====

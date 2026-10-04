----------------------- MODULE CoordinatedPaxos -----------------------
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Quorums, MaxBallot, Commands
ASSUME /\ Acceptors # {}
       /\ Quorums \subseteq SUBSET Acceptors
       /\ Quorums # {}
       /\ \A q, r \in Quorums: q \cap r # {}
       /\ 0 \notin Commands /\ -1 \notin Commands
       /\ MaxBallot \in Nat
Ballots == 0..MaxBallot
NoValue == -1
NoOp == 0
Values == Commands \cup {NoOp}

VARIABLES promise, lastBallot, lastValue, proposals, votes
vars == <<promise, lastBallot, lastValue, proposals, votes>>

Init == /\ promise = [a \in Acceptors |-> 0]
        /\ lastBallot = [a \in Acceptors |-> -1]
        /\ lastValue = [a \in Acceptors |-> NoOp]
        /\ proposals = [b \in Ballots |-> NoValue]
        /\ votes = {}

Suggest(v) == /\ proposals[0] = NoValue
              /\ proposals' = [proposals EXCEPT ![0] = v]
              /\ UNCHANGED <<promise, lastBallot, lastValue, votes>>

Highest(q) == CHOOSE a \in q: \A n \in q: lastBallot[n] <= lastBallot[a]
Revoke(b, q) ==
    LET a == Highest(q)
        v == IF lastBallot[a] = -1 THEN NoOp ELSE lastValue[a]
    IN /\ proposals[b] = NoValue
       /\ \A n \in q: promise[n] < b
       /\ promise' = [n \in Acceptors |-> IF n \in q THEN b ELSE promise[n]]
       /\ proposals' = [proposals EXCEPT ![b] = v]
       /\ UNCHANGED <<lastBallot, lastValue, votes>>

Accept(a, b) == /\ proposals[b] # NoValue
                /\ b >= promise[a]
                /\ promise' = [promise EXCEPT ![a] = b]
                /\ lastBallot' = [lastBallot EXCEPT ![a] = b]
                /\ lastValue' = [lastValue EXCEPT ![a] = proposals[b]]
                /\ votes' = votes \cup {<<a, b, proposals[b]>>}
                /\ UNCHANGED proposals

Next == \/ \E v \in Values: Suggest(v)
        \/ \E b \in 1..MaxBallot, q \in Quorums: Revoke(b, q)
        \/ \E a \in Acceptors, b \in Ballots: Accept(a, b)

QuorumChosen(b, v) == \E q \in Quorums: \A a \in q: <<a, b, v>> \in votes
Learned(v) == \/ (v = NoOp /\ proposals[0] = NoOp)
              \/ \E b \in Ballots: QuorumChosen(b, v)
Agreement == \A v, w \in Values: Learned(v) /\ Learned(w) => v = w
CoordinatorOrigin == \A v \in Commands: Learned(v) => proposals[0] = v
TypeOK == /\ promise \in [Acceptors -> Ballots]
          /\ lastBallot \in [Acceptors -> (-1..MaxBallot)]
          /\ lastValue \in [Acceptors -> Values]
          /\ proposals \in [Ballots -> (Values \cup {NoValue})]
          /\ votes \subseteq (Acceptors \X Ballots \X Values)
Spec == Init /\ [][Next]_vars
======================================================================

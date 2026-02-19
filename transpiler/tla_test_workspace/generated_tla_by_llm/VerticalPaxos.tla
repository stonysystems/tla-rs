---- MODULE VerticalPaxos ----
\* LLM-generated Vertical Paxos specification.
\* Models reconfigurable consensus with ballot-based rounds and witness sync.

EXTENDS Naturals, FiniteSets

CONSTANT Node, MaxBallot

VARIABLE ballot, promised, acceptedBal, acceptedVal, decided, witnessVal

None == -1

Init ==
    /\ ballot = [n \in Node |-> 0]
    /\ promised = [n \in Node |-> -1]
    /\ acceptedBal = [n \in Node |-> -1]
    /\ acceptedVal = [n \in Node |-> None]
    /\ decided = [n \in Node |-> FALSE]
    /\ witnessVal = [n \in Node |-> None]

Prepare(proposer, b) ==
    /\ b > ballot[proposer]
    /\ b <= MaxBallot
    /\ ballot' = [ballot EXCEPT ![proposer] = b]
    /\ UNCHANGED <<promised, acceptedBal, acceptedVal, decided, witnessVal>>

SendPromise(acceptor, proposer) ==
    /\ ballot[proposer] > promised[acceptor]
    /\ promised' = [promised EXCEPT ![acceptor] = ballot[proposer]]
    /\ UNCHANGED <<ballot, acceptedBal, acceptedVal, decided, witnessVal>>

Accept(proposer, acceptor, val) ==
    /\ ballot[proposer] >= promised[acceptor]
    /\ val # None
    /\ acceptedBal' = [acceptedBal EXCEPT ![acceptor] = ballot[proposer]]
    /\ acceptedVal' = [acceptedVal EXCEPT ![acceptor] = val]
    /\ UNCHANGED <<ballot, promised, decided, witnessVal>>

Commit(proposer) ==
    /\ ~decided[proposer]
    /\ LET accepting == {n \in Node : acceptedBal[n] = ballot[proposer]}
       IN Cardinality(accepting) * 2 > Cardinality(Node)
    /\ decided' = [decided EXCEPT ![proposer] = TRUE]
    /\ UNCHANGED <<ballot, promised, acceptedBal, acceptedVal, witnessVal>>

WitnessSync(node, witness) ==
    /\ node # witness
    /\ acceptedVal[witness] # None
    /\ witnessVal' = [witnessVal EXCEPT ![node] = acceptedVal[witness]]
    /\ UNCHANGED <<ballot, promised, acceptedBal, acceptedVal, decided>>

Next ==
    \/ \E p \in Node, b \in 1..MaxBallot : Prepare(p, b)
    \/ \E a, p \in Node : SendPromise(a, p)
    \/ \E p, a \in Node, v \in Nat : Accept(p, a, v)
    \/ \E p \in Node : Commit(p)
    \/ \E n, w \in Node : WitnessSync(n, w)

Spec == Init /\ [][Next]_<<ballot, promised, acceptedBal, acceptedVal, decided, witnessVal>>

DecisionConsistency ==
    \A n1, n2 \in Node :
        (decided[n1] /\ decided[n2]) => acceptedVal[n1] = acceptedVal[n2]

====

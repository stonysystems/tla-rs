----------------------- MODULE ChainReplication -----------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Requests, InitialNodes, MaxNodes
ASSUME /\ InitialNodes \in Nat \ {0}
       /\ MaxNodes >= InitialNodes

VARIABLES history, alive, submitted, previous
vars == <<history, alive, submitted, previous>>

Prefix(a, b) == /\ Len(a) <= Len(b)
                /\ \A k \in 1..Len(a): a[k] = b[k]
Committed == history[Len(history)]
RemoveAt(a, i) == [j \in 1..(Len(a)-1) |-> a[IF j < i THEN j ELSE j+1]]

Init == /\ history = [i \in 1..InitialNodes |-> <<>>]
        /\ alive = [i \in 1..InitialNodes |-> TRUE]
        /\ submitted = {}
        /\ previous = <<>>

Write(r) == /\ alive[1]
            /\ r \notin submitted
            /\ history' = [history EXCEPT ![1] = Append(@, r)]
            /\ submitted' = submitted \cup {r}
            /\ previous' = Committed
            /\ UNCHANGED alive

Forward(i) == /\ i \in 2..Len(history)
              /\ alive[i]
              /\ Len(history[i]) < Len(history[i-1])
              /\ history' = [history EXCEPT
                   ![i] = Append(@, history[i-1][Len(history[i])+1])]
              /\ previous' = Committed
              /\ UNCHANGED <<alive, submitted>>

Crash(i) == /\ alive' = [alive EXCEPT ![i] = FALSE]
            /\ previous' = Committed
            /\ UNCHANGED <<history, submitted>>

RemoveFailed(i) == /\ Len(history) > 1
                   /\ ~alive[i]
                   /\ history' = RemoveAt(history, i)
                   /\ alive' = RemoveAt(alive, i)
                   /\ previous' = Committed
                   /\ UNCHANGED submitted

Extend == /\ Len(history) < MaxNodes
          /\ alive[Len(history)]
          /\ history' = Append(history, Committed)
          /\ alive' = Append(alive, TRUE)
          /\ previous' = Committed
          /\ UNCHANGED submitted

Next == \/ \E r \in Requests: Write(r)
        \/ \E i \in 2..Len(history): Forward(i)
        \/ \E i \in 1..Len(history): Crash(i) \/ RemoveFailed(i)
        \/ Extend

TypeOK == /\ history \in Seq(Seq(Requests))
          /\ Len(history) \in 1..MaxNodes
          /\ alive \in [1..Len(history) -> BOOLEAN]
          /\ submitted \subseteq Requests
          /\ previous \in Seq(Requests)
Propagation == \A i, j \in 1..Len(history):
                 i <= j => Prefix(history[j], history[i])
Validity == \A i \in 1..Len(history):
              \A k \in 1..Len(history[i]): history[i][k] \in submitted
Unique == \A i \in 1..Len(history):
            \A k, l \in 1..Len(history[i]):
              k < l => history[i][k] # history[i][l]
CompletedPrefix == Prefix(previous, Committed)
Spec == Init /\ [][Next]_vars
=======================================================================

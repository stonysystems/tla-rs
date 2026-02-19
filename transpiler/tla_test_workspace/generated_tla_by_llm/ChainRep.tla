---- MODULE ChainRep ----
\* LLM-generated Chain Replication specification.
\* Models a chain of nodes forwarding writes from head to tail.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANT ChainLen, MaxVal

VARIABLE nodeLog, alive, pending

Nodes == 1..ChainLen
Head == 1
Tail == ChainLen

Init ==
    /\ nodeLog = [n \in Nodes |-> <<>>]
    /\ alive = Nodes
    /\ pending = [n \in Nodes |-> <<>>]

IsHead(n) == n = Head
IsTail(n) == n = Tail
Successor(n) == IF n < ChainLen THEN n + 1 ELSE 0
Predecessor(n) == IF n > 1 THEN n - 1 ELSE 0

ClientWrite(val) ==
    /\ Head \in alive
    /\ nodeLog' = [nodeLog EXCEPT ![Head] = Append(nodeLog[Head], val)]
    /\ pending' = [pending EXCEPT ![Head] = Append(pending[Head], val)]
    /\ UNCHANGED alive

ForwardToNext(n) ==
    /\ n \in alive
    /\ n # Tail
    /\ Successor(n) \in alive
    /\ Len(pending[n]) > 0
    /\ LET val == Head(pending[n])
           next == Successor(n)
       IN /\ nodeLog' = [nodeLog EXCEPT ![next] = Append(nodeLog[next], val)]
          /\ pending' = [pending EXCEPT
                ![n] = Tail(pending[n]),
                ![next] = Append(pending[next], val)]
    /\ UNCHANGED alive

Acknowledge(n) ==
    /\ n \in alive
    /\ IsTail(n)
    /\ Len(pending[n]) > 0
    /\ pending' = [pending EXCEPT ![n] = Tail(pending[n])]
    /\ UNCHANGED <<nodeLog, alive>>

NodeFail(n) ==
    /\ n \in alive
    /\ Cardinality(alive) > 1
    /\ alive' = alive \ {n}
    /\ UNCHANGED <<nodeLog, pending>>

Next ==
    \/ \E v \in 1..MaxVal : ClientWrite(v)
    \/ \E n \in Nodes : ForwardToNext(n)
    \/ \E n \in Nodes : Acknowledge(n)
    \/ \E n \in Nodes : NodeFail(n)

Spec == Init /\ [][Next]_<<nodeLog, alive, pending>>

\* Safety: tail log is a prefix of head log
TailPrefix ==
    Tail \in alive =>
        \A i \in 1..Len(nodeLog[Tail]) : nodeLog[Tail][i] = nodeLog[Head][i]

====

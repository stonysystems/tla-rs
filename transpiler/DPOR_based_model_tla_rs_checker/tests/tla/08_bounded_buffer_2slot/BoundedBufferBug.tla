---- MODULE BoundedBufferBug ----
EXTENDS Naturals
\* NEGATIVE variant: bounded buffer without proper count check.
\* Producer can write when buffer is full, causing data loss.

CONSTANT MaxVal
VARIABLE buf, head, tail, count, produced, consumed

Init ==
    /\ buf = [i \in {0, 1} |-> 0]
    /\ head = 0
    /\ tail = 0
    /\ count = 0
    /\ produced = 0
    /\ consumed = 0

\* BUG: no check on count < 2 — producer can overwrite
Produce ==
    /\ produced < MaxVal
    /\ buf' = [buf EXCEPT ![tail] = produced + 1]
    /\ tail' = (tail + 1) % 2
    /\ count' = count + 1
    /\ produced' = produced + 1
    /\ UNCHANGED <<head, consumed>>

Consume ==
    /\ count > 0
    /\ consumed' = buf[head]
    /\ head' = (head + 1) % 2
    /\ count' = count - 1
    /\ UNCHANGED <<buf, tail, produced>>

Next == Produce \/ Consume

\* This WILL be violated: count can exceed 2
BufferNotOverflow == count >= 0 /\ count <= 2

====

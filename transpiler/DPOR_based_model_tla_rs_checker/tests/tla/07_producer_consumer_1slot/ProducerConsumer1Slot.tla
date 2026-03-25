---- MODULE ProducerConsumer1Slot ----
\* Single-slot buffer: one producer, one consumer.

VARIABLE buf, buf_full, produced, consumed

Init ==
    /\ buf = 0
    /\ buf_full = FALSE
    /\ produced = 0
    /\ consumed = 0

Produce ==
    /\ ~buf_full
    /\ buf' = produced + 1
    /\ buf_full' = TRUE
    /\ produced' = produced + 1
    /\ UNCHANGED consumed

Consume ==
    /\ buf_full
    /\ consumed' = buf
    /\ buf_full' = FALSE
    /\ UNCHANGED <<buf, produced>>

Next == Produce \/ Consume

\* Consumer only sees values the producer wrote
SafetyInvariant == consumed <= produced

====

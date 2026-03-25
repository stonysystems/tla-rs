---- MODULE ReadersWritersBug ----
\* NEGATIVE variant: writer doesn't check for active readers.
\* Safety invariant is VIOLATED — writer enters while readers are active.

CONSTANT NumReaders, NumWriters
VARIABLE readers_active, writer_active, reader_pc, writer_pc

Readers == 1..NumReaders
Writers == 1..NumWriters

Init ==
    /\ readers_active = 0
    /\ writer_active = FALSE
    /\ reader_pc = [r \in Readers |-> "idle"]
    /\ writer_pc = [w \in Writers |-> "idle"]

ReaderEnter(r) ==
    /\ reader_pc[r] = "idle"
    /\ ~writer_active
    /\ readers_active' = readers_active + 1
    /\ reader_pc' = [reader_pc EXCEPT ![r] = "reading"]
    /\ UNCHANGED <<writer_active, writer_pc>>

ReaderExit(r) ==
    /\ reader_pc[r] = "reading"
    /\ readers_active' = readers_active - 1
    /\ reader_pc' = [reader_pc EXCEPT ![r] = "idle"]
    /\ UNCHANGED <<writer_active, writer_pc>>

\* BUG: writer doesn't check readers_active = 0
WriterEnter(w) ==
    /\ writer_pc[w] = "idle"
    /\ ~writer_active
    /\ writer_active' = TRUE
    /\ writer_pc' = [writer_pc EXCEPT ![w] = "writing"]
    /\ UNCHANGED <<readers_active, reader_pc>>

WriterExit(w) ==
    /\ writer_pc[w] = "writing"
    /\ writer_active' = FALSE
    /\ writer_pc' = [writer_pc EXCEPT ![w] = "idle"]
    /\ UNCHANGED <<readers_active, reader_pc>>

Next ==
    \/ \E r \in Readers : ReaderEnter(r) \/ ReaderExit(r)
    \/ \E w \in Writers : WriterEnter(w) \/ WriterExit(w)

\* VIOLATED: writer can be active while readers are reading
Safety ==
    /\ (writer_active => readers_active = 0)
    /\ (readers_active > 0 => ~writer_active)

====

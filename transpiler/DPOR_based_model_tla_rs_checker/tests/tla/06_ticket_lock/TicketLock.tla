---- MODULE TicketLock ----
\* Ticket-based mutual exclusion: processes take a number, wait for their turn.

CONSTANT NumProcs
VARIABLE next_ticket, serving, my_ticket, pc

Procs == 1..NumProcs

Init ==
    /\ next_ticket = 1
    /\ serving = 1
    /\ my_ticket = [p \in Procs |-> 0]
    /\ pc = [p \in Procs |-> "idle"]

TakeTicket(p) ==
    /\ pc[p] = "idle"
    /\ my_ticket' = [my_ticket EXCEPT ![p] = next_ticket]
    /\ next_ticket' = next_ticket + 1
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ UNCHANGED serving

Enter(p) ==
    /\ pc[p] = "waiting"
    /\ my_ticket[p] = serving
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<next_ticket, serving, my_ticket>>

Exit(p) ==
    /\ pc[p] = "critical"
    /\ serving' = serving + 1
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<next_ticket, my_ticket>>

Next == \E p \in Procs : TakeTicket(p) \/ Enter(p) \/ Exit(p)

MutualExclusion ==
    \A p1, p2 \in Procs :
        (pc[p1] = "critical" /\ pc[p2] = "critical") => p1 = p2

====

---- MODULE broadcast ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Configuration, RslMessage, AbstractEndPoint, RslPacket

BroadcastToEveryone(c, myidx, m, sent_packets) ==
    /\ Len(sent_packets) = Len(c.replica_ids)
    /\ 0 <= myidx
    /\ myidx < Len(c.replica_ids)
    /\ \A idx \in Int : (0 <= idx /\ idx < Len(sent_packets)) => sent_packets[idx] = [dst |-> c.replica_ids[idx], src |-> c.replica_ids[myidx], msg |-> m]

RECURSIVE BuildLBroadcast(_, _, _)
BuildLBroadcast(src, dsts, m) ==
    IF Len(dsts) = 0 THEN <<>> ELSE <<[dst |-> dsts[0], src |-> src, msg |-> m]>> + BuildLBroadcast(src, skip(dsts, 1), m)

====

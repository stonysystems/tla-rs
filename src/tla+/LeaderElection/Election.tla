---- MODULE election ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Constants, State

Init(s, c) ==
    /\ s.electing = {}
    /\ s.has_leader = FALSE
    /\ s.leader = 0
    /\ s.alive = c.nodes
    /\ s.has_highest = FALSE
    /\ s.highest_heard = 0

StartElection(s, s_, c, node) ==
    /\ node \in s.alive
    /\ s_.electing = s.electing \cup {node}
    /\ s_.has_leader = FALSE
    /\ s_.leader = 0
    /\ s_.alive = s.alive
    /\ s_.has_highest = s.has_highest
    /\ s_.highest_heard = s.highest_heard

RespondHigher(s, s_, c, node) ==
    /\ node \in s.alive
    /\ ~s.has_highest \/ node > s.highest_heard
    /\ s_.has_highest = TRUE
    /\ s_.highest_heard = node
    /\ s_.electing = s.electing
    /\ s_.has_leader = s.has_leader
    /\ s_.leader = s.leader
    /\ s_.alive = s.alive

BecomeLeader(s, s_, c, node) ==
    /\ node \in s.alive
    /\ node \in s.electing
    /\ s_.has_leader = TRUE
    /\ s_.leader = node
    /\ s_.electing = s.electing \ {node}
    /\ s_.alive = s.alive
    /\ s_.has_highest = s.has_highest
    /\ s_.highest_heard = s.highest_heard

NodeFail(s, s_, c, node) ==
    /\ node \in s.alive
    /\ s_.alive = s.alive \ {node}
    /\ s_.electing = s.electing \ {node}
    /\ IF s.has_leader /\ s.leader = node THEN s_.has_leader = FALSE /\ s_.leader = 0 ELSE s_.has_leader = s.has_leader /\ s_.leader = s.leader
    /\ s_.has_highest = s.has_highest
    /\ s_.highest_heard = s.highest_heard

Next(s, s_, c) ==
    \/ \E node \in Int : StartElection(s, s_, c, node)
    \/ \E node \in Int : RespondHigher(s, s_, c, node)
    \/ \E node \in Int : BecomeLeader(s, s_, c, node)
    \/ \E node \in Int : NodeFail(s, s_, c, node)

====

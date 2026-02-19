---- MODULE Election ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ElectionMessage, Constants, State

Init(s, c) ==
    /\ s.electing = {}
    /\ s.has_leader = FALSE
    /\ s.leader = 0
    /\ s.alive = c.nodes
    /\ s.has_highest = FALSE
    /\ s.highest_heard = 0
    /\ s.waiting_answer = FALSE
    /\ s.waiting_node = 0

DetectFailure(s, s_, c, node, sent_packets) ==
    /\ node \in s.alive
    /\ s.has_leader = TRUE
    /\ ~s.leader \in s.alive
    /\ s_.electing = s.electing \cup {node}
    /\ s_.waiting_answer = TRUE
    /\ s_.waiting_node = node
    /\ s_.has_leader = s.has_leader
    /\ s_.leader = s.leader
    /\ s_.alive = s.alive
    /\ s_.has_highest = s.has_highest
    /\ s_.highest_heard = s.highest_heard
    /\ sent_packets = <<[sender |-> node]>>

StartElection(s, s_, c, node, sent_packets) ==
    /\ node \in s.alive
    /\ s_.electing = s.electing \cup {node}
    /\ s_.has_leader = FALSE
    /\ s_.leader = 0
    /\ s_.waiting_answer = TRUE
    /\ s_.waiting_node = node
    /\ s_.alive = s.alive
    /\ s_.has_highest = s.has_highest
    /\ s_.highest_heard = s.highest_heard
    /\ sent_packets = <<[sender |-> node]>>

SendAnswer(s, s_, c, node, sender, sent_packets) ==
    /\ node \in s.alive
    /\ node > sender
    /\ s_.electing = s.electing \cup {node}
    /\ s_.has_highest = TRUE
    /\ s_.highest_heard = IF ~s.has_highest \/ node > s.highest_heard THEN node ELSE s.highest_heard
    /\ s_.has_leader = s.has_leader
    /\ s_.leader = s.leader
    /\ s_.alive = s.alive
    /\ s_.waiting_answer = s.waiting_answer
    /\ s_.waiting_node = s.waiting_node
    /\ sent_packets = <<[responder |-> node]>>

ReceiveAnswer(s, s_, c, node, responder, sent_packets) ==
    /\ node \in s.alive
    /\ s.waiting_answer = TRUE
    /\ s.waiting_node = node
    /\ s_.waiting_answer = FALSE
    /\ s_.waiting_node = 0
    /\ s_.electing = s.electing \ {node}
    /\ s_.has_leader = s.has_leader
    /\ s_.leader = s.leader
    /\ s_.alive = s.alive
    /\ s_.has_highest = s.has_highest
    /\ s_.highest_heard = s.highest_heard
    /\ sent_packets = <<>>

SendCoordinator(s, s_, c, node, sent_packets) ==
    /\ node \in s.alive
    /\ node \in s.electing
    /\ s.waiting_answer = TRUE
    /\ s.waiting_node = node
    /\ s_.has_leader = TRUE
    /\ s_.leader = node
    /\ s_.electing = s.electing \ {node}
    /\ s_.waiting_answer = FALSE
    /\ s_.waiting_node = 0
    /\ s_.alive = s.alive
    /\ s_.has_highest = s.has_highest
    /\ s_.highest_heard = s.highest_heard
    /\ sent_packets = <<[leader |-> node]>>

ReceiveCoordinator(s, s_, c, node, leader, sent_packets) ==
    /\ node \in s.alive
    /\ s_.has_leader = TRUE
    /\ s_.leader = leader
    /\ s_.electing = s.electing \ {node}
    /\ s_.alive = s.alive
    /\ s_.has_highest = s.has_highest
    /\ s_.highest_heard = s.highest_heard
    /\ s_.waiting_answer = s.waiting_answer
    /\ s_.waiting_node = s.waiting_node
    /\ sent_packets = <<>>

NodeFail(s, s_, c, node, sent_packets) ==
    /\ node \in s.alive
    /\ s_.alive = s.alive \ {node}
    /\ s_.electing = s.electing \ {node}
    /\ s_.has_leader = IF s.has_leader /\ s.leader = node THEN FALSE ELSE s.has_leader
    /\ s_.leader = IF s.has_leader /\ s.leader = node THEN 0 ELSE s.leader
    /\ s_.waiting_answer = IF s.waiting_answer /\ s.waiting_node = node THEN FALSE ELSE s.waiting_answer
    /\ s_.waiting_node = IF s.waiting_answer /\ s.waiting_node = node THEN 0 ELSE s.waiting_node
    /\ s_.has_highest = s.has_highest
    /\ s_.highest_heard = s.highest_heard
    /\ sent_packets = <<>>

Next(s, s_, c) ==
    \/ \E node \in Int, sent_packets \in Seq(ElectionMessage) : DetectFailure(s, s_, c, node, sent_packets)
    \/ \E node \in Int, sent_packets \in Seq(ElectionMessage) : StartElection(s, s_, c, node, sent_packets)
    \/ \E node \in Int, sender \in Int, sent_packets \in Seq(ElectionMessage) : SendAnswer(s, s_, c, node, sender, sent_packets)
    \/ \E node \in Int, responder \in Int, sent_packets \in Seq(ElectionMessage) : ReceiveAnswer(s, s_, c, node, responder, sent_packets)
    \/ \E node \in Int, sent_packets \in Seq(ElectionMessage) : SendCoordinator(s, s_, c, node, sent_packets)
    \/ \E node \in Int, leader \in Int, sent_packets \in Seq(ElectionMessage) : ReceiveCoordinator(s, s_, c, node, leader, sent_packets)
    \/ \E node \in Int, sent_packets \in Seq(ElectionMessage) : NodeFail(s, s_, c, node, sent_packets)

====

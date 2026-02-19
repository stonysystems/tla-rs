---- MODULE Chain ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS State, CRMessage, Constants

Init(s, c) ==
    /\ s.history = <<>>
    /\ s.pending_sent = {}
    /\ s.committed_count = 0
    /\ s.obj_value = 0
    /\ c.node_id = 0 => s.role.tag = Head
    /\ c.node_id = c.chain_len - 1 => s.role.tag = Tail
    /\ (c.node_id > 0 /\ c.node_id < c.chain_len - 1) => s.role.tag = Middle
    /\ s.has_predecessor = (c.node_id > 0)
    /\ s.predecessor = IF c.node_id > 0 THEN c.node_id - 1 ELSE 0
    /\ s.has_successor = (c.node_id < c.chain_len - 1)
    /\ s.successor = IF c.node_id < c.chain_len - 1 THEN c.node_id + 1 ELSE 0
    /\ s.alive = TRUE

HeadReceiveWrite(s, s_, c, value, sent_packets) ==
    /\ s.role.tag = Head
    /\ s.alive = TRUE
    /\ ~value \in s.pending_sent
    /\ s_.role = s.role
    /\ s_.history = Append(s.history, value)
    /\ s_.pending_sent = s.pending_sent \cup {value}
    /\ s_.committed_count = s.committed_count
    /\ s_.obj_value = s.obj_value
    /\ s_.has_predecessor = s.has_predecessor
    /\ s_.predecessor = s.predecessor
    /\ s_.has_successor = s.has_successor
    /\ s_.successor = s.successor
    /\ s_.alive = s.alive
    /\ sent_packets = <<>>

ForwardToSuccessor(s, s_, c, value, sent_packets) ==
    /\ s.role.tag = Head \/ s.role.tag = Middle
    /\ s.alive = TRUE
    /\ value \in s.pending_sent
    /\ s.has_successor = TRUE
    /\ s_.role = s.role
    /\ s_.history = s.history
    /\ s_.pending_sent = s.pending_sent
    /\ s_.committed_count = s.committed_count
    /\ s_.obj_value = s.obj_value
    /\ s_.has_predecessor = s.has_predecessor
    /\ s_.predecessor = s.predecessor
    /\ s_.has_successor = s.has_successor
    /\ s_.successor = s.successor
    /\ s_.alive = s.alive
    /\ sent_packets = <<[value |-> value]>>

ReceiveUpdate(s, s_, c, value, sent_packets) ==
    /\ s.role.tag = Middle \/ s.role.tag = Tail
    /\ s.alive = TRUE
    /\ ~value \in s.history
    /\ s_.role = s.role
    /\ s_.history = Append(s.history, value)
    /\ IF s.role.tag = Middle THEN s_.pending_sent = s.pending_sent \cup {value} ELSE s_.pending_sent = s.pending_sent
    /\ s_.committed_count = s.committed_count
    /\ s_.obj_value = s.obj_value
    /\ s_.has_predecessor = s.has_predecessor
    /\ s_.predecessor = s.predecessor
    /\ s_.has_successor = s.has_successor
    /\ s_.successor = s.successor
    /\ s_.alive = s.alive
    /\ sent_packets = <<>>

TailCommit(s, s_, c, value, sent_packets) ==
    /\ s.role.tag = Tail
    /\ s.alive = TRUE
    /\ value \in s.history
    /\ s_.role = s.role
    /\ s_.history = s.history
    /\ s_.pending_sent = s.pending_sent
    /\ s_.committed_count = s.committed_count + 1
    /\ s_.obj_value = value
    /\ s_.has_predecessor = s.has_predecessor
    /\ s_.predecessor = s.predecessor
    /\ s_.has_successor = s.has_successor
    /\ s_.successor = s.successor
    /\ s_.alive = s.alive
    /\ sent_packets = <<[value |-> value]>>

ReceiveAck(s, s_, c, value, sent_packets) ==
    /\ s.role.tag = Head \/ s.role.tag = Middle
    /\ s.alive = TRUE
    /\ value \in s.pending_sent
    /\ s_.role = s.role
    /\ s_.history = s.history
    /\ s_.pending_sent = s.pending_sent \ {value}
    /\ s_.committed_count = s.committed_count
    /\ s_.obj_value = s.obj_value
    /\ s_.has_predecessor = s.has_predecessor
    /\ s_.predecessor = s.predecessor
    /\ s_.has_successor = s.has_successor
    /\ s_.successor = s.successor
    /\ s_.alive = s.alive
    /\ sent_packets = <<>>

ClientRead(s, s_, c, sent_packets) ==
    /\ s.role.tag = Tail
    /\ s.alive = TRUE
    /\ s_.role = s.role
    /\ s_.history = s.history
    /\ s_.pending_sent = s.pending_sent
    /\ s_.committed_count = s.committed_count
    /\ s_.obj_value = s.obj_value
    /\ s_.has_predecessor = s.has_predecessor
    /\ s_.predecessor = s.predecessor
    /\ s_.has_successor = s.has_successor
    /\ s_.successor = s.successor
    /\ s_.alive = s.alive
    /\ sent_packets = <<>>

NodeFail(s, s_, c, sent_packets) ==
    /\ s.alive = TRUE
    /\ s_.alive = FALSE
    /\ s_.role = s.role
    /\ s_.history = s.history
    /\ s_.pending_sent = s.pending_sent
    /\ s_.committed_count = s.committed_count
    /\ s_.obj_value = s.obj_value
    /\ s_.has_predecessor = s.has_predecessor
    /\ s_.predecessor = s.predecessor
    /\ s_.has_successor = s.has_successor
    /\ s_.successor = s.successor
    /\ sent_packets = <<>>

Reconfigure(s, s_, c, new_has_predecessor, new_predecessor, new_has_successor, new_successor, sent_packets) ==
    /\ s.alive = TRUE
    /\ s_.has_predecessor = new_has_predecessor
    /\ s_.predecessor = new_predecessor
    /\ s_.has_successor = new_has_successor
    /\ s_.successor = new_successor
    /\ s_.role = s.role
    /\ s_.history = s.history
    /\ s_.pending_sent = s.pending_sent
    /\ s_.committed_count = s.committed_count
    /\ s_.obj_value = s.obj_value
    /\ s_.alive = s.alive
    /\ sent_packets = <<>>

Next(s, s_, c) ==
    \/ \E value \in Int, sent_packets \in Seq(CRMessage) : HeadReceiveWrite(s, s_, c, value, sent_packets)
    \/ \E value \in Int, sent_packets \in Seq(CRMessage) : ForwardToSuccessor(s, s_, c, value, sent_packets)
    \/ \E value \in Int, sent_packets \in Seq(CRMessage) : ReceiveUpdate(s, s_, c, value, sent_packets)
    \/ \E value \in Int, sent_packets \in Seq(CRMessage) : TailCommit(s, s_, c, value, sent_packets)
    \/ \E value \in Int, sent_packets \in Seq(CRMessage) : ReceiveAck(s, s_, c, value, sent_packets)
    \/ \E sent_packets \in Seq(CRMessage) : ClientRead(s, s_, c, sent_packets)
    \/ \E sent_packets \in Seq(CRMessage) : NodeFail(s, s_, c, sent_packets)
    \/ \E new_has_predecessor \in BOOLEAN, new_predecessor \in Int, new_has_successor \in BOOLEAN, new_successor \in Int, sent_packets \in Seq(CRMessage) : Reconfigure(s, s_, c, new_has_predecessor, new_predecessor, new_has_successor, new_successor, sent_packets)

====

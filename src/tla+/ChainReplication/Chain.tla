---- MODULE Chain ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Constants, State

Init(s, c) ==
    /\ s.history = <<>>
    /\ s.pending_sent = {}
    /\ s.committed_count = 0
    /\ s.obj_value = 0
    /\ c.node_id = 0 => s.role.tag = Head
    /\ c.node_id = c.chain_len - 1 => s.role.tag = Tail
    /\ (c.node_id > 0 /\ c.node_id < c.chain_len - 1) => s.role.tag = Middle

HeadReceiveWrite(s, s_, c, value) ==
    /\ s.role.tag = Head
    /\ ~value \in s.pending_sent
    /\ s_.role = s.role
    /\ s_.history = Append(s.history, value)
    /\ s_.pending_sent = s.pending_sent \cup {value}
    /\ s_.committed_count = s.committed_count
    /\ s_.obj_value = s.obj_value

ReceiveUpdate(s, s_, c, value) ==
    /\ s.role.tag = Middle \/ s.role.tag = Tail
    /\ ~value \in s.history
    /\ s_.role = s.role
    /\ s_.history = Append(s.history, value)
    /\ IF s.role.tag = Middle THEN s_.pending_sent = s.pending_sent \cup {value} ELSE s_.pending_sent = s.pending_sent
    /\ s_.committed_count = s.committed_count
    /\ s_.obj_value = s.obj_value

TailCommit(s, s_, c, value) ==
    /\ s.role.tag = Tail
    /\ value \in s.history
    /\ s_.role = s.role
    /\ s_.history = s.history
    /\ s_.pending_sent = s.pending_sent
    /\ s_.committed_count = s.committed_count + 1
    /\ s_.obj_value = value

ReceiveAck(s, s_, c, value) ==
    /\ s.role.tag = Head \/ s.role.tag = Middle
    /\ value \in s.pending_sent
    /\ s_.role = s.role
    /\ s_.history = s.history
    /\ s_.pending_sent = s.pending_sent \ {value}
    /\ s_.committed_count = s.committed_count
    /\ s_.obj_value = s.obj_value

ClientRead(s, s_, c) ==
    s.role.tag = Tail /\ s_ = s

Next(s, s_, c) ==
    \/ \E value \in Int : HeadReceiveWrite(s, s_, c, value)
    \/ \E value \in Int : ReceiveUpdate(s, s_, c, value)
    \/ \E value \in Int : TailCommit(s, s_, c, value)
    \/ \E value \in Int : ReceiveAck(s, s_, c, value)
    \/ ClientRead(s, s_, c)

====

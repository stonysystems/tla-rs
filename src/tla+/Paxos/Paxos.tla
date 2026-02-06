---- MODULE paxos ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS State, Constants

Init(s, c) ==
    /\ s.max_bal = {}
    /\ s.max_v_bal = {}
    /\ s.max_val = {}
    /\ s.msg_count = 0

Send1a(s, s_, c, b) ==
    /\ s_.max_bal = s.max_bal
    /\ s_.max_v_bal = s.max_v_bal
    /\ s_.max_val = s.max_val
    /\ s_.msg_count = s.msg_count + 1

Send1b(s, s_, c, b) ==
    /\ s_.max_bal = s.max_bal \cup {b}
    /\ s_.max_v_bal = s.max_v_bal
    /\ s_.max_val = s.max_val
    /\ s_.msg_count = s.msg_count + 1

Send2a(s, s_, c, b, v) ==
    /\ s_.max_bal = s.max_bal
    /\ s_.max_v_bal = s.max_v_bal
    /\ s_.max_val = s.max_val
    /\ s_.msg_count = s.msg_count + 1

Send2b(s, s_, c, b, v) ==
    /\ s_.max_bal = s.max_bal
    /\ s_.max_v_bal = s.max_v_bal \cup {b}
    /\ s_.max_val = s.max_val \cup {v}
    /\ s_.msg_count = s.msg_count + 1

Chosen(s, v) ==
    v \in s.max_val

Next(s, s_, c) ==
    \/ \E b \in Int : Send1a(s, s_, c, b)
    \/ \E b \in Int : Send1b(s, s_, c, b)
    \/ \E b \in Int, v \in Int : Send2a(s, s_, c, b, v)
    \/ \E b \in Int, v \in Int : Send2b(s, s_, c, b, v)

====

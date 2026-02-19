---- MODULE Twophase ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Constants, State, TPCMessage

Init(s, c) ==
    /\ s.tm_state.tag = Init
    /\ s.tm_prepared = {}
    /\ s.rm_prepared = {}
    /\ s.rm_committed = {}
    /\ s.rm_aborted = {}

TMSendPrepare(s, s_, c, sent_packets) ==
    /\ s.tm_state.tag = Init
    /\ s_.tm_state = s.tm_state
    /\ s_.tm_prepared = s.tm_prepared
    /\ s_.rm_prepared = s.rm_prepared
    /\ s_.rm_committed = s.rm_committed
    /\ s_.rm_aborted = s.rm_aborted
    /\ sent_packets = <<Prepare>>

RMReceivePrepare(s, s_, c, rm, sent_packets) ==
    /\ rm \in c.rm
    /\ ~rm \in s.rm_prepared
    /\ ~rm \in s.rm_aborted
    /\ s_.tm_state = s.tm_state
    /\ s_.tm_prepared = s.tm_prepared
    /\ s_.rm_prepared = s.rm_prepared \cup {rm}
    /\ s_.rm_committed = s.rm_committed
    /\ s_.rm_aborted = s.rm_aborted
    /\ sent_packets = <<[rm |-> rm]>>

RMAbort(s, s_, c, rm, sent_packets) ==
    /\ rm \in c.rm
    /\ ~rm \in s.rm_prepared
    /\ ~rm \in s.rm_aborted
    /\ ~rm \in s.rm_committed
    /\ s_.tm_state = s.tm_state
    /\ s_.tm_prepared = s.tm_prepared
    /\ s_.rm_prepared = s.rm_prepared
    /\ s_.rm_committed = s.rm_committed
    /\ s_.rm_aborted = s.rm_aborted \cup {rm}
    /\ sent_packets = <<>>

TMRcvPrepared(s, s_, c, r, sent_packets) ==
    /\ s.tm_state.tag = Init
    /\ r \in s.rm_prepared
    /\ s_.tm_state.tag = Init
    /\ s_.tm_prepared = s.tm_prepared \cup {r}
    /\ s_.rm_prepared = s.rm_prepared
    /\ s_.rm_committed = s.rm_committed
    /\ s_.rm_aborted = s.rm_aborted
    /\ sent_packets = <<>>

TMSendCommit(s, s_, c, sent_packets) ==
    /\ s.tm_state.tag = Init
    /\ s.tm_prepared = c.rm
    /\ s_.tm_state.tag = Committed
    /\ s_.tm_prepared = s.tm_prepared
    /\ s_.rm_prepared = s.rm_prepared
    /\ s_.rm_committed = s.rm_committed
    /\ s_.rm_aborted = s.rm_aborted
    /\ sent_packets = <<Commit>>

TMSendAbort(s, s_, c, sent_packets) ==
    /\ s.tm_state.tag = Init
    /\ s_.tm_state.tag = Aborted
    /\ s_.tm_prepared = s.tm_prepared
    /\ s_.rm_prepared = s.rm_prepared
    /\ s_.rm_committed = s.rm_committed
    /\ s_.rm_aborted = s.rm_aborted
    /\ sent_packets = <<Abort>>

RMReceiveCommit(s, s_, c, rm, sent_packets) ==
    /\ rm \in c.rm
    /\ rm \in s.rm_prepared
    /\ ~rm \in s.rm_committed
    /\ s_.tm_state = s.tm_state
    /\ s_.tm_prepared = s.tm_prepared
    /\ s_.rm_prepared = s.rm_prepared
    /\ s_.rm_committed = s.rm_committed \cup {rm}
    /\ s_.rm_aborted = s.rm_aborted
    /\ sent_packets = <<>>

RMReceiveAbort(s, s_, c, rm, sent_packets) ==
    /\ rm \in c.rm
    /\ ~rm \in s.rm_committed
    /\ ~rm \in s.rm_aborted
    /\ s_.tm_state = s.tm_state
    /\ s_.tm_prepared = s.tm_prepared
    /\ s_.rm_prepared = s.rm_prepared
    /\ s_.rm_committed = s.rm_committed
    /\ s_.rm_aborted = s.rm_aborted \cup {rm}
    /\ sent_packets = <<>>

Next(s, s_, c) ==
    \/ \E sent_packets \in Seq(TPCMessage) : TMSendPrepare(s, s_, c, sent_packets)
    \/ \E rm \in Int, sent_packets \in Seq(TPCMessage) : RMReceivePrepare(s, s_, c, rm, sent_packets)
    \/ \E rm \in Int, sent_packets \in Seq(TPCMessage) : RMAbort(s, s_, c, rm, sent_packets)
    \/ \E r \in Int, sent_packets \in Seq(TPCMessage) : TMRcvPrepared(s, s_, c, r, sent_packets)
    \/ \E sent_packets \in Seq(TPCMessage) : TMSendCommit(s, s_, c, sent_packets)
    \/ \E sent_packets \in Seq(TPCMessage) : TMSendAbort(s, s_, c, sent_packets)
    \/ \E rm \in Int, sent_packets \in Seq(TPCMessage) : RMReceiveCommit(s, s_, c, rm, sent_packets)
    \/ \E rm \in Int, sent_packets \in Seq(TPCMessage) : RMReceiveAbort(s, s_, c, rm, sent_packets)

====

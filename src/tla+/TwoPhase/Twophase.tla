---- MODULE Twophase ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS State, Constants

Init(s, c) ==
    /\ s.rm_state = {}
    /\ s.tm_state.tag = Init
    /\ s.tm_prepared = {}

TMRcvPrepared(s, s_, c, r) ==
    /\ s.tm_state.tag = Init
    /\ s_.tm_prepared = s.tm_prepared \cup {r}
    /\ s_.rm_state = s.rm_state
    /\ s_.tm_state.tag = Init

TMCommit(s, s_, c) ==
    /\ s.tm_state.tag = Init
    /\ s.tm_prepared = c.rm
    /\ s_.tm_state.tag = Committed
    /\ s_.rm_state = s.rm_state
    /\ s_.tm_prepared = s.tm_prepared

TMAbort(s, s_, c) ==
    /\ s.tm_state.tag = Init
    /\ s_.tm_state.tag = Aborted
    /\ s_.rm_state = s.rm_state
    /\ s_.tm_prepared = s.tm_prepared

Next(s, s_, c) ==
    \/ TMCommit(s, s_, c)
    \/ TMAbort(s, s_, c)
    \/ \E r \in Int : TMRcvPrepared(s, s_, c, r)

====

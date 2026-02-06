---- MODULE Primarybackup ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS State, Constants

Init(s, c) ==
    /\ s.role.tag = Primary
    /\ s.log_length = 0
    /\ s.last_value = 0
    /\ s.has_pending = FALSE
    /\ s.pending_value = 0
    /\ s.acked = TRUE

PrimaryWrite(s, s_, c, val) ==
    /\ s.role.tag = Primary
    /\ s.acked = TRUE
    /\ s.has_pending = FALSE
    /\ s.log_length < c.max_log_len
    /\ s_.role = s.role
    /\ s_.log_length = s.log_length
    /\ s_.last_value = s.last_value
    /\ s_.has_pending = TRUE
    /\ s_.pending_value = val
    /\ s_.acked = FALSE

BackupAck(s, s_, c) ==
    /\ s.role.tag = Primary
    /\ s.acked = FALSE
    /\ s.has_pending = TRUE
    /\ s_.role = s.role
    /\ s_.log_length = s.log_length
    /\ s_.last_value = s.last_value
    /\ s_.has_pending = s.has_pending
    /\ s_.pending_value = s.pending_value
    /\ s_.acked = TRUE

PrimaryCommit(s, s_, c) ==
    /\ s.role.tag = Primary
    /\ s.acked = TRUE
    /\ s.has_pending = TRUE
    /\ s_.role = s.role
    /\ s_.log_length = s.log_length + 1
    /\ s_.last_value = s.pending_value
    /\ s_.has_pending = FALSE
    /\ s_.pending_value = 0
    /\ s_.acked = TRUE

Failover(s, s_, c) ==
    /\ s.role.tag = Primary
    /\ s_.role.tag = Primary
    /\ s_.log_length = s.log_length
    /\ s_.last_value = s.last_value
    /\ s_.has_pending = FALSE
    /\ s_.pending_value = 0
    /\ s_.acked = TRUE

Next(s, s_, c) ==
    \/ \E val \in Int : PrimaryWrite(s, s_, c, val)
    \/ BackupAck(s, s_, c)
    \/ PrimaryCommit(s, s_, c)
    \/ Failover(s, s_, c)

====

---- MODULE Primarybackup ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Constants, State, PBMessage

Init(s, c) ==
    /\ s.role.tag = Primary
    /\ s.log_length = 0
    /\ s.last_value = 0
    /\ s.has_pending = FALSE
    /\ s.pending_value = 0
    /\ s.acked = TRUE
    /\ s.backup_log_length = 0
    /\ s.backup_last_value = 0
    /\ s.backup_synced = TRUE
    /\ s.view = 0

PrimaryWrite(s, s_, c, val, sent_packets) ==
    /\ s.role.tag = Primary
    /\ s.acked = TRUE
    /\ s.has_pending = FALSE
    /\ s.log_length < c.max_log_len
    /\ s_.has_pending = TRUE
    /\ s_.pending_value = val
    /\ s_.acked = FALSE
    /\ s_.role = s.role
    /\ s_.log_length = s.log_length
    /\ s_.last_value = s.last_value
    /\ s_.backup_log_length = s.backup_log_length
    /\ s_.backup_last_value = s.backup_last_value
    /\ s_.backup_synced = s.backup_synced
    /\ s_.view = s.view
    /\ sent_packets = <<>>

PrimarySendReplicate(s, s_, c, sent_packets) ==
    /\ s.role.tag = Primary
    /\ s.has_pending = TRUE
    /\ s.acked = FALSE
    /\ s_.role = s.role
    /\ s_.log_length = s.log_length
    /\ s_.last_value = s.last_value
    /\ s_.has_pending = s.has_pending
    /\ s_.pending_value = s.pending_value
    /\ s_.acked = s.acked
    /\ s_.backup_log_length = s.backup_log_length
    /\ s_.backup_last_value = s.backup_last_value
    /\ s_.backup_synced = s.backup_synced
    /\ s_.view = s.view
    /\ sent_packets = <<[val |-> s.pending_value]>>

BackupReceiveReplicate(s, s_, c, val, sent_packets) ==
    /\ s.role.tag = Primary
    /\ s_.backup_log_length = s.backup_log_length + 1
    /\ s_.backup_last_value = val
    /\ s_.backup_synced = TRUE
    /\ s_.role = s.role
    /\ s_.log_length = s.log_length
    /\ s_.last_value = s.last_value
    /\ s_.has_pending = s.has_pending
    /\ s_.pending_value = s.pending_value
    /\ s_.acked = s.acked
    /\ s_.view = s.view
    /\ sent_packets = <<>>

BackupSendAck(s, s_, c, sent_packets) ==
    /\ s.role.tag = Primary
    /\ s.backup_synced = TRUE
    /\ s_.role = s.role
    /\ s_.log_length = s.log_length
    /\ s_.last_value = s.last_value
    /\ s_.has_pending = s.has_pending
    /\ s_.pending_value = s.pending_value
    /\ s_.acked = s.acked
    /\ s_.backup_log_length = s.backup_log_length
    /\ s_.backup_last_value = s.backup_last_value
    /\ s_.backup_synced = s.backup_synced
    /\ s_.view = s.view
    /\ sent_packets = <<Ack>>

PrimaryReceiveAck(s, s_, c, sent_packets) ==
    /\ s.role.tag = Primary
    /\ s.has_pending = TRUE
    /\ s_.acked = TRUE
    /\ s_.role = s.role
    /\ s_.log_length = s.log_length
    /\ s_.last_value = s.last_value
    /\ s_.has_pending = s.has_pending
    /\ s_.pending_value = s.pending_value
    /\ s_.backup_log_length = s.backup_log_length
    /\ s_.backup_last_value = s.backup_last_value
    /\ s_.backup_synced = s.backup_synced
    /\ s_.view = s.view
    /\ sent_packets = <<>>

PrimaryCommit(s, s_, c, sent_packets) ==
    /\ s.role.tag = Primary
    /\ s.acked = TRUE
    /\ s.has_pending = TRUE
    /\ s_.log_length = s.log_length + 1
    /\ s_.last_value = s.pending_value
    /\ s_.has_pending = FALSE
    /\ s_.pending_value = 0
    /\ s_.acked = TRUE
    /\ s_.role = s.role
    /\ s_.backup_log_length = s.backup_log_length
    /\ s_.backup_last_value = s.backup_last_value
    /\ s_.backup_synced = s.backup_synced
    /\ s_.view = s.view
    /\ sent_packets = <<>>

PrimaryFail(s, s_, c, sent_packets) ==
    /\ s.role.tag = Primary
    /\ s_.role.tag = Inactive
    /\ s_.has_pending = FALSE
    /\ s_.pending_value = 0
    /\ s_.acked = TRUE
    /\ s_.log_length = s.log_length
    /\ s_.last_value = s.last_value
    /\ s_.backup_log_length = s.backup_log_length
    /\ s_.backup_last_value = s.backup_last_value
    /\ s_.backup_synced = FALSE
    /\ s_.view = s.view
    /\ sent_packets = <<>>

BackupPromote(s, s_, c, sent_packets) ==
    /\ s.role.tag = Inactive
    /\ s_.role.tag = Primary
    /\ s_.log_length = s.backup_log_length
    /\ s_.last_value = s.backup_last_value
    /\ s_.has_pending = FALSE
    /\ s_.pending_value = 0
    /\ s_.acked = TRUE
    /\ s_.backup_log_length = s.backup_log_length
    /\ s_.backup_last_value = s.backup_last_value
    /\ s_.backup_synced = TRUE
    /\ s_.view = s.view + 1
    /\ sent_packets = <<>>

Next(s, s_, c) ==
    \/ \E val \in Int, sent_packets \in Seq(PBMessage) : PrimaryWrite(s, s_, c, val, sent_packets)
    \/ \E sent_packets \in Seq(PBMessage) : PrimarySendReplicate(s, s_, c, sent_packets)
    \/ \E val \in Int, sent_packets \in Seq(PBMessage) : BackupReceiveReplicate(s, s_, c, val, sent_packets)
    \/ \E sent_packets \in Seq(PBMessage) : BackupSendAck(s, s_, c, sent_packets)
    \/ \E sent_packets \in Seq(PBMessage) : PrimaryReceiveAck(s, s_, c, sent_packets)
    \/ \E sent_packets \in Seq(PBMessage) : PrimaryCommit(s, s_, c, sent_packets)
    \/ \E sent_packets \in Seq(PBMessage) : PrimaryFail(s, s_, c, sent_packets)
    \/ \E sent_packets \in Seq(PBMessage) : BackupPromote(s, s_, c, sent_packets)

====

use vstd::prelude::*;

use crate::protocol::PrimaryBackup::types::*;

verus! {

/// Initial state: primary with empty log, backup synced, view 0
pub open spec fn LInit(s: LState, c: LConstants) -> bool {
    &&& s.role is Primary
    &&& s.log_length == 0
    &&& s.last_value == 0
    &&& s.has_pending == false
    &&& s.pending_value == 0
    &&& s.acked == true
    &&& s.backup_log_length == 0
    &&& s.backup_last_value == 0
    &&& s.backup_synced == true
    &&& s.view == 0
}

/// Primary receives a client write request
pub open spec fn LPrimaryWrite(s: LState, s_: LState, c: LConstants, val: int, sent_packets: Seq<LPBMessage>) -> bool {
    &&& s.role is Primary
    &&& s.acked == true
    &&& s.has_pending == false
    &&& s.log_length < c.max_log_len
    // Set pending write
    &&& s_.has_pending == true
    &&& s_.pending_value == val
    &&& s_.acked == false
    // Frame: everything else unchanged
    &&& s_.role == s.role
    &&& s_.log_length == s.log_length
    &&& s_.last_value == s.last_value
    &&& s_.backup_log_length == s.backup_log_length
    &&& s_.backup_last_value == s.backup_last_value
    &&& s_.backup_synced == s.backup_synced
    &&& s_.view == s.view
    // No messages sent
    &&& sent_packets == Seq::<LPBMessage>::empty()
}

/// Primary sends replicate message to backup with pending value
pub open spec fn LPrimarySendReplicate(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LPBMessage>) -> bool {
    &&& s.role is Primary
    &&& s.has_pending == true
    &&& s.acked == false
    // Frame: state unchanged (message is output, not state mutation)
    &&& s_.role == s.role
    &&& s_.log_length == s.log_length
    &&& s_.last_value == s.last_value
    &&& s_.has_pending == s.has_pending
    &&& s_.pending_value == s.pending_value
    &&& s_.acked == s.acked
    &&& s_.backup_log_length == s.backup_log_length
    &&& s_.backup_last_value == s.backup_last_value
    &&& s_.backup_synced == s.backup_synced
    &&& s_.view == s.view
    // Send replicate with pending value
    &&& sent_packets == seq![LPBMessage::Replicate { val: s.pending_value }]
}

/// Backup receives replicate and appends to its log
pub open spec fn LBackupReceiveReplicate(s: LState, s_: LState, c: LConstants, val: int, sent_packets: Seq<LPBMessage>) -> bool {
    &&& s.role is Primary      // Global state perspective: backup is alive
    // Backup appends the replicated value (val comes from the received message)
    &&& s_.backup_log_length == s.backup_log_length + 1
    &&& s_.backup_last_value == val
    &&& s_.backup_synced == true
    // Frame
    &&& s_.role == s.role
    &&& s_.log_length == s.log_length
    &&& s_.last_value == s.last_value
    &&& s_.has_pending == s.has_pending
    &&& s_.pending_value == s.pending_value
    &&& s_.acked == s.acked
    &&& s_.view == s.view
    // No messages sent
    &&& sent_packets == Seq::<LPBMessage>::empty()
}

/// Backup sends acknowledgment to primary
pub open spec fn LBackupSendAck(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LPBMessage>) -> bool {
    &&& s.role is Primary
    &&& s.backup_synced == true
    // Frame: state unchanged (message is output)
    &&& s_.role == s.role
    &&& s_.log_length == s.log_length
    &&& s_.last_value == s.last_value
    &&& s_.has_pending == s.has_pending
    &&& s_.pending_value == s.pending_value
    &&& s_.acked == s.acked
    &&& s_.backup_log_length == s.backup_log_length
    &&& s_.backup_last_value == s.backup_last_value
    &&& s_.backup_synced == s.backup_synced
    &&& s_.view == s.view
    // Send ack
    &&& sent_packets == seq![LPBMessage::Ack]
}

/// Primary receives ack from backup
pub open spec fn LPrimaryReceiveAck(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LPBMessage>) -> bool {
    &&& s.role is Primary
    &&& s.has_pending == true
    // Mark as acked
    &&& s_.acked == true
    // Frame
    &&& s_.role == s.role
    &&& s_.log_length == s.log_length
    &&& s_.last_value == s.last_value
    &&& s_.has_pending == s.has_pending
    &&& s_.pending_value == s.pending_value
    &&& s_.backup_log_length == s.backup_log_length
    &&& s_.backup_last_value == s.backup_last_value
    &&& s_.backup_synced == s.backup_synced
    &&& s_.view == s.view
    // No messages sent
    &&& sent_packets == Seq::<LPBMessage>::empty()
}

/// Primary commits the pending write to the log after receiving ack
/// and sends a ClientReply back to the requesting client.
pub open spec fn LPrimaryCommit(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LPBMessage>) -> bool {
    &&& s.role is Primary
    &&& s.acked == true
    &&& s.has_pending == true
    // Commit to log
    &&& s_.log_length == s.log_length + 1
    &&& s_.last_value == s.pending_value
    &&& s_.has_pending == false
    &&& s_.pending_value == 0
    &&& s_.acked == true
    // Frame
    &&& s_.role == s.role
    &&& s_.backup_log_length == s.backup_log_length
    &&& s_.backup_last_value == s.backup_last_value
    &&& s_.backup_synced == s.backup_synced
    &&& s_.view == s.view
    // Send ClientReply with the committed value
    &&& sent_packets == seq![LPBMessage::ClientReply { val: s.pending_value }]
}

/// Primary fails: becomes inactive, pending writes are lost
pub open spec fn LPrimaryFail(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LPBMessage>) -> bool {
    &&& s.role is Primary
    // Primary becomes inactive
    &&& s_.role is Inactive
    // Primary state cleared
    &&& s_.has_pending == false
    &&& s_.pending_value == 0
    &&& s_.acked == true
    // Frame: logs and backup state preserved
    &&& s_.log_length == s.log_length
    &&& s_.last_value == s.last_value
    &&& s_.backup_log_length == s.backup_log_length
    &&& s_.backup_last_value == s.backup_last_value
    &&& s_.backup_synced == false
    &&& s_.view == s.view
    // No messages sent
    &&& sent_packets == Seq::<LPBMessage>::empty()
}

/// Backup detects failure and promotes itself to primary
pub open spec fn LBackupPromote(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LPBMessage>) -> bool {
    &&& s.role is Inactive
    // Backup becomes new primary, uses backup's log state
    &&& s_.role is Primary
    &&& s_.log_length == s.backup_log_length
    &&& s_.last_value == s.backup_last_value
    // Reset pending state
    &&& s_.has_pending == false
    &&& s_.pending_value == 0
    &&& s_.acked == true
    // Backup state reset
    &&& s_.backup_log_length == s.backup_log_length
    &&& s_.backup_last_value == s.backup_last_value
    &&& s_.backup_synced == true
    // Increment view to prevent split-brain
    &&& s_.view == s.view + 1
    // No messages sent
    &&& sent_packets == Seq::<LPBMessage>::empty()
}

/// Next-state relation
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| (exists |val: int, sent_packets: Seq<LPBMessage>| LPrimaryWrite(s, s_, c, val, sent_packets))
    ||| (exists |sent_packets: Seq<LPBMessage>| LPrimarySendReplicate(s, s_, c, sent_packets))
    ||| (exists |val: int, sent_packets: Seq<LPBMessage>| LBackupReceiveReplicate(s, s_, c, val, sent_packets))
    ||| (exists |sent_packets: Seq<LPBMessage>| LBackupSendAck(s, s_, c, sent_packets))
    ||| (exists |sent_packets: Seq<LPBMessage>| LPrimaryReceiveAck(s, s_, c, sent_packets))
    ||| (exists |sent_packets: Seq<LPBMessage>| LPrimaryCommit(s, s_, c, sent_packets))
    ||| (exists |sent_packets: Seq<LPBMessage>| LPrimaryFail(s, s_, c, sent_packets))
    ||| (exists |sent_packets: Seq<LPBMessage>| LBackupPromote(s, s_, c, sent_packets))
}

/// Safety: when there is no pending write, pending_value must be cleared.
pub open spec fn LSafetyNoPendingImpliesClearedValue(s: LState, c: LConstants) -> bool {
    !s.has_pending ==> s.pending_value == 0
}

/// Safety: an unacknowledged state always corresponds to a pending write.
pub open spec fn LSafetyUnackedImpliesPending(s: LState, c: LConstants) -> bool {
    !s.acked ==> s.has_pending
}

/// Safety: inactive mode has no pending write and no sync channel.
pub open spec fn LSafetyInactiveStateIsQuiescent(s: LState, c: LConstants) -> bool {
    s.role is Inactive ==> (!s.has_pending && s.acked && !s.backup_synced)
}

}

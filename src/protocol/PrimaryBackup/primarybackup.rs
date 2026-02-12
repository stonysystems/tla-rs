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
    &&& s.msgs_replicate == false
    &&& s.msgs_replicate_val == 0
    &&& s.msgs_ack == false
}

/// Primary receives a client write request
pub open spec fn LPrimaryWrite(s: LState, s_: LState, c: LConstants, val: int) -> bool {
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
    &&& s_.msgs_replicate == s.msgs_replicate
    &&& s_.msgs_replicate_val == s.msgs_replicate_val
    &&& s_.msgs_ack == s.msgs_ack
}

/// Primary sends replicate message to backup with pending value
pub open spec fn LPrimarySendReplicate(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.role is Primary
    &&& s.has_pending == true
    &&& s.acked == false
    // Send replicate message
    &&& s_.msgs_replicate == true
    &&& s_.msgs_replicate_val == s.pending_value
    // Frame
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
    &&& s_.msgs_ack == s.msgs_ack
}

/// Backup receives replicate and appends to its log
pub open spec fn LBackupReceiveReplicate(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.role is Primary      // Global state perspective: backup is alive
    &&& s.msgs_replicate == true
    // Backup appends the replicated value
    &&& s_.backup_log_length == s.backup_log_length + 1
    &&& s_.backup_last_value == s.msgs_replicate_val
    &&& s_.backup_synced == true
    // Frame
    &&& s_.role == s.role
    &&& s_.log_length == s.log_length
    &&& s_.last_value == s.last_value
    &&& s_.has_pending == s.has_pending
    &&& s_.pending_value == s.pending_value
    &&& s_.acked == s.acked
    &&& s_.view == s.view
    &&& s_.msgs_replicate == s.msgs_replicate
    &&& s_.msgs_replicate_val == s.msgs_replicate_val
    &&& s_.msgs_ack == s.msgs_ack
}

/// Backup sends acknowledgment to primary
pub open spec fn LBackupSendAck(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.role is Primary
    &&& s.backup_synced == true
    &&& s.msgs_replicate == true
    // Send ack
    &&& s_.msgs_ack == true
    // Frame
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
    &&& s_.msgs_replicate == s.msgs_replicate
    &&& s_.msgs_replicate_val == s.msgs_replicate_val
}

/// Primary receives ack from backup
pub open spec fn LPrimaryReceiveAck(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.role is Primary
    &&& s.has_pending == true
    &&& s.msgs_ack == true
    // Mark as acked
    &&& s_.acked == true
    // Clear messages
    &&& s_.msgs_replicate == false
    &&& s_.msgs_replicate_val == 0
    &&& s_.msgs_ack == false
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
}

/// Primary commits the pending write to the log after receiving ack
pub open spec fn LPrimaryCommit(s: LState, s_: LState, c: LConstants) -> bool {
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
    &&& s_.msgs_replicate == s.msgs_replicate
    &&& s_.msgs_replicate_val == s.msgs_replicate_val
    &&& s_.msgs_ack == s.msgs_ack
}

/// Primary fails: becomes inactive, pending writes are lost
pub open spec fn LPrimaryFail(s: LState, s_: LState, c: LConstants) -> bool {
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
    // Clear messages
    &&& s_.msgs_replicate == false
    &&& s_.msgs_replicate_val == 0
    &&& s_.msgs_ack == false
}

/// Backup detects failure and promotes itself to primary
pub open spec fn LBackupPromote(s: LState, s_: LState, c: LConstants) -> bool {
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
    // Clear messages
    &&& s_.msgs_replicate == false
    &&& s_.msgs_replicate_val == 0
    &&& s_.msgs_ack == false
}

/// Next-state relation
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| (exists |val: int| LPrimaryWrite(s, s_, c, val))
    ||| LPrimarySendReplicate(s, s_, c)
    ||| LBackupReceiveReplicate(s, s_, c)
    ||| LBackupSendAck(s, s_, c)
    ||| LPrimaryReceiveAck(s, s_, c)
    ||| LPrimaryCommit(s, s_, c)
    ||| LPrimaryFail(s, s_, c)
    ||| LBackupPromote(s, s_, c)
}

}

use vstd::prelude::*;

use crate::protocol::PrimaryBackup::types::*;

verus! {

/// Initial state: node starts as primary with empty log
pub open spec fn LInit(s: LState, c: LConstants) -> bool {
    &&& s.role is Primary
    &&& s.log_length == 0
    &&& s.last_value == 0
    &&& s.has_pending == false
    &&& s.pending_value == 0
    &&& s.acked == true
}

/// Primary receives a client write request
/// Precondition: node is primary, no pending unacked write, log not full
pub open spec fn LPrimaryWrite(s: LState, s_: LState, c: LConstants, val: int) -> bool {
    &&& s.role is Primary
    &&& s.acked == true
    &&& s.has_pending == false
    &&& s.log_length < c.max_log_len
    &&& s_.role == s.role
    &&& s_.log_length == s.log_length
    &&& s_.last_value == s.last_value
    &&& s_.has_pending == true
    &&& s_.pending_value == val
    &&& s_.acked == false
}

/// Backup receives the pending write and acknowledges it
/// Precondition: node is primary, has pending unacked write
pub open spec fn LBackupAck(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.role is Primary
    &&& s.acked == false
    &&& s.has_pending == true
    &&& s_.role == s.role
    &&& s_.log_length == s.log_length
    &&& s_.last_value == s.last_value
    &&& s_.has_pending == s.has_pending
    &&& s_.pending_value == s.pending_value
    &&& s_.acked == true
}

/// Primary commits the pending write to the log after receiving ack
/// Precondition: node is primary, backup has acked, there is a pending write
pub open spec fn LPrimaryCommit(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.role is Primary
    &&& s.acked == true
    &&& s.has_pending == true
    &&& s_.role == s.role
    &&& s_.log_length == s.log_length + 1
    &&& s_.last_value == s.pending_value
    &&& s_.has_pending == false
    &&& s_.pending_value == 0
    &&& s_.acked == true
}

/// Failover: primary fails, backup becomes new primary
/// Pending writes are lost on failover
pub open spec fn LFailover(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.role is Primary
    &&& s_.role is Primary
    &&& s_.log_length == s.log_length
    &&& s_.last_value == s.last_value
    &&& s_.has_pending == false
    &&& s_.pending_value == 0
    &&& s_.acked == true
}

/// Next-state relation
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| (exists |val: int| LPrimaryWrite(s, s_, c, val))
    ||| LBackupAck(s, s_, c)
    ||| LPrimaryCommit(s, s_, c)
    ||| LFailover(s, s_, c)
}

}

use vstd::prelude::*;

verus! {

/// Role of a node in the primary-backup system
pub enum LNodeRole {
    Primary,
    Backup,
    Inactive,
}

/// State of the primary-backup system (global perspective)
pub struct LState {
    /// Role of this node (Primary, Backup, or Inactive)
    pub role: LNodeRole,
    /// Number of writes committed to the primary's log
    pub log_length: int,
    /// The last committed value
    pub last_value: int,
    /// Whether there is a pending write waiting for ack
    pub has_pending: bool,
    /// The pending write value (valid when has_pending is true)
    pub pending_value: int,
    /// Whether the backup has acknowledged the latest pending write
    pub acked: bool,
    // Backup-side state
    /// Number of writes committed to the backup's log
    pub backup_log_length: int,
    /// The last value committed on the backup
    pub backup_last_value: int,
    /// Whether the backup is synced with the primary
    pub backup_synced: bool,
    // View/epoch for split-brain prevention
    /// Current view/epoch number (incremented on failover)
    pub view: int,
    // Message flags
    /// Primary has sent a replicate message
    pub msgs_replicate: bool,
    /// Value being replicated
    pub msgs_replicate_val: int,
    /// Backup has sent an ack
    pub msgs_ack: bool,
}

/// System constants
pub struct LConstants {
    /// Maximum number of writes before we stop accepting
    pub max_log_len: int,
}

}

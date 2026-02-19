// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::protocol::PrimaryBackup::primarybackup::*;
use crate::protocol::PrimaryBackup::types::*;
use vstd::prelude::*;

verus! {

#[derive(Clone)]
pub struct CState {
    pub role: CNodeRole,
    pub log_length: u64,
    pub last_value: u64,
    pub has_pending: bool,
    pub pending_value: u64,
    pub acked: bool,
    pub backup_log_length: u64,
    pub backup_last_value: u64,
    pub backup_synced: bool,
    pub view: u64,
}

impl CState {
    pub open spec fn valid(&self) -> bool {
        &&& self.role.valid()
    }
}

impl View for CState {
    type V = LState;

    open spec fn view(&self) -> LState {
        LState {
            role: self.role@,
            log_length: self.log_length as int,
            last_value: self.last_value as int,
            has_pending: self.has_pending,
            pending_value: self.pending_value as int,
            acked: self.acked,
            backup_log_length: self.backup_log_length as int,
            backup_last_value: self.backup_last_value as int,
            backup_synced: self.backup_synced,
            view: self.view as int,
        }
    }
}

#[derive(Clone)]
pub struct CConstants {
    pub max_log_len: u64,
}

impl CConstants {
    pub open spec fn valid(&self) -> bool {
        true
    }
}

impl View for CConstants {
    type V = LConstants;

    open spec fn view(&self) -> LConstants {
        LConstants {
            max_log_len: self.max_log_len as int,
        }
    }
}

#[derive(Clone)]
pub enum CNodeRole {
    Primary,
    Backup,
    Inactive,
}

impl CNodeRole {
    pub open spec fn valid(&self) -> bool {
        match self {
            CNodeRole::Primary => true,
            CNodeRole::Backup => true,
            CNodeRole::Inactive => true,
        }
    }
}

impl View for CNodeRole {
    type V = LNodeRole;

    open spec fn view(&self) -> LNodeRole {
        match self {
            CNodeRole::Primary => LNodeRole::Primary,
            CNodeRole::Backup => LNodeRole::Backup,
            CNodeRole::Inactive => LNodeRole::Inactive,
        }
    }
}

#[derive(Clone)]
pub enum CPBMessage {
    Replicate {
        val: u64,
    },
    Ack,
}

impl CPBMessage {
    pub open spec fn valid(&self) -> bool {
        match self {
            CPBMessage::Replicate { val } => true,
            CPBMessage::Ack => true,
        }
    }
}

impl View for CPBMessage {
    type V = LPBMessage;

    open spec fn view(&self) -> LPBMessage {
        match self {
            CPBMessage::Replicate { val } => LPBMessage::Replicate { val: *val as int },
            CPBMessage::Ack => LPBMessage::Ack,
        }
    }
}

} // verus!

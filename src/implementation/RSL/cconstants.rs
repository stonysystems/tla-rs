use crate::common::native::io_s::EndPoint;
use crate::implementation::RSL::cconfiguration::CConfiguration;
use crate::implementation::RSL::types_i::{max_votes_len, RequestBatchSizeLimit};
use crate::protocol::RSL::constants::LReplicaConstantsValid;
use vstd::prelude::*;

// Type definitions are now in types_gen.rs.
// This module keeps replica-constants helpers outside generated manual_code injection.
pub use crate::generated::RSL::types_gen::{CConstants, CReplicaConstants};

verus! {
impl CReplicaConstants {
    pub fn CReplicaConstantsValid(&self) -> (res:bool)
        requires self.valid(),
        ensures res == LReplicaConstantsValid(self@)
    {
        self.my_index >= 0 && self.my_index < self.all.config.replica_ids.len() as u64
    }
}

pub fn InitReplicaConstants(end:&EndPoint, config:&CConfiguration) -> (rc:CReplicaConstants)
    requires
        config.valid(),
        end.valid_public_key(),
        config.replica_ids@.contains(*end),
    ensures
        rc.valid(),
        rc.all.config.replica_ids[rc.my_index as int] == end,
        rc.all.config == config,
        rc.all.params.max_log_length > 0,
        rc.all.params.max_log_length < 10000,
{
    let params = crate::implementation::RSL::cparameters::StaticParams();
    let (_found, index) = config.CGetReplicaIndex(end);
    let constants = CConstants{config:config.clone_up_to_view(), params:params};
    assert(constants.config.valid());
    assert(constants.params.valid());
    assert(0 <= constants.params.heartbeat_period < constants.params.max_integer_val);
    assert(0 < constants.params.max_batch_size as int <= RequestBatchSizeLimit());
    assert(constants.params.max_log_length < max_votes_len());

    let rconstants = CReplicaConstants{my_index:index as u64, all:constants};
    assert(rconstants.abstractable());
    assert(rconstants.all.valid());
    rconstants
}
}

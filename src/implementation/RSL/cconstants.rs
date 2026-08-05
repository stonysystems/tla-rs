use crate::common::native::io_s::EndPoint;
use crate::generated::RSL::types_gen::CParameters;
use crate::implementation::RSL::cconfiguration::{CConfiguration, ReplicaIndexValid};
use crate::implementation::RSL::types_i::{max_votes_len, RequestBatchSizeLimit};
use crate::protocol::RSL::constants::{LConstants, LReplicaConstants, LReplicaConstantsValid};
use vstd::prelude::*;

verus! {
pub struct CConstants {
    pub config: CConfiguration,
    pub params: CParameters,
}

// Verus cannot attach a specification to a derived Clone for a type whose
// clone is not a copy, so `#[derive(Clone)]` left `.clone()` opaque to every
// proof. Delegating to the spec'd `clone_up_to_view` gives the same postcondition
// without adding any trusted code.
impl Clone for CConstants {
    fn clone(&self) -> (result: Self)
    ensures
        result@ == self@,
        result.valid() == self.valid(),
        self.config.replica_ids.len() == result.config.replica_ids.len(),
    {
        self.clone_up_to_view()
    }
}

pub struct CReplicaConstants {
    pub my_index: u64,
    pub all: CConstants,
}

impl Clone for CReplicaConstants {
    fn clone(&self) -> (result: Self)
    ensures
        result@ == self@,
        result.valid() == self.valid(),
        self.all.config.replica_ids.len() == result.all.config.replica_ids.len(),
    {
        CReplicaConstants {
            my_index: self.my_index,
            all: self.all.clone_up_to_view(),
        }
    }
}

impl CConstants {
    pub fn clone_up_to_view(&self) -> (result:Self)
    ensures
        self@ == result@,
        result.valid() == self.valid(),
        self.config.replica_ids.len() == result.config.replica_ids.len(),
    {
        CConstants {
            config: self.config.clone_up_to_view(),
            params: CParameters {
                max_log_length: self.params.max_log_length,
                baseline_view_timeout_period: self.params.baseline_view_timeout_period,
                heartbeat_period: self.params.heartbeat_period,
                max_integer_val: self.params.max_integer_val,
                max_batch_size: self.params.max_batch_size,
                max_batch_delay: self.params.max_batch_delay,
            },
        }
    }

    pub open spec fn abstractable(self) -> bool
    {
        self.config.abstractable()
    }

    pub open spec fn valid(self) -> bool
    {
        &&& self.config.valid()
        &&& self.params.valid()
        &&& self.abstractable()
        &&& (0 <= self.params.heartbeat_period < self.params.max_integer_val)
        &&& (0 < self.params.max_batch_size as int <= RequestBatchSizeLimit())
        &&& (self.params.max_log_length < max_votes_len())
    }

    pub open spec fn view(self) -> LConstants
        recommends self.abstractable()
    {
        LConstants{
            config:self.config@,
            params:self.params@,
        }
    }
}

impl View for CConstants {
    type V = LConstants;

    open spec fn view(&self) -> LConstants {
        LConstants {
            config: self.config@,
            params: self.params@,
        }
    }
}

impl CReplicaConstants {
    pub fn clone_up_to_view(&self) -> (result:Self)
    requires
        self.valid(),
    ensures
        self@ == result@,
        result.valid(),
        self.all.config.replica_ids.len() == result.all.config.replica_ids.len(),
    {
        CReplicaConstants {
            my_index: self.my_index,
            all: self.all.clone_up_to_view(),
        }
    }

    pub open spec fn abstractable(self) -> bool
    {
        &&& self.all.abstractable()
        &&& ReplicaIndexValid(self.my_index, self.all.config)
    }

    pub open spec fn valid(self) -> bool
    {
        &&& self.abstractable()
        &&& self.all.valid()
    }

    pub open spec fn view(self) -> LReplicaConstants
        recommends self.abstractable()
    {
        LReplicaConstants{
            my_index: self.my_index as int,
            all: self.all@,
        }
    }
}

impl View for CReplicaConstants {
    type V = LReplicaConstants;

    open spec fn view(&self) -> LReplicaConstants {
        LReplicaConstants {
            my_index: self.my_index as int,
            all: self.all@,
        }
    }
}

impl CReplicaConstants {
    pub fn CReplicaConstantsValid(&self) -> (res:bool)
        requires self.valid(),
        ensures res == LReplicaConstantsValid(self@)
    {
        // my_index: u64, so the spec's `0 <= my_index` is automatic
        self.my_index < self.all.config.replica_ids.len() as u64
    }
}

pub fn InitReplicaConstants(end:&EndPoint, config:&CConfiguration) -> (rc:CReplicaConstants)
    requires
        config.valid(),
        end.valid_public_key(),
        config.replica_ids@.contains(*end),
    ensures
        rc.valid(),
        rc.all.config@ == config@,
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

use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::parameters::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::verus;
use vstd::*;

verus! {
    pub struct LConstants {
        pub config:LConfiguration,
        pub params:LParameters,
    }

    pub struct LReplicaConstants {
        pub my_index:int,
        pub all:LConstants,
    }

    pub open spec fn LReplicaConstantsValid(c:LReplicaConstants) -> bool
    {
        0 <= c.my_index < c.all.config.replica_ids.len()
    }
}

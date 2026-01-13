use crate::common::collections::seq_is_unique_v::*;
use crate::common::collections::seqs::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::cconfiguration::*;
use crate::implementation::RSL::cparameters::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
use builtin::*;
use builtin_macros::*;
use std::collections::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus! {
    #[derive(Clone)]
    pub struct CConstants {
        pub config: CConfiguration,
        pub params: CParameters,
    }

    impl CConstants {

        #[verifier(external_body)]
        pub fn clone_up_to_view(&self) -> (result:Self)
        ensures
            self == result,
            self@ == result@,
            result.valid()
        {
            CConstants {
                config: self.config.clone_up_to_view(),
                params: self.params.clone_up_to_view(),
            }
        }

        pub open spec fn abstractable(self) -> bool
        {
            self.config.abstractable()
        }

        pub open spec fn valid(self) -> bool
        {
            &&& self.config.valid()
            // &&& self.config.CWellFormedCConfiguration()
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

    #[derive(Clone)]
    pub struct CReplicaConstants {
        pub my_index: u64,
        pub all: CConstants,
    }

    impl CReplicaConstants {

        #[verifier(external_body)]
        pub fn clone_up_to_view(&self) -> (result:Self)
        ensures
            self@ == result@,
            result.valid() // This is needed in cloning because we have to prove the validity of of the cloned object
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
            // rc.all.params == StaticParams(),
    {
        let params = StaticParams();
        let (found, index) = config.CGetReplicaIndex(end);
        let constants = CConstants{config:config.clone_up_to_view(), params:params};
        assert(constants.config.valid());
        // assert(constants.config.CWellFormedCConfiguration());
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

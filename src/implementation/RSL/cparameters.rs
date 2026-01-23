use vstd::prelude::*;
use crate::common::collections::seq_is_unique_v::*;
use crate::common::collections::seq_is_unique_v::*;
use crate::common::collections::seqs::*;
use crate::common::collections::seqs::*;
use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::common::native::io_s::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::cconfiguration::*;
use crate::implementation::RSL::cconfiguration::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::common::upper_bound::*;
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::parameters::*;
use crate::protocol::RSL::parameters::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
use crate::services::RSL::app_state_machine::*;
use std::collections::*;
use std::collections::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus! {
    #[derive(Clone, Copy)]
    pub struct CParameters{
        pub max_log_length: u64,
        pub baseline_view_timeout_period: u64,
        pub heartbeat_period: u64,
        pub max_integer_val: u64,
        pub max_batch_size: u64,
        pub max_batch_delay: u64
    }

    impl CParameters{

        pub fn clone_up_to_view(&self) -> (result:Self)
        ensures self@ == result@
        {
            CParameters {
                max_log_length: self.max_log_length,
                baseline_view_timeout_period: self.baseline_view_timeout_period,
                heartbeat_period: self.heartbeat_period,
                max_integer_val: self.max_integer_val,
                max_batch_size: self.max_batch_size,
                max_batch_delay: self.max_batch_delay,
            }
        }

        pub open spec fn valid(self) -> bool
        {
            &&& self.max_integer_val > self.max_log_length > 0
            &&& self.max_integer_val > self.max_batch_delay
            &&& self.max_integer_val < 0x8000_0000_0000_0000
            &&& self.baseline_view_timeout_period > 0
            &&& self.max_integer_val > self.heartbeat_period > 0
            &&& self.max_batch_size > 0
        }

        pub open spec fn view(self) -> LParameters
        {
            LParameters{
                max_log_length: self.max_log_length as int,
                baseline_view_timeout_period: self.baseline_view_timeout_period as int,
                heartbeat_period: self.heartbeat_period as int,
                max_integer_val: UpperBound::UpperBoundFinite{n: self.max_integer_val as int},
                max_batch_size: self.max_batch_size as int,
                max_batch_delay: self.max_batch_delay as int,
            }
        }
    }

    pub fn StaticParams() -> (p:CParameters)
        ensures
            p.max_log_length > 0,
            p.max_log_length < 10000,
            p.valid(),
            p.max_log_length < max_votes_len(),
            0 < p.max_batch_size <= RequestBatchSizeLimit(),
    {
        CParameters{
            max_log_length: 1000,
            baseline_view_timeout_period: 400,
            heartbeat_period: 30,
            max_integer_val: 0x8000_0000_0000_0000 - 1,
            max_batch_size: 32,
            max_batch_delay: 30,
        }
    }
}

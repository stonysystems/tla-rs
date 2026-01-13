use crate::protocol::common::upper_bound::*;
use builtin::*;
use builtin_macros::*;
use vstd::*;

verus! {
    pub struct LParameters {
        pub max_log_length:int,
        pub baseline_view_timeout_period:int,
        pub heartbeat_period:int,
        pub max_integer_val:UpperBound,
        pub max_batch_size:int,
        pub max_batch_delay:int
    }

    pub open spec fn WFLParameters(p:LParameters) -> bool
    {
        &&& p.max_log_length > 0
        &&& p.baseline_view_timeout_period > 0
        &&& p.heartbeat_period > 0
        // &&& (p.max_integer_val.UpperBoundFinite? ==> p.max_integer_val.n > p.max_log_length)
        &&& p.max_batch_size > 0
        &&& p.max_batch_delay >= 0
    }
}

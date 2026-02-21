use crate::implementation::RSL::types_i::{max_votes_len, RequestBatchSizeLimit};
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::parameters::*;
use vstd::prelude::*;

// Type definitions are generated in types_gen.rs.
// This module owns CParameters validity/view semantics and StaticParams.
pub use crate::generated::RSL::types_gen::CParameters;

verus! {
impl CParameters{
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

impl View for CParameters {
    type V = LParameters;

    open spec fn view(&self) -> LParameters {
        LParameters {
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

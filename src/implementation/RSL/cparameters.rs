use crate::implementation::RSL::types_i::{max_votes_len, RequestBatchSizeLimit};
use vstd::prelude::*;

// Type definitions and most implementations are now in types_gen.rs.
// This module keeps `StaticParams` outside generated manual_code injection.
pub use crate::generated::RSL::types_gen::CParameters;

verus! {
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

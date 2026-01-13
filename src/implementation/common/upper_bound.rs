use crate::common::collections::seq_is_unique_v::*;
use crate::common::collections::seqs::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::cconfiguration::*;
use crate::protocol::common::upper_bound::*;
use crate::services::RSL::app_state_machine::*;
use builtin::*;
use builtin_macros::*;
use std::collections::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus! {

    pub fn CUpperBoundedAddition(x:u64, y:u64, u:u64) -> (sum:u64)
        ensures
            sum as int == UpperBoundedAddition(x as int, y as int, UpperBound::UpperBoundFinite{n:u as int})
    {
        if y >= u {
            u
        } else if x >= u - y {
            u
        } else {
            x + y
        }
    }
}

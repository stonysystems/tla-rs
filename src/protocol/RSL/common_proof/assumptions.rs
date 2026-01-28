use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::message::*;
use vstd::prelude::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

use crate::common::collections::maps2::*;
use crate::common::framework::environment_s::*;
use crate::common::logic::temporal_s::*;
use crate::common::native::io_s::*;

verus! {
    pub open spec fn IsValidBehaviorPrefix(
        b:Behavior<RslState>,
        c:LConstants,
        i:int
    ) -> bool
    {
        &&& imaptotal(b)
        &&& RslInit(c, b[0])
        &&& (forall |j:int| #![trigger b[j]] 0 <= j < i ==> RslNext(b[j], b[j+1]))
    }
}

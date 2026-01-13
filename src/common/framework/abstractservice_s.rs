#![allow(unused_imports)]
use super::environment_s::*;
use crate::common::logic::*;
use crate::common::native::io_s::*;
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    // pub trait AbstractService {
    //     type ServiceState;

    //     spec fn Service_Init(s: Self::ServiceState, serverAddresses: Set<AbstractEndPoint>) -> bool;
    //     spec fn Service_Next(s: Self::ServiceState, s_: Self::ServiceState) -> bool;
    //     spec fn Service_Correspondence(concretePkts: Set<LPacket<AbstractEndPoint, Seq<u8>>>, serviceState: Self::ServiceState) -> bool;
    // }
} // !verus

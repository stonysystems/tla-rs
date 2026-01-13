#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;

verus! {
    pub enum LockMessage{
        Transfer{transfer_epoch:int},
        Locked{locked_epoch:int},
        Invalid
    }

    pub type LockEnvironment = LEnvironment<AbstractEndPoint, LockMessage>;
    pub type LockPacket = LPacket<AbstractEndPoint, LockMessage>;
    pub type LockIo = LIoOp<AbstractEndPoint, LockMessage>;
}

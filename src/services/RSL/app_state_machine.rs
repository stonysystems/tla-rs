use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::seq::*;
use vstd::set::*;

use vstd::pervasive::*;
use builtin::*;
use builtin_macros::*;

verus! {
    pub type AppState = u64;

    pub enum AppMessage {
        AppIncrementRequest{},
        AppIncrementReply{
            response : u64,
        },
        AppInvalidReply{},
    }

    pub open spec fn AppInitialize() -> AppState
    {
        0
    }

    pub open spec fn CappedIncr(v:u64) -> u64
    {
        if v == 0xffff_ffff_ffff_ffff {
            v 
        } else {
            (v + 1) as u64
        }
    }

    pub open spec fn AppHandleRequest(m:AppState, request:AppMessage) -> (AppState, AppMessage)
    {
        if request is AppIncrementRequest {
            (CappedIncr(m), AppMessage::AppIncrementReply{response:CappedIncr(m)})
        } else {
            (m, AppMessage::AppInvalidReply{})
        }
    }
}
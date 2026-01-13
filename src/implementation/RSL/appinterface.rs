use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
// use crate::protocol::RSL::configuration::*;
// use crate::protocol::RSL::constants::*;
// use crate::protocol::RSL::broadcast::*;
// use crate::protocol::RSL::environment::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;

use crate::implementation::common::marshalling::*;

verus! {
    pub type CAppState = u64;

    pub open spec fn CAppStateIsAbstractable(s:&CAppState) -> bool {
        true
    }

    pub open spec fn CAppStateIsValid(s:&CAppState) -> bool {
        true
    }

    pub open spec fn AbstractifyCAppStateToAppState(s:&CAppState) -> AppState
        recommends CAppStateIsAbstractable(s)
    {
        *s
    }

    // #[derive(Clone, PartialEq)]
    // pub enum CAppMessage {
    //     CAppIncrement{},
    //     CAppReply{
    //         response:u64,
    //     },
    //     CAppInvalid{},
    // }

    define_enum_and_derive_marshalable! {
        #[derive(Clone, PartialEq, Eq, Hash)]
        pub enum CAppMessage {
            #[tag = 0]
            CAppIncrement,
            #[tag = 1]
            CAppReply { #[o=o0]response: u64 },
            #[tag = 2]
            CAppInvalid,
        }
        [rlimit attr = verifier::rlimit(25)]
    }

    impl CAppMessage {

        pub fn clone_up_to_view(&self) -> (res: CAppMessage)
            ensures res@ == self@
        {
            match self {
                CAppMessage::CAppIncrement {} => CAppMessage::CAppIncrement {},
                CAppMessage::CAppReply { response } => CAppMessage::CAppReply { response: *response },
                CAppMessage::CAppInvalid {} => CAppMessage::CAppInvalid {},
            }
        }

        pub open spec fn abstractable(&self) -> bool {
            true
        }

        pub open spec fn valid(&self) -> bool {
            self.abstractable()
        }

        pub open spec fn view(&self) -> AppMessage
            recommends
                self.abstractable()
        {
            match self {
                CAppMessage::CAppIncrement{} => AppMessage::AppIncrementRequest{},
                CAppMessage::CAppReply{response} => AppMessage::AppIncrementReply{response: *response},
                CAppMessage::CAppInvalid{} => AppMessage::AppInvalidReply{},
            }
        }

        pub proof fn view_equal_spec()
            ensures forall |x: &CAppMessage, y: &CAppMessage| #[trigger] x.view_equal(y) <==> x@ == y@
        {
            assert forall |x: &CAppMessage, y: &CAppMessage|
            #[trigger] x.view_equal(y) <==> x@ == y@ by
            {
            match (x, y) {
                (CAppMessage::CAppIncrement {  }, CAppMessage::CAppIncrement { }) => {},
                (CAppMessage::CAppReply { response:r1 }, CAppMessage::CAppReply { response:r2 }) => {},
                (CAppMessage::CAppInvalid {  }, CAppMessage::CAppInvalid {  }) => {},
                _ => {
                assert(!x.view_equal(y) && x@ != y@);
                }
            }
            }
        }
    }

    pub fn CAppStateInit() -> (s:CAppState)
        ensures
            CAppStateIsAbstractable(&s),
            AbstractifyCAppStateToAppState(&s) == AppInitialize(),
    {
        0 
    }

    pub fn CappendIncrImpl(v:&u64) -> (rc:u64)
            requires 0 <= *v <= 0xffff_ffff_ffff_ffff
            ensures rc == CappedIncr(*v)
        {
            if (*v == 0xffff_ffff_ffff_ffff) {
                // return v;
                *v
            } else {
                // return v + 1;
                v + 1
            }
        }

    pub fn HandleAppRequest(appState:&CAppState, request:&CAppMessage) -> (rc:(CAppState, CAppMessage))
        requires
            CAppStateIsAbstractable(appState),
            request.abstractable(),
        ensures
            CAppStateIsAbstractable(&rc.0),
            rc.1.abstractable(),
            AppHandleRequest(AbstractifyCAppStateToAppState(appState), request.view()) ==
            (AbstractifyCAppStateToAppState(&rc.0), rc.1.view())
    {
        match request {
            CAppMessage::CAppIncrement {} => {(CappendIncrImpl(appState), CAppMessage::CAppReply{response: CappendIncrImpl(appState)})},
            _ => {(*appState, CAppMessage::CAppInvalid{})}
        }
    }

}

#![allow(unused_imports)]
use super::distributedsystem_s::*;
use super::environment_s::*;
use super::host_s::*;
use crate::common::logic::*;
use crate::common::native::io_s::*;
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    // trait IronFleetMain<H_s: HostSpec, D_s: DistributedSystem<H_s>> {
    //     fn IronfleetMain(Ghost(env): Ghost<&mut HostEnvironment>, netc:&NetClient, args:Seq<Seq<char>>)
    //     requires env.Valid() && env.ok@.ok(),
    //              env.net@.history().len() == 0,
    //              netc.env == env,
    //              ValidPhysicalAddress(EndPoint{public_key: netc.MyPublicKey()}),
    //     {
    //         let ret = H_s::HostInitImpl(env, netc, args);
    //         let ok = ret.ok;
    //         let host_state = ret.host_state;
    //         let config = H_s::ParseCommandLineConfiguration(args);
    //         let id = EndPoint{public_key: netc.MyPublicKey()};
    //         assert(ok ==> H_s::HostInit(host_state, config, id));

    //         while (ok)
    //           invariant ok ==> H_s::HostStateInvariants(host_state, *env),
    //                     ok ==> env.Valid() && env.ok@.ok()
    //         {
    //           let ghost old_net_history = env.net@.history();
    //           let ghost old_state = host_state;

    //           let ghost implRet = H_s::HostNextImpl(Ghost(env), host_state);
    //           if ok {
    //             // Correctly executed one action
    //             assert(H_s::HostNext(old_state, host_state, implRet.ios@));

    //             // Connect the low-level IO events to the spec-level IO events
    //             assert(implRet.recvs@ + implRet.clocks@ + implRet.sends@ == implRet.ios@);

    //             // These obligations enable us to apply reduction
    //             assert(env.net@.history() == old_net_history + implRet.recvs@ + implRet.clocks@ + implRet.sends@);
    //             assert(forall |e | implRet.recvs@.contains(e) ==> e is Receive && (implRet.clocks@.contains(e) ==> e is ReadClock || e is TimeoutReceive) && (implRet.sends@.contains(e) ==> e is Send)) ;
    //             assert(implRet.clocks@.len() <= 1);
    //           }
    //         }
    //     }
    // }
}

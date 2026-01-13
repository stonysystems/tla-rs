#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

use super::types::*;
use crate::common::framework::args_t::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;

verus! {
    pub type AbstractConfig = Seq<AbstractEndPoint>;

    pub struct AbstractNode {
        pub held: bool,
        pub epoch: nat,
        pub my_index: nat,
        pub config: AbstractConfig,
    }

    pub open spec fn parse_arg_as_end_point(arg: AbstractArg) -> AbstractEndPoint
    {
        AbstractEndPoint{id: arg}
    }

    pub open spec fn unchecked_parse_args(args: AbstractArgs) -> Seq<AbstractEndPoint>
    {
        args.map(|idx, arg: AbstractArg| parse_arg_as_end_point(arg))
    }

    pub open spec(checked) fn parse_args(args: AbstractArgs) -> Option<Seq<AbstractEndPoint>>
    {
        let end_points = unchecked_parse_args(args);
        if forall |i| #![auto] 0 <= i < end_points.len() ==> end_points[i].valid_physical_address() {
            Some(end_points)
        } else {
            None
        }
    }

    pub open spec fn NodeInit(s:AbstractNode, my_index: nat, config:AbstractConfig) -> bool
    {
        &&& s.epoch == (if my_index == 0 { 1i32 as nat } else {0i32 as nat})
        &&& 0 <= my_index < config.len() as nat
        &&& s.my_index == my_index
        &&& s.held == (my_index == 0)
        &&& s.config =~= config
    }

    pub open spec fn NodeGrant(s:AbstractNode, s_:AbstractNode, ios:Seq<LockIo>) -> bool
    {
        &&& s.my_index == s_.my_index // change
        &&& if s.held && s.epoch < 0xFFFF_FFFF_FFFF_FFFF
            {
                &&& !s_.held
                &&& ios.len() == 1 && ios[0] is Send
                &&& s.config.len() > 0
                &&& s_.config =~= s.config
                &&& s_.epoch == s.epoch
                &&& {
                    let outbound_packet = ios[0]->s;
                    &&& outbound_packet.msg is Transfer
                    &&& outbound_packet.msg->transfer_epoch == s.epoch + 1
                    &&& outbound_packet.dst == s.config[((s.my_index + 1) % (s.config.len())) as int]
                }
                } else {
                    &&& s == s_
                    &&& ios.len() == 0
                    &&& s_.config =~= s.config
                }
    }

    pub open spec fn ignore_unparseable_packets() -> bool {
        true
    }

    pub open spec fn NodeAccept(s:AbstractNode, s_:AbstractNode, ios:Seq<LockIo>) -> bool
    {
        &&& s.my_index == s_.my_index
        &&& ios.len() >= 1
        &&& if ios[0] is TimeoutReceive {
            s == s_ && ios.len() == 1
        } else if ios[0] is Receive {
            // NOTE: Need to prove that demarshalled messages when not valid size are CInvalid to get around this
            // Otherwise ios[0]->r.msg is Transfer can still be true, and the condition fails, which is why we have the
            // || condition to maintain the protocol state when packets are ignored.
            ||| {
                if !s.held  && s.config.contains(ios[0]->r.src) && ios[0]->r.msg is Transfer && ios[0]->r.msg->transfer_epoch > s.epoch {
                        &&& s_.held
                        &&& ios.len() == 2
                        &&& ios[1] is Send
                        &&& ios[1]->s.msg is Locked
                        &&& s_.epoch == ios[0]->r.msg->transfer_epoch == ios[1]->s.msg->locked_epoch
                        &&& s_.config == s.config
                } else {
                    &&& s == s_
                    &&& ios.len() == 1
                    &&& s_.config =~= s.config
                 }
            }
            ||| {
                &&& s == s_
                &&& s_.config =~= s.config
                &&& ios.len() == 1
                &&& ignore_unparseable_packets()
            }
            } else {
                true
            }
    }

    pub open spec fn NodeNext(s:AbstractNode, s_:AbstractNode, ios:Seq<LockIo>) -> bool
    {
        ||| NodeGrant(s, s_, ios)
        ||| NodeAccept(s, s_, ios)
    }
}

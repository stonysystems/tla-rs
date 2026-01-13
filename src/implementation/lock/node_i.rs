#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

use crate::common::collections::seq_is_unique_v::{endpoints_contain, seq_is_unique};
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::AbstractEndPoint;
use crate::common::native::io_s::{abstractify_end_points, EndPoint};
use crate::implementation::common::marshalling::*;
use crate::implementation::lock::message_i::*;
use crate::protocol::lock::types::*;
use crate::protocol::lock::{self, node::*};

use super::message_i::CLockPacket;

verus! {
    pub type ConcreteConfig = Vec<EndPoint>;

    pub struct Node {
        pub held: bool,
        pub epoch: u64,
        pub my_index: usize,
        pub config: ConcreteConfig
    }

    pub open spec fn valid_config(c:ConcreteConfig) -> bool
    {
        // &&& 0 < c.len() < 0x1_0000_0000_0000_0000
        &&& (forall |i: int| #![auto] 0 <= i < c.len() ==> c[i]@.valid_physical_address())
        &&& seq_is_unique(abstractify_end_points(c))
    }

    pub open spec fn valid_config_index(c:ConcreteConfig, index:usize) -> bool
    {
        0 <= index < c.len()
    }

    impl Node {
        pub open spec fn view(self) -> AbstractNode {
            AbstractNode{
                held: self.held,
                epoch: self.epoch as nat,
                my_index: self.my_index as nat,
                config: abstractify_end_points(self.config),
            }
        }


        pub open spec fn valid(self) -> bool {
            &&& valid_config_index(self.config, self.my_index)
            &&& valid_config(self.config)
        }

        pub fn init(my_index: usize, config: ConcreteConfig) -> (rc:Self)
            requires 0 < (config.len() as nat) < 0x1_0000_0000_0000_0000,
                     0 <= my_index < config.len(),
                    valid_config(config),
            ensures rc.valid(),
                    NodeInit(rc@, my_index as nat, abstractify_end_points(config)),
                    rc@.my_index == my_index as nat,
                    rc@.config == abstractify_end_points(config),
        {

            let node = Node{
                held: my_index == 0,
                epoch: if my_index == 0 {1} else {0},
                my_index,
                config,
            };
            return node;
        }

        pub fn grant(&mut self) -> (rc: (Option<CLockPacket>, Ghost<Seq<LockIo>>))
            requires old(self).valid(),
            ensures NodeGrant(old(self)@, self@, rc.1@),
                    old(self)@.my_index == self@.my_index && old(self)@.config =~= self@.config,
                    ({
                    let (packet, Ghost(ios)) = rc;
                        {
                        &&& ios.len() == 0 || ios.len() == 1
                        &&& packet is Some ==> ios.len() == 1 && ios[0] is Send && ios[0]->s == packet.unwrap()@
                        &&& optional_clock_packet_is_valid(packet)
                        &&& (packet is Some ==> packet.unwrap().src@ == old(self)@.config[old(self)@.my_index as int])
                        &&& packet is None ==> ios.len() == 0 && self@ == old(self)@
                        }
                    }),
                    self.valid()
        {
            if self.held && self.epoch < 0xFFFF_FFFF_FFFF_FFFF {
                self.held = false;
                let dst_index = (self.my_index + 1) % (self.config.len());
                assert(0 <= dst_index < self.config.len());
                let packet = Some(LPacket{
                    dst: self.config[dst_index].clone_up_to_view(),
                    src: self.config[self.my_index].clone_up_to_view(),
                    msg: CMessage::CTransfer{transfer_epoch: self.epoch + 1} });

                let ghost ios = seq![LIoOp::Send{s: packet.unwrap()@}];

                proof {
                    let abstract_packet = packet.unwrap();
                    assert(abstract_packet.abstractable());
                    assert(abstract_packet.msg.is_marshalable()) by {
                        vstd::bytes::lemma_auto_spec_u64_to_from_le_bytes();
                    };
                }
                // print "I grant the lock ", s.epoch, "\n";
                (packet, Ghost(ios))
            } else {
                (None, Ghost(Seq::empty()))
            }
        }

        #[verifier::external_body]
        pub fn print_accept(epoch: u64, s: &str) {
            println!("{} {}", epoch, s);
        }

        pub fn accept(&mut self, transfer_packet: CLockPacket) -> (rc: (Option<CLockPacket>, Ghost<Seq<LockIo>>))
            requires old(self).valid(),
            ensures  NodeAccept(old(self)@, self@, rc.1@),
                     self@.my_index == old(self)@.my_index && self@.config == old(self)@.config,
                     ({
                        let (locked_packet, Ghost(ios)) = rc;
                        // &&& ios.len() == 1 || ios.len() == 2
                        &&& locked_packet is None ==> ios.len() == 1 && ios[0] is Receive
                                                        && ios[0]->r == transfer_packet@
                        &&& locked_packet is Some ==> ios.len() == 2
                                                    && ios =~= seq![LIoOp::Receive{r: transfer_packet@},
                                                        LIoOp::Send{s: locked_packet.unwrap()@}]
                        &&& optional_clock_packet_is_valid(locked_packet)
                        &&& locked_packet is Some && optional_clock_packet_is_valid(locked_packet) ==> locked_packet.unwrap().src@ == old(self)@.config[old(self)@.my_index as int]
                     }),
              self.valid(),
        {
            let ghost ios = seq![LIoOp::Receive{r: transfer_packet@}];

            if !self.held
                    && endpoints_contain(&self.config, &transfer_packet.src)
                    {
                        let ret = match (transfer_packet.msg){
                            CMessage::CTransfer{transfer_epoch} => {
                                if transfer_epoch > self.epoch {
                                    self.held = true;
                                    self.epoch = transfer_epoch;
                                    let locked_packet = Some(LPacket{
                                                                dst: transfer_packet.src.clone_up_to_view(),
                                                                src: self.config[self.my_index].clone_up_to_view(),
                                                                msg: CMessage::CLocked{locked_epoch: transfer_epoch}

                                                            });
                                    proof {
                                        assert(locked_packet.unwrap().msg.is_marshalable()) by {
                                            vstd::bytes::lemma_auto_spec_u64_to_from_le_bytes();
                                        };
                                        ios = ios.add(seq![LIoOp::Send{s: locked_packet.unwrap()@}]);
                                    }
                                    Self::print_accept(transfer_epoch, "I hold the lock!");
                                    (locked_packet, Ghost(ios))
                                } else {
                                    (None, Ghost(ios))
                                }
                            }
                            _ => {
                                (None,Ghost(ios))
                            }
                        };
                        ret
            } else  {
                // Self::print_accept("I don't hold the lock!");
                (None, Ghost(ios))
            }
        }
    }
}

// Complete Lock service NodeGrant example with both spec and exec
// Tests: I/O patterns with enum variants, packet sending, complex conditionals
// Based on Lock protocol node.rs NodeGrant predicate

use vstd::prelude::*;
use vstd::seq::*;

verus! {
    // === SPEC TYPES ===

    #[derive(PartialEq, Eq, Structural)]
    pub struct AbstractEndPoint {
        pub id: int,
    }

    impl AbstractEndPoint {
        pub open spec fn valid_physical_address(&self) -> bool {
            self.id >= 0
        }
    }

    pub type AbstractConfig = Seq<AbstractEndPoint>;

    pub struct AbstractNode {
        pub held: bool,
        pub epoch: nat,
        pub my_index: nat,
        pub config: AbstractConfig,
    }

    // Extensional equality for AbstractNode
    pub open spec fn nodes_eq(a: AbstractNode, b: AbstractNode) -> bool {
        &&& a.held == b.held
        &&& a.epoch == b.epoch
        &&& a.my_index == b.my_index
        &&& a.config =~= b.config
    }

    #[derive(PartialEq, Eq, Structural)]
    pub enum LockMessage {
        Transfer { transfer_epoch: int },
        Locked { locked_epoch: int },
        Invalid,
    }

    #[derive(PartialEq, Eq, Structural)]
    pub struct LockPacket {
        pub dst: AbstractEndPoint,
        pub src: AbstractEndPoint,
        pub msg: LockMessage,
    }

    #[derive(PartialEq, Eq, Structural)]
    pub enum LockIo {
        Send { s: LockPacket },
        Receive { r: LockPacket },
        TimeoutReceive,
    }

    // === SPEC PREDICATE (from Lock node.rs) ===

    pub open spec fn NodeGrant(s: AbstractNode, s_: AbstractNode, ios: Seq<LockIo>) -> bool
    {
        &&& s.my_index == s_.my_index
        &&& if s.held && s.epoch < 0xFFFF_FFFF_FFFF_FFFFu64 as nat
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
                &&& nodes_eq(s, s_)
                &&& ios.len() == 0
            }
    }

    // === EXEC TYPES ===

    pub struct CEndPoint {
        pub id: i64,
    }

    impl CEndPoint {
        pub open spec fn well_formed(&self) -> bool {
            self.id >= 0
        }

        pub fn clone_for_view(&self) -> (result: CEndPoint)
            ensures result@ == self@
        {
            CEndPoint { id: self.id }
        }
    }

    impl View for CEndPoint {
        type V = AbstractEndPoint;
        open spec fn view(&self) -> AbstractEndPoint {
            AbstractEndPoint { id: self.id as int }
        }
    }

    // Config as Vec of endpoints
    pub struct CConfig {
        pub endpoints: Vec<CEndPoint>,
    }

    impl CConfig {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.endpoints@.len() > 0
            &&& forall |i: int| 0 <= i < self.endpoints@.len() ==> self.endpoints@[i].well_formed()
        }

        pub fn len(&self) -> (result: usize)
            ensures result == self@.len()
        {
            self.endpoints.len()
        }

        pub fn get(&self, idx: usize) -> (result: &CEndPoint)
            requires idx < self@.len()
            ensures result@ == self@[idx as int]
        {
            &self.endpoints[idx]
        }

        pub fn clone_for_view(&self) -> (result: CConfig)
            requires self.well_formed()
            ensures result@ == self@, result.well_formed()
        {
            let mut new_endpoints: Vec<CEndPoint> = Vec::new();
            let mut i: usize = 0;
            while i < self.endpoints.len()
                invariant
                    i <= self.endpoints@.len(),
                    new_endpoints@.len() == i,
                    forall |j: int| 0 <= j < i ==> new_endpoints@[j]@ == self.endpoints@[j]@,
                    forall |j: int| 0 <= j < i ==> new_endpoints@[j].well_formed(),
                    self.well_formed(),
                decreases self.endpoints@.len() - i
            {
                new_endpoints.push(self.endpoints[i].clone_for_view());
                i = i + 1;
            }
            CConfig { endpoints: new_endpoints }
        }
    }

    impl View for CConfig {
        type V = AbstractConfig;
        open spec fn view(&self) -> AbstractConfig {
            Seq::new(self.endpoints@.len(), |i: int| self.endpoints@[i]@)
        }
    }

    pub struct CNode {
        pub held: bool,
        pub epoch: u64,
        pub my_index: u64,
        pub config: CConfig,
    }

    impl CNode {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.config.well_formed()
            &&& (self.my_index as int) < self.config@.len()
        }
    }

    impl View for CNode {
        type V = AbstractNode;
        open spec fn view(&self) -> AbstractNode {
            AbstractNode {
                held: self.held,
                epoch: self.epoch as nat,
                my_index: self.my_index as nat,
                config: self.config@,
            }
        }
    }

    // Message types
    pub enum CLockMessage {
        Transfer { transfer_epoch: i64 },
        Locked { locked_epoch: i64 },
        Invalid,
    }

    impl CLockMessage {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for CLockMessage {
        type V = LockMessage;
        open spec fn view(&self) -> LockMessage {
            match self {
                CLockMessage::Transfer { transfer_epoch } =>
                    LockMessage::Transfer { transfer_epoch: *transfer_epoch as int },
                CLockMessage::Locked { locked_epoch } =>
                    LockMessage::Locked { locked_epoch: *locked_epoch as int },
                CLockMessage::Invalid => LockMessage::Invalid,
            }
        }
    }

    pub struct CLockPacket {
        pub dst: CEndPoint,
        pub src: CEndPoint,
        pub msg: CLockMessage,
    }

    impl CLockPacket {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.dst.well_formed()
            &&& self.src.well_formed()
            &&& self.msg.well_formed()
        }
    }

    impl View for CLockPacket {
        type V = LockPacket;
        open spec fn view(&self) -> LockPacket {
            LockPacket {
                dst: self.dst@,
                src: self.src@,
                msg: self.msg@,
            }
        }
    }

    pub enum CLockIo {
        Send { s: CLockPacket },
        Receive { r: CLockPacket },
        TimeoutReceive,
    }

    impl CLockIo {
        pub open spec fn well_formed(&self) -> bool {
            match self {
                CLockIo::Send { s } => s.well_formed(),
                CLockIo::Receive { r } => r.well_formed(),
                CLockIo::TimeoutReceive => true,
            }
        }
    }

    impl View for CLockIo {
        type V = LockIo;
        open spec fn view(&self) -> LockIo {
            match self {
                CLockIo::Send { s } => LockIo::Send { s: s@ },
                CLockIo::Receive { r } => LockIo::Receive { r: r@ },
                CLockIo::TimeoutReceive => LockIo::TimeoutReceive,
            }
        }
    }

    // Helper to convert Vec<CLockIo> to Seq<LockIo>
    pub open spec fn ios_view(ios: &Vec<CLockIo>) -> Seq<LockIo> {
        Seq::new(ios@.len(), |i: int| ios@[i]@)
    }

    // === EXEC FUNCTION ===

    // Result struct for NodeGrant
    pub struct NodeGrantResult {
        pub node: CNode,
        pub ios: Vec<CLockIo>,
    }

    impl NodeGrantResult {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.node.well_formed()
            &&& forall |i: int| 0 <= i < self.ios@.len() ==> self.ios@[i].well_formed()
        }
    }

    pub fn c_node_grant(s: &CNode) -> (result: NodeGrantResult)
        requires
            s.well_formed(),
            s.my_index < 0xFFFF_FFFF_FFFF_FFFFu64,  // Ensure no overflow on my_index + 1
            s.epoch < 0x7FFF_FFFF_FFFF_FFFFu64,    // Ensure epoch+1 fits in i64
        ensures
            result.well_formed(),
            NodeGrant(s@, result.node@, ios_view(&result.ios)),
    {
        if s.held && s.epoch < 0xFFFF_FFFF_FFFF_FFFFu64 {
            // Need to compute: (my_index + 1) % config.len()
            let config_len = s.config.len() as u64;

            // Proof: config.len() > 0 from well_formed
            proof {
                assert(s.config.well_formed());
                assert(s.config@.len() > 0);
            }

            let next_idx = ((s.my_index + 1) % config_len) as usize;

            // Proof: next_idx is valid
            proof {
                assert(next_idx < s.config@.len());
            }

            let dst = s.config.get(next_idx).clone_for_view();
            let src = s.config.get(s.my_index as usize).clone_for_view();

            let transfer_epoch = (s.epoch + 1) as i64;
            let outbound_packet = CLockPacket {
                dst: dst,
                src: src,
                msg: CLockMessage::Transfer { transfer_epoch },
            };

            let io = CLockIo::Send { s: outbound_packet };
            let mut ios: Vec<CLockIo> = Vec::new();
            ios.push(io);

            let s_ = CNode {
                held: false,
                epoch: s.epoch,
                my_index: s.my_index,
                config: s.config.clone_for_view(),
            };

            // Proof: verify all conditions of NodeGrant spec
            proof {
                let spec_ios = ios_view(&ios);

                // Check my_index preserved
                assert(s@.my_index == s_@.my_index);

                // Check condition s.held && s.epoch < max
                assert(s@.held);
                assert(s@.epoch < 0xFFFF_FFFF_FFFF_FFFFu64 as nat);

                // Check !s_.held
                assert(!s_@.held);

                // Check ios.len() == 1 && ios[0] is Send
                assert(spec_ios.len() == 1);
                assert(spec_ios[0] is Send);

                // Check s.config.len() > 0
                assert(s@.config.len() > 0);

                // Check s_.config =~= s.config
                assert(s_@.config =~= s@.config);

                // Check s_.epoch == s.epoch
                assert(s_@.epoch == s@.epoch);

                // Check outbound packet properties
                let outbound = spec_ios[0]->s;
                assert(outbound.msg is Transfer);

                // The transfer_epoch matches
                assert(transfer_epoch as int == s@.epoch + 1);
                assert(outbound.msg->transfer_epoch == s@.epoch + 1);

                // The destination matches
                let expected_idx = ((s@.my_index + 1) % (s@.config.len())) as int;
                assert(next_idx as int == expected_idx);
                assert(outbound.dst == s@.config[expected_idx]);
            }

            NodeGrantResult { node: s_, ios: ios }
        } else {
            // No change, no I/O
            let s_ = CNode {
                held: s.held,
                epoch: s.epoch,
                my_index: s.my_index,
                config: s.config.clone_for_view(),
            };
            let ios: Vec<CLockIo> = Vec::new();

            // Proof hint for the "no grant" case
            proof {
                let spec_ios = ios_view(&ios);

                // Check condition: !(s.held && s.epoch < max)
                assert(!(s@.held && s@.epoch < 0xFFFF_FFFF_FFFF_FFFFu64 as nat));

                // Check ios.len() == 0
                assert(spec_ios.len() == 0);

                // Check nodes_eq (all fields match)
                assert(s@.held == s_@.held);
                assert(s@.epoch == s_@.epoch);
                assert(s@.my_index == s_@.my_index);
                assert(s@.config =~= s_@.config);
                assert(nodes_eq(s@, s_@));
            }

            NodeGrantResult { node: s_, ios: ios }
        }
    }
}

fn main() {}

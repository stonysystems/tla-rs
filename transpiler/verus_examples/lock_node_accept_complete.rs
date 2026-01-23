// Complete Lock service NodeAccept example with both spec and exec
// Tests: I/O patterns with Receive/TimeoutReceive, disjunction, packet inspection
// Based on Lock protocol node.rs NodeAccept predicate

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

    pub open spec fn ignore_unparseable_packets() -> bool {
        true
    }

    // === SPEC PREDICATE (from Lock node.rs) ===
    // Simplified: handles TimeoutReceive and valid Receive cases
    // The original has a complex disjunction for handling unparseable packets

    pub open spec fn NodeAccept(s: AbstractNode, s_: AbstractNode, ios: Seq<LockIo>) -> bool
    {
        &&& s.my_index == s_.my_index
        &&& ios.len() >= 1
        &&& if ios[0] is TimeoutReceive {
            nodes_eq(s, s_) && ios.len() == 1
        } else if ios[0] is Receive {
            // Case 1: Valid transfer received - accept lock
            ||| {
                if !s.held && s.config.contains(ios[0]->r.src) && ios[0]->r.msg is Transfer && ios[0]->r.msg->transfer_epoch > s.epoch {
                    &&& s_.held
                    &&& ios.len() == 2
                    &&& ios[1] is Send
                    &&& ios[1]->s.msg is Locked
                    &&& s_.epoch == ios[0]->r.msg->transfer_epoch
                    &&& ios[1]->s.msg->locked_epoch == s_.epoch
                    &&& s_.config =~= s.config
                } else {
                    &&& nodes_eq(s, s_)
                    &&& ios.len() == 1
                }
            }
            // Case 2: Ignore unparseable packets
            ||| {
                &&& nodes_eq(s, s_)
                &&& ios.len() == 1
                &&& ignore_unparseable_packets()
            }
        } else {
            true
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

        pub fn eq(&self, other: &CEndPoint) -> (result: bool)
            ensures result == (self@ == other@)
        {
            self.id == other.id
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
            &&& forall |i: int| #![auto] 0 <= i < self.endpoints@.len() ==> self.endpoints@[i].well_formed()
        }

        pub fn len(&self) -> (result: usize)
            ensures result == self@.len()
        {
            self.endpoints.len()
        }

        pub fn contains(&self, ep: &CEndPoint) -> (result: bool)
            requires self.well_formed()
            ensures result == self@.contains(ep@)
        {
            let mut i: usize = 0;
            while i < self.endpoints.len()
                invariant
                    i <= self.endpoints@.len(),
                    forall |j: int| #![auto] 0 <= j < i ==> self.endpoints@[j]@ != ep@,
                decreases self.endpoints@.len() - i
            {
                if self.endpoints[i].eq(ep) {
                    proof {
                        // Found a match at index i
                        assert(self.endpoints@[i as int]@ == ep@);
                        // Show that self@ contains ep@ by finding it in the sequence
                        assert(self@[i as int] == ep@);
                    }
                    return true;
                }
                i = i + 1;
            }
            proof {
                // No match found - show self@ doesn't contain ep@
                assert(forall |j: int| #![auto] 0 <= j < self.endpoints@.len() ==> self.endpoints@[j]@ != ep@);
                // self@[k] == self.endpoints@[k]@ for all k
                assert(forall |k: int| #![auto] 0 <= k < self@.len() ==> self@[k] == self.endpoints@[k]@);
            }
            false
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
                    forall |j: int| #![auto] 0 <= j < i ==> new_endpoints@[j]@ == self.endpoints@[j]@,
                    forall |j: int| #![auto] 0 <= j < i ==> new_endpoints@[j].well_formed(),
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

        pub fn is_transfer(&self) -> (result: bool)
            ensures result == (self@ is Transfer)
        {
            matches!(self, CLockMessage::Transfer { .. })
        }

        #[verifier::external_body]
        pub fn get_transfer_epoch(&self) -> (result: i64)
            requires self@ is Transfer
            ensures result as int == self@->transfer_epoch
        {
            match self {
                CLockMessage::Transfer { transfer_epoch } => *transfer_epoch,
                _ => panic!("unreachable"),
            }
        }
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

        pub fn is_receive(&self) -> (result: bool)
            ensures result == (self@ is Receive)
        {
            matches!(self, CLockIo::Receive { .. })
        }

        pub fn is_timeout(&self) -> (result: bool)
            ensures result == (self@ is TimeoutReceive)
        {
            matches!(self, CLockIo::TimeoutReceive)
        }

        #[verifier::external_body]
        pub fn get_receive_packet(&self) -> (result: &CLockPacket)
            requires self@ is Receive
            ensures result@ == self@->r
        {
            match self {
                CLockIo::Receive { r } => r,
                _ => panic!("unreachable"),
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

    // Result struct for NodeAccept
    pub struct NodeAcceptResult {
        pub node: CNode,
        pub ios: Vec<CLockIo>,
    }

    impl NodeAcceptResult {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.node.well_formed()
            &&& forall |i: int| #![auto] 0 <= i < self.ios@.len() ==> self.ios@[i].well_formed()
        }
    }

    // Simplified version that handles timeout and basic receive cases
    // In real implementation would read from network
    pub fn c_node_accept_timeout(s: &CNode) -> (result: NodeAcceptResult)
        requires
            s.well_formed(),
        ensures
            result.well_formed(),
            NodeAccept(s@, result.node@, ios_view(&result.ios)),
    {
        // Timeout case: no change, single timeout IO
        let mut ios: Vec<CLockIo> = Vec::new();
        ios.push(CLockIo::TimeoutReceive);

        let s_ = CNode {
            held: s.held,
            epoch: s.epoch,
            my_index: s.my_index,
            config: s.config.clone_for_view(),
        };

        proof {
            let spec_ios = ios_view(&ios);
            assert(s@.my_index == s_@.my_index);
            assert(spec_ios.len() >= 1);
            assert(spec_ios[0] is TimeoutReceive);
            assert(nodes_eq(s@, s_@));
        }

        NodeAcceptResult { node: s_, ios: ios }
    }

    // Accept a valid transfer packet
    pub fn c_node_accept_transfer(s: &CNode, recv_packet: &CLockPacket, locked_dst: CEndPoint) -> (result: NodeAcceptResult)
        requires
            s.well_formed(),
            recv_packet.well_formed(),
            locked_dst.well_formed(),
            !s.held,
            s.config@.contains(recv_packet.src@),
            recv_packet.msg@ is Transfer,
            recv_packet.msg@->transfer_epoch > s.epoch as int,
            recv_packet.msg@->transfer_epoch <= i64::MAX as int,
        ensures
            result.well_formed(),
            NodeAccept(s@, result.node@, ios_view(&result.ios)),
    {
        let new_epoch = recv_packet.msg.get_transfer_epoch() as u64;

        // Create the locked message to send
        let locked_packet = CLockPacket {
            dst: locked_dst,
            src: s.config.endpoints[s.my_index as usize].clone_for_view(),
            msg: CLockMessage::Locked { locked_epoch: new_epoch as i64 },
        };

        let mut ios: Vec<CLockIo> = Vec::new();
        ios.push(CLockIo::Receive { r: CLockPacket {
            dst: recv_packet.dst.clone_for_view(),
            src: recv_packet.src.clone_for_view(),
            msg: CLockMessage::Transfer { transfer_epoch: new_epoch as i64 },
        }});
        ios.push(CLockIo::Send { s: locked_packet });

        let s_ = CNode {
            held: true,
            epoch: new_epoch,
            my_index: s.my_index,
            config: s.config.clone_for_view(),
        };

        proof {
            let spec_ios = ios_view(&ios);
            assert(s@.my_index == s_@.my_index);
            assert(spec_ios.len() >= 1);
            assert(spec_ios[0] is Receive);

            // The disjunction is satisfied by the first branch
            assert(!s@.held);
            assert(s@.config.contains(spec_ios[0]->r.src));
            assert(spec_ios[0]->r.msg is Transfer);
            assert(spec_ios[0]->r.msg->transfer_epoch > s@.epoch);

            assert(s_@.held);
            assert(spec_ios.len() == 2);
            assert(spec_ios[1] is Send);
            assert(spec_ios[1]->s.msg is Locked);
            assert(s_@.epoch == spec_ios[0]->r.msg->transfer_epoch);
            assert(spec_ios[1]->s.msg->locked_epoch == s_@.epoch);
            assert(s_@.config =~= s@.config);
        }

        NodeAcceptResult { node: s_, ios: ios }
    }

    // Ignore an invalid packet (second disjunction case)
    pub fn c_node_accept_ignore(s: &CNode, recv_packet: &CLockPacket) -> (result: NodeAcceptResult)
        requires
            s.well_formed(),
            recv_packet.well_formed(),
        ensures
            result.well_formed(),
            NodeAccept(s@, result.node@, ios_view(&result.ios)),
    {
        let mut ios: Vec<CLockIo> = Vec::new();
        ios.push(CLockIo::Receive { r: CLockPacket {
            dst: recv_packet.dst.clone_for_view(),
            src: recv_packet.src.clone_for_view(),
            msg: match &recv_packet.msg {
                CLockMessage::Transfer { transfer_epoch } =>
                    CLockMessage::Transfer { transfer_epoch: *transfer_epoch },
                CLockMessage::Locked { locked_epoch } =>
                    CLockMessage::Locked { locked_epoch: *locked_epoch },
                CLockMessage::Invalid => CLockMessage::Invalid,
            },
        }});

        let s_ = CNode {
            held: s.held,
            epoch: s.epoch,
            my_index: s.my_index,
            config: s.config.clone_for_view(),
        };

        proof {
            let spec_ios = ios_view(&ios);
            assert(s@.my_index == s_@.my_index);
            assert(spec_ios.len() >= 1);
            assert(spec_ios[0] is Receive);

            // The disjunction is satisfied by the second branch (ignore)
            assert(nodes_eq(s@, s_@));
            assert(spec_ios.len() == 1);
            assert(ignore_unparseable_packets());
        }

        NodeAcceptResult { node: s_, ios: ios }
    }
}

fn main() {}

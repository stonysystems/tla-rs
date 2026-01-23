// Complete RSL Broadcast example with both spec and exec
// Tests: Broadcast pattern - sending packets to all replicas
// Based on RSL broadcast.rs LBroadcastToEveryone predicate

use vstd::prelude::*;
use vstd::seq::*;

verus! {
    // === SPEC TYPES ===

    #[derive(PartialEq, Eq, Structural)]
    pub struct AbstractEndPoint {
        pub id: int,
    }

    #[derive(PartialEq, Eq, Structural)]
    pub enum Message {
        Heartbeat { value: int },
        Request { data: int },
    }

    #[derive(PartialEq, Eq, Structural)]
    pub struct Packet {
        pub dst: AbstractEndPoint,
        pub src: AbstractEndPoint,
        pub msg: Message,
    }

    pub struct Configuration {
        pub replica_ids: Seq<AbstractEndPoint>,
    }

    // === SPEC PREDICATE (from RSL broadcast.rs) ===

    pub open spec fn LBroadcastToEveryone(
        c: Configuration,
        myidx: int,
        m: Message,
        sent_packets: Seq<Packet>
    ) -> bool
    {
        &&& sent_packets.len() == c.replica_ids.len()
        &&& 0 <= myidx < c.replica_ids.len()
        &&& forall |idx: int| #![auto] 0 <= idx < sent_packets.len() ==> sent_packets[idx] == Packet {
            dst: c.replica_ids[idx],
            src: c.replica_ids[myidx],
            msg: m,
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

    pub enum CMessage {
        Heartbeat { value: i64 },
        Request { data: i64 },
    }

    impl CMessage {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn clone_for_view(&self) -> (result: CMessage)
            ensures result@ == self@
        {
            match self {
                CMessage::Heartbeat { value } => CMessage::Heartbeat { value: *value },
                CMessage::Request { data } => CMessage::Request { data: *data },
            }
        }
    }

    impl View for CMessage {
        type V = Message;
        open spec fn view(&self) -> Message {
            match self {
                CMessage::Heartbeat { value } => Message::Heartbeat { value: *value as int },
                CMessage::Request { data } => Message::Request { data: *data as int },
            }
        }
    }

    pub struct CPacket {
        pub dst: CEndPoint,
        pub src: CEndPoint,
        pub msg: CMessage,
    }

    impl CPacket {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.dst.well_formed()
            &&& self.src.well_formed()
            &&& self.msg.well_formed()
        }
    }

    impl View for CPacket {
        type V = Packet;
        open spec fn view(&self) -> Packet {
            Packet {
                dst: self.dst@,
                src: self.src@,
                msg: self.msg@,
            }
        }
    }

    pub struct CConfiguration {
        pub replica_ids: Vec<CEndPoint>,
    }

    impl CConfiguration {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.replica_ids@.len() > 0
            &&& forall |i: int| #![auto] 0 <= i < self.replica_ids@.len() ==> self.replica_ids@[i].well_formed()
        }

        pub fn len(&self) -> (result: usize)
            ensures result == self@.replica_ids.len()
        {
            self.replica_ids.len()
        }

        pub fn get(&self, idx: usize) -> (result: &CEndPoint)
            requires idx < self@.replica_ids.len()
            ensures result@ == self@.replica_ids[idx as int]
        {
            &self.replica_ids[idx]
        }
    }

    impl View for CConfiguration {
        type V = Configuration;
        open spec fn view(&self) -> Configuration {
            Configuration {
                replica_ids: Seq::new(self.replica_ids@.len(), |i: int| self.replica_ids@[i]@),
            }
        }
    }

    // Helper to convert Vec<CPacket> to Seq<Packet>
    pub open spec fn packets_view(packets: &Vec<CPacket>) -> Seq<Packet> {
        Seq::new(packets@.len(), |i: int| packets@[i]@)
    }

    // === EXEC FUNCTION ===

    pub fn c_broadcast_to_everyone(config: &CConfiguration, my_idx: usize, msg: &CMessage) -> (result: Vec<CPacket>)
        requires
            config.well_formed(),
            my_idx < config@.replica_ids.len(),
        ensures
            packets_view(&result).len() == config@.replica_ids.len(),
            LBroadcastToEveryone(config@, my_idx as int, msg@, packets_view(&result)),
    {
        let mut packets: Vec<CPacket> = Vec::new();
        let src = config.get(my_idx).clone_for_view();

        let mut i: usize = 0;
        while i < config.len()
            invariant
                i <= config.replica_ids@.len(),
                packets@.len() == i,
                my_idx < config@.replica_ids.len(),
                src@ == config@.replica_ids[my_idx as int],
                forall |j: int| #![auto] 0 <= j < i ==> packets@[j]@ == (Packet {
                    dst: config@.replica_ids[j],
                    src: config@.replica_ids[my_idx as int],
                    msg: msg@,
                }),
            decreases config.replica_ids@.len() - i
        {
            let dst = config.get(i).clone_for_view();
            let packet = CPacket {
                dst: dst,
                src: src.clone_for_view(),
                msg: msg.clone_for_view(),
            };
            packets.push(packet);
            i = i + 1;
        }

        proof {
            // Verify the broadcast predicate
            assert(packets_view(&packets).len() == config@.replica_ids.len());
            assert(0 <= my_idx as int);
            assert((my_idx as int) < config@.replica_ids.len());
        }

        packets
    }

    // Example usage: broadcast a heartbeat message
    pub fn c_send_heartbeat(config: &CConfiguration, my_idx: usize, value: i64) -> (result: Vec<CPacket>)
        requires
            config.well_formed(),
            my_idx < config@.replica_ids.len(),
        ensures
            LBroadcastToEveryone(config@, my_idx as int, (Message::Heartbeat { value: value as int }), packets_view(&result)),
    {
        let msg = CMessage::Heartbeat { value };
        c_broadcast_to_everyone(config, my_idx, &msg)
    }
}

fn main() {}

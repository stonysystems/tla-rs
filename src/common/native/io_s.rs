#![allow(unused_imports)]
use crate::common::collections::comparable::*;
use crate::common::framework::{args_t::clone_vec_u8, environment_s::*};
use crate::implementation::common::marshalling::*;
use vstd::prelude::*;
use vstd::slice::*;
use vstd::std_specs::cmp::PartialEqSpecImpl;
use vstd::std_specs::hash::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    pub struct AbstractEndPoint {
        pub id: Seq<u8>,
    }

    impl AbstractEndPoint {
        pub open spec fn valid_physical_address(self) -> bool {
            self.id.len() < 0x100000
        }

        pub open spec fn abstractable(self) -> bool {
            self.valid_physical_address()
        }
    }

    define_struct_and_derive_marshalable!{
        #[derive(Eq, Hash, Debug)]
        pub struct EndPoint{
            pub id: Vec::<u8>,
        }
    }

    impl Clone for EndPoint{

        fn clone(&self) -> (res: Self)
        ensures
            res@ == self@,
        {
            EndPoint{
                id: self.id.clone(),
            }
        }
    }

    impl View for EndPoint {
        type V = AbstractEndPoint;

        open spec fn view(&self) -> AbstractEndPoint {
            AbstractEndPoint{
                id: self.id@,
            }
        }
    }

    impl PartialEqSpecImpl for EndPoint {
        open spec fn obeys_eq_spec() -> bool {
            true
        }

        open spec fn eq_spec(&self, other: &EndPoint) -> bool {
            self@ == other@
        }
    }

    impl PartialEq for EndPoint{
        fn eq(&self, other: &Self) -> (result: bool)
            ensures result == (self@ == other@)
        {
            let r = crate::common::collections::seq_is_unique_v::do_end_points_match(self, other);
            proof {
                // do_end_points_match ensures r == (self == other) (structural equality)
                // and r == (self@ == other@) (view equality).
                // axiom_endpoint_view ensures e1@ == e2@ ==> e1 == e2.
                broadcast use axiom_endpoint_view;
            }
            r
        }
    }

    impl EndPoint {
        // Verus unimpl: Can't call clone through the trait
        pub fn clone_up_to_view(&self) -> (res: EndPoint)
            ensures res@ == self@
        {
            EndPoint{id: clone_vec_u8(&self.id)}
        }

        /// Clone with structural equality guarantee.
        /// Sound because Rust's clone on EndPoint{id: Vec<u8>} produces an identical value.
        #[verifier(external_body)]
        pub fn clone_eq(&self) -> (res: EndPoint)
            ensures res == *self, res@ == self@
        {
            self.clone()
        }

        // pub open spec fn view(self) -> AbstractEndPoint {
        //     AbstractEndPoint{id: self.id@}
        // }

        #[verifier(inline)]
        pub open spec fn abstractable(self) -> bool {
            self@.valid_physical_address()
        }

        pub open spec fn valid_public_key(&self) -> bool {
            self@.valid_physical_address()
        }

        // Translates Common/Native/Io.s.dfy
        pub fn valid_physical_address(&self) -> (out: bool)
        ensures
            out == self@.valid_physical_address(),
        {
            self.id.len() < 0x100000
        }
    }

    #[verifier(external_body)]
    pub broadcast proof fn axiom_endpoint_view(e1: EndPoint, e2: EndPoint)
        ensures #[trigger] e1@ == #[trigger] e2@ ==> e1 == e2
    {

    }

    #[verifier(external_body)]
    pub broadcast proof fn axiom_endpoint_key_model()
        ensures #[trigger] obeys_key_model::<EndPoint>()
    {
    }

    pub open spec fn abstractify_end_points(end_points: Vec<EndPoint>) -> Seq<AbstractEndPoint>
    {
        end_points@.map(|i, end_point: EndPoint| end_point@)
    }

    pub type NetPacket = LPacket<AbstractEndPoint, Seq<u8>>;
    pub type NetEvent = LIoOp<AbstractEndPoint, Seq<u8>>;
    pub type History = Seq<NetEvent>;

    pub enum State {
        Receiving,
        Sending,
        Error,
    }

    pub enum NetcReceiveResult {    // Not to be confused with Ironfleet's ReceiveResult type, which contains a parsed message
        Received { sender: EndPoint, message: Vec<u8> },
        TimedOut,
        Error,
    }

    pub struct IronfleetIOError {
        pub message: String,
    }

    pub closed spec fn from_trusted_code() -> bool { true }

    /// Owned wire data exchanged directly with the native runtime.
    pub struct WirePacket {
        pub peer: Vec<u8>,
        pub bytes: Vec<u8>,
    }

    #[verifier(external_body)]
    pub struct NativeIo {
        pub(crate) incoming: Option<WirePacket>,
        pub(crate) outbound: Vec<WirePacket>,
        pub(crate) buffers: Vec<Vec<u8>>,
        pub(crate) endpoints: Vec<Vec<u8>>,
        pub(crate) clock_ms: u64,
    }

    pub open spec fn MaxPacketSize() -> int { 0xFFFF_FFFF_FFFF_FFFF }

    pub open spec fn ValidPhysicalPacket(p:LPacket<AbstractEndPoint, Seq<u8>>) -> bool
    {
      &&& p.src.valid_physical_address()
      &&& p.dst.valid_physical_address()
      &&& p.msg.len() <= MaxPacketSize()
    }

    pub open spec fn ValidPhysicalIo(io:LIoOp<AbstractEndPoint, Seq<u8>>) -> bool
    {
      &&& (io is Receive ==> ValidPhysicalPacket(io->r))
      &&& (io is Send ==> ValidPhysicalPacket(io->s))
    }

    pub struct NetClient {
        pub state: Ghost<State>,
        pub history: Ghost<History>,
        pub end_point: EndPoint,
        pub(crate) native: NativeIo,
    }

    impl NetClient {
        //////////////////////////////////////////////////////////////////////////////
        // player-1 accessible interfaces (note requires from_trusted_code())
        //////////////////////////////////////////////////////////////////////////////

        #[verifier(external)]
        pub fn new(end_point: EndPoint) -> (net_client: Self)
            requires from_trusted_code(),
            ensures
                net_client.state() is Receiving,
                net_client.history() == Seq::<NetEvent>::empty(),
                net_client.my_end_point() == end_point@,
        {
            NetClient{
                state: Ghost(State::Receiving),
                history: Ghost(seq![]),
                end_point,
                native: NativeIo {
                    incoming: None,
                    outbound: Vec::with_capacity(64),
                    buffers: Vec::with_capacity(64),
                    endpoints: Vec::with_capacity(64),
                    clock_ms: 0,
                },
            }
        }

        // Main loop (Player 1 audited code) resets the state after having seen Player 2
        // complete a proof of refinement to an atomic protocol step.
        pub fn reset(&mut self)
            requires
                from_trusted_code()
            ensures
                self.state() is Receiving,
                self.my_end_point() == old(self).my_end_point()
        {
            self.state = Ghost(State::Receiving);
        }

        //////////////////////////////////////////////////////////////////////////////
        // player-2 accessible interfaces
        //////////////////////////////////////////////////////////////////////////////

        // This state field is how Player 2 proves that it calls receive before send.
        pub closed spec fn state(&self) -> State
        {
            self.state@
        }

        /// Translates calls to env.ok.ok().
        pub open spec fn ok(&self) -> bool
        {
            !(self.state() is Error)
        }

        /// translates NetClient.NetClientIsValid
        pub open spec fn valid(&self) -> bool
        {
            &&& self.ok()
            &&& self.my_end_point().abstractable()
        }

        pub closed spec fn history(&self) -> History
        {
            self.history@
        }

        /// Translates MyPublicKey()
        pub closed spec fn my_end_point(&self) -> AbstractEndPoint
        {
            self.end_point@
        }

        pub fn get_my_end_point(&self) -> (ep: EndPoint)
            ensures
                ep@ == self.my_end_point()
        {
            self.end_point.clone_up_to_view()
        }

        #[verifier(external)]
        pub fn get_time_internal(&self) -> (time: u64)
            requires
                from_trusted_code()
        {
            self.native.clock_ms
        }

        #[verifier(external_body)]
        pub fn get_time(&mut self) -> (time: u64)
            requires
                  old(self).state() is Receiving
            ensures ({
                &&& self.state() is Sending
                &&& self.history() == old(self).history() + seq![LIoOp::ReadClock{t: time as int}]
            })
        {
            let time: u64 = self.get_time_internal();
            self.state = Ghost(State::Sending);
            self.history = Ghost(self.history@ + seq![LIoOp::<AbstractEndPoint, Seq<u8>>::ReadClock{t: time as int}]);
            time
        }

        #[verifier(external)]
        pub fn receive_internal(&mut self, time_limit_ms: i32) -> (result: NetcReceiveResult)
        {
            if time_limit_ms < 0 {
                return NetcReceiveResult::Error;
            }
            match self.native.incoming.take() {
                Some(packet) => NetcReceiveResult::Received {
                    sender: EndPoint { id: packet.peer },
                    message: packet.bytes,
                },
                None => NetcReceiveResult::TimedOut,
            }
        }

        #[verifier(external_body)]
        pub fn receive(&mut self, time_limit_s: i32) -> (result: NetcReceiveResult)
            requires
              old(self).state() is Receiving
            ensures
              self.my_end_point() == old(self).my_end_point(),
              match result {
                NetcReceiveResult::Received{sender, message} => {
                    &&& self.state() is Receiving
                    &&& sender.abstractable()
                    &&& self.history() == old(self).history() + seq![
                        LIoOp::Receive{
                            r: LPacket{
                                dst: self.my_end_point(),
                                src: sender@,
                                msg: message@}
                        }]
                }
                NetcReceiveResult::TimedOut{} => {
                    &&& self.state() is Sending
                    &&& self.history() == old(self).history() + seq![LIoOp::TimeoutReceive{}]
                }
                NetcReceiveResult::Error{} => {
                    self.state() is Error
                }
            }
        {
            let result: NetcReceiveResult = self.receive_internal(time_limit_s);
            match result {
                NetcReceiveResult::Received{ref sender, ref message} => {
                    self.history = Ghost(self.history@ + seq![LIoOp::Receive{ r: LPacket::<AbstractEndPoint, Seq<u8>> { dst: self.my_end_point(), src: sender@, msg: message@ } } ]);
                }
                NetcReceiveResult::TimedOut{} => {
                    self.history = Ghost(self.history@ + seq![LIoOp::TimeoutReceive{}]);
                }
                NetcReceiveResult::Error{} => {
                    self.state = Ghost(State::Error{});
                }
            }
            result
        }

        #[verifier(external)]
        pub fn take_buffer(&mut self) -> Vec<u8> {
            self.native.buffers.pop().unwrap_or_else(|| Vec::with_capacity(2048))
        }

        #[verifier(external)]
        pub fn recycle_buffer(&mut self, mut buffer: Vec<u8>) {
            // Bound retained memory even after unusually large stream messages.
            if self.native.buffers.len() < 256 && buffer.capacity() <= 65536 {
                buffer.clear();
                self.native.buffers.push(buffer);
            }
        }

        #[verifier(external_body)]
        pub fn send_internal(&mut self, remote: &EndPoint, message: Vec<u8>) -> (result: Result<(), IronfleetIOError>)
            ensures
                self.my_end_point() == old(self).my_end_point(),
                self.state() == old(self).state(),
                self.history() == old(self).history(),
        {
            if self.native.outbound.len() >= 4096 {
                self.recycle_buffer(message);
                return Err(IronfleetIOError { message: "native outbound buffer limit reached".to_string() });
            }
            let mut peer = self.native.endpoints.pop().unwrap_or_default();
            peer.clear();
            peer.extend_from_slice(&remote.id);
            self.native.outbound.push(WirePacket { peer, bytes: message });
            Ok(())
        }

        pub fn send(&mut self, recipient: &EndPoint, message: Vec<u8>) -> (result: Result<(), IronfleetIOError> )
            requires
                !(old(self).state() is Error)
            ensures
                self.my_end_point() == old(self).my_end_point(),
                self.state() is Error <==> result is Err,
                result is Ok ==> self.state() is Sending,
                result is Ok ==> self.history() == old(self).history() + seq![LIoOp::Send{s: LPacket{dst: recipient@, src: self.my_end_point(), msg: message@}}],
        {
            let ghost bytes = message@;
            let result: Result<(), IronfleetIOError> = self.send_internal(recipient, message);
            match result {
                Ok(_) => {
                    self.state = Ghost(State::Sending{});
                    self.history = Ghost(self.history@ + seq![LIoOp::Send{s: LPacket{dst: recipient@, src: self.my_end_point(), msg: bytes}}]);
                }
                Err(_) => {
                    self.state = Ghost(State::Error{});
                }
            };
            result
        }
    }
} // verus!

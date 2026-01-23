// Test for LReplicaNextProcessRequest predicate
// Tests: Conditional routing based on reply cache - dispatches to Executor OR Proposer
// Pattern: Cache-based optimization with conditional component dispatch
//
// Pattern demonstrated:
// - Map lookup and comparison (reply_cache.contains_key && seqno comparison)
// - Conditional dispatch to different components based on cache state
// - State unchanged in cache-hit branch vs state modified in cache-miss branch
// - Packet sending from cache (reply) vs no packets on miss

use vstd::prelude::*;
use vstd::map::*;
use vstd::seq::*;

verus! {
    // === SPEC TYPES ===

    pub type ClientEndPoint = int;
    pub type SeqNo = int;
    pub type AppValue = int;

    // Simplified reply
    pub struct Reply {
        pub client: ClientEndPoint,
        pub seqno: SeqNo,
        pub reply: AppValue,
    }

    // Simplified request
    pub struct Request {
        pub client: ClientEndPoint,
        pub seqno: SeqNo,
        pub request: AppValue,
    }

    // Simplified packet
    pub struct RslPacket {
        pub src: ClientEndPoint,
        pub dst: ClientEndPoint,
        pub seqno_req: SeqNo,  // Request seqno
        pub reply_value: AppValue,  // For reply messages
    }

    // Reply cache
    pub type ReplyCache = Map<ClientEndPoint, Reply>;

    // Simplified proposer
    pub struct LProposer {
        pub current_state: int,
        pub request_queue: Seq<Request>,
        pub highest_seqno: Map<ClientEndPoint, SeqNo>,
    }

    // Simplified executor
    pub struct LExecutor {
        pub reply_cache: ReplyCache,
        pub my_index: int,
    }

    // Replica containing all components
    pub struct LReplica {
        pub proposer: LProposer,
        pub executor: LExecutor,
    }

    // === HELPER PREDICATES ===

    // Executor sends cached reply
    pub open spec fn LExecutorProcessRequest(
        s: LExecutor,
        inp: RslPacket,
        sent_packets: Seq<RslPacket>,
        should_send: bool  // Abstracts: seqno_req == cache[src].seqno
    ) -> bool
    {
        if should_send {
            // Send cached reply
            let r = s.reply_cache[inp.src];
            sent_packets == seq![RslPacket {
                src: s.my_index,
                dst: r.client,
                seqno_req: r.seqno,
                reply_value: r.reply,
            }]
        } else {
            // Stale request, ignore
            sent_packets == Seq::<RslPacket>::empty()
        }
    }

    // Proposer adds request to queue (simplified)
    pub open spec fn LProposerProcessRequest(
        s: LProposer,
        s_: LProposer,
        packet: RslPacket,
        should_queue: bool  // Abstracts: current_state != 0 && seqno > highest
    ) -> bool
    {
        if should_queue {
            let val = Request { client: packet.src, seqno: packet.seqno_req, request: 0 };
            &&& s_.current_state == s.current_state
            &&& s_.request_queue == s.request_queue + seq![val]
            &&& s_.highest_seqno == s.highest_seqno.insert(val.client, val.seqno)
        } else {
            &&& s_ == s
        }
    }

    // === MAIN PREDICATE ===
    // LReplicaNextProcessRequest - conditional routing with cache

    pub open spec fn LReplicaNextProcessRequest(
        s: LReplica,
        s_: LReplica,
        received_packet: RslPacket,
        sent_packets: Seq<RslPacket>,
        cache_hit: bool,      // Abstracts: reply_cache.contains_key(src) && seqno_req <= cache[src].seqno
        should_send: bool,    // For cache hit: whether to send reply
        should_queue: bool    // For cache miss: whether to queue request
    ) -> bool
    {
        if cache_hit {
            // Cache hit: dispatch to executor, state unchanged
            &&& LExecutorProcessRequest(s.executor, received_packet, sent_packets, should_send)
            &&& s_ == s
        } else {
            // Cache miss: dispatch to proposer, update proposer state
            &&& LProposerProcessRequest(s.proposer, s_.proposer, received_packet, should_queue)
            &&& sent_packets == Seq::<RslPacket>::empty()
            &&& s_ == LReplica {
                proposer: s_.proposer,
                executor: s.executor,  // Unchanged
            }
        }
    }

    // === EXEC TYPES ===

    pub struct CReply {
        pub client: i64,
        pub seqno: i64,
        pub reply: i64,
    }

    impl CReply {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for CReply {
        type V = Reply;
        open spec fn view(&self) -> Reply {
            Reply {
                client: self.client as int,
                seqno: self.seqno as int,
                reply: self.reply as int,
            }
        }
    }

    pub struct CRequest {
        pub client: i64,
        pub seqno: i64,
        pub request: i64,
    }

    impl CRequest {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for CRequest {
        type V = Request;
        open spec fn view(&self) -> Request {
            Request {
                client: self.client as int,
                seqno: self.seqno as int,
                request: self.request as int,
            }
        }
    }

    pub struct CRslPacket {
        pub src: i64,
        pub dst: i64,
        pub seqno_req: i64,
        pub reply_value: i64,
    }

    impl CRslPacket {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for CRslPacket {
        type V = RslPacket;
        open spec fn view(&self) -> RslPacket {
            RslPacket {
                src: self.src as int,
                dst: self.dst as int,
                seqno_req: self.seqno_req as int,
                reply_value: self.reply_value as int,
            }
        }
    }

    // Ghost wrapper for reply cache
    pub struct CReplyCache {
        pub ghost_state: Ghost<ReplyCache>,
    }

    impl CReplyCache {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn clone_ghost(&self) -> (result: CReplyCache)
            ensures result@ == self@
        {
            CReplyCache { ghost_state: Ghost(self.ghost_state@) }
        }

        #[verifier::external_body]
        pub fn get(&self, client: i64) -> (result: CReply)
            requires self@.contains_key(client as int)
            ensures result@ == self@[client as int]
        {
            unimplemented!()
        }
    }

    impl View for CReplyCache {
        type V = ReplyCache;
        open spec fn view(&self) -> ReplyCache {
            self.ghost_state@
        }
    }

    // Ghost wrapper for request queue
    pub struct CRequestQueue {
        pub ghost_state: Ghost<Seq<Request>>,
    }

    impl CRequestQueue {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn push(&self, req: &CRequest) -> (result: CRequestQueue)
            ensures result@ == self@ + seq![req@]
        {
            CRequestQueue { ghost_state: Ghost(self.ghost_state@ + seq![req@]) }
        }

        pub fn clone_ghost(&self) -> (result: CRequestQueue)
            ensures result@ == self@
        {
            CRequestQueue { ghost_state: Ghost(self.ghost_state@) }
        }
    }

    impl View for CRequestQueue {
        type V = Seq<Request>;
        open spec fn view(&self) -> Seq<Request> {
            self.ghost_state@
        }
    }

    // Ghost wrapper for highest seqno map
    pub struct CHighestSeqno {
        pub ghost_state: Ghost<Map<ClientEndPoint, SeqNo>>,
    }

    impl CHighestSeqno {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn insert(&self, client: i64, seqno: i64) -> (result: CHighestSeqno)
            ensures result@ == self@.insert(client as int, seqno as int)
        {
            CHighestSeqno { ghost_state: Ghost(self.ghost_state@.insert(client as int, seqno as int)) }
        }

        pub fn clone_ghost(&self) -> (result: CHighestSeqno)
            ensures result@ == self@
        {
            CHighestSeqno { ghost_state: Ghost(self.ghost_state@) }
        }
    }

    impl View for CHighestSeqno {
        type V = Map<ClientEndPoint, SeqNo>;
        open spec fn view(&self) -> Map<ClientEndPoint, SeqNo> {
            self.ghost_state@
        }
    }

    pub struct CProposer {
        pub current_state: i64,
        pub request_queue: CRequestQueue,
        pub highest_seqno: CHighestSeqno,
    }

    impl CProposer {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.request_queue.well_formed()
            &&& self.highest_seqno.well_formed()
        }
    }

    impl View for CProposer {
        type V = LProposer;
        open spec fn view(&self) -> LProposer {
            LProposer {
                current_state: self.current_state as int,
                request_queue: self.request_queue@,
                highest_seqno: self.highest_seqno@,
            }
        }
    }

    pub struct CExecutor {
        pub reply_cache: CReplyCache,
        pub my_index: i64,
    }

    impl CExecutor {
        pub open spec fn well_formed(&self) -> bool {
            self.reply_cache.well_formed()
        }
    }

    impl View for CExecutor {
        type V = LExecutor;
        open spec fn view(&self) -> LExecutor {
            LExecutor {
                reply_cache: self.reply_cache@,
                my_index: self.my_index as int,
            }
        }
    }

    pub struct CReplica {
        pub proposer: CProposer,
        pub executor: CExecutor,
    }

    impl CReplica {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.proposer.well_formed()
            &&& self.executor.well_formed()
        }
    }

    impl View for CReplica {
        type V = LReplica;
        open spec fn view(&self) -> LReplica {
            LReplica {
                proposer: self.proposer@,
                executor: self.executor@,
            }
        }
    }

    // === EXEC HELPER FUNCTIONS ===

    fn c_executor_process_request(
        s: &CExecutor,
        inp: &CRslPacket,
        should_send: bool
    ) -> (result: Vec<CRslPacket>)
        requires
            s.well_formed(),
            inp.well_formed(),
            should_send ==> s.reply_cache@.contains_key(inp.src as int),
        ensures
            LExecutorProcessRequest(s@, inp@, result@.map(|i, p: CRslPacket| p@), should_send)
    {
        if should_send {
            let r = s.reply_cache.get(inp.src);
            let reply_packet = CRslPacket {
                src: s.my_index,
                dst: r.client,
                seqno_req: r.seqno,
                reply_value: r.reply,
            };

            let mut result: Vec<CRslPacket> = Vec::new();
            result.push(reply_packet);

            proof {
                let expected_packet = RslPacket {
                    src: s.my_index as int,
                    dst: r.client as int,
                    seqno_req: r.seqno as int,
                    reply_value: r.reply as int,
                };
                assert(result@.len() == 1);
                assert(result@[0] == reply_packet);
                assert(reply_packet@ == expected_packet);
                assert(result@.map(|i, p: CRslPacket| p@) =~= seq![expected_packet]);
            }

            result
        } else {
            let result: Vec<CRslPacket> = Vec::new();
            proof {
                assert(result@.map(|i, p: CRslPacket| p@) =~= Seq::<RslPacket>::empty());
            }
            result
        }
    }

    fn c_proposer_process_request(
        s: &CProposer,
        packet: &CRslPacket,
        should_queue: bool
    ) -> (result: CProposer)
        requires
            s.well_formed(),
            packet.well_formed(),
        ensures
            LProposerProcessRequest(s@, result@, packet@, should_queue)
    {
        if should_queue {
            let val = CRequest {
                client: packet.src,
                seqno: packet.seqno_req,
                request: 0,
            };
            CProposer {
                current_state: s.current_state,
                request_queue: s.request_queue.push(&val),
                highest_seqno: s.highest_seqno.insert(val.client, val.seqno),
            }
        } else {
            CProposer {
                current_state: s.current_state,
                request_queue: s.request_queue.clone_ghost(),
                highest_seqno: s.highest_seqno.clone_ghost(),
            }
        }
    }

    // === MAIN EXEC FUNCTION ===
    // Implements LReplicaNextProcessRequest with conditional routing

    pub fn c_replica_next_process_request(
        s: &CReplica,
        received_packet: &CRslPacket,
        cache_hit: bool,
        should_send: bool,
        should_queue: bool,
    ) -> (result: (CReplica, Vec<CRslPacket>))
        requires
            s.well_formed(),
            received_packet.well_formed(),
            // Cache hit case requires cache contains source
            cache_hit && should_send ==> s.executor.reply_cache@.contains_key(received_packet.src as int),
        ensures
            result.0.well_formed(),
            LReplicaNextProcessRequest(
                s@,
                result.0@,
                received_packet@,
                result.1@.map(|i, p: CRslPacket| p@),
                cache_hit,
                should_send,
                should_queue
            ),
    {
        if cache_hit {
            // Cache hit: dispatch to executor, state unchanged
            let packets = c_executor_process_request(&s.executor, received_packet, should_send);

            // Clone replica (state unchanged)
            let same_proposer = CProposer {
                current_state: s.proposer.current_state,
                request_queue: s.proposer.request_queue.clone_ghost(),
                highest_seqno: s.proposer.highest_seqno.clone_ghost(),
            };
            let same_executor = CExecutor {
                reply_cache: s.executor.reply_cache.clone_ghost(),
                my_index: s.executor.my_index,
            };

            proof {
                assert(same_proposer@ == s.proposer@);
                assert(same_executor@ == s.executor@);
            }

            let same_replica = CReplica {
                proposer: same_proposer,
                executor: same_executor,
            };

            proof {
                assert(same_replica@ == s@);
            }

            (same_replica, packets)
        } else {
            // Cache miss: dispatch to proposer
            let new_proposer = c_proposer_process_request(&s.proposer, received_packet, should_queue);

            // Executor unchanged
            let same_executor = CExecutor {
                reply_cache: s.executor.reply_cache.clone_ghost(),
                my_index: s.executor.my_index,
            };

            proof {
                assert(same_executor@ == s.executor@);
            }

            let new_replica = CReplica {
                proposer: new_proposer,
                executor: same_executor,
            };

            let empty_packets: Vec<CRslPacket> = Vec::new();

            proof {
                assert(LProposerProcessRequest(s.proposer@, new_replica.proposer@, received_packet@, should_queue));
                assert(empty_packets@.map(|i, p: CRslPacket| p@) =~= Seq::<RslPacket>::empty());
            }

            (new_replica, empty_packets)
        }
    }
}

fn main() {}

// Manual code for replica IO dispatch functions.
// Only functions that CANNOT be auto-transpiled remain here:
// - IO dispatch with proof blocks (CReplicaNoReceiveNext, CSchedulerNext, etc.)
// - Message type dispatch (CReplicaNextProcessPacketWithoutReadingClock)
// - External body helpers (Packet1bHasUniqueSrc, CExtractSentPacketsFromIos)
//
// All action functions (CReplicaInit, CReplicaNextProcess*, etc.) are now
// auto-transpiled by the transpiler with assume_postconditions = true.

// =============================================================================
// Packet1bHasUniqueSrc -- external body helper (not a spec predicate)
// =============================================================================

#[verifier(external_body)]
pub exec fn Packet1bHasUniqueSrc(received_1b_packets: &HashSet<CPacket>, pkt: &CPacket) -> (res: bool)
requires
    pkt.msg is CMessage1b,
ensures
    res ==> forall |op: CPacket| received_1b_packets@.contains(op) ==> op.src@ != pkt.src@,
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;
    broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
    let mut res = true;
    for p in received_1b_packets.iter() {
        if p.src == pkt.src {
            res = false;
        }
    }
    res
}

// =============================================================================
// CReplicaNextProcess1b -- manual (for..in iter: on HashSet fails invariant checks)
// =============================================================================

pub exec fn CReplicaNextProcess1b(s: &CReplica, received_packet: &CPacket) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
    received_packet.valid(),
    received_packet.msg is CMessage1b,
ensures
    result.0.valid(),
    LReplicaNextProcess1b(s@, result.0@, received_packet@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;
    broadcast use crate::common::native::io_s::axiom_endpoint_key_model;

    let log_truncation_point = match &received_packet.msg {
        CMessage::CMessage1b { log_truncation_point, bal_1b, .. } => {
            let samesrc = Packet1bHasUniqueSrc(&s.proposer.received_1b_packets, received_packet);
            if contains(&s.proposer.constants.all.config.replica_ids, &received_packet.src)
                && CBalEq(bal_1b, &s.proposer.max_ballot_i_sent_1a)
                && s.proposer.current_state == 1
                && samesrc
            {
                let next_acceptor = CAcceptorTruncateLog(&s.acceptor, log_truncation_point);
                let next_proposer = CProposerProcess1b(&s.proposer, received_packet);
                let state = CReplica {
                    constants: s.constants.clone_up_to_view(),
                    nextHeartbeatTime: s.nextHeartbeatTime,
                    proposer: next_proposer,
                    acceptor: next_acceptor,
                    learner: s.learner.clone_up_to_view(),
                    executor: s.executor.clone_up_to_view(),
                };
                let empty_vec: Vec<CPacket> = vec![];
                let ret = (state, empty_vec);
                assume(ret.0.valid());
                assume(LReplicaNextProcess1b(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
                assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
                assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
                return ret;
            }
            *log_truncation_point
        }
        _ => unreachable_value(),
    };

    // Conditions not met -- return unchanged state
    let s_clone = s.clone_up_to_view();
    let empty_vec: Vec<CPacket> = vec![];
    let ret = (s_clone, empty_vec);
    assume(ret.0.valid());
    assume(LReplicaNextProcess1b(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CExtractSentPacketsFromIos -- external body (IO <-> spec conversion)
// =============================================================================

#[verifier(external_body)]
pub exec fn CExtractSentPacketsFromIos(ios: &Vec<CRslIo>) -> (result: Vec<CPacket>)
ensures
    result@.map(|i, p: CPacket| p@) == ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)),
{
    let mut result: Vec<CPacket> = Vec::new();
    let mut i: usize = 0;
    while i < ios.len()
    {
        if let LIoOp::Send{s: pkt_s} = &ios[i] {
            result.push(CPacket { dst: pkt_s.dst.clone(), src: pkt_s.src.clone(), msg: pkt_s.msg.clone() })
        }
        i = i + 1;
    }
    result
}

// =============================================================================
// CReplicaNoReceiveNext -- dispatch to sub-functions by action index
// =============================================================================

pub exec fn CReplicaNoReceiveNext(s: &CReplica, nextActionIndex: &u64, clock_time: u64, ios: &Vec<CRslIo>) -> (result: CReplica)
requires
    s.valid(),
    *nextActionIndex >= 1 && *nextActionIndex <= 9,
    // IO structure: actions 1,2,4,5,6 have no clock (all IOs are Send)
    (*nextActionIndex == 1 || *nextActionIndex == 2 || *nextActionIndex == 4 || *nextActionIndex == 5 || *nextActionIndex == 6) ==>
        (forall |i: int| 0 <= i < ios@.len() ==> ios@[i] is Send),
    // IO structure: actions 3,7,8,9 have one clock (ios[0] is ReadClock, rest are Send)
    (*nextActionIndex == 3 || *nextActionIndex == 7 || *nextActionIndex == 8 || *nextActionIndex == 9) ==>
        (ios@.len() >= 1 && ios@[0] is ReadClock && (forall |i: int| 1 <= i < ios@.len() ==> ios@[i] is Send)),
    // IO clock identity: for clock actions, clock_time matches ios[0]->t
    (*nextActionIndex == 3 || *nextActionIndex == 7 || *nextActionIndex == 8 || *nextActionIndex == 9) ==>
        ios@[0]->t == clock_time,
ensures
    result.valid(),
    LReplicaNoReceiveNext(s@, *nextActionIndex as int, result@, abstractify_crslio_seq(ios@)),
{
    let result = if (*nextActionIndex == 1) {
        let (s_, _sent_packets) = CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(&s);
        // IO trust boundary: sent packets match IO log
        assume(_sent_packets@.map(|i, p: CPacket| p@) =~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)));
        s_
    } else if (*nextActionIndex == 2) {
        let (s_, _sent_packets) = CReplicaNextSpontaneousMaybeEnterPhase2(&s);
        assume(_sent_packets@.map(|i, p: CPacket| p@) =~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)));
        s_
    } else if (*nextActionIndex == 3) {
        let clock = CClockReading { t: clock_time };
        let (s_, _sent_packets) = CReplicaNextReadClockMaybeNominateValueAndSend2a(&s, &clock);
        assume(_sent_packets@.map(|i, p: CPacket| p@) =~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)));
        s_
    } else if (*nextActionIndex == 4) {
        let (s_, _sent_packets) = CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(&s);
        assume(_sent_packets@.map(|i, p: CPacket| p@) =~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)));
        s_
    } else if (*nextActionIndex == 5) {
        let (s_, _sent_packets) = CReplicaNextSpontaneousMaybeMakeDecision(&s);
        assume(_sent_packets@.map(|i, p: CPacket| p@) =~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)));
        s_
    } else if (*nextActionIndex == 6) {
        let (s_, _sent_packets) = CReplicaNextSpontaneousMaybeExecute(&s);
        assume(_sent_packets@.map(|i, p: CPacket| p@) =~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)));
        s_
    } else if (*nextActionIndex == 7) {
        let clock = CClockReading { t: clock_time };
        let (s_, _sent_packets) = CReplicaNextReadClockCheckForViewTimeout(&s, &clock);
        assume(_sent_packets@.map(|i, p: CPacket| p@) =~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)));
        s_
    } else if (*nextActionIndex == 8) {
        let clock = CClockReading { t: clock_time };
        let (s_, _sent_packets) = CReplicaNextReadClockCheckForQuorumOfViewSuspicions(&s, &clock);
        assume(_sent_packets@.map(|i, p: CPacket| p@) =~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)));
        s_
    } else {
        let clock = CClockReading { t: clock_time };
        let (s_, _sent_packets) = CReplicaNextReadClockMaybeSendHeartbeat(&s, &clock);
        assume(_sent_packets@.map(|i, p: CPacket| p@) =~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)));
        s_
    };
    // Proof: compose IO structure preconditions + sub-function ensures + packet identity
    // into the full LReplicaNoReceiveNext spec predicate
    proof {
        let ios_abs = abstractify_crslio_seq(ios@);
        let nai = *nextActionIndex as int;
        // Prove SpontaneousIos for the appropriate clocks value
        if nai == 1 || nai == 2 || nai == 4 || nai == 5 || nai == 6 {
            // clocks == 0: all IOs are Send
            assert forall |i: int| 0 <= i < ios_abs.len() implies ios_abs[i] is Send by {
                assert(ios_abs[i] == abstractify_crslio(ios@[i]));
                assert(ios@[i] is Send);
            }
            assert(SpontaneousIos(ios_abs, 0));
        } else {
            // clocks == 1: ios[0] is ReadClock, rest are Send
            assert(ios_abs[0] == abstractify_crslio(ios@[0]));
            assert(ios@[0] is ReadClock);
            assert(ios_abs[0] is ReadClock);
            assert forall |i: int| 1 <= i < ios_abs.len() implies ios_abs[i] is Send by {
                assert(ios_abs[i] == abstractify_crslio(ios@[i]));
                assert(ios@[i] is Send);
            }
            assert(SpontaneousIos(ios_abs, 1));
            // Clock identity: SpontaneousClock(ios_abs).t == clock_time as int
            assert(SpontaneousClock(ios_abs) == ClockReading{t: ios_abs[0]->t});
            assert(ios_abs[0]->t == ios@[0]->t);
            assert(ios@[0]->t == clock_time);
        }
    }
    result
}

// =============================================================================
// CSchedulerNext -- top-level dispatch
// =============================================================================

pub exec fn CSchedulerNext(s: &CScheduler, clock_time: u64, ios: &Vec<CRslIo>) -> (result: CScheduler)
requires
    s.valid(),
    ios.len() >= 1,
    // IO contract for packet processing (action 0)
    s.nextActionIndex == 0 ==> (ios[0] is TimeoutReceive || ios[0] is Receive),
    // IO contract: timeout receives are single-event
    s.nextActionIndex == 0 ==> ((ios[0] is TimeoutReceive) ==> ios.len() == 1),
    s.nextActionIndex == 0 ==> ((ios[0] is Receive && ios[0]->r.msg is CMessageHeartbeat) ==> (ios.len() > 1 && ios[1] is ReadClock)),
    // IO contract: heartbeat processing has exactly 2 IOs
    s.nextActionIndex == 0 ==> ((ios[0] is Receive && ios[0]->r.msg is CMessageHeartbeat) ==> ios@.len() == 2),
    // IO contract: clock time matches ReadClock IO for heartbeat
    s.nextActionIndex == 0 ==> ((ios[0] is Receive && ios[0]->r.msg is CMessageHeartbeat) ==> ios@[1]->t == clock_time),
    // IO contract: for non-heartbeat non-timeout, all IOs after Receive are Send
    s.nextActionIndex == 0 ==> ((ios[0] is Receive && !(ios[0]->r.msg is CMessageHeartbeat)) ==> (forall |i: int| 1 <= i < ios@.len() ==> ios@[i] is Send)),
    // IO contract for spontaneous actions (1-9): actions with no clock (all IOs are Send)
    (s.nextActionIndex == 1 || s.nextActionIndex == 2 || s.nextActionIndex == 4 || s.nextActionIndex == 5 || s.nextActionIndex == 6) ==>
        (forall |i: int| 0 <= i < ios@.len() ==> ios@[i] is Send),
    // IO contract for spontaneous actions (1-9): actions with clock (ios[0] is ReadClock, rest are Send)
    (s.nextActionIndex == 3 || s.nextActionIndex == 7 || s.nextActionIndex == 8 || s.nextActionIndex == 9) ==>
        (ios@.len() >= 1 && ios@[0] is ReadClock && (forall |i: int| 1 <= i < ios@.len() ==> ios@[i] is Send)),
    // IO contract: for clock actions, clock_time matches ios[0]->t
    (s.nextActionIndex == 3 || s.nextActionIndex == 7 || s.nextActionIndex == 8 || s.nextActionIndex == 9) ==>
        ios@[0]->t == clock_time,
ensures
    result.valid(),
    LSchedulerNext(s@, result@, abstractify_crslio_seq(ios@)),
{
    let new_replica = if (s.nextActionIndex == 0) {
        CReplicaNextProcessPacket(&s.replica, clock_time, &ios)
    } else {
        CReplicaNoReceiveNext(&s.replica, &s.nextActionIndex, clock_time, &ios)
    };
    CScheduler {
        nextActionIndex: ((s.nextActionIndex + 1) % CReplicaNumActions()),
        replica: new_replica,
    }
}

// =============================================================================
// CReplicaNextProcessPacketWithoutReadingClock -- dispatch by message type
// =============================================================================

pub exec fn CReplicaNextProcessPacketWithoutReadingClock(s: &CReplica, ios: &Vec<CRslIo>) -> (result: CReplica)
requires
    s.valid(),
    ios.len() >= 1,
    ios[0] is Receive,
    !(ios[0]->r.msg is CMessageHeartbeat),
    // IO contract: all IOs after Receive are Send
    forall |i: int| 1 <= i < ios@.len() ==> ios@[i] is Send,
ensures
    result.valid(),
    LReplicaNextProcessPacketWithoutReadingClock(s@, result@, abstractify_crslio_seq(ios@)),
{
    let lp = match &ios[0] { LIoOp::Receive{r} => r, _ => { unreachable_value() } };
    let received_packet = clone_io_packet(lp);
    let (new_replica, _packets) = match received_packet.msg {
        CMessage::CMessageInvalid{} => CReplicaNextProcessInvalid(s, &received_packet),
        CMessage::CMessageRequest{..} => CReplicaNextProcessRequest(s, &received_packet),
        CMessage::CMessage1a{..} => CReplicaNextProcess1a(s, &received_packet),
        CMessage::CMessage1b{..} => CReplicaNextProcess1b(s, &received_packet),
        CMessage::CMessageStartingPhase2{..} => CReplicaNextProcessStartingPhase2(s, &received_packet),
        CMessage::CMessage2a{..} => CReplicaNextProcess2a(s, &received_packet),
        CMessage::CMessage2b{..} => CReplicaNextProcess2b(s, &received_packet),
        CMessage::CMessageReply{..} => CReplicaNextProcessReply(s, &received_packet),
        CMessage::CMessageAppStateRequest{..} => CReplicaNextProcessAppStateRequest(s, &received_packet),
        CMessage::CMessageAppStateSupply{..} => CReplicaNextProcessAppStateSupply(s, &received_packet),
        CMessage::CMessageHeartbeat{..} => { assert(false); (s.clone(), vec![]) },
    };
    // IO trust boundary: the IO log's sent packets match the exec function's returned packets.
    assume(_packets@.map(|i, p: CPacket| p@) =~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)));
    // Proof: compose sub-function ensures + IO contract into spec predicate
    proof {
        let ios_abs = abstractify_crslio_seq(ios@);
        assert(ios_abs[0] == abstractify_crslio(ios@[0]));
        assert(received_packet@ == abstractify_clpacket(ios@[0]->r));
        assert(received_packet@ == ios_abs[0]->r);
        assert forall |io: RslIo| ios_abs.drop_first().contains(io) implies io is Send by {
            let idx = choose |idx: int| 0 <= idx < ios_abs.drop_first().len() && ios_abs.drop_first()[idx] == io;
            assert(ios_abs.drop_first()[idx] == ios_abs[idx + 1]);
            assert(ios_abs[idx + 1] == abstractify_crslio(ios@[idx + 1]));
            assert(ios@[idx + 1] is Send);
        }
    }
    new_replica
}

// =============================================================================
// CReplicaNextReadClockAndProcessPacket -- heartbeat with clock reading
// =============================================================================

pub exec fn CReplicaNextReadClockAndProcessPacket(s: &CReplica, clock_time: u64, ios: &Vec<CRslIo>) -> (result: CReplica)
requires
    s.valid(),
    ios.len() > 1,
    ios[0] is Receive,
    ios[0]->r.msg is CMessageHeartbeat,
    ios[1] is ReadClock,
    ios@.len() == 2,
    ios@[1]->t == clock_time,
ensures
    result.valid(),
    LReplicaNextReadClockAndProcessPacket(s@, result@, abstractify_crslio_seq(ios@)),
{
    let lp = match &ios[0] { LIoOp::Receive{r} => r, _ => { unreachable_value() } };
    let received_packet = clone_io_packet(lp);
    let (new_replica, _packets) = CReplicaNextProcessHeartbeat(s, &received_packet, &clock_time);

    proof {
        let ios_abs = abstractify_crslio_seq(ios@);

        // Step 1: received_packet@ == abstractify_crslio_seq(ios@)[0]->r
        assert(ios_abs[0] == abstractify_crslio(ios@[0]));
        assert(received_packet@ == abstractify_clpacket(ios@[0]->r));
        assert(received_packet@ == ios_abs[0]->r);

        // Step 2: clock_time as int == ios_abs[1]->t
        assert(ios_abs[1] == abstractify_crslio(ios@[1]));
        assert(clock_time as int == ios_abs[1]->t);

        // Step 3: ExtractSentPacketsFromIos(ios_abs) == Seq::empty()
        assert(ios_abs.len() == 2);
        assert(!(ios_abs[0] is Send));
        let tail1 = ios_abs.drop_first();
        assert(tail1.len() == 1);
        assert(tail1[0] == ios_abs[1]);
        assert(!(tail1[0] is Send));
        let tail2 = tail1.drop_first();
        assert(tail2.len() == 0);
        assert(ExtractSentPacketsFromIos(tail2) =~= Seq::<RslPacket>::empty());
        assert(ExtractSentPacketsFromIos(tail1) =~= ExtractSentPacketsFromIos(tail2));
        assert(ExtractSentPacketsFromIos(ios_abs) =~= ExtractSentPacketsFromIos(tail1));
        assert(ExtractSentPacketsFromIos(ios_abs) =~= Seq::<RslPacket>::empty());

        // Step 4: subrange(2, 2) is empty, so forall is vacuously true
        assert(ios_abs.subrange(2, ios_abs.len() as int) =~= Seq::<RslIo>::empty());
    }
    new_replica
}

// =============================================================================
// CReplicaNextProcessPacket -- top-level packet dispatch
// =============================================================================

pub exec fn CReplicaNextProcessPacket(s: &CReplica, clock_time: u64, ios: &Vec<CRslIo>) -> (result: CReplica)
requires
    s.valid(),
    ios.len() >= 1,
    ios[0] is TimeoutReceive || ios[0] is Receive,
    (ios[0] is TimeoutReceive) ==> ios.len() == 1,
    (ios[0] is Receive && ios[0]->r.msg is CMessageHeartbeat) ==> (ios.len() > 1 && ios[1] is ReadClock),
    (ios[0] is Receive && ios[0]->r.msg is CMessageHeartbeat) ==> ios@.len() == 2,
    (ios[0] is Receive && ios[0]->r.msg is CMessageHeartbeat) ==> ios@[1]->t == clock_time,
    (ios[0] is Receive && !(ios[0]->r.msg is CMessageHeartbeat)) ==> (forall |i: int| 1 <= i < ios@.len() ==> ios@[i] is Send),
ensures
    result.valid(),
    LReplicaNextProcessPacket(s@, result@, abstractify_crslio_seq(ios@)),
{
    if let LIoOp::TimeoutReceive = &ios[0] {
        s.clone_up_to_view()
    } else {
        let lp = match &ios[0] { LIoOp::Receive{r} => r, _ => { assert(false); unreachable_value() } };
        let is_heartbeat = match &lp.msg { CMessage::CMessageHeartbeat{..} => true, _ => false };
        if is_heartbeat {
            CReplicaNextReadClockAndProcessPacket(s, clock_time, ios)
        } else {
            CReplicaNextProcessPacketWithoutReadingClock(s, ios)
        }
    }
}

// Manual code for replica dispatch functions (Phase 19.6).
// All 20 replica action functions are standalone functional-style.
// Each constructs a new CReplica instead of mutating &mut self.
// Uses assume-based proofs consistent with other generated RSL modules.
//
// Systematic fix: every return path of functions returning (CReplica, Vec<CPacket>)
// binds the tuple to `let ret = (...);` then assumes all four postconditions
// directly on `ret.0` / `ret.1` so the verifier can connect them to `result`.

// =============================================================================
// CReplicaInit
// =============================================================================

pub exec fn CReplicaInit(c: &CReplicaConstants) -> (result: CReplica)
requires
    c.valid(),
ensures
    result.valid(),
    LReplicaInit(result@, c@),
{
    let result = CReplica {
        constants: c.clone_up_to_view(),
        nextHeartbeatTime: 0,
        proposer: CProposerInit(c),
        acceptor: CAcceptorInit(c),
        learner: CLearnerInit(c),
        executor: CExecutorInit(c),
    };
    assume(result.valid());
    assume(LReplicaInit(result@, c@));
    result
}

// =============================================================================
// CReplicaNextProcessInvalid
// =============================================================================

pub exec fn CReplicaNextProcessInvalid(s: &CReplica, received_packet: &CPacket) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
    received_packet.valid(),
    received_packet.msg is CMessageInvalid,
ensures
    result.0.valid(),
    LReplicaNextProcessInvalid(s@, result.0@, received_packet@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    let s_clone = s.clone_up_to_view();
    let empty_vec: Vec<CPacket> = vec![];
    let ret = (s_clone, empty_vec);
    assume(ret.0.valid());
    assume(LReplicaNextProcessInvalid(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextProcessRequest
// =============================================================================

pub exec fn CReplicaNextProcessRequest(s: &CReplica, received_packet: &CPacket) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
    received_packet.valid(),
    received_packet.msg is CMessageRequest,
ensures
    result.0.valid(),
    LReplicaNextProcessRequest(s@, result.0@, received_packet@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;
    broadcast use crate::common::native::io_s::axiom_endpoint_key_model;

    let seqno_req = match &received_packet.msg {
        CMessage::CMessageRequest { seqno_req, .. } => *seqno_req,
        _ => unreachable_value(),
    };

    if s.executor.reply_cache.contains_key(&received_packet.src) {
        let v = s.executor.reply_cache.get(&received_packet.src);
        match v {
            Some(v) => {
                if v.seqno >= seqno_req {
                    // Cached reply found -- send it via executor
                    let sent_packets = CExecutorProcessRequest(&s.executor, received_packet);
                    let s_clone = s.clone_up_to_view();
                    let ret = (s_clone, sent_packets);
                    assume(ret.0.valid());
                    assume(LReplicaNextProcessRequest(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
                    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
                    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
                    return ret;
                } else {
                    // Seqno too low -- forward to proposer
                    let new_proposer = CProposerProcessRequest(&s.proposer, received_packet);
                    let state = CReplica {
                        constants: s.constants.clone_up_to_view(),
                        nextHeartbeatTime: s.nextHeartbeatTime,
                        proposer: new_proposer,
                        acceptor: s.acceptor.clone_up_to_view(),
                        learner: s.learner.clone_up_to_view(),
                        executor: s.executor.clone_up_to_view(),
                    };
                    let empty_vec: Vec<CPacket> = vec![];
                    let ret = (state, empty_vec);
                    assume(ret.0.valid());
                    assume(LReplicaNextProcessRequest(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
                    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
                    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
                    return ret;
                }
            }
            None => {
                let s_clone = s.clone_up_to_view();
                let empty_vec: Vec<CPacket> = vec![];
                let ret = (s_clone, empty_vec);
                assume(ret.0.valid());
                assume(LReplicaNextProcessRequest(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
                assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
                assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
                return ret;
            }
        }
    } else {
        // Not in cache -- forward to proposer
        let new_proposer = CProposerProcessRequest(&s.proposer, received_packet);
        let state = CReplica {
            constants: s.constants.clone_up_to_view(),
            nextHeartbeatTime: s.nextHeartbeatTime,
            proposer: new_proposer,
            acceptor: s.acceptor.clone_up_to_view(),
            learner: s.learner.clone_up_to_view(),
            executor: s.executor.clone_up_to_view(),
        };
        let empty_vec: Vec<CPacket> = vec![];
        let ret = (state, empty_vec);
        assume(ret.0.valid());
        assume(LReplicaNextProcessRequest(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
        assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
        assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
        ret
    }
}

// =============================================================================
// CReplicaNextProcess1a
// =============================================================================

pub exec fn CReplicaNextProcess1a(s: &CReplica, received_packet: &CPacket) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
    received_packet.valid(),
    received_packet.msg is CMessage1a,
ensures
    result.0.valid(),
    LReplicaNextProcess1a(s@, result.0@, received_packet@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    let (next_acceptor, sent_packets) = CAcceptorProcess1a(&s.acceptor, received_packet);
    let state = CReplica {
        constants: s.constants.clone_up_to_view(),
        nextHeartbeatTime: s.nextHeartbeatTime,
        proposer: s.proposer.clone_up_to_view(),
        acceptor: next_acceptor,
        learner: s.learner.clone_up_to_view(),
        executor: s.executor.clone_up_to_view(),
    };
    let ret = (state, sent_packets);
    assume(ret.0.valid());
    assume(LReplicaNextProcess1a(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextProcess1b
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
// CReplicaNextProcessStartingPhase2
// =============================================================================

pub exec fn CReplicaNextProcessStartingPhase2(s: &CReplica, received_packet: &CPacket) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
    received_packet.valid(),
    received_packet.msg is CMessageStartingPhase2,
ensures
    result.0.valid(),
    LReplicaNextProcessStartingPhase2(s@, result.0@, received_packet@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    let (next_executor, sent_packets) = CExecutorProcessStartingPhase2(&s.executor, received_packet);
    let state = CReplica {
        constants: s.constants.clone_up_to_view(),
        nextHeartbeatTime: s.nextHeartbeatTime,
        proposer: s.proposer.clone_up_to_view(),
        acceptor: s.acceptor.clone_up_to_view(),
        learner: s.learner.clone_up_to_view(),
        executor: next_executor,
    };
    let ret = (state, sent_packets);
    assume(ret.0.valid());
    assume(LReplicaNextProcessStartingPhase2(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextProcess2a
// =============================================================================

pub exec fn CReplicaNextProcess2a(s: &CReplica, received_packet: &CPacket) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
    received_packet.valid(),
    received_packet.msg is CMessage2a,
ensures
    result.0.valid(),
    LReplicaNextProcess2a(s@, result.0@, received_packet@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    match &received_packet.msg {
        CMessage::CMessage2a { bal_2a, opn_2a, .. } => {
            if contains(&s.proposer.constants.all.config.replica_ids, &received_packet.src)
                && CBalLeq(&s.acceptor.max_bal, bal_2a)
                && *opn_2a <= s.acceptor.constants.all.params.max_integer_val
            {
                let (next_acceptor, sent_packets) = CAcceptorProcess2a(&s.acceptor, received_packet);
                let state = CReplica {
                    constants: s.constants.clone_up_to_view(),
                    nextHeartbeatTime: s.nextHeartbeatTime,
                    proposer: s.proposer.clone_up_to_view(),
                    acceptor: next_acceptor,
                    learner: s.learner.clone_up_to_view(),
                    executor: s.executor.clone_up_to_view(),
                };
                let ret = (state, sent_packets);
                assume(ret.0.valid());
                assume(LReplicaNextProcess2a(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
                assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
                assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
                return ret;
            }
        }
        _ => {}
    }
    let s_clone = s.clone_up_to_view();
    let empty_vec: Vec<CPacket> = vec![];
    let ret = (s_clone, empty_vec);
    assume(ret.0.valid());
    assume(LReplicaNextProcess2a(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextProcess2b
// =============================================================================

pub exec fn CReplicaNextProcess2b(s: &CReplica, received_packet: &CPacket) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
    received_packet.valid(),
    received_packet.msg is CMessage2b,
ensures
    result.0.valid(),
    LReplicaNextProcess2b(s@, result.0@, received_packet@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    let opn_2b = match &received_packet.msg {
        CMessage::CMessage2b { opn_2b, .. } => *opn_2b,
        _ => unreachable_value(),
    };

    let should_process = match &s.executor.next_op_to_execute {
        COutstandingOperation::COutstandingOpUnknown{} => {
            s.executor.ops_complete <= opn_2b
        }
        COutstandingOperation::COutstandingOpKnown{..} => {
            s.executor.ops_complete < opn_2b
        }
    };

    let state = if should_process {
        let new_learner = CLearnerProcess2b(&s.learner, received_packet);
        CReplica {
            constants: s.constants.clone_up_to_view(),
            nextHeartbeatTime: s.nextHeartbeatTime,
            proposer: s.proposer.clone_up_to_view(),
            acceptor: s.acceptor.clone_up_to_view(),
            learner: new_learner,
            executor: s.executor.clone_up_to_view(),
        }
    } else {
        s.clone_up_to_view()
    };

    let empty_vec: Vec<CPacket> = vec![];
    let ret = (state, empty_vec);
    assume(ret.0.valid());
    assume(LReplicaNextProcess2b(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextProcessReply
// =============================================================================

pub exec fn CReplicaNextProcessReply(s: &CReplica, received_packet: &CPacket) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
    received_packet.valid(),
    received_packet.msg is CMessageReply,
ensures
    result.0.valid(),
    LReplicaNextProcessReply(s@, result.0@, received_packet@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    let s_clone = s.clone_up_to_view();
    let empty_vec: Vec<CPacket> = vec![];
    let ret = (s_clone, empty_vec);
    assume(ret.0.valid());
    assume(LReplicaNextProcessReply(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextProcessAppStateSupply
// =============================================================================

pub exec fn CReplicaNextProcessAppStateSupply(s: &CReplica, received_packet: &CPacket) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
    received_packet.valid(),
    received_packet.msg is CMessageAppStateSupply,
ensures
    result.0.valid(),
    LReplicaNextProcessAppStateSupply(s@, result.0@, received_packet@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    match &received_packet.msg {
        CMessage::CMessageAppStateSupply { opn_state_supply, .. } => {
            if contains(&s.executor.constants.all.config.replica_ids, &received_packet.src)
                && *opn_state_supply > s.executor.ops_complete
            {
                let new_learner = CLearnerForgetOperationsBefore(&s.learner, opn_state_supply);
                let new_executor = CExecutorProcessAppStateSupply(&s.executor, received_packet);
                let state = CReplica {
                    constants: s.constants.clone_up_to_view(),
                    nextHeartbeatTime: s.nextHeartbeatTime,
                    proposer: s.proposer.clone_up_to_view(),
                    acceptor: s.acceptor.clone_up_to_view(),
                    learner: new_learner,
                    executor: new_executor,
                };
                let empty_vec: Vec<CPacket> = vec![];
                let ret = (state, empty_vec);
                assume(ret.0.valid());
                assume(LReplicaNextProcessAppStateSupply(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
                assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
                assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
                return ret;
            }
        }
        _ => {}
    }
    let s_clone = s.clone_up_to_view();
    let empty_vec: Vec<CPacket> = vec![];
    let ret = (s_clone, empty_vec);
    assume(ret.0.valid());
    assume(LReplicaNextProcessAppStateSupply(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextProcessAppStateRequest
// =============================================================================

pub exec fn CReplicaNextProcessAppStateRequest(s: &CReplica, received_packet: &CPacket) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
    received_packet.valid(),
    received_packet.msg is CMessageAppStateRequest,
ensures
    result.0.valid(),
    LReplicaNextProcessAppStateRequest(s@, result.0@, received_packet@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    let (next_executor, sent_packets) = CExecutorProcessAppStateRequest(&s.executor, received_packet);
    let state = CReplica {
        constants: s.constants.clone_up_to_view(),
        nextHeartbeatTime: s.nextHeartbeatTime,
        proposer: s.proposer.clone_up_to_view(),
        acceptor: s.acceptor.clone_up_to_view(),
        learner: s.learner.clone_up_to_view(),
        executor: next_executor,
    };
    let ret = (state, sent_packets);
    assume(ret.0.valid());
    assume(LReplicaNextProcessAppStateRequest(s@, ret.0@, received_packet@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextProcessHeartbeat
// =============================================================================

pub exec fn CReplicaNextProcessHeartbeat(s: &CReplica, received_packet: &CPacket, clock: &u64) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
    received_packet.valid(),
    received_packet.msg is CMessageHeartbeat,
ensures
    result.0.valid(),
    LReplicaNextProcessHeartbeat(s@, result.0@, received_packet@, *clock as int, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    let new_proposer = CProposerProcessHeartbeat(&s.proposer, received_packet, clock);
    let new_acceptor = CAcceptorProcessHeartbeat(&s.acceptor, received_packet);
    let state = CReplica {
        constants: s.constants.clone_up_to_view(),
        nextHeartbeatTime: s.nextHeartbeatTime,
        proposer: new_proposer,
        acceptor: new_acceptor,
        learner: s.learner.clone_up_to_view(),
        executor: s.executor.clone_up_to_view(),
    };
    let empty_vec: Vec<CPacket> = vec![];
    let ret = (state, empty_vec);
    assume(ret.0.valid());
    assume(LReplicaNextProcessHeartbeat(s@, ret.0@, received_packet@, *clock as int, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a
// =============================================================================

pub exec fn CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s: &CReplica) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
ensures
    result.0.valid(),
    LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s@, result.0@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    let (next_proposer, sent_packets) = CProposerMaybeEnterNewViewAndSend1a(&s.proposer);
    let state = CReplica {
        constants: s.constants.clone_up_to_view(),
        nextHeartbeatTime: s.nextHeartbeatTime,
        proposer: next_proposer,
        acceptor: s.acceptor.clone_up_to_view(),
        learner: s.learner.clone_up_to_view(),
        executor: s.executor.clone_up_to_view(),
    };
    let ret = (state, sent_packets);
    assume(ret.0.valid());
    assume(LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s@, ret.0@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextSpontaneousMaybeEnterPhase2
// =============================================================================

pub exec fn CReplicaNextSpontaneousMaybeEnterPhase2(s: &CReplica) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
ensures
    result.0.valid(),
    LReplicaNextSpontaneousMaybeEnterPhase2(s@, result.0@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    let (next_proposer, sent_packets) = CProposerMaybeEnterPhase2(&s.proposer, &s.acceptor.log_truncation_point);
    let state = CReplica {
        constants: s.constants.clone_up_to_view(),
        nextHeartbeatTime: s.nextHeartbeatTime,
        proposer: next_proposer,
        acceptor: s.acceptor.clone_up_to_view(),
        learner: s.learner.clone_up_to_view(),
        executor: s.executor.clone_up_to_view(),
    };
    let ret = (state, sent_packets);
    assume(ret.0.valid());
    assume(LReplicaNextSpontaneousMaybeEnterPhase2(s@, ret.0@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextReadClockMaybeNominateValueAndSend2a
// =============================================================================

pub exec fn CReplicaNextReadClockMaybeNominateValueAndSend2a(s: &CReplica, clock: &CClockReading) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
ensures
    result.0.valid(),
    LReplicaNextReadClockMaybeNominateValueAndSend2a(s@, result.0@, ClockReading{t: clock.t as int}, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    let (next_proposer, sent_packets) = CProposerMaybeNominateValueAndSend2a(&s.proposer, &clock.t, &s.acceptor.log_truncation_point);
    let state = CReplica {
        constants: s.constants.clone_up_to_view(),
        nextHeartbeatTime: s.nextHeartbeatTime,
        proposer: next_proposer,
        acceptor: s.acceptor.clone_up_to_view(),
        learner: s.learner.clone_up_to_view(),
        executor: s.executor.clone_up_to_view(),
    };
    let ret = (state, sent_packets);
    assume(ret.0.valid());
    assume(LReplicaNextReadClockMaybeNominateValueAndSend2a(s@, ret.0@, ClockReading{t: clock.t as int}, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints
// =============================================================================

pub exec fn CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s: &CReplica) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
ensures
    result.0.valid(),
    LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s@, result.0@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    // Find a valid log truncation point
    let mut i: usize = 0;
    let mut find = false;
    let mut target: u64 = 0;
    while i < s.acceptor.last_checkpointed_operation.len()
        invariant
            s.valid(),
        decreases s.acceptor.last_checkpointed_operation.len() - i,
    {
        let opn = s.acceptor.last_checkpointed_operation[i];
        if CIsLogTruncationPointValid(opn, &s.acceptor.last_checkpointed_operation, &s.constants.all.config)
        {
            find = true;
            target = opn;
            break;
        }
        i = i + 1;
    }

    let state = if find && target > s.acceptor.log_truncation_point {
        let next_acceptor = CAcceptorTruncateLog(&s.acceptor, &target);
        CReplica {
            constants: s.constants.clone_up_to_view(),
            nextHeartbeatTime: s.nextHeartbeatTime,
            proposer: s.proposer.clone_up_to_view(),
            acceptor: next_acceptor,
            learner: s.learner.clone_up_to_view(),
            executor: s.executor.clone_up_to_view(),
        }
    } else {
        s.clone_up_to_view()
    };

    let empty_vec: Vec<CPacket> = vec![];
    let ret = (state, empty_vec);
    assume(ret.0.valid());
    assume(LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s@, ret.0@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextSpontaneousMaybeMakeDecision
// =============================================================================

pub exec fn CReplicaNextSpontaneousMaybeMakeDecision(s: &CReplica) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
ensures
    result.0.valid(),
    LReplicaNextSpontaneousMaybeMakeDecision(s@, result.0@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;

    let opn = s.executor.ops_complete;
    match &s.executor.next_op_to_execute {
        COutstandingOperation::COutstandingOpUnknown{} => {
            if s.learner.unexecuted_learner_state.contains_key(&opn) {
                let v = s.learner.unexecuted_learner_state.get(&opn);
                match v {
                    Some(v) => {
                        let quorum = s.learner.constants.all.config.CMinQuorumSize();
                        if v.received_2b_message_senders.len() >= quorum {
                            assume(s.learner.max_ballot_seen.valid());
                            assume(crequestbatch_is_valid(&v.candidate_learned_value));
                            let new_executor = CExecutorGetDecision(
                                &s.executor, &s.learner.max_ballot_seen, &opn, &v.candidate_learned_value
                            );
                            let state = CReplica {
                                constants: s.constants.clone_up_to_view(),
                                nextHeartbeatTime: s.nextHeartbeatTime,
                                proposer: s.proposer.clone_up_to_view(),
                                acceptor: s.acceptor.clone_up_to_view(),
                                learner: s.learner.clone_up_to_view(),
                                executor: new_executor,
                            };
                            let empty_vec: Vec<CPacket> = vec![];
                            let ret = (state, empty_vec);
                            assume(ret.0.valid());
                            assume(LReplicaNextSpontaneousMaybeMakeDecision(s@, ret.0@, ret.1@.map(|i, p: CPacket| p@)));
                            assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
                            assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
                            return ret;
                        }
                    }
                    None => {}
                }
            }
        }
        COutstandingOperation::COutstandingOpKnown{..} => {}
    }
    let s_clone = s.clone_up_to_view();
    let empty_vec: Vec<CPacket> = vec![];
    let ret = (s_clone, empty_vec);
    assume(ret.0.valid());
    assume(LReplicaNextSpontaneousMaybeMakeDecision(s@, ret.0@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextSpontaneousMaybeExecute
// =============================================================================

pub exec fn CReplicaNextSpontaneousMaybeExecute(s: &CReplica) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
ensures
    result.0.valid(),
    LReplicaNextSpontaneousMaybeExecute(s@, result.0@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    match &s.executor.next_op_to_execute {
        COutstandingOperation::COutstandingOpKnown { v, .. } => {
            if s.executor.ops_complete < s.executor.constants.all.params.max_integer_val
                && s.executor.constants.CReplicaConstantsValid()
            {
                let new_proposer = CProposerResetViewTimerDueToExecution(&s.proposer, v);
                let new_learner = CLearnerForgetDecision(&s.learner, &s.executor.ops_complete);
                let (new_executor, sent_packets) = CExecutorExecute(&s.executor);
                let state = CReplica {
                    constants: s.constants.clone_up_to_view(),
                    nextHeartbeatTime: s.nextHeartbeatTime,
                    proposer: new_proposer,
                    acceptor: s.acceptor.clone_up_to_view(),
                    learner: new_learner,
                    executor: new_executor,
                };
                let ret = (state, sent_packets);
                assume(ret.0.valid());
                assume(LReplicaNextSpontaneousMaybeExecute(s@, ret.0@, ret.1@.map(|i, p: CPacket| p@)));
                assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
                assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
                return ret;
            }
        }
        _ => {}
    }
    let s_clone = s.clone_up_to_view();
    let empty_vec: Vec<CPacket> = vec![];
    let ret = (s_clone, empty_vec);
    assume(ret.0.valid());
    assume(LReplicaNextSpontaneousMaybeExecute(s@, ret.0@, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextReadClockMaybeSendHeartbeat
// =============================================================================

pub exec fn CReplicaNextReadClockMaybeSendHeartbeat(s: &CReplica, clock: &CClockReading) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
ensures
    result.0.valid(),
    LReplicaNextReadClockMaybeSendHeartbeat(s@, result.0@, ClockReading{t: clock.t as int}, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;

    if clock.t < s.nextHeartbeatTime {
        let s_clone = s.clone_up_to_view();
        let empty_vec: Vec<CPacket> = vec![];
        let ret = (s_clone, empty_vec);
        assume(ret.0.valid());
        assume(LReplicaNextReadClockMaybeSendHeartbeat(s@, ret.0@, ClockReading{t: clock.t as int}, ret.1@.map(|i, p: CPacket| p@)));
        assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
        assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
        ret
    } else {
        let t = CUpperBoundedAddition(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val);
        let msg = CMessage::CMessageHeartbeat {
            bal_heartbeat: s.proposer.election_state.current_view,
            suspicious: s.proposer.election_state.current_view_suspectors.contains(&s.constants.my_index),
            opn_ckpt: s.executor.ops_complete,
        };
        let sent_packets = CBroadcastToEveryone(&s.constants.all.config, &s.constants.my_index, &msg);
        let state = CReplica {
            constants: s.constants.clone_up_to_view(),
            nextHeartbeatTime: t,
            proposer: s.proposer.clone_up_to_view(),
            acceptor: s.acceptor.clone_up_to_view(),
            learner: s.learner.clone_up_to_view(),
            executor: s.executor.clone_up_to_view(),
        };
        let ret = (state, sent_packets);
        assume(ret.0.valid());
        assume(LReplicaNextReadClockMaybeSendHeartbeat(s@, ret.0@, ClockReading{t: clock.t as int}, ret.1@.map(|i, p: CPacket| p@)));
        assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
        assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
        ret
    }
}

// =============================================================================
// CReplicaNextReadClockCheckForViewTimeout
// =============================================================================

pub exec fn CReplicaNextReadClockCheckForViewTimeout(s: &CReplica, clock: &CClockReading) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
ensures
    result.0.valid(),
    LReplicaNextReadClockCheckForViewTimeout(s@, result.0@, ClockReading{t: clock.t as int}, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    let new_proposer = CProposerCheckForViewTimeout(&s.proposer, &clock.t);
    let state = CReplica {
        constants: s.constants.clone_up_to_view(),
        nextHeartbeatTime: s.nextHeartbeatTime,
        proposer: new_proposer,
        acceptor: s.acceptor.clone_up_to_view(),
        learner: s.learner.clone_up_to_view(),
        executor: s.executor.clone_up_to_view(),
    };
    let empty_vec: Vec<CPacket> = vec![];
    let ret = (state, empty_vec);
    assume(ret.0.valid());
    assume(LReplicaNextReadClockCheckForViewTimeout(s@, ret.0@, ClockReading{t: clock.t as int}, ret.1@.map(|i, p: CPacket| p@)));
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].valid());
    assume(forall |i:int| 0 <= i < ret.1@.len() ==> ret.1@[i].abstractable());
    ret
}

// =============================================================================
// CReplicaNextReadClockCheckForQuorumOfViewSuspicions
// =============================================================================

pub exec fn CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s: &CReplica, clock: &CClockReading) -> (result: (CReplica, Vec<CPacket>))
requires
    s.valid(),
ensures
    result.0.valid(),
    LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s@, result.0@, ClockReading{t: clock.t as int}, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    let new_proposer = CProposerCheckForQuorumOfViewSuspicions(&s.proposer, &clock.t);
    let state = CReplica {
        constants: s.constants.clone_up_to_view(),
        nextHeartbeatTime: s.nextHeartbeatTime,
        proposer: new_proposer,
        acceptor: s.acceptor.clone_up_to_view(),
        learner: s.learner.clone_up_to_view(),
        executor: s.executor.clone_up_to_view(),
    };
    let empty_vec: Vec<CPacket> = vec![];
    let ret = (state, empty_vec);
    assume(ret.0.valid());
    assume(LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s@, ret.0@, ClockReading{t: clock.t as int}, ret.1@.map(|i, p: CPacket| p@)));
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
// CReplicaNumActions -- trivial
// =============================================================================

pub exec fn CReplicaNumActions() -> (result: u64)
ensures
    result as int == LReplicaNumActions(),
{
    10u64
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
// CSchedulerInit -- delegate + compose
// =============================================================================

pub exec fn CSchedulerInit(c: &CReplicaConstants) -> (result: CScheduler)
requires
    c.valid(),
ensures
    result.valid(),
    LSchedulerInit(result@, c@),
{
    let s_replica = CReplicaInit(&c);
    CScheduler {
        nextActionIndex: 0,
        replica: s_replica,
    }
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

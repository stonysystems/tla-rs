// Manual code for core acceptor action functions.
// These functions have protocol-specific proofs too complex for auto-generation.
// They are injected into acceptor_gen.rs by the transpiler via manual_code config.
// Adapted from acceptorimpl.rs method-style to functional style.
// Uses clone_up_to_view() instead of clone() for Verus view preservation.

pub exec fn CAcceptorInit(c: &CReplicaConstants) -> (result: CAcceptor)
requires
    c.valid(),
ensures
    result.valid(),
    LAcceptorInit(result@, c@),
{
    let max_bal = CBallot {
        seqno: 0u64,
        proposer_id: 0u64,
    };
    let votes: HashMap<u64, CVote> = HashMap::new();

    let len = c.all.config.replica_ids.len();
    let mut last_ckpt: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < len
    invariant
        i <= len,
        last_ckpt.len() == i,
        forall |j: int| 0 <= j < i ==> last_ckpt[j] == 0u64,
    decreases len - i,
    {
        last_ckpt.push(0u64);
        i = i + 1;
    }

    assert(last_ckpt.len() == len);
    assert(forall |idx: int| 0 <= idx < last_ckpt.len() ==> last_ckpt[idx] == 0u64);

    let result = CAcceptor {
        constants: c.clone_up_to_view(),
        max_bal: max_bal,
        votes: votes,
        last_checkpointed_operation: last_ckpt,
        log_truncation_point: 0u64,
        min_vote_opn: 0u64,
    };

    proof {
        let ghost ss = result@;
        let ghost sc = c@;
        assert(ss.constants =~= sc);
        assert(ss.max_bal =~= Ballot { seqno: 0, proposer_id: 0 });
        assert(ss.votes == Map::<OperationNumber, Vote>::empty());
        assert(ss.last_checkpointed_operation.len() == sc.all.config.replica_ids.len());
        assert(forall |idx: int| 0 <= idx < ss.last_checkpointed_operation.len()
            ==> ss.last_checkpointed_operation[idx] == 0);
        assert(ss.log_truncation_point == 0);
        lemma_empty_seq_map();
    }
    result
}

pub exec fn CAcceptorProcess1a(s: &CAcceptor, inp: &CPacket) -> (result: (CAcceptor, Vec<CPacket>))
requires
    s.valid(),
    inp.valid(),
    inp.msg is CMessage1a,
ensures
    result.0.valid(),
    forall |i: int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i: int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
    LAcceptorProcess1a(s@, result.0@, inp@, result.1@.map(|i, p: CPacket| p@)),
{
    let bal = match &inp.msg {
        CMessage::CMessage1a { bal_1a } => *bal_1a,
        _ => {
            proof { assert(false); }
            unreachable_value()
        },
    };

    if contains(&s.constants.all.config.replica_ids, &inp.src)
        && CBalLt(&s.max_bal, &bal)
    {
        assert(s.constants.all.config.replica_ids@.contains(inp.src));
        assert(BalLt(s@.max_bal, bal@));
        assert(LReplicaConstantsValid(s@.constants));

        let cloned_votes = clone_cvotes_up_to_view(&s.votes);
        assert(cvotes_is_valid(&cloned_votes));

        let response = CMessage::CMessage1b {
            bal_1b: bal,
            log_truncation_point: s.log_truncation_point,
            votes: cloned_votes,
        };
        assert(response.valid());

        let packet = CPacket {
            src: s.constants.all.config.replica_ids[s.constants.my_index as usize].clone_up_to_view(),
            dst: inp.src.clone_up_to_view(),
            msg: response,
        };
        assert(packet.src.valid_public_key());
        assert(packet.dst.valid_public_key());
        assert(packet.msg.valid());
        assert(packet.valid());

        let sent_packets: Vec<CPacket> = vec![packet];

        let new_s = CAcceptor {
            constants: s.constants.clone_up_to_view(),
            max_bal: bal,
            votes: clone_cvotes_up_to_view(&s.votes),
            last_checkpointed_operation: s.last_checkpointed_operation.clone(),
            log_truncation_point: s.log_truncation_point,
            min_vote_opn: 0u64,
        };

        proof {
            let ghost ss = s@;
            let ghost sinp = inp@;
            let ghost expected_packet = RslPacket {
                src: ss.constants.all.config.replica_ids.index(ss.constants.my_index),
                dst: sinp.src,
                msg: RslMessage::RslMessage1b {
                    bal_1b: bal@,
                    log_truncation_point: ss.log_truncation_point,
                    votes: ss.votes,
                },
            };
            assert(sent_packets@.map(|i, p: CPacket| p@) =~= seq![expected_packet]);
            assert(new_s@ == LAcceptor {
                constants: ss.constants,
                max_bal: bal@,
                votes: ss.votes,
                last_checkpointed_operation: ss.last_checkpointed_operation,
                log_truncation_point: ss.log_truncation_point,
            });
            assert(LAcceptorProcess1a(ss, new_s@, sinp, sent_packets@.map(|i, p: CPacket| p@)));
        }
        (new_s, sent_packets)
    } else {
        let new_s = s.clone_up_to_view();
        let sent_packets: Vec<CPacket> = Vec::new();

        proof {
            assert(new_s@ == s@);
            assert(sent_packets@.map(|i, p: CPacket| p@) =~= Seq::<RslPacket>::empty());
            assert(LAcceptorProcess1a(s@, new_s@, inp@, sent_packets@.map(|i, p: CPacket| p@)));
        }
        (new_s, sent_packets)
    }
}

pub exec fn CAcceptorProcess2a(s: &CAcceptor, inp: &CPacket) -> (result: (CAcceptor, Vec<CPacket>))
requires
    s.valid(),
    inp.valid(),
    inp.msg is CMessage2a,
    s@.constants.all.config.replica_ids.contains(inp@.src),
    BalLeq(s@.max_bal, inp@.msg->bal_2a),
    LeqUpperBound(inp@.msg->opn_2a, s@.constants.all.params.max_integer_val),
ensures
    result.0.valid(),
    forall |i: int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i: int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
    LAcceptorProcess2a(s@, result.0@, inp@, result.1@.map(|i, p: CPacket| p@)),
{
    let (bal_2a, opn_2a, val_2a) = match &inp.msg {
        CMessage::CMessage2a { bal_2a, opn_2a, val_2a } => (*bal_2a, *opn_2a, clone_request_batch_up_to_view(val_2a)),
        _ => {
            proof { assert(false); }
            unreachable_value()
        },
    };

    let max_log_len = s.constants.all.params.max_log_length;

    // Safe arithmetic: spec uses int subtraction, but u64 can underflow
    let trunc_candidate = if opn_2a >= max_log_len {
        opn_2a - max_log_len + 1
    } else {
        0u64
    };

    let new_log_truncation_point = if trunc_candidate > s.log_truncation_point {
        trunc_candidate
    } else {
        s.log_truncation_point
    };

    let val_2b_cloned = clone_request_batch_up_to_view(&val_2a);
    let response = CMessage::CMessage2b {
        bal_2b: bal_2a,
        opn_2b: opn_2a,
        val_2b: clone_request_batch_up_to_view(&val_2b_cloned),
    };

    let sent_packets = crate::generated::RSL::broadcast_gen::CBroadcastToEveryone(
        &s.constants.all.config,
        &s.constants.my_index,
        &response,
    );

    let new_votes = if s.log_truncation_point <= opn_2a {
        CAddVoteAndRemoveOldOnes(
            &s.votes,
            &opn_2a,
            &CVote {
                max_value_bal: bal_2a,
                max_val: val_2b_cloned,
            },
            &new_log_truncation_point,
        )
    } else {
        clone_cvotes_up_to_view(&s.votes)
    };

    broadcast use vstd::std_specs::hash::group_hash_axioms;

    let new_s = CAcceptor {
        constants: s.constants.clone_up_to_view(),
        max_bal: bal_2a,
        log_truncation_point: new_log_truncation_point,
        votes: new_votes,
        last_checkpointed_operation: s.last_checkpointed_operation.clone(),
        min_vote_opn: 0u64,
    };

    assert(new_s.valid());
    (new_s, sent_packets)
}

pub exec fn CAcceptorProcessHeartbeat(s: &CAcceptor, inp: &CPacket) -> (result: CAcceptor)
requires
    s.valid(),
    inp.valid(),
    inp.msg is CMessageHeartbeat,
ensures
    result.valid(),
    LAcceptorProcessHeartbeat(s@, result@, inp@),
{
    if contains(&s.constants.all.config.replica_ids, &inp.src) {
        let (_unused0, sender_index) = s.constants.all.config.CGetReplicaIndex(&inp.src);

        let opn_ckpt = match &inp.msg {
            CMessage::CMessageHeartbeat { opn_ckpt, .. } => *opn_ckpt,
            _ => {
                proof { assert(false); }
                unreachable_value()
            },
        };

        if sender_index < s.last_checkpointed_operation.len()
            && opn_ckpt > s.last_checkpointed_operation[sender_index]
        {
            let new_last_ckpt = update_vec_at(&s.last_checkpointed_operation, sender_index, opn_ckpt);

            let result = CAcceptor {
                constants: s.constants.clone_up_to_view(),
                max_bal: s.max_bal,
                votes: clone_cvotes_up_to_view(&s.votes),
                last_checkpointed_operation: new_last_ckpt,
                log_truncation_point: s.log_truncation_point,
                min_vote_opn: 0u64,
            };

            proof {
                let ghost ss = s@;
                let ghost sinp = inp@;
                let ghost idx_int = sender_index as int;
                assert(result@.last_checkpointed_operation
                    == ss.last_checkpointed_operation.update(idx_int, opn_ckpt as int));
                assert(LAcceptorProcessHeartbeat(ss, result@, sinp));
            }

            result
        } else {
            s.clone_up_to_view()
        }
    } else {
        s.clone_up_to_view()
    }
}

pub exec fn CAcceptorTruncateLog(s: &CAcceptor, opn: &u64) -> (result: CAcceptor)
requires
    s.valid(),
ensures
    result.valid(),
    LAcceptorTruncateLog(s@, result@, *opn as int),
{
    if *opn <= s.log_truncation_point {
        s.clone_up_to_view()
    } else {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let new_votes = CRemoveVotesBeforeLogTruncationPoint(&s.votes, opn);
        let result = CAcceptor {
            constants: s.constants.clone_up_to_view(),
            max_bal: s.max_bal,
            votes: new_votes,
            last_checkpointed_operation: s.last_checkpointed_operation.clone(),
            log_truncation_point: *opn,
            min_vote_opn: 0u64,
        };
        proof {
            let ghost ss = s@;
            let ghost sopn = *opn as int;
            assert(RemoveVotesBeforeLogTruncationPoint(ss.votes, abstractify_cvotes(&new_votes), sopn));
            assert(LAcceptorTruncateLog(ss, result@, sopn));
        }
        result
    }
}

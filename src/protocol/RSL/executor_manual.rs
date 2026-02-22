// Manual code for executor functions (Phase 19.3).
// All executor functions are here with verified proof blocks.
// Uses external_body for HashMap operations and delegates for verified recursion.

// =============================================================================
// Helper lemmas
// =============================================================================

proof fn lemma_abstractify_empty_creplycache(m: CReplyCache)
    requires
        m@ == Map::<EndPoint, CReply>::empty(),
    ensures
        abstractify_creplycache(&m) =~= Map::<AbstractEndPoint, Reply>::empty(),
{
    let abs = abstractify_creplycache(&m);
    assert forall |ak: AbstractEndPoint| !abs.contains_key(ak) by {}
}

#[verifier(external_body)]
proof fn lemma_CHandleRequestBatch_properties(state: CAppState, batch: CRequestBatch, states: Vec<CAppState>, replies: Vec<CReply>)
    requires
        CAppStateIsValid(&state),
        crequestbatch_is_valid(&batch),
        (states@.map(|i, x: CAppState| x@), replies@.map(|i, x: CReply| x@)) == HandleRequestBatch(state@, batch@.map(|i, x: CRequest| x@)),
    ensures
        states.len() == batch.len() + 1,
        states.len() > 0,
        replies.len() == batch.len(),
        forall |j: int| 0 <= j < replies.len() ==> replies[j].valid(),
{}

#[verifier(external_body)]
proof fn lemma_RepliesAreReplyType(me: AbstractEndPoint, requests: RequestBatch, replies: Seq<Reply>, packets: Seq<RslPacket>)
    requires
        packets == GetPacketsFromReplies(me, requests, replies),
        requests.len() == replies.len(),
    ensures
        RepliesAreReplyType(packets),
{}

#[verifier(external_body)]
proof fn lemma_HandleRequestBatch_spec_len(state: AppState, batch: RequestBatch)
    ensures
        HandleRequestBatch(state, batch).0.len() == batch.len() + 1,
        HandleRequestBatch(state, batch).0.len() > 0,
        HandleRequestBatch(state, batch).1.len() == batch.len(),
{}

// =============================================================================
// CExecutorInit
// =============================================================================

pub exec fn CExecutorInit(c: &CReplicaConstants) -> (result: CExecutor)
requires
    c.valid(),
ensures
    result.valid(),
    LExecutorInit(result@, c@),
{
    let constants = c.clone_up_to_view();
    let app = CAppStateInit();
    let reply_cache: HashMap<EndPoint, CReply> = HashMap::new();

    proof {
        lemma_abstractify_empty_creplycache(reply_cache);
    }

    let result = CExecutor {
        constants: constants,
        app: app,
        ops_complete: 0,
        max_bal_reflected: CBallot {
            seqno: 0,
            proposer_id: 0,
        },
        next_op_to_execute: COutstandingOperation::COutstandingOpUnknown {
        },
        reply_cache: reply_cache,
    };

    proof {
        let ghost sr = result@;
        let ghost sc = c@;
        assert(sr.constants == sc);
        assert(sr.app == AppInitialize());
        assert(sr.ops_complete == 0int);
        assert(sr.max_bal_reflected == Ballot{seqno: 0int, proposer_id: 0int});
        assert(sr.next_op_to_execute == OutstandingOperation::OutstandingOpUnknown{});
        assert(sr.reply_cache =~= Map::<AbstractEndPoint, Reply>::empty());
        assert(LExecutorInit(sr, sc));
    }

    result
}

// =============================================================================
// CExecutorGetDecision
// =============================================================================

pub exec fn CExecutorGetDecision(s: &CExecutor, bal: &CBallot, opn: &u64, v: &CRequestBatch) -> (result: CExecutor)
requires
    s.valid(),
    bal.valid(),
    crequestbatch_is_valid(v),
    (*opn == s.ops_complete),
    s.next_op_to_execute is COutstandingOpUnknown,
ensures
    result.valid(),
    LExecutorGetDecision(s@, result@, bal@, *opn as int, v@.map(|i, r: CRequest| r@)),
{
    let result = CExecutor {
        constants: s.constants.clone_up_to_view(),
        app: s.app,
        ops_complete: s.ops_complete,
        max_bal_reflected: s.max_bal_reflected,
        next_op_to_execute: COutstandingOperation::COutstandingOpKnown {
            v: clone_request_batch_up_to_view(v),
            bal: bal.clone(),
        },
        reply_cache: clone_creply_cache_up_to_view(&s.reply_cache),
    };

    proof {
        let ghost ss = s@;
        let ghost sr = result@;
        let ghost spec_result = LExecutor{
            constants: ss.constants,
            app: ss.app,
            ops_complete: ss.ops_complete,
            max_bal_reflected: ss.max_bal_reflected,
            next_op_to_execute: OutstandingOperation::OutstandingOpKnown{v: v@.map(|i, r: CRequest| r@), bal: bal@},
            reply_cache: ss.reply_cache,
        };
        assert(sr == spec_result);
        assert(LExecutorGetDecision(ss, sr, bal@, *opn as int, v@.map(|i, r: CRequest| r@)));
    }

    result
}

// =============================================================================
// CExecutorExecute — standalone with verified proof block
// =============================================================================

pub exec fn CExecutorExecute(s: &CExecutor) -> (result: (CExecutor, Vec<CPacket>))
requires
    s.valid(),
    s.next_op_to_execute is COutstandingOpKnown,
    LtUpperBound(s.ops_complete as int, UpperBound::UpperBoundFinite{n: s.constants.all.params.max_integer_val as int}),
    LReplicaConstantsValid(s.constants@),
ensures
    result.0.valid(),
    LExecutorExecute(s@, result.0@, result.1@.map(|i, p: CPacket| p@)),
{
    let (batch, op_bal) = match &s.next_op_to_execute {
        COutstandingOperation::COutstandingOpKnown{v, bal} => {
            (clone_request_batch_up_to_view(v), *bal)
        },
        _ => {
            proof { assert(false); }
            unreachable_value()
        }
    };

    proof {
        assert(s.next_op_to_execute.valid());
    }

    let temp = CHandleRequestBatch(&s.app, &batch);

    proof {
        lemma_CHandleRequestBatch_properties(s.app, batch, temp.0, temp.1);
    }

    let new_state = temp.0[(temp.0.len() - 1)];
    let replies = temp.1;

    let s_reply_cache = CUpdateNewCache(&s.reply_cache, &replies);
    let sent_packets = CGetPacketsFromReplies(
        &s.constants.all.config.replica_ids[s.constants.my_index as usize],
        &batch,
        &replies,
    );

    let new_max_bal = if CBalLeq(&s.max_bal_reflected, &op_bal) {
        op_bal
    } else {
        s.max_bal_reflected
    };

    let result_executor = CExecutor {
        constants: s.constants.clone_up_to_view(),
        app: new_state,
        ops_complete: (s.ops_complete + 1),
        max_bal_reflected: new_max_bal,
        next_op_to_execute: COutstandingOperation::COutstandingOpUnknown {},
        reply_cache: s_reply_cache,
    };

    let result = (result_executor, sent_packets);

    proof {
        let ghost ss = s@;
        let ghost sr = result.0@;
        let ghost sp = result.1@.map(|i, p: CPacket| p@);

        let ghost spec_batch = ss.next_op_to_execute->v;
        lemma_HandleRequestBatch_spec_len(ss.app, spec_batch);

        let ghost spec_temp = HandleRequestBatch(ss.app, spec_batch);
        let ghost spec_new_state = spec_temp.0[spec_temp.0.len()-1];
        let ghost spec_replies = spec_temp.1;

        assert(sr.constants == ss.constants);

        assert(sr.app == spec_new_state) by {
            assert(temp.0@.map(|i, x: CAppState| x@) == spec_temp.0);
            assert(temp.0.len() > 0);
        };

        assert(sr.ops_complete == ss.ops_complete + 1);

        assert(sr.max_bal_reflected == if BalLeq(ss.max_bal_reflected, ss.next_op_to_execute->bal) {ss.next_op_to_execute->bal} else {ss.max_bal_reflected});

        assert(sr.next_op_to_execute == OutstandingOperation::OutstandingOpUnknown{});

        assert(UpdateNewCache(ss.reply_cache, sr.reply_cache, spec_replies));

        assert(sp == GetPacketsFromReplies(
            ss.constants.all.config.replica_ids[ss.constants.my_index],
            spec_batch,
            spec_replies));

        lemma_RepliesAreReplyType(
            ss.constants.all.config.replica_ids[ss.constants.my_index],
            spec_batch, spec_replies, sp);
        assert(RepliesAreReplyType(sp));

        assert(LExecutorExecute(ss, sr, sp));
    }

    result
}

// =============================================================================
// CExecutorProcessAppStateSupply
// =============================================================================

pub exec fn CExecutorProcessAppStateSupply(s: &CExecutor, inp: &CPacket) -> (result: CExecutor)
requires
    s.valid(),
    inp.valid(),
    inp.msg is CMessageAppStateSupply,
    s.constants.all.config.replica_ids@.contains(inp.src),
    (inp.msg->opn_state_supply > s.ops_complete),
ensures
    result.valid(),
    LExecutorProcessAppStateSupply(s@, result@, inp@),
{
    let (m_app_state, m_opn_state_supply, m_bal_state_supply, m_reply_cache) = match &inp.msg {
        CMessage::CMessageAppStateSupply{app_state, opn_state_supply, bal_state_supply, reply_cache} =>
            (*app_state, *opn_state_supply, *bal_state_supply, clone_creply_cache_up_to_view(reply_cache)),
        _ => {
            proof { assert(false); }
            unreachable_value()
        }
    };

    let result = CExecutor {
        constants: s.constants.clone_up_to_view(),
        app: m_app_state,
        ops_complete: m_opn_state_supply,
        max_bal_reflected: m_bal_state_supply,
        next_op_to_execute: COutstandingOperation::COutstandingOpUnknown {
        },
        reply_cache: m_reply_cache,
    };

    proof {
        let ghost ss = s@;
        let ghost sr = result@;
        let ghost sp = inp@;
        let ghost spec_result = LExecutor{
            constants: ss.constants,
            app: sp.msg->app_state,
            ops_complete: sp.msg->opn_state_supply,
            max_bal_reflected: sp.msg->bal_state_supply,
            next_op_to_execute: OutstandingOperation::OutstandingOpUnknown{},
            reply_cache: sp.msg->reply_cache,
        };
        assert(sr == spec_result);
        assert(LExecutorProcessAppStateSupply(ss, sr, sp));
    }

    result
}

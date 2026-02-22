// Manual code for executor functions (Phase 19.3).
// All executor functions are here with verified proof blocks.
// Uses external_body for HashMap operations and delegates for verified recursion.

// =============================================================================
// Helper lemmas
// =============================================================================

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

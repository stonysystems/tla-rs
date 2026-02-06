---- MODULE State_machine ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Request, AppState, RequestBatch

HandleRequest(state, request) ==
    LET unused_0 == AppHandleRequest(state, request.request)
    IN <<new_state, [client |-> request.client, seqno |-> request.seqno, reply |-> reply]>>

RECURSIVE HandleRequestBatchHidden(_, _)
HandleRequestBatchHidden(state, batch) ==
    IF Len(batch) = 0 THEN <<<<state>>, <<>>>> ELSE LET unused_2 == HandleRequestBatchHidden(state, drop_last(batch))
IN LET unused_2 == AppHandleRequest(Last(restStates), Last(batch).request)
IN <<restStates + <<new_state>>, restReplies + <<[client |-> Last(batch).client, seqno |-> Last(batch).seqno, reply |-> reply]>>>>

HandleRequestBatch(state, batch) ==
    LET unused_3 == HandleRequestBatchHidden(state, batch)
    IN <<states, replies>>

====

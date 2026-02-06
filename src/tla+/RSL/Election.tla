---- MODULE election ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS UpperBound, ReplicaConstants, Ballot, Constants, RslPacket, ElectionState, RequestBatch, Request

ElectionState ==
    [constants |-> ReplicaConstants, current_view |-> Ballot, current_view_suspectors |-> SUBSET Int, epoch_end_time |-> Int, epoch_length |-> Int, requests_received_this_epoch |-> Seq(Request), requests_received_prev_epochs |-> Seq(Request)]

ComputeSuccessorView(b, c) ==
    IF b.proposer_id + 1 < Len(c.config.replica_ids) THEN [seqno |-> b.seqno, proposer_id |-> b.proposer_id + 1] ELSE [seqno |-> b.seqno + 1, proposer_id |-> 0]

BoundRequestSequence(s, lengthBound) ==
    IF lengthBound.tag = UpperBoundFinite /\ 0 <= lengthBound.n /\ lengthBound.n < Len(s) THEN SubSeq(s, 0, lengthBound.n) ELSE s

RequestsMatch(r1, r2) ==
    /\ r1.tag = Request
    /\ r2.tag = Request
    /\ r1.client = r2.client
    /\ r1.seqno = r2.seqno

RequestSatisfiedBy(r1, r2) ==
    /\ r1.tag = Request
    /\ r2.tag = Request
    /\ r1.client = r2.client
    /\ r1.seqno <= r2.seqno

RECURSIVE RemoveAllSatisfiedRequestsInSequence(_, _)
RemoveAllSatisfiedRequestsInSequence(s, r) ==
    IF Len(s) = 0 THEN <<>> ELSE IF RequestSatisfiedBy(s[0], r) THEN RemoveAllSatisfiedRequestsInSequence(drop_first(s), r) ELSE <<s[0]>> + RemoveAllSatisfiedRequestsInSequence(drop_first(s), r)

ElectionStateInit(es, c) ==
    /\ es.constants = c
    /\ es.current_view = [seqno |-> 1, proposer_id |-> 0]
    /\ es.current_view_suspectors = {}
    /\ es.epoch_end_time = 0
    /\ es.epoch_length = c.all.params.baseline_view_timeout_period
    /\ es.requests_received_this_epoch = <<>>
    /\ es.requests_received_prev_epochs = <<>>

ElectionStateProcessHeartbeat(es, es_, p, clock) ==
    IF ~p.src \in es.constants.all.config.replica_ids THEN es_ = es ELSE LET sender_index == GetReplicaIndex(p.src, es.constants.all.config)
IN IF p.msg.bal_heartbeat = es.current_view /\ p.msg.suspicious THEN es_ = [constants |-> es.constants, current_view |-> es.current_view, current_view_suspectors |-> es.current_view_suspectors + {sender_index}, epoch_end_time |-> es.epoch_end_time, epoch_length |-> es.epoch_length, requests_received_this_epoch |-> es.requests_received_this_epoch, requests_received_prev_epochs |-> es.requests_received_prev_epochs] ELSE IF BalLt(es.current_view, p.msg.bal_heartbeat) THEN LET new_epoch_length == UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val)
IN es_ = [constants |-> es.constants, current_view |-> p.msg.bal_heartbeat, current_view_suspectors |-> IF p.msg.suspicious THEN {sender_index} ELSE {}, epoch_end_time |-> UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val), epoch_length |-> new_epoch_length, requests_received_this_epoch |-> <<>>, requests_received_prev_epochs |-> BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val)] ELSE es_ = es

ElectionStateCheckForViewTimeout(es, es_, clock) ==
    IF clock < es.epoch_end_time THEN es_ = es ELSE IF Len(es.requests_received_prev_epochs) = 0 THEN LET new_epoch_length == es.constants.all.params.baseline_view_timeout_period
IN es_ = [constants |-> es.constants, current_view |-> es.current_view, current_view_suspectors |-> es.current_view_suspectors, epoch_end_time |-> UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val), epoch_length |-> new_epoch_length, requests_received_this_epoch |-> <<>>, requests_received_prev_epochs |-> es.requests_received_this_epoch] ELSE es_ = [constants |-> es.constants, current_view |-> es.current_view, current_view_suspectors |-> es.current_view_suspectors + {es.constants.my_index}, epoch_end_time |-> UpperBoundedAddition(clock, es.epoch_length, es.constants.all.params.max_integer_val), epoch_length |-> es.epoch_length, requests_received_this_epoch |-> <<>>, requests_received_prev_epochs |-> BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val)]

ElectionStateCheckForQuorumOfViewSuspicions(es, es_, clock) ==
    IF Len(es.current_view_suspectors) < MinQuorumSize(es.constants.all.config) \/ ~LtUpperBound(es.current_view.seqno, es.constants.all.params.max_integer_val) THEN es_ = es ELSE LET new_epoch_length == UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val)
IN es_ = [constants |-> es.constants, current_view |-> ComputeSuccessorView(es.current_view, es.constants.all), current_view_suspectors |-> {}, epoch_end_time |-> UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val), epoch_length |-> new_epoch_length, requests_received_this_epoch |-> <<>>, requests_received_prev_epochs |-> BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val)]

ElectionStateReflectReceivedRequest(es, es_, req) ==
    IF \E earlier_req \in Request : (earlier_req \in es.requests_received_prev_epochs \/ earlier_req \in es.requests_received_this_epoch) /\ RequestsMatch(earlier_req, req) THEN es_ = es ELSE es_ = [constants |-> es.constants, current_view |-> es.current_view, current_view_suspectors |-> es.current_view_suspectors, epoch_end_time |-> es.epoch_end_time, epoch_length |-> es.epoch_length, requests_received_this_epoch |-> BoundRequestSequence(es.requests_received_this_epoch + <<req>>, es.constants.all.params.max_integer_val), requests_received_prev_epochs |-> es.requests_received_prev_epochs]

RECURSIVE RemoveExecutedRequestBatch(_, _)
RemoveExecutedRequestBatch(reqs, batch) ==
    IF Len(batch) = 0 THEN reqs ELSE RemoveExecutedRequestBatch(RemoveAllSatisfiedRequestsInSequence(reqs, batch[0]), drop_first(batch))

ElectionStateReflectExecutedRequestBatch(es, es_, batch) ==
    es_ = [constants |-> es.constants, current_view |-> es.current_view, current_view_suspectors |-> es.current_view_suspectors, epoch_end_time |-> es.epoch_end_time, epoch_length |-> es.epoch_length, requests_received_this_epoch |-> RemoveExecutedRequestBatch(es.requests_received_this_epoch, batch), requests_received_prev_epochs |-> RemoveExecutedRequestBatch(es.requests_received_prev_epochs, batch)]

====

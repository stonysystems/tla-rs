---- MODULE Executor ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ReplicaConstants, AbstractEndPoint, ReplyCache, RequestBatch, Request, Ballot, Reply, RslPacket, OperationNumber, Executor

Executor ==
    [constants |-> ReplicaConstants, app |-> AppState, ops_complete |-> Int, max_bal_reflected |-> Ballot, next_op_to_execute |-> OutstandingOperation, reply_cache |-> ReplyCache]

OutstandingOperation ==
    {OutstandingOpKnown, OutstandingOpUnknown}

ExecutorInit(s, c) ==
    /\ s.constants = c
    /\ s.app = AppInitialize
    /\ s.ops_complete = 0
    /\ s.max_bal_reflected = [seqno |-> 0, proposer_id |-> 0]
    /\ s.next_op_to_execute = <<>>
    /\ s.reply_cache = <<>>

ExecutorGetDecision(s, s_, bal, opn, v) ==
    s_ = [constants |-> s.constants, app |-> s.app, ops_complete |-> s.ops_complete, max_bal_reflected |-> s.max_bal_reflected, next_op_to_execute |-> [v |-> v, bal |-> bal], reply_cache |-> s.reply_cache]

RECURSIVE GetPacketsFromReplies(_, _, _)
GetPacketsFromReplies(me, requests, replies) ==
    IF Len(requests) = 0 THEN <<>> ELSE <<[dst |-> requests[0].client, src |-> me, msg |-> [seqno_reply |-> requests[0].seqno, reply |-> replies[0].reply]]>> + GetPacketsFromReplies(me, drop_first(requests), drop_first(replies))

RECURSIVE ClientsInReplies(_)
ClientsInReplies(replies) ==
    IF Len(replies) = 0 THEN <<>> ELSE [ClientsInReplies(drop_first(replies)) EXCEPT ![replies[0].client] = replies[0]]

RepliesAreReplyType(replies) ==
    \A p \in RslPacket : p \in replies => p.msg.tag = RslMessageReply

UpdateNewCache(c, c_, replies) ==
    LET nc == ClientsInReplies(replies)
    IN \A client \in AbstractEndPoint : client \in DOMAIN c_ => ((client \in DOMAIN c /\ c_[client] = c[client]) \/ \E req_idx \in Int : 0 <= req_idx /\ req_idx < Len(replies) /\ replies[req_idx].client = client /\ c_[client] = replies[req_idx]) /\ \A client \in AbstractEndPoint : client \in DOMAIN c_ <=> (client \in DOMAIN nc \/ client \in DOMAIN c) /\ \A client \in AbstractEndPoint : client \in DOMAIN c_ => c_[client] = IF client \in DOMAIN c THEN c[client] ELSE nc[client] /\ \A client \in AbstractEndPoint : (client \in DOMAIN nc \/ client \in DOMAIN c) => (client \in DOMAIN c_ /\ c_[client] = IF client \in DOMAIN c THEN c[client] ELSE nc[client])

ExecutorExecute(s, s_, sent_packets) ==
    LET batch == s.next_op_to_execute.v
    IN LET temp == HandleRequestBatch(s.app, batch)
IN LET new_state == temp[1][Len(temp[1]) - 1]
IN LET replies == temp[2]
IN LET clients == ClientsInReplies(replies)
IN s_.constants = s.constants /\ s_.app = new_state /\ s_.ops_complete = s.ops_complete + 1 /\ s_.max_bal_reflected = IF BalLeq(s.max_bal_reflected, s.next_op_to_execute.bal) THEN s.next_op_to_execute.bal ELSE s.max_bal_reflected /\ s_.next_op_to_execute = <<>> /\ UpdateNewCache(s.reply_cache, s_.reply_cache, replies) /\ sent_packets = GetPacketsFromReplies(s.constants.all.config.replica_ids[s.constants.my_index], batch, replies) /\ RepliesAreReplyType(sent_packets)

ExecutorProcessAppStateSupply(s, s_, inp) ==
    LET m == inp.msg
    IN s_ = [constants |-> s.constants, app |-> m.app_state, ops_complete |-> m.opn_state_supply, max_bal_reflected |-> m.bal_state_supply, next_op_to_execute |-> <<>>, reply_cache |-> m.reply_cache]

ExecutorProcessAppStateRequest(s, s_, inp, sent_packets) ==
    LET m == inp.msg
    IN IF inp.src \in s.constants.all.config.replica_ids /\ BalLeq(s.max_bal_reflected, m.bal_state_req) /\ s.ops_complete >= m.opn_state_req /\ ReplicaConstantsValid(s.constants) THEN s_ = s /\ sent_packets = <<[dst |-> inp.src, src |-> s.constants.all.config.replica_ids[s.constants.my_index], msg |-> [bal_state_supply |-> s.max_bal_reflected, opn_state_supply |-> s.ops_complete, app_state |-> s.app, reply_cache |-> s.reply_cache]]>> ELSE s_ = s /\ sent_packets = <<>>

ExecutorProcessStartingPhase2(s, s_, inp, sent_packets) ==
    IF inp.src \in s.constants.all.config.replica_ids /\ inp.msg.logTruncationPoint_2 > s.ops_complete THEN s_ = s /\ BroadcastToEveryone(s.constants.all.config, s.constants.my_index, [bal_state_req |-> inp.msg.bal_2, opn_state_req |-> inp.msg.logTruncationPoint_2], sent_packets) ELSE s_ = s /\ sent_packets = <<>>

ExecutorProcessRequest(s, inp, sent_packets) ==
    IF inp.msg.seqno_req = s.reply_cache[inp.src].seqno /\ ReplicaConstantsValid(s.constants) THEN LET r == s.reply_cache[inp.src]
IN sent_packets = <<[dst |-> r.client, src |-> s.constants.all.config.replica_ids[s.constants.my_index], msg |-> [seqno_reply |-> r.seqno, reply |-> r.reply]]>> ELSE sent_packets = <<>>

====

---- MODULE Proposer ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS RequestBatch, Proposer, OperationNumber, Ballot, ReplicaConstants, RslPacket

Proposer ==
    [constants |-> ReplicaConstants, current_state |-> Int, request_queue |-> Seq(Request), max_ballot_i_sent_1a |-> Ballot, next_operation_number_to_propose |-> Int, received_1b_packets |-> SUBSET RslPacket, highest_seqno_requested_by_client_this_view |-> [AbstractEndPoint -> Int], incomplete_batch_timer |-> IncompleteBatchTimer, election_state |-> ElectionState]

IncompleteBatchTimer ==
    {IncompleteBatchTimerOn, IncompleteBatchTimerOff}

IsAfterLogTruncationPoint(opn, received_1b_packets) ==
    \A p \in RslPacket : (p \in received_1b_packets /\ p.msg.tag = RslMessage1b) => p.msg.log_truncation_point <= opn

SetOfMessage1b(S) ==
    \A p \in RslPacket : p \in S => p.msg.tag = RslMessage1b

SetOfMessage1bAboutBallot(S, b) ==
    SetOfMessage1b(S) /\ \A p \in RslPacket : p \in S => p.msg.bal_1b = b

ExistVotesHasProposalLargeThanOpn(p, op) ==
    \E opn \in OperationNumber : opn \in DOMAIN p.msg.votes /\ opn > op

ExistsAcceptorHasProposalLargeThanOpn(S, op) ==
    \E p \in RslPacket : p \in S /\ ExistVotesHasProposalLargeThanOpn(p, op)

AllAcceptorsHadNoProposal(S, opn) ==
    \A p \in RslPacket : p \in S => ~opn \in DOMAIN p.msg.votes

Lmax_balInS(c, S, opn) ==
    \A p \in RslPacket : (p \in S /\ opn \in DOMAIN p.msg.votes) => BalLeq(p.msg.votes[opn].max_value_bal, c)

ExistsBallotInS(v, c, S, opn) ==
    \E p \in RslPacket : p \in S /\ opn \in DOMAIN p.msg.votes /\ p.msg.votes[opn].max_value_bal = c /\ p.msg.votes[opn].max_val = v

ValIsHighestNumberedProposalAtBallot(v, c, S, opn) ==
    Lmax_balInS(c, S, opn) /\ ExistsBallotInS(v, c, S, opn)

ValIsHighestNumberedProposal(v, S, opn) ==
    \E c \in Ballot : ValIsHighestNumberedProposalAtBallot(v, c, S, opn)

ProposerCanNominateUsingOperationNumber(s, log_truncation_point, opn) ==
    /\ s.election_state.current_view = s.max_ballot_i_sent_1a
    /\ s.current_state = 2
    /\ Len(s.received_1b_packets) >= MinQuorumSize(s.constants.all.config)
    /\ SetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
    /\ IsAfterLogTruncationPoint(opn, s.received_1b_packets)
    /\ opn < UpperBoundedAddition(log_truncation_point, s.constants.all.params.max_log_length, s.constants.all.params.max_integer_val)
    /\ opn >= 0
    /\ LtUpperBound(opn, s.constants.all.params.max_integer_val)

ProposerInit(s, c) ==
    /\ s.constants = c
    /\ s.current_state = 0
    /\ s.request_queue = <<>>
    /\ s.max_ballot_i_sent_1a = [seqno |-> 0, proposer_id |-> c.my_index]
    /\ s.next_operation_number_to_propose = 0
    /\ s.received_1b_packets = {}
    /\ s.highest_seqno_requested_by_client_this_view = <<>>
    /\ ElectionStateInit(s.election_state, c)
    /\ s.incomplete_batch_timer.tag = IncompleteBatchTimerOff

ProposerProcessRequest(s, s_, packet) ==
    LET val == [client |-> packet.src, seqno |-> packet.msg.seqno_req, request |-> packet.msg.val]
    IN ElectionStateReflectReceivedRequest(s.election_state, s_.election_state, val) /\ IF s.current_state # 0 /\ (~val.client \in DOMAIN s.highest_seqno_requested_by_client_this_view \/ val.seqno > s.highest_seqno_requested_by_client_this_view[val.client]) THEN s_ = [constants |-> s.constants, current_state |-> s.current_state, request_queue |-> s.request_queue + <<val>>, max_ballot_i_sent_1a |-> s.max_ballot_i_sent_1a, next_operation_number_to_propose |-> s.next_operation_number_to_propose, received_1b_packets |-> s.received_1b_packets, highest_seqno_requested_by_client_this_view |-> [s.highest_seqno_requested_by_client_this_view EXCEPT ![val.client] = val.seqno], incomplete_batch_timer |-> s.incomplete_batch_timer, election_state |-> s_.election_state] ELSE s_ = [constants |-> s.constants, current_state |-> s.current_state, request_queue |-> s.request_queue, max_ballot_i_sent_1a |-> s.max_ballot_i_sent_1a, next_operation_number_to_propose |-> s.next_operation_number_to_propose, received_1b_packets |-> s.received_1b_packets, highest_seqno_requested_by_client_this_view |-> s.highest_seqno_requested_by_client_this_view, incomplete_batch_timer |-> s.incomplete_batch_timer, election_state |-> s_.election_state]

ProposerMaybeEnterNewViewAndSend1a(s, s_, sent_packets) ==
    IF s.election_state.current_view.proposer_id = s.constants.my_index /\ BalLt(s.max_ballot_i_sent_1a, s.election_state.current_view) THEN s_ = [constants |-> s.constants, current_state |-> 1, request_queue |-> s.election_state.requests_received_prev_epochs + s.election_state.requests_received_this_epoch, max_ballot_i_sent_1a |-> s.election_state.current_view, next_operation_number_to_propose |-> s.next_operation_number_to_propose, received_1b_packets |-> {}, highest_seqno_requested_by_client_this_view |-> <<>>, incomplete_batch_timer |-> s.incomplete_batch_timer, election_state |-> s.election_state] /\ BroadcastToEveryone(s.constants.all.config, s.constants.my_index, [bal_1a |-> s.election_state.current_view], sent_packets) ELSE s_ = s /\ sent_packets = <<>>

ProposerProcess1b(s, s_, p) ==
    s_ = [constants |-> s.constants, current_state |-> s.current_state, request_queue |-> s.request_queue, max_ballot_i_sent_1a |-> s.max_ballot_i_sent_1a, next_operation_number_to_propose |-> s.next_operation_number_to_propose, received_1b_packets |-> s.received_1b_packets + {p}, highest_seqno_requested_by_client_this_view |-> s.highest_seqno_requested_by_client_this_view, incomplete_batch_timer |-> s.incomplete_batch_timer, election_state |-> s.election_state]

ProposerMaybeEnterPhase2(s, s_, log_truncation_point, sent_packets) ==
    IF Len(s.received_1b_packets) >= MinQuorumSize(s.constants.all.config) /\ SetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a) /\ s.current_state = 1 THEN s_ = [constants |-> s.constants, current_state |-> 2, request_queue |-> s.request_queue, max_ballot_i_sent_1a |-> s.max_ballot_i_sent_1a, next_operation_number_to_propose |-> log_truncation_point, received_1b_packets |-> s.received_1b_packets, highest_seqno_requested_by_client_this_view |-> s.highest_seqno_requested_by_client_this_view, incomplete_batch_timer |-> s.incomplete_batch_timer, election_state |-> s.election_state] /\ BroadcastToEveryone(s.constants.all.config, s.constants.my_index, [bal_2 |-> s.max_ballot_i_sent_1a, logTruncationPoint_2 |-> log_truncation_point], sent_packets) ELSE s_ = s /\ sent_packets = <<>>

ProposerNominateNewValueAndSend2a(s, s_, clock, log_truncation_point, sent_packets) ==
    LET batchSize == IF Len(s.request_queue) <= s.constants.all.params.max_batch_size \/ s.constants.all.params.max_batch_size < 0 THEN Len(s.request_queue) ELSE s.constants.all.params.max_batch_size
    IN LET v == SubSeq(s.request_queue, 0, batchSize)
IN LET opn == s.next_operation_number_to_propose
IN s_ = [constants |-> s.constants, current_state |-> s.current_state, request_queue |-> SubSeq(s.request_queue, batchSize, Len(s.request_queue)), max_ballot_i_sent_1a |-> s.max_ballot_i_sent_1a, next_operation_number_to_propose |-> s.next_operation_number_to_propose + 1, received_1b_packets |-> s.received_1b_packets, highest_seqno_requested_by_client_this_view |-> s.highest_seqno_requested_by_client_this_view, incomplete_batch_timer |-> IF Len(s.request_queue) > batchSize THEN [when |-> UpperBoundedAddition(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)] ELSE <<>>, election_state |-> s.election_state] /\ BroadcastToEveryone(s.constants.all.config, s.constants.my_index, [bal_2a |-> s.max_ballot_i_sent_1a, opn_2a |-> opn, val_2a |-> v], sent_packets)

ProposerNominateOldValueAndSend2a(s, s_, log_truncation_point, sent_packets) ==
    LET opn == s.next_operation_number_to_propose
    IN \E p \in RslPacket : p \in s.received_1b_packets /\ ValIsHighestNumberedProposal(p.msg.votes[opn].max_val, s.received_1b_packets, opn) /\ s_ = [constants |-> s.constants, current_state |-> s.current_state, request_queue |-> s.request_queue, max_ballot_i_sent_1a |-> s.max_ballot_i_sent_1a, next_operation_number_to_propose |-> s.next_operation_number_to_propose + 1, received_1b_packets |-> s.received_1b_packets, highest_seqno_requested_by_client_this_view |-> s.highest_seqno_requested_by_client_this_view, incomplete_batch_timer |-> s.incomplete_batch_timer, election_state |-> s.election_state] /\ BroadcastToEveryone(s.constants.all.config, s.constants.my_index, [bal_2a |-> s.max_ballot_i_sent_1a, opn_2a |-> opn, val_2a |-> p.msg.votes[opn].max_val], sent_packets)

ProposerMaybeNominateValueAndSend2a(s, s_, clock, log_truncation_point, sent_packets) ==
    IF ~ProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose) THEN s_ = s /\ sent_packets = <<>> ELSE IF ~AllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose) THEN ProposerNominateOldValueAndSend2a(s, s_, log_truncation_point, sent_packets) ELSE IF ExistsAcceptorHasProposalLargeThanOpn(s.received_1b_packets, s.next_operation_number_to_propose) \/ Len(s.request_queue) >= s.constants.all.params.max_batch_size \/ (Len(s.request_queue) > 0 /\ s.incomplete_batch_timer.tag = IncompleteBatchTimerOn /\ clock >= s.incomplete_batch_timer.when) THEN ProposerNominateNewValueAndSend2a(s, s_, clock, log_truncation_point, sent_packets) ELSE IF Len(s.request_queue) > 0 /\ s.incomplete_batch_timer.tag = IncompleteBatchTimerOff THEN s_ = [constants |-> s.constants, current_state |-> s.current_state, request_queue |-> s.request_queue, max_ballot_i_sent_1a |-> s.max_ballot_i_sent_1a, next_operation_number_to_propose |-> s.next_operation_number_to_propose, received_1b_packets |-> s.received_1b_packets, highest_seqno_requested_by_client_this_view |-> s.highest_seqno_requested_by_client_this_view, incomplete_batch_timer |-> [when |-> UpperBoundedAddition(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)], election_state |-> s.election_state] /\ sent_packets = <<>> ELSE s_ = s /\ sent_packets = <<>>

ProposerProcessHeartbeat(s, s_, p, clock) ==
    /\ ElectionStateProcessHeartbeat(s.election_state, s_.election_state, p, clock)
    /\ IF BalLt(s.election_state.current_view, s_.election_state.current_view) THEN s_.current_state = 0 /\ s_.request_queue = <<>> ELSE s_.current_state = s.current_state /\ s_.request_queue = s.request_queue
    /\ s_ = [constants |-> s.constants, current_state |-> s_.current_state, request_queue |-> s_.request_queue, max_ballot_i_sent_1a |-> s.max_ballot_i_sent_1a, next_operation_number_to_propose |-> s.next_operation_number_to_propose, received_1b_packets |-> s.received_1b_packets, highest_seqno_requested_by_client_this_view |-> s.highest_seqno_requested_by_client_this_view, incomplete_batch_timer |-> s.incomplete_batch_timer, election_state |-> s_.election_state]

ProposerCheckForViewTimeout(s, s_, clock) ==
    ElectionStateCheckForViewTimeout(s.election_state, s_.election_state, clock) /\ s_ = [constants |-> s.constants, current_state |-> s.current_state, request_queue |-> s.request_queue, max_ballot_i_sent_1a |-> s.max_ballot_i_sent_1a, next_operation_number_to_propose |-> s.next_operation_number_to_propose, received_1b_packets |-> s.received_1b_packets, highest_seqno_requested_by_client_this_view |-> s.highest_seqno_requested_by_client_this_view, incomplete_batch_timer |-> s.incomplete_batch_timer, election_state |-> s_.election_state]

ProposerCheckForQuorumOfViewSuspicions(s, s_, clock) ==
    /\ ElectionStateCheckForQuorumOfViewSuspicions(s.election_state, s_.election_state, clock)
    /\ IF BalLt(s.election_state.current_view, s_.election_state.current_view) THEN s_.current_state = 0 /\ s_.request_queue = <<>> ELSE s_.current_state = s.current_state /\ s_.request_queue = s.request_queue
    /\ s_ = [constants |-> s.constants, current_state |-> s_.current_state, request_queue |-> s_.request_queue, max_ballot_i_sent_1a |-> s.max_ballot_i_sent_1a, next_operation_number_to_propose |-> s.next_operation_number_to_propose, received_1b_packets |-> s.received_1b_packets, highest_seqno_requested_by_client_this_view |-> s.highest_seqno_requested_by_client_this_view, incomplete_batch_timer |-> s.incomplete_batch_timer, election_state |-> s_.election_state]

ProposerResetViewTimerDueToExecution(s, s_, val) ==
    ElectionStateReflectExecutedRequestBatch(s.election_state, s_.election_state, val) /\ s_ = [constants |-> s.constants, current_state |-> s.current_state, request_queue |-> s.request_queue, max_ballot_i_sent_1a |-> s.max_ballot_i_sent_1a, next_operation_number_to_propose |-> s.next_operation_number_to_propose, received_1b_packets |-> s.received_1b_packets, highest_seqno_requested_by_client_this_view |-> s.highest_seqno_requested_by_client_this_view, incomplete_batch_timer |-> s.incomplete_batch_timer, election_state |-> s_.election_state]

====

---- MODULE replica ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ReplicaConstants, RslPacket, ClockReading, Replica, RslIo, Scheduler

Replica ==
    [constants |-> ReplicaConstants, nextHeartbeatTime |-> Int, proposer |-> Proposer, acceptor |-> Acceptor, learner |-> Learner, executor |-> Executor]

Scheduler ==
    [replica |-> Replica, nextActionIndex |-> Int]

ReplicaInit(r, c) ==
    /\ r.constants = c
    /\ r.nextHeartbeatTime = 0
    /\ ProposerInit(r.proposer, c)
    /\ AcceptorInit(r.acceptor, c)
    /\ LearnerInit(r.learner, c)
    /\ ExecutorInit(r.executor, c)

ReplicaNextProcessInvalid(s, s_, received_packet, sent_packets) ==
    s_ = s /\ sent_packets = <<>>

ReplicaNextProcessRequest(s, s_, received_packet, sent_packets) ==
    IF received_packet.src \in DOMAIN s.executor.reply_cache /\ received_packet.msg.seqno_req <= s.executor.reply_cache[received_packet.src].seqno THEN ExecutorProcessRequest(s.executor, received_packet, sent_packets) /\ s_ = s ELSE ProposerProcessRequest(s.proposer, s_.proposer, received_packet) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s_.proposer, acceptor |-> s.acceptor, learner |-> s.learner, executor |-> s.executor] /\ sent_packets = <<>>

ReplicaNextProcess1a(s, s_, received_packet, sent_packets) ==
    AcceptorProcess1a(s.acceptor, s_.acceptor, received_packet, sent_packets) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s.proposer, acceptor |-> s_.acceptor, learner |-> s.learner, executor |-> s.executor]

ReplicaNextProcess1b(s, s_, received_packet, sent_packets) ==
    IF received_packet.src \in s.proposer.constants.all.config.replica_ids /\ received_packet.msg.bal_1b = s.proposer.max_ballot_i_sent_1a /\ s.proposer.current_state = 1 /\ \A other_packet \in RslPacket : other_packet \in s.proposer.received_1b_packets => other_packet.src # received_packet.src THEN ProposerProcess1b(s.proposer, s_.proposer, received_packet) /\ AcceptorTruncateLog(s.acceptor, s_.acceptor, received_packet.msg.log_truncation_point) /\ sent_packets = <<>> /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s_.proposer, acceptor |-> s_.acceptor, learner |-> s.learner, executor |-> s.executor] ELSE s_ = s /\ sent_packets = <<>>

ReplicaNextProcessStartingPhase2(s, s_, received_packet, sent_packets) ==
    ExecutorProcessStartingPhase2(s.executor, s_.executor, received_packet, sent_packets) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s.proposer, acceptor |-> s.acceptor, learner |-> s.learner, executor |-> s_.executor]

ReplicaNextProcess2a(s, s_, received_packet, sent_packets) ==
    LET m == received_packet.msg
    IN IF received_packet.src \in s.acceptor.constants.all.config.replica_ids /\ BalLeq(s.acceptor.max_bal, m.bal_2a) /\ LeqUpperBound(m.opn_2a, s.acceptor.constants.all.params.max_integer_val) THEN AcceptorProcess2a(s.acceptor, s_.acceptor, received_packet, sent_packets) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s.proposer, acceptor |-> s_.acceptor, learner |-> s.learner, executor |-> s.executor] ELSE s_ = s /\ sent_packets = <<>>

ReplicaNextProcess2b(s, s_, received_packet, sent_packets) ==
    LET opn == received_packet.msg.opn_2b
    IN LET op_learnable == s.executor.ops_complete < opn \/ (s.executor.ops_complete = opn /\ s.executor.next_op_to_execute.tag = OutstandingOpUnknown)
IN IF op_learnable THEN LearnerProcess2b(s.learner, s_.learner, received_packet) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s.proposer, acceptor |-> s.acceptor, learner |-> s_.learner, executor |-> s.executor] /\ sent_packets = <<>> ELSE s_ = s /\ sent_packets = <<>>

ReplicaNextProcessReply(s, s_, received_packet, sent_packets) ==
    s_ = s /\ sent_packets = <<>>

ReplicaNextProcessAppStateSupply(s, s_, received_packet, sent_packets) ==
    IF received_packet.src \in s.executor.constants.all.config.replica_ids /\ received_packet.msg.opn_state_supply > s.executor.ops_complete THEN LearnerForgetOperationsBefore(s.learner, s_.learner, received_packet.msg.opn_state_supply) /\ ExecutorProcessAppStateSupply(s.executor, s_.executor, received_packet) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s.proposer, acceptor |-> s.acceptor, learner |-> s_.learner, executor |-> s_.executor] /\ sent_packets = <<>> ELSE s_ = s /\ sent_packets = <<>>

ReplicaNextProcessAppStateRequest(s, s_, received_packet, sent_packets) ==
    ExecutorProcessAppStateRequest(s.executor, s_.executor, received_packet, sent_packets) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s.proposer, acceptor |-> s.acceptor, learner |-> s.learner, executor |-> s_.executor]

ReplicaNextProcessHeartbeat(s, s_, received_packet, clock, sent_packets) ==
    /\ ProposerProcessHeartbeat(s.proposer, s_.proposer, received_packet, clock)
    /\ AcceptorProcessHeartbeat(s.acceptor, s_.acceptor, received_packet)
    /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s_.proposer, acceptor |-> s_.acceptor, learner |-> s.learner, executor |-> s.executor]
    /\ sent_packets = <<>>

ReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s, s_, sent_packets) ==
    ProposerMaybeEnterNewViewAndSend1a(s.proposer, s_.proposer, sent_packets) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s_.proposer, acceptor |-> s.acceptor, learner |-> s.learner, executor |-> s.executor]

ReplicaNextSpontaneousMaybeEnterPhase2(s, s_, sent_packets) ==
    ProposerMaybeEnterPhase2(s.proposer, s_.proposer, s.acceptor.log_truncation_point, sent_packets) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s_.proposer, acceptor |-> s.acceptor, learner |-> s.learner, executor |-> s.executor]

ReplicaNextReadClockMaybeNominateValueAndSend2a(s, s_, clock, sent_packets) ==
    ProposerMaybeNominateValueAndSend2a(s.proposer, s_.proposer, clock.t, s.acceptor.log_truncation_point, sent_packets) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s_.proposer, acceptor |-> s.acceptor, learner |-> s.learner, executor |-> s.executor]

ReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s_, sent_packets) ==
    \E opn \in OperationNumber : opn \in s.acceptor.last_checkpointed_operation /\ IsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) /\ IF opn > s.acceptor.log_truncation_point THEN AcceptorTruncateLog(s.acceptor, s_.acceptor, opn) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s.proposer, acceptor |-> s_.acceptor, learner |-> s.learner, executor |-> s.executor] /\ sent_packets = <<>> ELSE s_ = s /\ sent_packets = <<>>

ReplicaNextSpontaneousMaybeMakeDecision(s, s_, sent_packets) ==
    LET opn == s.executor.ops_complete
    IN IF s.executor.next_op_to_execute.tag = OutstandingOpUnknown /\ opn \in DOMAIN s.learner.unexecuted_learner_state /\ Len(s.learner.unexecuted_learner_state[opn].received_2b_message_senders) >= MinQuorumSize(s.learner.constants.all.config) THEN ExecutorGetDecision(s.executor, s_.executor, s.learner.max_ballot_seen, opn, s.learner.unexecuted_learner_state[opn].candidate_learned_value) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s.proposer, acceptor |-> s.acceptor, learner |-> s.learner, executor |-> s_.executor] /\ sent_packets = <<>> ELSE s_ = s /\ sent_packets = <<>>

ReplicaNextSpontaneousMaybeExecute(s, s_, sent_packets) ==
    IF s.executor.next_op_to_execute.tag = OutstandingOpKnown /\ LtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val) /\ ReplicaConstantsValid(s.executor.constants) THEN LET v == s.executor.next_op_to_execute.v
IN ProposerResetViewTimerDueToExecution(s.proposer, s_.proposer, v) /\ LearnerForgetDecision(s.learner, s_.learner, s.executor.ops_complete) /\ ExecutorExecute(s.executor, s_.executor, sent_packets) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s_.proposer, acceptor |-> s.acceptor, learner |-> s_.learner, executor |-> s_.executor] ELSE s_ = s /\ sent_packets = <<>>

ReplicaNextReadClockMaybeSendHeartbeat(s, s_, clock, sent_packets) ==
    IF clock.t < s.nextHeartbeatTime THEN s_ = s /\ sent_packets = <<>> ELSE s_.nextHeartbeatTime = UpperBoundedAddition(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val) /\ BroadcastToEveryone(s.constants.all.config, s.constants.my_index, [bal_heartbeat |-> s.proposer.election_state.current_view, suspicious |-> s.constants.my_index \in s.proposer.election_state.current_view_suspectors, opn_ckpt |-> s.executor.ops_complete], sent_packets) /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s_.nextHeartbeatTime, proposer |-> s.proposer, acceptor |-> s.acceptor, learner |-> s.learner, executor |-> s.executor]

ReplicaNextReadClockCheckForViewTimeout(s, s_, clock, sent_packets) ==
    /\ ProposerCheckForViewTimeout(s.proposer, s_.proposer, clock.t)
    /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s_.proposer, acceptor |-> s.acceptor, learner |-> s.learner, executor |-> s.executor]
    /\ sent_packets = <<>>

ReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s_, clock, sent_packets) ==
    /\ ProposerCheckForQuorumOfViewSuspicions(s.proposer, s_.proposer, clock.t)
    /\ s_ = [constants |-> s.constants, nextHeartbeatTime |-> s.nextHeartbeatTime, proposer |-> s_.proposer, acceptor |-> s.acceptor, learner |-> s.learner, executor |-> s.executor]
    /\ sent_packets = <<>>

RECURSIVE ExtractSentPacketsFromIos(_)
ExtractSentPacketsFromIos(ios) ==
    IF Len(ios) = 0 THEN <<>> ELSE IF ios[0].tag = Send THEN <<ios[0].s>> + ExtractSentPacketsFromIos(drop_first(ios)) ELSE ExtractSentPacketsFromIos(drop_first(ios))

ReplicaNextReadClockAndProcessPacket(s, s_, ios) ==
    /\ Len(ios) > 1
    /\ ios[1].tag = ReadClock
    /\ \A io \in RslIo : io \in SubSeq(ios, 2, Len(ios)) => io.tag = Send
    /\ ReplicaNextProcessHeartbeat(s, s_, ios[0].r, ios[1].t, ExtractSentPacketsFromIos(ios))

ReplicaNextProcessPacketWithoutReadingClock(s, s_, ios) ==
    LET sent_packets == ExtractSentPacketsFromIos(ios)
    IN \A io \in RslIo : io \in drop_first(ios) => io.tag = Send /\ ReplicaNextProcessInvalid(s, s_, ios[0].r, sent_packets)

ReplicaNextProcessPacket(s, s_, ios) ==
    Len(ios) >= 1 /\ IF ios[0].tag = TimeoutReceive THEN s_ = s /\ Len(ios) = 1 ELSE ios[0].tag = Receive /\ IF ios[0].r.msg.tag = RslMessageHeartbeat THEN ReplicaNextReadClockAndProcessPacket(s, s_, ios) ELSE ReplicaNextProcessPacketWithoutReadingClock(s, s_, ios)

ReplicaNumActions ==
    10

SpontaneousIos(ios, clocks) ==
    /\ clocks <= Len(ios)
    /\ \A i \in Int : (0 <= i /\ i < clocks) => ios[i].tag = ReadClock
    /\ \A i \in Int : (clocks <= i /\ i < Len(ios)) => ios[i].tag = Send

SpontaneousClock(ios) ==
    IF SpontaneousIos(ios, 1) THEN [t |-> ios[0].t] ELSE [t |-> 0]

ReplicaNoReceiveNext(s, nextActionIndex, s_, ios) ==
    LET sent_packets == ExtractSentPacketsFromIos(ios)
    IN IF nextActionIndex = 1 THEN SpontaneousIos(ios, 0) /\ ReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s, s_, sent_packets) ELSE IF nextActionIndex = 2 THEN SpontaneousIos(ios, 0) /\ ReplicaNextSpontaneousMaybeEnterPhase2(s, s_, sent_packets) ELSE IF nextActionIndex = 3 THEN SpontaneousIos(ios, 1) /\ ReplicaNextReadClockMaybeNominateValueAndSend2a(s, s_, SpontaneousClock(ios), sent_packets) ELSE IF nextActionIndex = 4 THEN SpontaneousIos(ios, 0) /\ ReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s_, sent_packets) ELSE IF nextActionIndex = 5 THEN SpontaneousIos(ios, 0) /\ ReplicaNextSpontaneousMaybeMakeDecision(s, s_, sent_packets) ELSE IF nextActionIndex = 6 THEN SpontaneousIos(ios, 0) /\ ReplicaNextSpontaneousMaybeExecute(s, s_, sent_packets) ELSE IF nextActionIndex = 7 THEN SpontaneousIos(ios, 1) /\ ReplicaNextReadClockCheckForViewTimeout(s, s_, SpontaneousClock(ios), sent_packets) ELSE IF nextActionIndex = 8 THEN SpontaneousIos(ios, 1) /\ ReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s_, SpontaneousClock(ios), sent_packets) ELSE nextActionIndex = 9 /\ SpontaneousIos(ios, 1) /\ ReplicaNextReadClockMaybeSendHeartbeat(s, s_, SpontaneousClock(ios), sent_packets)

SchedulerInit(s, c) ==
    ReplicaInit(s.replica, c) /\ s.nextActionIndex = 0

SchedulerNext(s, s_, ios) ==
    s_.nextActionIndex = (s.nextActionIndex + 1) % ReplicaNumActions /\ IF s.nextActionIndex = 0 THEN ReplicaNextProcessPacket(s.replica, s_.replica, ios) ELSE ReplicaNoReceiveNext(s.replica, s.nextActionIndex, s_.replica, ios)

====

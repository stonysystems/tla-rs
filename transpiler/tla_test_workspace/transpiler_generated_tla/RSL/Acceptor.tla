---- MODULE Acceptor ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Vote, Configuration, RslPacket, Acceptor, Votes, OperationNumber, ReplicaConstants

Acceptor ==
    [constants |-> ReplicaConstants, max_bal |-> Ballot, votes |-> Votes, last_checkpointed_operation |-> Seq(OperationNumber), log_truncation_point |-> OperationNumber]

IsLogTruncationPointValid(log_truncation_point, last_checkpointed_operation, config) ==
    IsNthHighestValueInSequence(log_truncation_point, last_checkpointed_operation, MinQuorumSize(config))

RemoveVotesBeforeLogTruncationPoint(votes, votes_, log_truncation_point) ==
    /\ \A opn \in OperationNumber : opn \in DOMAIN votes_ => (opn \in DOMAIN votes /\ votes_[opn] = votes[opn])
    /\ \A opn \in OperationNumber : opn < log_truncation_point => ~opn \in DOMAIN votes_
    /\ \A opn \in OperationNumber : (opn >= log_truncation_point /\ opn \in DOMAIN votes) => opn \in DOMAIN votes_

AddVoteAndRemoveOldOnes(votes, votes_, new_opn, new_vote, log_truncation_point) ==
    \A opn \in OperationNumber : opn \in DOMAIN votes_ <=> (opn >= log_truncation_point /\ (opn \in DOMAIN votes \/ opn = new_opn)) /\ \A opn \in OperationNumber : opn \in DOMAIN votes_ => votes_[opn] = IF opn = new_opn THEN new_vote ELSE votes[opn]

AcceptorInit(a, c) ==
    /\ a.constants = c
    /\ a.max_bal = [seqno |-> 0, proposer_id |-> 0]
    /\ a.votes = <<>>
    /\ Len(a.last_checkpointed_operation) = Len(c.all.config.replica_ids)
    /\ \A idx \in Int : (0 <= idx /\ idx < Len(a.last_checkpointed_operation)) => a.last_checkpointed_operation[idx] = 0
    /\ a.log_truncation_point = 0

AcceptorProcess1a(s, s_, inp, sent_packets) ==
    LET m == inp.msg
    IN LET bal == inp.msg.bal_1a
IN IF inp.src \in s.constants.all.config.replica_ids /\ BalLt(s.max_bal, bal) /\ ReplicaConstantsValid(s.constants) THEN sent_packets = <<[src |-> s.constants.all.config.replica_ids[s.constants.my_index], dst |-> inp.src, msg |-> [bal_1b |-> bal, log_truncation_point |-> s.log_truncation_point, votes |-> s.votes]]>> /\ s_ = [constants |-> s.constants, max_bal |-> bal, votes |-> s.votes, last_checkpointed_operation |-> s.last_checkpointed_operation, log_truncation_point |-> s.log_truncation_point] ELSE s_ = s /\ sent_packets = <<>>

AcceptorProcess2a(s, s_, inp, sent_packets) ==
    LET m == inp.msg
    IN LET newLogTruncationPoint == IF inp.msg.opn_2a - s.constants.all.params.max_log_length + 1 > s.log_truncation_point THEN inp.msg.opn_2a - s.constants.all.params.max_log_length + 1 ELSE s.log_truncation_point
IN BroadcastToEveryone(s.constants.all.config, s.constants.my_index, [bal_2b |-> m.bal_2a, opn_2b |-> m.opn_2a, val_2b |-> m.val_2a], sent_packets) /\ s_.max_bal = m.bal_2a /\ s_.log_truncation_point = newLogTruncationPoint /\ IF s.log_truncation_point <= m.opn_2a THEN AddVoteAndRemoveOldOnes(s.votes, s_.votes, m.opn_2a, [max_value_bal |-> m.bal_2a, max_val |-> m.val_2a], newLogTruncationPoint) ELSE s_.votes = s.votes /\ s_.constants = s.constants /\ s_.last_checkpointed_operation = s.last_checkpointed_operation

AcceptorProcessHeartbeat(s, s_, inp) ==
    IF inp.src \in s.constants.all.config.replica_ids THEN LET sender_index == GetReplicaIndex(inp.src, s.constants.all.config)
IN IF 0 <= sender_index /\ sender_index < Len(s.last_checkpointed_operation) /\ inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index] THEN s_.last_checkpointed_operation = update(s.last_checkpointed_operation, sender_index, inp.msg.opn_ckpt) /\ s_.constants = s.constants /\ s_.max_bal = s.max_bal /\ s_.votes = s.votes /\ s_.log_truncation_point = s.log_truncation_point ELSE s_ = s ELSE s_ = s

AcceptorTruncateLog(s, s_, opn) ==
    IF opn <= s.log_truncation_point THEN s_ = s ELSE s_ = [constants |-> s.constants, max_bal |-> s.max_bal, votes |-> s_.votes, last_checkpointed_operation |-> s.last_checkpointed_operation, log_truncation_point |-> opn] /\ RemoveVotesBeforeLogTruncationPoint(s.votes, s_.votes, opn)

====

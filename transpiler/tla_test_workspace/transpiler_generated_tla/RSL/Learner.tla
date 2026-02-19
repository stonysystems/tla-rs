---- MODULE Learner ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ReplicaConstants, RslPacket, Learner, OperationNumber

Learner ==
    [constants |-> ReplicaConstants, max_ballot_seen |-> Ballot, unexecuted_learner_state |-> earnerState]

LearnerInit(l, c) ==
    /\ l.constants = c
    /\ l.max_ballot_seen = [seqno |-> 0, proposer_id |-> 0]
    /\ l.unexecuted_learner_state = <<>>

LearnerProcess2b(s, s_, packet) ==
    LET m == packet.msg
    IN LET opn == m.opn_2b
IN IF ~packet.src \in s.constants.all.config.replica_ids \/ BalLt(m.bal_2b, s.max_ballot_seen) THEN s_ = s ELSE IF BalLt(s.max_ballot_seen, m.bal_2b) THEN LET tup_ == [received_2b_message_senders |-> {packet.src}, candidate_learned_value |-> m.val_2b]
IN s_ = [constants |-> s.constants, max_ballot_seen |-> m.bal_2b, unexecuted_learner_state |-> {<<opn, tup_>>}] ELSE IF ~opn \in DOMAIN s.unexecuted_learner_state THEN LET tup_ == [received_2b_message_senders |-> {packet.src}, candidate_learned_value |-> m.val_2b]
IN s_ = [constants |-> s.constants, max_ballot_seen |-> m.bal_2b, unexecuted_learner_state |-> [s.unexecuted_learner_state EXCEPT ![opn] = tup_]] ELSE IF packet.src \in s.unexecuted_learner_state[opn].received_2b_message_senders THEN s_ = s ELSE LET tup == s.unexecuted_learner_state[opn]
IN LET tup_ == [received_2b_message_senders |-> tup.received_2b_message_senders + {packet.src}, candidate_learned_value |-> tup.candidate_learned_value]
IN s_ = [constants |-> s.constants, max_ballot_seen |-> s.max_ballot_seen, unexecuted_learner_state |-> [s.unexecuted_learner_state EXCEPT ![opn] = tup_]]

LearnerForgetDecision(s, s_, opn) ==
    IF opn \in DOMAIN s.unexecuted_learner_state THEN s_ = [constants |-> s.constants, max_ballot_seen |-> s.max_ballot_seen, unexecuted_learner_state |-> s.unexecuted_learner_state \ {opn}] ELSE s_ = s

LearnerForgetOperationsBefore(s, s_, ops_complete) ==
    /\ \A k \in OperationNumber : k \in DOMAIN s_.unexecuted_learner_state <=> (k >= ops_complete /\ k \in DOMAIN s.unexecuted_learner_state)
    /\ \A k \in OperationNumber : k \in DOMAIN s_.unexecuted_learner_state => s_.unexecuted_learner_state[k] = s.unexecuted_learner_state[k]
    /\ s_ = [constants |-> s.constants, max_ballot_seen |-> s.max_ballot_seen, unexecuted_learner_state |-> s_.unexecuted_learner_state]

====

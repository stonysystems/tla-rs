---- MODULE Types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Ballot

Ballot ==
    [seqno |-> Int, proposer_id |-> Int]

Vote ==
    [max_value_bal |-> Ballot, max_val |-> Seq(Request)]

Reply ==
    [client |-> AbstractEndPoint, seqno |-> Int, reply |-> AppMessage]

LearnerTuple ==
    [received_2b_message_senders |-> SUBSET AbstractEndPoint, candidate_learned_value |-> Seq(Request)]

Request ==
    [client |-> AbstractEndPoint, seqno |-> Int, request |-> AppMessage]

ClockReading ==
    [t |-> Int]

BalLeq(ba, bb) ==
    ba.seqno < bb.seqno \/ (ba.seqno = bb.seqno /\ ba.proposer_id <= bb.proposer_id)

====

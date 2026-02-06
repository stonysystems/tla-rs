---- MODULE types ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Ballot

Request ==
    [client |-> AbstractEndPoint, seqno |-> Int, request |-> AppMessage]

Ballot ==
    [seqno |-> Int, proposer_id |-> Int]

ClockReading ==
    [t |-> Int]

Reply ==
    [client |-> AbstractEndPoint, seqno |-> Int, reply |-> AppMessage]

Vote ==
    [max_value_bal |-> Ballot, max_val |-> Seq(Request)]

LearnerTuple ==
    [received_2b_message_senders |-> SUBSET AbstractEndPoint, candidate_learned_value |-> Seq(Request)]

BalLeq(ba, bb) ==
    ba.seqno < bb.seqno \/ (ba.seqno = bb.seqno /\ ba.proposer_id <= bb.proposer_id)

====

---- MODULE Paxos ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS State, Constants

Init(s, c) ==
    /\ s.promised_bal = 0
    /\ s.accepted_bal = 0
    /\ s.accepted_val = 0
    /\ s.proposer_bal = 0
    /\ s.phase.tag = Idle
    /\ s.promises_rcvd = {}
    /\ s.highest_accepted_bal = 0
    /\ s.highest_accepted_val = 0
    /\ s.proposed_val = 0
    /\ s.accepts_rcvd = {}
    /\ s.decided_val = 0

Send1a(s, s_, c, b) ==
    /\ s.phase.tag = Idle
    /\ b > s.proposer_bal
    /\ s_.proposer_bal = b
    /\ s_.phase.tag = Phase1
    /\ s_.promises_rcvd = {}
    /\ s_.highest_accepted_bal = 0
    /\ s_.highest_accepted_val = 0
    /\ s_.proposed_val = s.proposed_val
    /\ s_.promised_bal = s.promised_bal
    /\ s_.accepted_bal = s.accepted_bal
    /\ s_.accepted_val = s.accepted_val
    /\ s_.accepts_rcvd = s.accepts_rcvd
    /\ s_.decided_val = s.decided_val

Send1b(s, s_, c, b) ==
    /\ b >= s.promised_bal
    /\ s_.promised_bal = b
    /\ s_.accepted_bal = s.accepted_bal
    /\ s_.accepted_val = s.accepted_val
    /\ s_.proposer_bal = s.proposer_bal
    /\ s_.phase = s.phase
    /\ s_.promises_rcvd = s.promises_rcvd
    /\ s_.highest_accepted_bal = s.highest_accepted_bal
    /\ s_.highest_accepted_val = s.highest_accepted_val
    /\ s_.proposed_val = s.proposed_val
    /\ s_.accepts_rcvd = s.accepts_rcvd
    /\ s_.decided_val = s.decided_val

RecvPromise(s, s_, c, a, a_accepted_bal, a_accepted_val) ==
    /\ s.phase.tag = Phase1
    /\ a \in c.acceptors
    /\ ~a \in s.promises_rcvd
    /\ s_.promises_rcvd = s.promises_rcvd \cup {a}
    /\ s_.highest_accepted_bal = IF a_accepted_bal > s.highest_accepted_bal THEN a_accepted_bal ELSE s.highest_accepted_bal
    /\ s_.highest_accepted_val = IF a_accepted_bal > s.highest_accepted_bal THEN a_accepted_val ELSE s.highest_accepted_val
    /\ s_.proposer_bal = s.proposer_bal
    /\ s_.phase.tag = Phase1
    /\ s_.proposed_val = s.proposed_val
    /\ s_.promised_bal = s.promised_bal
    /\ s_.accepted_bal = s.accepted_bal
    /\ s_.accepted_val = s.accepted_val
    /\ s_.accepts_rcvd = s.accepts_rcvd
    /\ s_.decided_val = s.decided_val

Send2a(s, s_, c, v) ==
    /\ s.phase.tag = Phase1
    /\ Len(s.promises_rcvd) >= c.quorum_size
    /\ s_.proposed_val = IF s.highest_accepted_bal > 0 THEN s.highest_accepted_val ELSE v
    /\ s_.phase.tag = Phase2
    /\ s_.accepts_rcvd = {}
    /\ s_.proposer_bal = s.proposer_bal
    /\ s_.promises_rcvd = s.promises_rcvd
    /\ s_.highest_accepted_bal = s.highest_accepted_bal
    /\ s_.highest_accepted_val = s.highest_accepted_val
    /\ s_.promised_bal = s.promised_bal
    /\ s_.accepted_bal = s.accepted_bal
    /\ s_.accepted_val = s.accepted_val
    /\ s_.decided_val = s.decided_val

Send2b(s, s_, c, b, v) ==
    /\ b >= s.promised_bal
    /\ s_.promised_bal = b
    /\ s_.accepted_bal = b
    /\ s_.accepted_val = v
    /\ s_.proposer_bal = s.proposer_bal
    /\ s_.phase = s.phase
    /\ s_.promises_rcvd = s.promises_rcvd
    /\ s_.highest_accepted_bal = s.highest_accepted_bal
    /\ s_.highest_accepted_val = s.highest_accepted_val
    /\ s_.proposed_val = s.proposed_val
    /\ s_.accepts_rcvd = s.accepts_rcvd
    /\ s_.decided_val = s.decided_val

RecvAccepted(s, s_, c, a) ==
    /\ s.phase.tag = Phase2
    /\ a \in c.acceptors
    /\ ~a \in s.accepts_rcvd
    /\ s_.accepts_rcvd = s.accepts_rcvd \cup {a}
    /\ s_.proposer_bal = s.proposer_bal
    /\ s_.phase.tag = Phase2
    /\ s_.promises_rcvd = s.promises_rcvd
    /\ s_.highest_accepted_bal = s.highest_accepted_bal
    /\ s_.highest_accepted_val = s.highest_accepted_val
    /\ s_.proposed_val = s.proposed_val
    /\ s_.promised_bal = s.promised_bal
    /\ s_.accepted_bal = s.accepted_bal
    /\ s_.accepted_val = s.accepted_val
    /\ s_.decided_val = s.decided_val

Learn(s, s_, c) ==
    /\ s.phase.tag = Phase2
    /\ Len(s.accepts_rcvd) >= c.quorum_size
    /\ s_.phase.tag = Decided
    /\ s_.decided_val = s.proposed_val
    /\ s_.proposer_bal = s.proposer_bal
    /\ s_.promises_rcvd = s.promises_rcvd
    /\ s_.highest_accepted_bal = s.highest_accepted_bal
    /\ s_.highest_accepted_val = s.highest_accepted_val
    /\ s_.proposed_val = s.proposed_val
    /\ s_.accepts_rcvd = s.accepts_rcvd
    /\ s_.promised_bal = s.promised_bal
    /\ s_.accepted_bal = s.accepted_bal
    /\ s_.accepted_val = s.accepted_val

Next(s, s_, c) ==
    \/ \E b \in Int : Send1a(s, s_, c, b)
    \/ \E b \in Int : Send1b(s, s_, c, b)
    \/ \E a \in Int, ab \in Int, av \in Int : RecvPromise(s, s_, c, a, ab, av)
    \/ \E v \in Int : Send2a(s, s_, c, v)
    \/ \E b \in Int, v \in Int : Send2b(s, s_, c, b, v)
    \/ \E a \in Int : RecvAccepted(s, s_, c, a)
    \/ Learn(s, s_, c)

====

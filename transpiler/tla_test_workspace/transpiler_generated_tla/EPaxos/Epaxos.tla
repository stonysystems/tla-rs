---- MODULE Epaxos ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS EPaxosMessage, State, Constants

Init(s, c) ==
    /\ s.ballot = 0
    /\ s.phase.tag = Empty
    /\ s.cmd = 0
    /\ s.seq = 0
    /\ s.dep_count = 0
    /\ s.is_leader = FALSE
    /\ s.committed_count = 0
    /\ s.executed_count = 0
    /\ s.preaccept_senders = {}
    /\ s.accept_senders = {}
    /\ s.has_conflict = FALSE
    /\ s.max_resp_seq = 0
    /\ c.num_replicas >= 3
    /\ c.quorum_size > 0
    /\ c.fast_quorum_size >= c.quorum_size

Propose(s, s_, c, value, sent_packets) ==
    /\ s.phase.tag = Empty
    /\ s_.ballot = s.ballot
    /\ s_.phase.tag = PreAccepted
    /\ s_.cmd = value
    /\ s_.seq = s.committed_count + 1
    /\ s_.dep_count = 0
    /\ s_.is_leader = TRUE
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count
    /\ s_.preaccept_senders = {} \cup {c.my_id}
    /\ s_.accept_senders = {}
    /\ s_.has_conflict = FALSE
    /\ s_.max_resp_seq = 0
    /\ sent_packets = <<[ballot |-> s.ballot, cmd |-> value, seq |-> s.committed_count + 1]>>

SendPreAcceptOk(s, s_, c, local_conflict, local_seq, sent_packets) ==
    /\ sent_packets = <<[sender |-> c.my_id, seq |-> local_seq, conflict |-> local_conflict]>>
    /\ s_.ballot = s.ballot
    /\ s_.phase = s.phase
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = s.dep_count
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count
    /\ s_.preaccept_senders = s.preaccept_senders
    /\ s_.accept_senders = s.accept_senders
    /\ s_.has_conflict = s.has_conflict
    /\ s_.max_resp_seq = s.max_resp_seq

ReceivePreAcceptOk(s, s_, c, pa_sender, pa_seq, pa_conflict, sent_packets) ==
    /\ s.phase.tag = PreAccepted
    /\ s.is_leader = TRUE
    /\ ~pa_sender \in s.preaccept_senders
    /\ s_.preaccept_senders = s.preaccept_senders \cup {pa_sender}
    /\ s_.has_conflict = IF pa_conflict THEN TRUE ELSE s.has_conflict
    /\ s_.dep_count = IF pa_conflict THEN s.dep_count + 1 ELSE s.dep_count
    /\ s_.max_resp_seq = IF pa_seq > s.max_resp_seq THEN pa_seq ELSE s.max_resp_seq
    /\ s_.seq = IF pa_seq > s.seq THEN pa_seq ELSE s.seq
    /\ sent_packets = <<>>
    /\ s_.ballot = s.ballot
    /\ s_.phase = s.phase
    /\ s_.cmd = s.cmd
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count
    /\ s_.accept_senders = s.accept_senders

FastCommit(s, s_, c, sent_packets) ==
    /\ s.phase.tag = PreAccepted
    /\ s.is_leader = TRUE
    /\ Len(s.preaccept_senders) >= c.fast_quorum_size
    /\ s.has_conflict = FALSE
    /\ s_.ballot = s.ballot
    /\ s_.phase.tag = Committed
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = s.dep_count
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count + 1
    /\ s_.executed_count = s.executed_count
    /\ s_.preaccept_senders = s.preaccept_senders
    /\ s_.accept_senders = s.accept_senders
    /\ s_.has_conflict = s.has_conflict
    /\ s_.max_resp_seq = s.max_resp_seq
    /\ sent_packets = <<[cmd |-> s.cmd, seq |-> s.seq]>>

StartAccept(s, s_, c, sent_packets) ==
    /\ s.phase.tag = PreAccepted
    /\ s.is_leader = TRUE
    /\ Len(s.preaccept_senders) >= c.quorum_size
    /\ s.has_conflict = TRUE
    /\ s_.ballot = s.ballot
    /\ s_.phase.tag = Accepted
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = s.dep_count
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count
    /\ s_.preaccept_senders = s.preaccept_senders
    /\ s_.accept_senders = {} \cup {c.my_id}
    /\ s_.has_conflict = s.has_conflict
    /\ s_.max_resp_seq = s.max_resp_seq
    /\ sent_packets = <<[ballot |-> s.ballot, cmd |-> s.cmd, seq |-> s.seq]>>

SendAcceptOk(s, s_, c, sent_packets) ==
    /\ sent_packets = <<[sender |-> c.my_id]>>
    /\ s_.ballot = s.ballot
    /\ s_.phase = s.phase
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = s.dep_count
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count
    /\ s_.preaccept_senders = s.preaccept_senders
    /\ s_.accept_senders = s.accept_senders
    /\ s_.has_conflict = s.has_conflict
    /\ s_.max_resp_seq = s.max_resp_seq

ReceiveAcceptOk(s, s_, c, ao_sender, sent_packets) ==
    /\ s.phase.tag = Accepted
    /\ s.is_leader = TRUE
    /\ ~ao_sender \in s.accept_senders
    /\ s_.accept_senders = s.accept_senders \cup {ao_sender}
    /\ sent_packets = <<>>
    /\ s_.ballot = s.ballot
    /\ s_.phase = s.phase
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = s.dep_count
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count
    /\ s_.preaccept_senders = s.preaccept_senders
    /\ s_.has_conflict = s.has_conflict
    /\ s_.max_resp_seq = s.max_resp_seq

SlowCommit(s, s_, c, sent_packets) ==
    /\ s.phase.tag = Accepted
    /\ s.is_leader = TRUE
    /\ Len(s.accept_senders) >= c.quorum_size
    /\ s_.ballot = s.ballot
    /\ s_.phase.tag = Committed
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = s.dep_count
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count + 1
    /\ s_.executed_count = s.executed_count
    /\ s_.preaccept_senders = s.preaccept_senders
    /\ s_.accept_senders = s.accept_senders
    /\ s_.has_conflict = s.has_conflict
    /\ s_.max_resp_seq = s.max_resp_seq
    /\ sent_packets = <<[cmd |-> s.cmd, seq |-> s.seq]>>

Execute(s, s_, c, sent_packets) ==
    /\ s.phase.tag = Committed
    /\ s_.ballot = s.ballot
    /\ s_.phase.tag = Executed
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = s.dep_count
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count + 1
    /\ s_.preaccept_senders = s.preaccept_senders
    /\ s_.accept_senders = s.accept_senders
    /\ s_.has_conflict = s.has_conflict
    /\ s_.max_resp_seq = s.max_resp_seq
    /\ sent_packets = <<>>

Recover(s, s_, c, new_ballot, sent_packets) ==
    /\ s.phase.tag = PreAccepted \/ s.phase.tag = Accepted
    /\ new_ballot > s.ballot
    /\ s_.ballot = new_ballot
    /\ s_.phase.tag = PreAccepted
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = 0
    /\ s_.is_leader = TRUE
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count
    /\ s_.preaccept_senders = {} \cup {c.my_id}
    /\ s_.accept_senders = {}
    /\ s_.has_conflict = FALSE
    /\ s_.max_resp_seq = 0
    /\ sent_packets = <<[ballot |-> new_ballot, cmd |-> s.cmd, seq |-> s.seq]>>

NewInstance(s, s_, c, sent_packets) ==
    /\ s.phase.tag = Executed
    /\ s_.ballot = s.ballot
    /\ s_.phase.tag = Empty
    /\ s_.cmd = 0
    /\ s_.seq = 0
    /\ s_.dep_count = 0
    /\ s_.is_leader = FALSE
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count
    /\ s_.preaccept_senders = {}
    /\ s_.accept_senders = {}
    /\ s_.has_conflict = FALSE
    /\ s_.max_resp_seq = 0
    /\ sent_packets = <<>>

Next(s, s_, c) ==
    \/ \E value \in Int, sent_packets \in Seq(EPaxosMessage) : Propose(s, s_, c, value, sent_packets)
    \/ \E local_conflict \in BOOLEAN, local_seq \in Int, sent_packets \in Seq(EPaxosMessage) : SendPreAcceptOk(s, s_, c, local_conflict, local_seq, sent_packets)
    \/ \E pa_sender \in Int, pa_seq \in Int, pa_conflict \in BOOLEAN, sent_packets \in Seq(EPaxosMessage) : ReceivePreAcceptOk(s, s_, c, pa_sender, pa_seq, pa_conflict, sent_packets)
    \/ \E sent_packets \in Seq(EPaxosMessage) : FastCommit(s, s_, c, sent_packets)
    \/ \E sent_packets \in Seq(EPaxosMessage) : StartAccept(s, s_, c, sent_packets)
    \/ \E sent_packets \in Seq(EPaxosMessage) : SendAcceptOk(s, s_, c, sent_packets)
    \/ \E ao_sender \in Int, sent_packets \in Seq(EPaxosMessage) : ReceiveAcceptOk(s, s_, c, ao_sender, sent_packets)
    \/ \E sent_packets \in Seq(EPaxosMessage) : SlowCommit(s, s_, c, sent_packets)
    \/ \E sent_packets \in Seq(EPaxosMessage) : Execute(s, s_, c, sent_packets)
    \/ \E new_ballot \in Int, sent_packets \in Seq(EPaxosMessage) : Recover(s, s_, c, new_ballot, sent_packets)
    \/ \E sent_packets \in Seq(EPaxosMessage) : NewInstance(s, s_, c, sent_packets)

====

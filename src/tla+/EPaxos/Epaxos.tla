---- MODULE epaxos ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS State, Constants

Init(s, c) ==
    /\ s.ballot = 0
    /\ s.phase.tag = Empty
    /\ s.cmd = 0
    /\ s.seq = 0
    /\ s.dep_count = 0
    /\ s.preaccept_count = 0
    /\ s.accept_count = 0
    /\ s.is_leader = FALSE
    /\ s.committed_count = 0
    /\ s.executed_count = 0
    /\ c.num_replicas >= 3
    /\ c.quorum_size > 0
    /\ c.fast_quorum_size >= c.quorum_size

Propose(s, s_, c, value) ==
    /\ s.phase.tag = Empty
    /\ s_.ballot = s.ballot
    /\ s_.phase.tag = PreAccepted
    /\ s_.cmd = value
    /\ s_.seq = s.committed_count + 1
    /\ s_.dep_count = 0
    /\ s_.preaccept_count = 1
    /\ s_.accept_count = 0
    /\ s_.is_leader = TRUE
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count

ReceivePreAccept(s, s_, c, has_conflict) ==
    /\ s.phase.tag = PreAccepted
    /\ s.is_leader = TRUE
    /\ s.preaccept_count < c.num_replicas
    /\ s_.ballot = s.ballot
    /\ s_.phase = s.phase
    /\ s_.cmd = s.cmd
    /\ s_.seq = IF has_conflict /\ s.seq <= s.committed_count THEN s.seq + 1 ELSE s.seq
    /\ s_.dep_count = IF has_conflict THEN s.dep_count + 1 ELSE s.dep_count
    /\ s_.preaccept_count = s.preaccept_count + 1
    /\ s_.accept_count = s.accept_count
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count

FastCommit(s, s_, c) ==
    /\ s.phase.tag = PreAccepted
    /\ s.is_leader = TRUE
    /\ s.preaccept_count >= c.fast_quorum_size
    /\ s.dep_count = 0
    /\ s_.ballot = s.ballot
    /\ s_.phase.tag = Committed
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = s.dep_count
    /\ s_.preaccept_count = s.preaccept_count
    /\ s_.accept_count = s.accept_count
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count + 1
    /\ s_.executed_count = s.executed_count

StartAccept(s, s_, c) ==
    /\ s.phase.tag = PreAccepted
    /\ s.is_leader = TRUE
    /\ s.preaccept_count >= c.quorum_size
    /\ s.dep_count > 0
    /\ s_.ballot = s.ballot
    /\ s_.phase.tag = Accepted
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = s.dep_count
    /\ s_.preaccept_count = s.preaccept_count
    /\ s_.accept_count = 1
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count

ReceiveAccept(s, s_, c) ==
    /\ s.phase.tag = Accepted
    /\ s.is_leader = TRUE
    /\ s.accept_count < c.num_replicas
    /\ s_.ballot = s.ballot
    /\ s_.phase = s.phase
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = s.dep_count
    /\ s_.preaccept_count = s.preaccept_count
    /\ s_.accept_count = s.accept_count + 1
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count

SlowCommit(s, s_, c) ==
    /\ s.phase.tag = Accepted
    /\ s.is_leader = TRUE
    /\ s.accept_count >= c.quorum_size
    /\ s_.ballot = s.ballot
    /\ s_.phase.tag = Committed
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = s.dep_count
    /\ s_.preaccept_count = s.preaccept_count
    /\ s_.accept_count = s.accept_count
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count + 1
    /\ s_.executed_count = s.executed_count

Execute(s, s_, c) ==
    /\ s.phase.tag = Committed
    /\ s_.ballot = s.ballot
    /\ s_.phase.tag = Executed
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = s.dep_count
    /\ s_.preaccept_count = s.preaccept_count
    /\ s_.accept_count = s.accept_count
    /\ s_.is_leader = s.is_leader
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count + 1

Recover(s, s_, c, new_ballot) ==
    /\ s.phase.tag = PreAccepted \/ s.phase.tag = Accepted
    /\ new_ballot > s.ballot
    /\ s_.ballot = new_ballot
    /\ s_.phase.tag = PreAccepted
    /\ s_.cmd = s.cmd
    /\ s_.seq = s.seq
    /\ s_.dep_count = 0
    /\ s_.preaccept_count = 1
    /\ s_.accept_count = 0
    /\ s_.is_leader = TRUE
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count

NewInstance(s, s_, c) ==
    /\ s.phase.tag = Executed
    /\ s_.ballot = s.ballot
    /\ s_.phase.tag = Empty
    /\ s_.cmd = 0
    /\ s_.seq = 0
    /\ s_.dep_count = 0
    /\ s_.preaccept_count = 0
    /\ s_.accept_count = 0
    /\ s_.is_leader = FALSE
    /\ s_.committed_count = s.committed_count
    /\ s_.executed_count = s.executed_count

Next(s, s_, c) ==
    \/ \E value \in Int : Propose(s, s_, c, value)
    \/ \E has_conflict \in BOOLEAN : ReceivePreAccept(s, s_, c, has_conflict)
    \/ FastCommit(s, s_, c)
    \/ StartAccept(s, s_, c)
    \/ ReceiveAccept(s, s_, c)
    \/ SlowCommit(s, s_, c)
    \/ Execute(s, s_, c)
    \/ \E new_ballot \in Int : Recover(s, s_, c, new_ballot)
    \/ NewInstance(s, s_, c)

====

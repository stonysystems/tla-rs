---- MODULE Pbft ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS State, Constants

Init(s, c) ==
    /\ s.view = 0
    /\ s.phase.tag = PrePrepare
    /\ s.prepare_count = 0
    /\ s.commit_count = 0
    /\ s.seq_num = 0
    /\ s.is_primary = TRUE
    /\ c.n >= (3 * c.f) + 1
    /\ c.f >= 0

PrePrepare(s, s_, c) ==
    /\ s.phase.tag = PrePrepare
    /\ s.is_primary = TRUE
    /\ s_.phase.tag = Prepare
    /\ s_.view = s.view
    /\ s_.prepare_count = 1
    /\ s_.commit_count = 0
    /\ s_.seq_num = s.seq_num
    /\ s_.is_primary = s.is_primary

ReceivePrepare(s, s_, c) ==
    /\ s.phase.tag = Prepare
    /\ s.prepare_count < c.n
    /\ s_.phase = s.phase
    /\ s_.view = s.view
    /\ s_.prepare_count = s.prepare_count + 1
    /\ s_.commit_count = s.commit_count
    /\ s_.seq_num = s.seq_num
    /\ s_.is_primary = s.is_primary

EnterCommit(s, s_, c) ==
    /\ s.phase.tag = Prepare
    /\ s.prepare_count >= (2 * c.f) + 1
    /\ s_.phase.tag = Commit
    /\ s_.view = s.view
    /\ s_.prepare_count = s.prepare_count
    /\ s_.commit_count = 1
    /\ s_.seq_num = s.seq_num
    /\ s_.is_primary = s.is_primary

ReceiveCommit(s, s_, c) ==
    /\ s.phase.tag = Commit
    /\ s.commit_count < c.n
    /\ s_.phase = s.phase
    /\ s_.view = s.view
    /\ s_.prepare_count = s.prepare_count
    /\ s_.commit_count = s.commit_count + 1
    /\ s_.seq_num = s.seq_num
    /\ s_.is_primary = s.is_primary

ExecuteReply(s, s_, c) ==
    /\ s.phase.tag = Commit
    /\ s.commit_count >= (2 * c.f) + 1
    /\ s_.phase.tag = Replied
    /\ s_.view = s.view
    /\ s_.prepare_count = 0
    /\ s_.commit_count = 0
    /\ s_.seq_num = s.seq_num + 1
    /\ s_.is_primary = s.is_primary

ViewChange(s, s_, c) ==
    /\ s_.view = s.view + 1
    /\ s_.phase.tag = PrePrepare
    /\ s_.prepare_count = 0
    /\ s_.commit_count = 0
    /\ s_.seq_num = s.seq_num
    /\ s_.is_primary = s.is_primary

NewRound(s, s_, c) ==
    /\ s.phase.tag = Replied
    /\ s_.phase.tag = PrePrepare
    /\ s_.view = s.view
    /\ s_.prepare_count = 0
    /\ s_.commit_count = 0
    /\ s_.seq_num = s.seq_num
    /\ s_.is_primary = s.is_primary

Next(s, s_, c) ==
    \/ PrePrepare(s, s_, c)
    \/ ReceivePrepare(s, s_, c)
    \/ EnterCommit(s, s_, c)
    \/ ReceiveCommit(s, s_, c)
    \/ ExecuteReply(s, s_, c)
    \/ ViewChange(s, s_, c)
    \/ NewRound(s, s_, c)

====

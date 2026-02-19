---- MODULE Pbft ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS PBFTMessage, Constants, State

Init(s, c) ==
    /\ s.view = 0
    /\ s.phase.tag = PrePrepare
    /\ s.prepare_senders = {}
    /\ s.commit_senders = {}
    /\ s.seq_num = 0
    /\ s.is_primary = TRUE
    /\ s.request_digest = 0
    /\ s.checkpoint_seq = 0
    /\ s.checkpoint_digest = 0
    /\ s.low_watermark = 0
    /\ s.high_watermark = c.checkpoint_interval
    /\ c.n >= (3 * c.f) + 1
    /\ c.f >= 0
    /\ c.checkpoint_interval > 0

PrePrepare(s, s_, c, digest, sent_packets) ==
    /\ s.phase.tag = PrePrepare
    /\ s.is_primary = TRUE
    /\ s.seq_num >= s.low_watermark
    /\ s.seq_num < s.high_watermark
    /\ s_.phase.tag = Prepare
    /\ s_.request_digest = digest
    /\ s_.prepare_senders = {} \cup {c.node_id}
    /\ s_.commit_senders = {}
    /\ s_.view = s.view
    /\ s_.seq_num = s.seq_num
    /\ s_.is_primary = s.is_primary
    /\ s_.checkpoint_seq = s.checkpoint_seq
    /\ s_.checkpoint_digest = s.checkpoint_digest
    /\ s_.low_watermark = s.low_watermark
    /\ s_.high_watermark = s.high_watermark
    /\ sent_packets = <<[view |-> s.view, seq |-> s.seq_num, digest |-> digest]>>

ReceivePrePrepare(s, s_, c, view, seq, digest, sent_packets) ==
    /\ s.phase.tag = PrePrepare
    /\ s.is_primary = FALSE
    /\ view = s.view
    /\ s_.phase.tag = Prepare
    /\ s_.request_digest = digest
    /\ s_.prepare_senders = {} \cup {c.node_id}
    /\ s_.commit_senders = {}
    /\ s_.view = s.view
    /\ s_.seq_num = seq
    /\ s_.is_primary = s.is_primary
    /\ s_.checkpoint_seq = s.checkpoint_seq
    /\ s_.checkpoint_digest = s.checkpoint_digest
    /\ s_.low_watermark = s.low_watermark
    /\ s_.high_watermark = s.high_watermark
    /\ sent_packets = <<>>

ReceivePrepare(s, s_, c, sender, sent_packets) ==
    /\ s.phase.tag = Prepare
    /\ ~sender \in s.prepare_senders
    /\ s_.prepare_senders = s.prepare_senders \cup {sender}
    /\ s_.phase = s.phase
    /\ s_.view = s.view
    /\ s_.commit_senders = s.commit_senders
    /\ s_.seq_num = s.seq_num
    /\ s_.is_primary = s.is_primary
    /\ s_.request_digest = s.request_digest
    /\ s_.checkpoint_seq = s.checkpoint_seq
    /\ s_.checkpoint_digest = s.checkpoint_digest
    /\ s_.low_watermark = s.low_watermark
    /\ s_.high_watermark = s.high_watermark
    /\ sent_packets = <<>>

EnterCommit(s, s_, c, sent_packets) ==
    /\ s.phase.tag = Prepare
    /\ Len(s.prepare_senders) >= (2 * c.f) + 1
    /\ s_.phase.tag = Commit
    /\ s_.commit_senders = {} \cup {c.node_id}
    /\ s_.view = s.view
    /\ s_.prepare_senders = s.prepare_senders
    /\ s_.seq_num = s.seq_num
    /\ s_.is_primary = s.is_primary
    /\ s_.request_digest = s.request_digest
    /\ s_.checkpoint_seq = s.checkpoint_seq
    /\ s_.checkpoint_digest = s.checkpoint_digest
    /\ s_.low_watermark = s.low_watermark
    /\ s_.high_watermark = s.high_watermark
    /\ sent_packets = <<>>

ReceiveCommit(s, s_, c, sender, sent_packets) ==
    /\ s.phase.tag = Commit
    /\ ~sender \in s.commit_senders
    /\ s_.commit_senders = s.commit_senders \cup {sender}
    /\ s_.phase = s.phase
    /\ s_.view = s.view
    /\ s_.prepare_senders = s.prepare_senders
    /\ s_.seq_num = s.seq_num
    /\ s_.is_primary = s.is_primary
    /\ s_.request_digest = s.request_digest
    /\ s_.checkpoint_seq = s.checkpoint_seq
    /\ s_.checkpoint_digest = s.checkpoint_digest
    /\ s_.low_watermark = s.low_watermark
    /\ s_.high_watermark = s.high_watermark
    /\ sent_packets = <<>>

ExecuteReply(s, s_, c, sent_packets) ==
    /\ s.phase.tag = Commit
    /\ Len(s.commit_senders) >= (2 * c.f) + 1
    /\ s_.phase.tag = Replied
    /\ s_.seq_num = s.seq_num + 1
    /\ s_.prepare_senders = {}
    /\ s_.commit_senders = {}
    /\ s_.view = s.view
    /\ s_.is_primary = s.is_primary
    /\ s_.request_digest = s.request_digest
    /\ s_.checkpoint_seq = s.checkpoint_seq
    /\ s_.checkpoint_digest = s.checkpoint_digest
    /\ s_.low_watermark = s.low_watermark
    /\ s_.high_watermark = s.high_watermark
    /\ sent_packets = <<>>

Checkpoint(s, s_, c, digest, sent_packets) ==
    /\ s.phase.tag = Replied
    /\ s.seq_num > s.checkpoint_seq
    /\ s_.checkpoint_seq = s.seq_num
    /\ s_.checkpoint_digest = digest
    /\ s_.low_watermark = s.seq_num
    /\ s_.high_watermark = s.seq_num + c.checkpoint_interval
    /\ s_.view = s.view
    /\ s_.phase = s.phase
    /\ s_.prepare_senders = s.prepare_senders
    /\ s_.commit_senders = s.commit_senders
    /\ s_.seq_num = s.seq_num
    /\ s_.is_primary = s.is_primary
    /\ s_.request_digest = s.request_digest
    /\ sent_packets = <<>>

ViewChange(s, s_, c, sent_packets) ==
    /\ s_.view = s.view + 1
    /\ s_.phase.tag = PrePrepare
    /\ s_.prepare_senders = {}
    /\ s_.commit_senders = {}
    /\ s_.request_digest = 0
    /\ s_.seq_num = s.seq_num
    /\ s_.is_primary = s.is_primary
    /\ s_.checkpoint_seq = s.checkpoint_seq
    /\ s_.checkpoint_digest = s.checkpoint_digest
    /\ s_.low_watermark = s.low_watermark
    /\ s_.high_watermark = s.high_watermark
    /\ sent_packets = <<>>

NewRound(s, s_, c, sent_packets) ==
    /\ s.phase.tag = Replied
    /\ s_.phase.tag = PrePrepare
    /\ s_.prepare_senders = {}
    /\ s_.commit_senders = {}
    /\ s_.request_digest = 0
    /\ s_.view = s.view
    /\ s_.seq_num = s.seq_num
    /\ s_.is_primary = s.is_primary
    /\ s_.checkpoint_seq = s.checkpoint_seq
    /\ s_.checkpoint_digest = s.checkpoint_digest
    /\ s_.low_watermark = s.low_watermark
    /\ s_.high_watermark = s.high_watermark
    /\ sent_packets = <<>>

Next(s, s_, c) ==
    \/ \E digest \in Int, sent_packets \in Seq(PBFTMessage) : PrePrepare(s, s_, c, digest, sent_packets)
    \/ \E view \in Int, seq \in Int, digest \in Int, sent_packets \in Seq(PBFTMessage) : ReceivePrePrepare(s, s_, c, view, seq, digest, sent_packets)
    \/ \E sender \in Int, sent_packets \in Seq(PBFTMessage) : ReceivePrepare(s, s_, c, sender, sent_packets)
    \/ \E sent_packets \in Seq(PBFTMessage) : EnterCommit(s, s_, c, sent_packets)
    \/ \E sender \in Int, sent_packets \in Seq(PBFTMessage) : ReceiveCommit(s, s_, c, sender, sent_packets)
    \/ \E sent_packets \in Seq(PBFTMessage) : ExecuteReply(s, s_, c, sent_packets)
    \/ \E digest \in Int, sent_packets \in Seq(PBFTMessage) : Checkpoint(s, s_, c, digest, sent_packets)
    \/ \E sent_packets \in Seq(PBFTMessage) : ViewChange(s, s_, c, sent_packets)
    \/ \E sent_packets \in Seq(PBFTMessage) : NewRound(s, s_, c, sent_packets)

====

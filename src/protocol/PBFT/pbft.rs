/// Simplified PBFT (Practical Byzantine Fault Tolerance) protocol.
///
/// Models the core PBFT consensus phases:
/// 1. Pre-prepare: Primary broadcasts client request
/// 2. Prepare: Replicas exchange prepare messages (need 2f+1)
/// 3. Commit: Replicas exchange commit messages (need 2f+1)
/// 4. Reply: Execute request and send result to client
/// 5. View change: On timeout, increment view number
/// 6. Checkpoint: Periodic stable checkpoints to bound log growth
use vstd::prelude::*;
use crate::protocol::PBFT::types::*;

verus! {

/// Initial state: view 0, pre-prepare phase, primary node
pub open spec fn LInit(s: LState, c: LConstants) -> bool {
    &&& s.view == 0
    &&& s.phase is PrePrepare
    &&& s.prepare_senders == Set::<int>::empty()
    &&& s.commit_senders == Set::<int>::empty()
    &&& s.seq_num == 0
    &&& s.is_primary == true
    &&& s.request_digest == 0
    &&& s.checkpoint_seq == 0
    &&& s.checkpoint_digest == 0
    &&& s.low_watermark == 0
    &&& s.high_watermark == c.checkpoint_interval
    &&& c.n >= 3 * c.f + 1
    &&& c.f >= 0
    &&& c.checkpoint_interval > 0
}

/// Pre-prepare: Primary broadcasts a client request to all replicas.
/// Sends a pre-prepare message and moves to Prepare phase.
pub open spec fn LPrePrepare(
    s: LState, s_: LState, c: LConstants, digest: int,
    sent_packets: Seq<LPBFTMessage>,
) -> bool {
    &&& s.phase is PrePrepare
    &&& s.is_primary == true
    &&& s.seq_num >= s.low_watermark
    &&& s.seq_num < s.high_watermark
    // Move to Prepare phase
    &&& s_.phase is Prepare
    &&& s_.request_digest == digest
    &&& s_.prepare_senders == Set::<int>::empty().insert(c.node_id)
    &&& s_.commit_senders == Set::<int>::empty()
    // Frame
    &&& s_.view == s.view
    &&& s_.seq_num == s.seq_num
    &&& s_.is_primary == s.is_primary
    &&& s_.checkpoint_seq == s.checkpoint_seq
    &&& s_.checkpoint_digest == s.checkpoint_digest
    &&& s_.low_watermark == s.low_watermark
    &&& s_.high_watermark == s.high_watermark
    // Send pre-prepare message
    &&& sent_packets == seq![LPBFTMessage::PrePrepare { view: s.view, seq: s.seq_num, digest }]
}

/// Receive a pre-prepare message (backup only) and accept it.
pub open spec fn LReceivePrePrepare(
    s: LState, s_: LState, c: LConstants,
    view: int, seq: int, digest: int,
    sent_packets: Seq<LPBFTMessage>,
) -> bool {
    &&& s.phase is PrePrepare
    &&& s.is_primary == false
    &&& view == s.view
    // Accept the pre-prepare, move to Prepare
    &&& s_.phase is Prepare
    &&& s_.request_digest == digest
    &&& s_.prepare_senders == Set::<int>::empty().insert(c.node_id)
    &&& s_.commit_senders == Set::<int>::empty()
    // Frame
    &&& s_.view == s.view
    &&& s_.seq_num == seq
    &&& s_.is_primary == s.is_primary
    &&& s_.checkpoint_seq == s.checkpoint_seq
    &&& s_.checkpoint_digest == s.checkpoint_digest
    &&& s_.low_watermark == s.low_watermark
    &&& s_.high_watermark == s.high_watermark
    // No messages sent
    &&& sent_packets == Seq::<LPBFTMessage>::empty()
}

/// Receive a prepare message from another replica.
/// Adds sender to prepare_senders set.
pub open spec fn LReceivePrepare(
    s: LState, s_: LState, c: LConstants, sender: int,
    sent_packets: Seq<LPBFTMessage>,
) -> bool {
    &&& s.phase is Prepare
    &&& !s.prepare_senders.contains(sender)
    &&& s_.prepare_senders == s.prepare_senders.insert(sender)
    // Frame
    &&& s_.phase == s.phase
    &&& s_.view == s.view
    &&& s_.commit_senders == s.commit_senders
    &&& s_.seq_num == s.seq_num
    &&& s_.is_primary == s.is_primary
    &&& s_.request_digest == s.request_digest
    &&& s_.checkpoint_seq == s.checkpoint_seq
    &&& s_.checkpoint_digest == s.checkpoint_digest
    &&& s_.low_watermark == s.low_watermark
    &&& s_.high_watermark == s.high_watermark
    // No messages sent
    &&& sent_packets == Seq::<LPBFTMessage>::empty()
}

/// Enter commit phase when enough prepares received (quorum = 2f+1).
/// Uses prepare_senders.len() for quorum check.
pub open spec fn LEnterCommit(
    s: LState, s_: LState, c: LConstants,
    sent_packets: Seq<LPBFTMessage>,
) -> bool {
    &&& s.phase is Prepare
    &&& s.prepare_senders.len() >= 2 * c.f + 1
    &&& s_.phase is Commit
    &&& s_.commit_senders == Set::<int>::empty().insert(c.node_id)
    // Frame
    &&& s_.view == s.view
    &&& s_.prepare_senders == s.prepare_senders
    &&& s_.seq_num == s.seq_num
    &&& s_.is_primary == s.is_primary
    &&& s_.request_digest == s.request_digest
    &&& s_.checkpoint_seq == s.checkpoint_seq
    &&& s_.checkpoint_digest == s.checkpoint_digest
    &&& s_.low_watermark == s.low_watermark
    &&& s_.high_watermark == s.high_watermark
    // No messages sent
    &&& sent_packets == Seq::<LPBFTMessage>::empty()
}

/// Receive a commit message from another replica.
/// Adds sender to commit_senders set.
pub open spec fn LReceiveCommit(
    s: LState, s_: LState, c: LConstants, sender: int,
    sent_packets: Seq<LPBFTMessage>,
) -> bool {
    &&& s.phase is Commit
    &&& !s.commit_senders.contains(sender)
    &&& s_.commit_senders == s.commit_senders.insert(sender)
    // Frame
    &&& s_.phase == s.phase
    &&& s_.view == s.view
    &&& s_.prepare_senders == s.prepare_senders
    &&& s_.seq_num == s.seq_num
    &&& s_.is_primary == s.is_primary
    &&& s_.request_digest == s.request_digest
    &&& s_.checkpoint_seq == s.checkpoint_seq
    &&& s_.checkpoint_digest == s.checkpoint_digest
    &&& s_.low_watermark == s.low_watermark
    &&& s_.high_watermark == s.high_watermark
    // No messages sent
    &&& sent_packets == Seq::<LPBFTMessage>::empty()
}

/// Execute request and reply to client when enough commits received.
/// Uses commit_senders.len() for quorum check.
pub open spec fn LExecuteReply(
    s: LState, s_: LState, c: LConstants,
    sent_packets: Seq<LPBFTMessage>,
) -> bool {
    &&& s.phase is Commit
    &&& s.commit_senders.len() >= 2 * c.f + 1
    &&& s_.phase is Replied
    &&& s_.seq_num == s.seq_num + 1
    &&& s_.prepare_senders == Set::<int>::empty()
    &&& s_.commit_senders == Set::<int>::empty()
    // Frame
    &&& s_.view == s.view
    &&& s_.is_primary == s.is_primary
    &&& s_.request_digest == s.request_digest
    &&& s_.checkpoint_seq == s.checkpoint_seq
    &&& s_.checkpoint_digest == s.checkpoint_digest
    &&& s_.low_watermark == s.low_watermark
    &&& s_.high_watermark == s.high_watermark
    // No messages sent
    &&& sent_packets == Seq::<LPBFTMessage>::empty()
}

/// Create a stable checkpoint after processing K requests.
/// Advances low_watermark and high_watermark.
pub open spec fn LCheckpoint(
    s: LState, s_: LState, c: LConstants, digest: int,
    sent_packets: Seq<LPBFTMessage>,
) -> bool {
    &&& s.phase is Replied
    &&& s.seq_num > s.checkpoint_seq
    // Create checkpoint
    &&& s_.checkpoint_seq == s.seq_num
    &&& s_.checkpoint_digest == digest
    // Advance watermarks
    &&& s_.low_watermark == s.seq_num
    &&& s_.high_watermark == s.seq_num + c.checkpoint_interval
    // Frame
    &&& s_.view == s.view
    &&& s_.phase == s.phase
    &&& s_.prepare_senders == s.prepare_senders
    &&& s_.commit_senders == s.commit_senders
    &&& s_.seq_num == s.seq_num
    &&& s_.is_primary == s.is_primary
    &&& s_.request_digest == s.request_digest
    // No messages sent
    &&& sent_packets == Seq::<LPBFTMessage>::empty()
}

/// View change: on timeout, increment view and reset to PrePrepare.
pub open spec fn LViewChange(
    s: LState, s_: LState, c: LConstants,
    sent_packets: Seq<LPBFTMessage>,
) -> bool {
    &&& s_.view == s.view + 1
    &&& s_.phase is PrePrepare
    &&& s_.prepare_senders == Set::<int>::empty()
    &&& s_.commit_senders == Set::<int>::empty()
    &&& s_.request_digest == 0
    // Frame
    &&& s_.seq_num == s.seq_num
    &&& s_.is_primary == s.is_primary
    &&& s_.checkpoint_seq == s.checkpoint_seq
    &&& s_.checkpoint_digest == s.checkpoint_digest
    &&& s_.low_watermark == s.low_watermark
    &&& s_.high_watermark == s.high_watermark
    // No messages sent
    &&& sent_packets == Seq::<LPBFTMessage>::empty()
}

/// Start new round: after reply, return to PrePrepare for next request.
pub open spec fn LNewRound(
    s: LState, s_: LState, c: LConstants,
    sent_packets: Seq<LPBFTMessage>,
) -> bool {
    &&& s.phase is Replied
    &&& s_.phase is PrePrepare
    &&& s_.prepare_senders == Set::<int>::empty()
    &&& s_.commit_senders == Set::<int>::empty()
    &&& s_.request_digest == 0
    // Frame
    &&& s_.view == s.view
    &&& s_.seq_num == s.seq_num
    &&& s_.is_primary == s.is_primary
    &&& s_.checkpoint_seq == s.checkpoint_seq
    &&& s_.checkpoint_digest == s.checkpoint_digest
    &&& s_.low_watermark == s.low_watermark
    &&& s_.high_watermark == s.high_watermark
    // No messages sent
    &&& sent_packets == Seq::<LPBFTMessage>::empty()
}

/// Next-state relation: disjunction of all transitions.
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| exists |digest: int, sent_packets: Seq<LPBFTMessage>| LPrePrepare(s, s_, c, digest, sent_packets)
    ||| exists |view: int, seq: int, digest: int, sent_packets: Seq<LPBFTMessage>| LReceivePrePrepare(s, s_, c, view, seq, digest, sent_packets)
    ||| exists |sender: int, sent_packets: Seq<LPBFTMessage>| LReceivePrepare(s, s_, c, sender, sent_packets)
    ||| exists |sent_packets: Seq<LPBFTMessage>| LEnterCommit(s, s_, c, sent_packets)
    ||| exists |sender: int, sent_packets: Seq<LPBFTMessage>| LReceiveCommit(s, s_, c, sender, sent_packets)
    ||| exists |sent_packets: Seq<LPBFTMessage>| LExecuteReply(s, s_, c, sent_packets)
    ||| exists |digest: int, sent_packets: Seq<LPBFTMessage>| LCheckpoint(s, s_, c, digest, sent_packets)
    ||| exists |sent_packets: Seq<LPBFTMessage>| LViewChange(s, s_, c, sent_packets)
    ||| exists |sent_packets: Seq<LPBFTMessage>| LNewRound(s, s_, c, sent_packets)
}

} // verus!

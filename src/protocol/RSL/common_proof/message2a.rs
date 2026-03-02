use crate::protocol::RSL::acceptor::*;
use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::environment::*;
use crate::protocol::RSL::common_proof::max_ballot_sent_1a::*;
use crate::protocol::RSL::common_proof::packet_sending::*;
use crate::protocol::RSL::common_proof::receive1b::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::proposer::*;
use crate::protocol::RSL::replica::*;
use crate::protocol::RSL::types::*;
use vstd::prelude::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

use crate::common::collections::maps2::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::framework::environment_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::logic::temporal_s::*;
use crate::common::native::io_s::*;

verus! {

    /// All packets in a LBroadcastToEveryone share the same message.
    /// If two packets p1, p2 are both in sent_packets from a broadcast, then p1.msg == p2.msg.
    pub proof fn lemma_BroadcastPacketsHaveSameMessage(
        c: LConfiguration,
        myidx: int,
        m: RslMessage,
        sent_packets: Seq<RslPacket>,
        p1: RslPacket,
        p2: RslPacket,
    )
        requires
            LBroadcastToEveryone(c, myidx, m, sent_packets),
            sent_packets.contains(p1),
            sent_packets.contains(p2),
        ensures
            p1.msg == p2.msg,
    {
        // sent_packets.contains(p1) means exists |i1| sent_packets[i1] == p1
        // LBroadcastToEveryone gives sent_packets[i1].msg == m for all valid i1
        let i1 = choose |i1: int| 0 <= i1 < sent_packets.len() && sent_packets[i1] == p1;
        let i2 = choose |i2: int| 0 <= i2 < sent_packets.len() && sent_packets[i2] == p2;
        assert(sent_packets[i1] =~= LPacket { dst: c.replica_ids[i1], src: c.replica_ids[myidx], msg: m });
        assert(sent_packets[i2] =~= LPacket { dst: c.replica_ids[i2], src: c.replica_ids[myidx], msg: m });
    }

    /// When two packets are both sent by the same LProposerMaybeNominateValueAndSend2a action,
    /// they have the same message (because the action broadcasts a single message to all replicas).
    pub proof fn lemma_2aSentInSameStepHaveSameMessage(
        s: LProposer,
        s_: LProposer,
        clock: int,
        log_truncation_point: int,
        sent_packets: Seq<RslPacket>,
        p1: RslPacket,
        p2: RslPacket,
    )
        requires
            LProposerMaybeNominateValueAndSend2a(s, s_, clock, log_truncation_point, sent_packets),
            sent_packets.contains(p1),
            sent_packets.contains(p2),
        ensures
            p1.msg == p2.msg,
    {
        lemma_MaybeNominate_nonempty_implies_old_or_new(s, s_, clock, log_truncation_point, sent_packets);
        if LProposerNominateOldValueAndSend2a(s, s_, log_truncation_point, sent_packets) {
            let opn = s.next_operation_number_to_propose;
            let p_1b: RslPacket = choose |p_1b: RslPacket|
                s.received_1b_packets.contains(p_1b)
                && LValIsHighestNumberedProposal(p_1b.msg->votes[opn].max_val, s.received_1b_packets, opn)
                && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
                    RslMessage::RslMessage2a{bal_2a: s.max_ballot_i_sent_1a, opn_2a: opn, val_2a: p_1b.msg->votes[opn].max_val},
                    sent_packets);
            lemma_BroadcastPacketsHaveSameMessage(
                s.constants.all.config, s.constants.my_index,
                RslMessage::RslMessage2a{bal_2a: s.max_ballot_i_sent_1a, opn_2a: opn, val_2a: p_1b.msg->votes[opn].max_val},
                sent_packets, p1, p2);
        } else {
            let opn = s.next_operation_number_to_propose;
            let batchSize = if s.request_queue.len() <= s.constants.all.params.max_batch_size || s.constants.all.params.max_batch_size < 0 {
                s.request_queue.len() as int
            } else {
                s.constants.all.params.max_batch_size
            };
            let v = s.request_queue.subrange(0, batchSize);
            lemma_BroadcastPacketsHaveSameMessage(
                s.constants.all.config, s.constants.my_index,
                RslMessage::RslMessage2a{bal_2a: s.max_ballot_i_sent_1a, opn_2a: opn, val_2a: v},
                sent_packets, p1, p2);
        }
    }

    /// When LProposerMaybeNominateValueAndSend2a produces non-empty sent_packets,
    /// it must be via either LProposerNominateOldValueAndSend2a or
    /// LProposerNominateNewValueAndSend2a (the other branches produce empty packets).
    pub proof fn lemma_MaybeNominate_nonempty_implies_old_or_new(
        s: LProposer,
        s_: LProposer,
        clock: int,
        log_truncation_point: int,
        sent_packets: Seq<RslPacket>,
    )
        requires
            LProposerMaybeNominateValueAndSend2a(s, s_, clock, log_truncation_point, sent_packets),
            sent_packets.len() > 0,
        ensures
            LProposerNominateOldValueAndSend2a(s, s_, log_truncation_point, sent_packets) ||
            LProposerNominateNewValueAndSend2a(s, s_, clock, log_truncation_point, sent_packets),
    {
        // Case split on the if-else-if chain in LProposerMaybeNominateValueAndSend2a:
        // - Branch 1 (line 368): !LProposerCanNominate → sent_packets == empty (contradicts len > 0)
        // - Branch 2 (line 371): !LAllAcceptorsHadNoProposal → LProposerNominateOldValueAndSend2a
        // - Branch 3 (line 373): LAllAcceptorsHadNoProposal → LProposerNominateNewValueAndSend2a
        // - Branch 4 (line 378): timer set → sent_packets == empty (contradicts len > 0)
        // - Branch 5 (line 391): do nothing → sent_packets == empty (contradicts len > 0)
        // Verus case-splits automatically.
    }

    pub proof fn lemma_2aMessageImplicationsForProposerState(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        p:RslPacket
    ) -> (
        proposer_idx:int
    )
        requires IsValidBehaviorPrefix(b, c, i),
                0 <= i,
                b[i].environment.sentPackets.contains(p),
                c.config.replica_ids.contains(p.src),
                p.msg is RslMessage2a,
        ensures
                0 <= proposer_idx < c.config.replica_ids.len(),
                0 <= proposer_idx < b[i].replicas.len(),
                p.src == c.config.replica_ids[proposer_idx],
                p.msg->bal_2a.proposer_id == proposer_idx,
                // //   var s := b[i].replicas[proposer_idx].replica.proposer;
                (BalLt(p.msg->bal_2a, b[i].replicas[proposer_idx].replica.proposer.max_ballot_i_sent_1a)
                || (&& b[i].replicas[proposer_idx].replica.proposer.max_ballot_i_sent_1a == p.msg->bal_2a
                        && b[i].replicas[proposer_idx].replica.proposer.current_state != 1
                        && b[i].replicas[proposer_idx].replica.proposer.next_operation_number_to_propose > p.msg->opn_2a)),
        decreases i
    {
        if i == 0
        {
          // sentPackets is empty at init, contradicting requires b[i].environment.sentPackets.contains(p)
          lemma_ConstantsAllConsistent(b, c, 0);
          assert(b[0].environment.sentPackets.len() == 0);
          return arbitrary();
        }

        lemma_AssumptionsMakeValidTransition(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i-1);

        if b[i-1].environment.sentPackets.contains(p)
        {
          let proposer_idx = lemma_2aMessageImplicationsForProposerState(b, c, i-1, p);
          let s = b[i-1].replicas[proposer_idx].replica.proposer;
          let s_ = b[i].replicas[proposer_idx].replica.proposer;
          if s_ != s
          {
            let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, proposer_idx);
          }
          assert(p.msg->bal_2a.proposer_id == proposer_idx);
          return proposer_idx;
        }

        // let ios:Seq<RslIo>;
        let (proposer_idx, ios) = lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i-1], b[i], p);
        lemma_max_balISent1aHasMeAsProposer(b, c, i-1, proposer_idx);

        let s = b[i-1].replicas[proposer_idx].replica.proposer;
        let s_ = b[i].replicas[proposer_idx].replica.proposer;
        let a = b[i-1].replicas[proposer_idx].replica.acceptor;

        let pkts = ExtractSentPacketsFromIos(ios);
        lemma_ExtractSentPacketsFromIos(ios);
        assert(pkts.contains(p));

        assert(LProposerMaybeNominateValueAndSend2a(s, s_, SpontaneousClock(ios).t, a.log_truncation_point, pkts));
        // pkts.contains(p) implies pkts is non-empty, so the Maybe action must have
        // used one of the nominating branches (others produce empty sent_packets).
        lemma_MaybeNominate_nonempty_implies_old_or_new(s, s_, SpontaneousClock(ios).t, a.log_truncation_point, pkts);

        assert(p.msg->bal_2a.proposer_id == proposer_idx);
        proposer_idx
    }



    pub proof fn lemma_Find2aThatCausedVote(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        idx:int,
        opn:OperationNumber
    ) -> (
          p:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i,
                 0 <= idx < b[i].replicas.len(),
                 b[i].replicas[idx].replica.acceptor.votes.contains_key(opn),
        ensures
                b[i].environment.sentPackets.contains(p),
                c.config.replica_ids.contains(p.src),
                p.msg is RslMessage2a,
                p.msg->opn_2a == opn,
                p.msg->val_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_val,
                p.msg->bal_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal,
        decreases i
    {
        if i == 0
        {
          // At init, acceptor votes are empty (LAcceptorInit requires votes == Map::empty()),
          // so votes.contains_key(opn) is false, contradicting requires.
          lemma_ConstantsAllConsistent(b, c, 0);
          assert(b[0].replicas[idx].replica.acceptor.votes == Map::<OperationNumber, Vote>::empty());
          return arbitrary();
        }

        lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
        lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);
        lemma_AssumptionsMakeValidTransition(b, c, i-1);

        let s = b[i-1].replicas[idx].replica.acceptor;
        let s_ = b[i].replicas[idx].replica.acceptor;

        if s.votes.contains_key(opn) && s_.votes[opn] == s.votes[opn]
        {
          let p = lemma_Find2aThatCausedVote(b, c, i-1, idx, opn);
          assert(b[i].environment.sentPackets.contains(p));
          return p;
        }
        let nextActionIndex = b[i-1].replicas[idx].nextActionIndex;
        assert(s_.votes.contains_key(opn));
        if !s.votes.contains_key(opn) {
            assert(nextActionIndex == 0 || nextActionIndex == 4);
            if nextActionIndex == 4 {
                // Action 4 = LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints
                // → LAcceptorTruncateLog → either s_ == s or RemoveVotesBeforeLogTruncationPoint
                // RemoveVotesBeforeLogTruncationPoint ensures: votes_.contains_key(opn) ==> votes.contains_key(opn)
                // So no new keys are added, contradicting !s.votes.contains_key(opn) && s_.votes.contains_key(opn).
                let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
                assert(false);
            }
            assert(nextActionIndex == 0);
            let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
            let p = ios[0]->r;
            if p.msg is RslMessage1b {
                // Processing 1b calls LReplicaNextProcess1b → LAcceptorTruncateLog
                // → either s_ == s or RemoveVotesBeforeLogTruncationPoint
                // No new vote keys are added, contradicting !s.votes.contains_key(opn) && s_.votes.contains_key(opn).
                assert(false);
            }
            assert(p.msg is RslMessage2a);
        } else if s_.votes[opn] != s.votes[opn] {
            assert(nextActionIndex == 0);
            let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
            let p = ios[0]->r;
            assert(p.msg is RslMessage2a);
        }

        assert(nextActionIndex == 0);

        let e = b[i-1].environment;
        let e_ = b[i].environment;

        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);

        let p = ios[0]->r;
        assert(LEnvironment_Next(e, e_));
        assert(IsValidLEnvStep(e, e.nextStep));
        assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
        assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
        assert(ios[0] is Receive);
        // assert(ios[0]->r.dst == e.nextStep->actor);
        assert(p.dst == e.nextStep->actor);
        assert(e.nextStep->actor == c.config.replica_ids[idx]);

        let pkts = ExtractSentPacketsFromIos(ios);
        lemma_ExtractSentPacketsFromIos(ios);

        // assert(p.msg is RslMessage2a);

        assert(LAcceptorProcess2a(s, s_, p, pkts));

        assert(e.nextStep is LEnvStepHostIos);
        assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
        assert(forall |io| ios.contains(io) && match_ios_recv(io, e.sentPackets));
        assert(ios.contains(ios[0]) && ios[0] is Receive);
        assert(match_ios_recv(ios[0], e.sentPackets));
        assert(e.sentPackets.contains(ios[0]->r));
        assert(b[i].environment.sentPackets.contains(p));
        return p;
    }


    pub proof fn lemma_2aMessagesFromSameBallotAndOperationMatch(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        p1:RslPacket,
        p2:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                0 <= i,
                b[i].environment.sentPackets.contains(p1),
                b[i].environment.sentPackets.contains(p2),
                c.config.replica_ids.contains(p1.src),
                c.config.replica_ids.contains(p2.src),
                p1.msg is RslMessage2a,
                p2.msg is RslMessage2a,
                p1.msg->opn_2a == p2.msg->opn_2a,
                p1.msg->bal_2a == p2.msg->bal_2a,
        ensures  p1.msg->val_2a == p2.msg->val_2a,
        decreases 2 * i + 1
    {
        if i == 0
        {
          // At init, sentPackets is empty (LEnvironment_Init requires len()==0),
          // so b[0].environment.sentPackets.contains(p1) is false, contradicting requires.
          lemma_ConstantsAllConsistent(b, c, 0);
          assert(b[0].environment.sentPackets.len() == 0);
          return;
        }

        if b[i-1].environment.sentPackets.contains(p2) && !b[i-1].environment.sentPackets.contains(p1)
        {
          lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(b, c, i, p2, p1);
          assert(p1.msg->val_2a == p2.msg->val_2a);
        }
        else
        {
          lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(b, c, i, p1, p2);
          assert(p1.msg->val_2a == p2.msg->val_2a);
        }
    }

    pub proof fn lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        p1:RslPacket,
        p2:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                0 < i,
                b[i].environment.sentPackets.contains(p1),
                b[i].environment.sentPackets.contains(p2),
                c.config.replica_ids.contains(p1.src),
                c.config.replica_ids.contains(p2.src),
                p1.msg is RslMessage2a,
                p2.msg is RslMessage2a,
                p1.msg->opn_2a == p2.msg->opn_2a,
                p1.msg->bal_2a == p2.msg->bal_2a,
                b[i-1].environment.sentPackets.contains(p2) ==> b[i-1].environment.sentPackets.contains(p1),
        ensures  p1.msg->val_2a == p2.msg->val_2a,
        decreases 2 * i
    {
        lemma_AssumptionsMakeValidTransition(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i-1);

        if b[i-1].environment.sentPackets.contains(p2)
        {
          // Both packets had already been sent by i-1, so we induction.
          lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i-1, p1, p2);
          assert(p1.msg->val_2a == p2.msg->val_2a);
          return;
        }

        let (proposer_idx, ios) = lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i-1], b[i], p2);

        if !b[i-1].environment.sentPackets.contains(p1)
        {
          // Both packets were sent in step i-1→i, so they're both in ios.
          assert(ios.contains(LIoOp::Send{s:p1}));
          assert(ios.contains(LIoOp::Send{s:p2}));
          // Extract sent_packets and show both p1,p2 are in it
          let pkts = ExtractSentPacketsFromIos(ios);
          lemma_ExtractSentPacketsFromIos(ios);
          assert(pkts.contains(p1));
          assert(pkts.contains(p2));
          // The action is LReplicaNextReadClockMaybeNominateValueAndSend2a, which calls
          // LProposerMaybeNominateValueAndSend2a on the proposer. Both packets come from
          // the same broadcast, so they have the same message.
          let s = b[i-1].replicas[proposer_idx].replica.proposer;
          let s_ = b[i].replicas[proposer_idx].replica.proposer;
          let a = b[i-1].replicas[proposer_idx].replica.acceptor;
          lemma_2aSentInSameStepHaveSameMessage(s, s_, SpontaneousClock(ios).t, a.log_truncation_point, pkts, p1, p2);
          assert(p1.msg == p2.msg);
          return;
        }

        // p1 was already sent before step i; p2 is newly sent in step i.
        // We'll derive a contradiction: the proposer can't send p2 given its state.

        // Get proposer state implications for p1 at step i-1
        let alt_proposer_idx = lemma_2aMessageImplicationsForProposerState(b, c, i-1, p1);
        // Get proposer state implications for p2 at step i (to identify the replica)
        let alt2_proposer_idx = lemma_2aMessageImplicationsForProposerState(b, c, i, p2);
        assert(alt_proposer_idx == alt2_proposer_idx);
        assert(ReplicasDistinct(c.config.replica_ids, proposer_idx, alt_proposer_idx));
        assert(proposer_idx == alt_proposer_idx);

        // The proposer state at step i-1 (pre-state of the action that sends p2)
        let s = b[i-1].replicas[proposer_idx].replica.proposer;
        let s_ = b[i].replicas[proposer_idx].replica.proposer;
        let a = b[i-1].replicas[proposer_idx].replica.acceptor;
        let pkts = ExtractSentPacketsFromIos(ios);
        lemma_ExtractSentPacketsFromIos(ios);
        assert(pkts.contains(p2));

        // The proposer action is LProposerMaybeNominateValueAndSend2a, which (since pkts
        // is non-empty) must be either Old or New nomination.
        assert(LProposerMaybeNominateValueAndSend2a(s, s_, SpontaneousClock(ios).t, a.log_truncation_point, pkts));
        lemma_MaybeNominate_nonempty_implies_old_or_new(s, s_, SpontaneousClock(ios).t, a.log_truncation_point, pkts);

        // In both Old and New nomination, the broadcast message has:
        //   bal_2a == s.max_ballot_i_sent_1a and opn_2a == s.next_operation_number_to_propose
        // Since p2 is in the broadcast, p2.msg has these fields.
        // Use LBroadcastToEveryone structure: all packets have msg == m
        let i2 = choose |i2: int| 0 <= i2 < pkts.len() && pkts[i2] == p2;
        if LProposerNominateOldValueAndSend2a(s, s_, a.log_truncation_point, pkts) {
            let opn = s.next_operation_number_to_propose;
            let p_1b: RslPacket = choose |p_1b: RslPacket|
                s.received_1b_packets.contains(p_1b)
                && LValIsHighestNumberedProposal(p_1b.msg->votes[opn].max_val, s.received_1b_packets, opn)
                && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
                    RslMessage::RslMessage2a{bal_2a: s.max_ballot_i_sent_1a, opn_2a: opn, val_2a: p_1b.msg->votes[opn].max_val},
                    pkts);
            assert(pkts[i2] =~= LPacket { dst: s.constants.all.config.replica_ids[i2],
                src: s.constants.all.config.replica_ids[s.constants.my_index],
                msg: RslMessage::RslMessage2a{bal_2a: s.max_ballot_i_sent_1a, opn_2a: opn, val_2a: p_1b.msg->votes[opn].max_val} });
        } else {
            let opn = s.next_operation_number_to_propose;
            let batchSize = if s.request_queue.len() <= s.constants.all.params.max_batch_size || s.constants.all.params.max_batch_size < 0 {
                s.request_queue.len() as int
            } else {
                s.constants.all.params.max_batch_size
            };
            let v = s.request_queue.subrange(0, batchSize);
            assert(pkts[i2] =~= LPacket { dst: s.constants.all.config.replica_ids[i2],
                src: s.constants.all.config.replica_ids[s.constants.my_index],
                msg: RslMessage::RslMessage2a{bal_2a: s.max_ballot_i_sent_1a, opn_2a: opn, val_2a: v} });
        }
        // Now we know: p2.msg->bal_2a == s.max_ballot_i_sent_1a, p2.msg->opn_2a == s.next_operation_number_to_propose
        assert(p2.msg->bal_2a == s.max_ballot_i_sent_1a);
        assert(p2.msg->opn_2a == s.next_operation_number_to_propose);

        // Since p1.msg->bal_2a == p2.msg->bal_2a, we have p1.msg->bal_2a == s.max_ballot_i_sent_1a
        // Since p1.msg->opn_2a == p2.msg->opn_2a, we have p1.msg->opn_2a == s.next_operation_number_to_propose
        //
        // From lemma_2aMessageImplicationsForProposerState(b, c, i-1, p1):
        //   BalLt(p1.msg->bal_2a, s.max_ballot_i_sent_1a) — i.e., BalLt(s.max_ballot_i_sent_1a, s.max_ballot_i_sent_1a), which is false
        //   OR s.next_operation_number_to_propose > p1.msg->opn_2a — i.e., s.next_opn > s.next_opn, which is false
        // Both disjuncts are false → contradiction.
        assert(!BalLt(s.max_ballot_i_sent_1a, s.max_ballot_i_sent_1a));
        assert(p1.msg->opn_2a == s.next_operation_number_to_propose);
        assert(false);
    }


    pub proof fn lemma_2aMessageHas1bQuorumPermittingIt(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        p: RslPacket
    ) -> (q: Set<RslPacket>)
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            b[i].environment.sentPackets.contains(p),
            c.config.replica_ids.contains(p.src),
            p.msg is RslMessage2a,
        ensures
            // q.subset_of(b[i].environment.sentPackets),
            q <= b[i].environment.sentPackets,
            q.len() >= LMinQuorumSize(c.config),
            LIsAfterLogTruncationPoint(p.msg->opn_2a, q),
            LSetOfMessage1bAboutBallot(q, p.msg->bal_2a),
            LAllAcceptorsHadNoProposal(q, p.msg->opn_2a) || LValIsHighestNumberedProposal(p.msg->val_2a, q, p.msg->opn_2a),
            forall|p1, p2: RslPacket| q.contains(p1) && q.contains(p2) && p1 != p2 ==> p1.src != p2.src,
            forall|p1: RslPacket| q.contains(p1) ==> c.config.replica_ids.contains(p1.src),
        decreases i
    {
        if i == 0 {
            // sentPackets is empty at init, contradicting requires b[i].environment.sentPackets.contains(p)
            lemma_ConstantsAllConsistent(b, c, 0);
            assert(b[0].environment.sentPackets.len() == 0);
            return arbitrary();
        }

        if b[i - 1].environment.sentPackets.contains(p) {
            let q_prev = lemma_2aMessageHas1bQuorumPermittingIt(b, c, i - 1, p);
            lemma_PacketSetStaysInSentPackets(b, c, i - 1, i, q_prev);
            return q_prev;
        }

        lemma_ConstantsAllConsistent(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
        let (idx, ios) = lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i - 1], b[i], p);
        let q_new = b[i - 1].replicas[idx].replica.proposer.received_1b_packets;

        let s = b[i-1].replicas[idx].replica.proposer;
        let s_ = b[i].replicas[idx].replica.proposer;
        let a = b[i-1].replicas[idx].replica.acceptor;

        let pkts = ExtractSentPacketsFromIos(ios);
        lemma_ExtractSentPacketsFromIos(ios);
        assert(pkts.contains(p));

        assert(LProposerMaybeNominateValueAndSend2a(s, s_, SpontaneousClock(ios).t, a.log_truncation_point, pkts));
        lemma_MaybeNominate_nonempty_implies_old_or_new(s, s_, SpontaneousClock(ios).t, a.log_truncation_point, pkts);

        assert forall|p_1b: RslPacket| q_new.contains(p_1b) implies b[i].environment.sentPackets.contains(p_1b)
        by {
            lemma_PacketInReceived1bWasSent(b, c, i - 1, idx, p_1b);
            lemma_PacketStaysInSentPackets(b, c, i - 1, i, p_1b);
        }

        lemma_Received1bPacketsAreFrommax_balISent1a(b, c, i - 1, idx);

        assert(q_new.len() >= LMinQuorumSize(c.config));
        assert(LIsAfterLogTruncationPoint(p.msg->opn_2a, q_new));
        assert(LSetOfMessage1bAboutBallot(q_new, p.msg->bal_2a));
        assert(LAllAcceptorsHadNoProposal(q_new, p.msg->opn_2a) || LValIsHighestNumberedProposal(p.msg->val_2a, q_new, p.msg->opn_2a));
        assert(forall|p1, p2: RslPacket| q_new.contains(p1) && q_new.contains(p2) && p1 != p2 ==> p1.src != p2.src);
        assert(forall|p1: RslPacket| q_new.contains(p1) ==> c.config.replica_ids.contains(p1.src));

        return q_new;
    }


    pub proof fn lemma_2aMessageHasValidBallot(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        p: RslPacket
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            b[i].environment.sentPackets.contains(p),
            c.config.replica_ids.contains(p.src),
            p.msg is RslMessage2a,
        ensures
            p.msg->bal_2a.seqno >= 0,
            0 <= p.msg->bal_2a.proposer_id < c.config.replica_ids.len(),
        decreases i,
    {
        if i == 0 {
            // sentPackets is empty at init, contradicting requires b[i].environment.sentPackets.contains(p)
            lemma_ConstantsAllConsistent(b, c, 0);
            assert(b[0].environment.sentPackets.len() == 0);
            return;
        }

        lemma_ConstantsAllConsistent(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);

        if b[i - 1].environment.sentPackets.contains(p) {
            lemma_2aMessageHasValidBallot(b, c, i - 1, p);
            return;
        }



        let (idx, ios) = lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i - 1], b[i], p);

        let s = b[i-1].replicas[idx].replica.proposer;
        let s_ = b[i].replicas[idx].replica.proposer;
        let a = b[i-1].replicas[idx].replica.acceptor;

        let pkts = ExtractSentPacketsFromIos(ios);
        lemma_ExtractSentPacketsFromIos(ios);

        assert(LProposerMaybeNominateValueAndSend2a(s, s_, SpontaneousClock(ios).t, a.log_truncation_point, pkts));
        lemma_max_balISent1aHasMeAsProposer(b, c, i - 1, idx);

        assert(pkts.contains(p));
        // LProposerMaybeNominateValueAndSend2a → LBroadcastToEveryone(_, _, RslMessage2a{bal_2a: s.max_ballot_i_sent_1a, ...}, pkts)
        // All packets in pkts have msg->bal_2a == s.max_ballot_i_sent_1a. In non-sending branches, pkts is empty.
        let j = choose |j:int| 0 <= j < pkts.len() && pkts[j] == p;
        assert(p.msg->bal_2a == s.max_ballot_i_sent_1a);

        assert(p.msg->bal_2a.seqno >= 0);
        assert(0 <= p.msg->bal_2a.proposer_id);
        assert(p.msg->bal_2a.proposer_id < c.config.replica_ids.len());
    }
}

use crate::protocol::RSL::acceptor::*;
use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::max_ballot::*;
use crate::protocol::RSL::common_proof::message2b::*;
use crate::protocol::RSL::common_proof::packet_sending::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
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

  #[verifier(external_body)]
  pub proof fn lemma_1bMessageImplicationsForCAcceptor(
      b:Behavior<RslState>,
      c:LConstants,
      i:int,
      opn:OperationNumber,
      p:RslPacket
  ) -> (
      acceptor_idx:int
  )
      requires IsValidBehaviorPrefix(b, c, i),
                0 <= i,
                b[i].environment.sentPackets.contains(p),
                c.config.replica_ids.contains(p.src),
                p.msg is RslMessage1b,
      ensures
              0 <= acceptor_idx < c.config.replica_ids.len(),
              0 <= acceptor_idx < b[i].replicas.len(),
              p.src == c.config.replica_ids[acceptor_idx],
              BalLeq(p.msg->bal_1b, b[i].replicas[acceptor_idx].replica.acceptor.max_bal),
            //   // var s := b[i].replicas[acceptor_idx].replica.acceptor;
              p.msg->votes.contains_key(opn) && opn >= b[i].replicas[acceptor_idx].replica.acceptor.log_truncation_point ==>
                  b[i].replicas[acceptor_idx].replica.acceptor.votes.contains_key(opn)
                  && (BalLeq(p.msg->bal_1b, b[i].replicas[acceptor_idx].replica.acceptor.votes[opn].max_value_bal)
                    || b[i].replicas[acceptor_idx].replica.acceptor.votes[opn] == Vote{max_value_bal:p.msg->votes[opn].max_value_bal, max_val:p.msg->votes[opn].max_val}),
            //   // var s := b[i].replicas[acceptor_idx].replica.acceptor;
              !p.msg->votes.contains_key(opn) && opn >= b[i].replicas[acceptor_idx].replica.acceptor.log_truncation_point ==>
                (!b[i].replicas[acceptor_idx].replica.acceptor.votes.contains_key(opn)
                  || (b[i].replicas[acceptor_idx].replica.acceptor.votes.contains_key(opn) && BalLeq(p.msg->bal_1b, b[i].replicas[acceptor_idx].replica.acceptor.votes[opn].max_value_bal))),
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
            let acceptor_idx = lemma_1bMessageImplicationsForCAcceptor(b, c, i-1, opn, p);
            let s = b[i-1].replicas[acceptor_idx].replica.acceptor;
            let s_ = b[i].replicas[acceptor_idx].replica.acceptor;

            if opn < s_.log_truncation_point
            {
                return acceptor_idx;
            }
            if s_.log_truncation_point == s.log_truncation_point && s_.votes == s.votes
            {
                return acceptor_idx;
            }

            assert(opn >= s_.log_truncation_point >= s.log_truncation_point);
            if p.msg->votes.contains_key(opn)
            {
            lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, acceptor_idx);

            if s_.votes[opn].max_value_bal == s.votes[opn].max_value_bal
            {
                lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(b, c, i-1, opn, s.votes[opn].max_value_bal, acceptor_idx);
            }
            }
            return acceptor_idx;
        }

        let (acceptor_idx, ios) = lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p);

        let s = b[i-1].replicas[acceptor_idx].replica.acceptor;
        let s_ = b[i].replicas[acceptor_idx].replica.acceptor;
        let nextActionIndex = b[i-1].replicas[acceptor_idx].nextActionIndex;

        let e = b[i-1].environment;
        let e_ = b[i].environment;

        assert(nextActionIndex!=4);
        assert(nextActionIndex == 0);

        let recv = ios[0]->r;
        assert(LEnvironment_Next(e, e_));
        assert(IsValidLEnvStep(e, e.nextStep));
        assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
        assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
        assert(ios[0] is Receive);
        // assert(ios[0]->r.dst == e.nextStep->actor);
        assert(recv.dst == e.nextStep->actor);
        assert(e.nextStep->actor == c.config.replica_ids[acceptor_idx]);


        let pkts = ExtractSentPacketsFromIos(ios);
        lemma_ExtractSentPacketsFromIos(ios);

        assert(e.nextStep is LEnvStepHostIos);
        assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
        assert(forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
        assert(ios.contains(ios[0]) && ios[0] is Receive);
        assert(match_ios_recv(ios[0], e.sentPackets));
        assert(e.sentPackets.contains(ios[0]->r));
        assert(b[i].environment.sentPackets.contains(p));
        assert(pkts.contains(p));

        assert(recv.msg is RslMessage1a);


        assert(p.msg is RslMessage1b);
        assert(LReplicaNextProcess1a(b[i-1].replicas[acceptor_idx].replica, b[i].replicas[acceptor_idx].replica, recv, pkts));
        assert(LAcceptorProcess1a(s, s_, recv, pkts));

        assert(recv.msg->bal_1a == s_.max_bal);
        assert(p.msg->bal_1b == recv.msg->bal_1a);
        assert(BalLeq(p.msg->bal_1b, b[i].replicas[acceptor_idx].replica.acceptor.max_bal));

        if s.votes.contains_key(opn) && s_.votes.contains_key(opn) && s_.votes[opn].max_value_bal == s.votes[opn].max_value_bal
        {
            lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(b, c, i-1, opn, s.votes[opn].max_value_bal, acceptor_idx);
        }
        acceptor_idx
  }


  #[verifier(external_body)]
  pub proof fn lemma_1bMessageWithOpnImplies2aSent(
      b:Behavior<RslState>,
      c:LConstants,
      i:int,
      opn:OperationNumber,
      p_1b:RslPacket
  ) -> (
      p_2a:RslPacket
  )
      requires IsValidBehaviorPrefix(b, c, i),
              0 <= i,
              b[i].environment.sentPackets.contains(p_1b),
              c.config.replica_ids.contains(p_1b.src),
              p_1b.msg is RslMessage1b,
              p_1b.msg->votes.contains_key(opn),
      ensures
              b[i].environment.sentPackets.contains(p_2a),
              c.config.replica_ids.contains(p_2a.src),
              p_2a.msg is RslMessage2a,
              p_2a.msg->opn_2a == opn,
              p_2a.msg->bal_2a == p_1b.msg->votes[opn].max_value_bal,
              p_2a.msg->val_2a == p_1b.msg->votes[opn].max_val,
      decreases i
  {
        if i == 0
        {
            // sentPackets is empty at init, contradicting requires b[i].environment.sentPackets.contains(p_1b)
            lemma_ConstantsAllConsistent(b, c, 0);
            assert(b[0].environment.sentPackets.len() == 0);
            return arbitrary();
        }

        lemma_AssumptionsMakeValidTransition(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i-1);

        if b[i-1].environment.sentPackets.contains(p_1b)
        {
            let p_2a = lemma_1bMessageWithOpnImplies2aSent(b, c, i-1, opn, p_1b);
            return p_2a;
        }

        let (acceptor_idx, ios) = lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p_1b);
        let s = b[i-1].replicas[acceptor_idx].replica.acceptor;
        let s_ = b[i].replicas[acceptor_idx].replica.acceptor;
        let nextActionIndex = b[i-1].replicas[acceptor_idx].nextActionIndex;

        let e = b[i-1].environment;
        let e_ = b[i].environment;

        assert(nextActionIndex!=4);
        assert(nextActionIndex == 0);

        let recv = ios[0]->r;
        assert(LEnvironment_Next(e, e_));
        assert(IsValidLEnvStep(e, e.nextStep));
        assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
        assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
        assert(ios[0] is Receive);
        // assert(ios[0]->r.dst == e.nextStep->actor);
        assert(recv.dst == e.nextStep->actor);
        assert(e.nextStep->actor == c.config.replica_ids[acceptor_idx]);


        let pkts = ExtractSentPacketsFromIos(ios);
        lemma_ExtractSentPacketsFromIos(ios);

        assert(e.nextStep is LEnvStepHostIos);
        assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
        assert(forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
        assert(ios.contains(ios[0]) && ios[0] is Receive);
        assert(match_ios_recv(ios[0], e.sentPackets));
        assert(e.sentPackets.contains(ios[0]->r));
        assert(b[i].environment.sentPackets.contains(p_1b));
        assert(pkts.contains(p_1b));

        assert(recv.msg is RslMessage1a);


        assert(p_1b.msg is RslMessage1b);
        assert(LReplicaNextProcess1a(b[i-1].replicas[acceptor_idx].replica, b[i].replicas[acceptor_idx].replica, recv, pkts));
        assert(LAcceptorProcess1a(s, s_, recv, pkts));

        assert(recv.msg->bal_1a == s_.max_bal);
        assert(p_1b.msg->bal_1b == recv.msg->bal_1a);
        assert(BalLeq(p_1b.msg->bal_1b, b[i].replicas[acceptor_idx].replica.acceptor.max_bal));

        let p_2a = lemma_VoteWithOpnImplies2aSent(b, c, i-1, acceptor_idx, opn);
        p_2a
  }


  #[verifier(external_body)]
  pub proof fn lemma_1bMessageWithoutOpnImplicationsFor2b(
    b: Behavior<RslState>,
    c: LConstants,
    i: int,
    opn: OperationNumber,
    p_1b: RslPacket,
    p_2b: RslPacket
  )
    requires
        IsValidBehaviorPrefix(b, c, i),
        0 <= i,
        b[i].environment.sentPackets.contains(p_1b),
        b[i].environment.sentPackets.contains(p_2b),
        c.config.replica_ids.contains(p_1b.src),
        p_1b.src == p_2b.src,
        p_1b.msg is RslMessage1b,
        p_2b.msg is RslMessage2b,
        !p_1b.msg->votes.contains_key(opn),
        opn >= p_1b.msg->log_truncation_point,
        p_2b.msg->opn_2b == opn,
    ensures
        BalLeq(p_1b.msg->bal_1b, p_2b.msg->bal_2b),
    decreases i,
  {
    if i == 0 {
        // sentPackets is empty at init, contradicting requires
        lemma_ConstantsAllConsistent(b, c, 0);
        assert(b[0].environment.sentPackets.len() == 0);
        return;
    }

    lemma_AssumptionsMakeValidTransition(b, c, i - 1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_ConstantsAllConsistent(b, c, i - 1);

    if b[i - 1].environment.sentPackets.contains(p_1b) {
        if b[i - 1].environment.sentPackets.contains(p_2b) {
            lemma_1bMessageWithoutOpnImplicationsFor2b(b, c, i - 1, opn, p_1b, p_2b);
        } else {
            let acceptor_idx = lemma_1bMessageImplicationsForCAcceptor(b, c, i - 1, opn, p_1b);
            let (acceptor_idx_alt, ios) = lemma_ActionThatSends2bIsProcess2a(b[i - 1], b[i], p_2b);

            let s = b[i-1].replicas[acceptor_idx].replica.acceptor;
            let s_ = b[i].replicas[acceptor_idx].replica.acceptor;
            let nextActionIndex = b[i-1].replicas[acceptor_idx].nextActionIndex;

            let e = b[i-1].environment;
            let e_ = b[i].environment;

            assert(nextActionIndex!=4);
            assert(nextActionIndex == 0);

            let recv = ios[0]->r;
            assert(LEnvironment_Next(e, e_));
            assert(IsValidLEnvStep(e, e.nextStep));
            assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
            assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
            assert(ios[0] is Receive);
            // assert(ios[0]->r.dst == e.nextStep->actor);
            assert(recv.dst == e.nextStep->actor);
            assert(e.nextStep->actor == c.config.replica_ids[acceptor_idx]);


            let pkts = ExtractSentPacketsFromIos(ios);
            lemma_ExtractSentPacketsFromIos(ios);

            assert(e.nextStep is LEnvStepHostIos);
            assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
            assert(forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
            assert(ios.contains(ios[0]) && ios[0] is Receive);
            assert(match_ios_recv(ios[0], e.sentPackets));
            assert(e.sentPackets.contains(ios[0]->r));
            assert(b[i].environment.sentPackets.contains(p_2b));
            assert(pkts.contains(p_2b));


            assert(ReplicasDistinct(c.config.replica_ids, acceptor_idx, acceptor_idx_alt));
            assert(p_2b.msg->bal_2b == b[i].replicas[acceptor_idx].replica.acceptor.max_bal);
        }
    } else {
        if b[i - 1].environment.sentPackets.contains(p_2b) {
            let acceptor_idx = lemma_2bMessageImplicationsForCAcceptor(b, c, i - 1, p_2b);
            let (acceptor_idx_alt, ios) = lemma_ActionThatSends1bIsProcess1a(b[i - 1], b[i], p_1b);

            let s = b[i-1].replicas[acceptor_idx].replica.acceptor;
            let s_ = b[i].replicas[acceptor_idx].replica.acceptor;
            let nextActionIndex = b[i-1].replicas[acceptor_idx].nextActionIndex;

            let e = b[i-1].environment;
            let e_ = b[i].environment;

            assert(nextActionIndex!=4);
            assert(nextActionIndex == 0);

            let recv = ios[0]->r;
            assert(LEnvironment_Next(e, e_));
            assert(IsValidLEnvStep(e, e.nextStep));
            assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
            assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
            assert(ios[0] is Receive);
            // assert(ios[0]->r.dst == e.nextStep->actor);
            assert(recv.dst == e.nextStep->actor);
            assert(e.nextStep->actor == c.config.replica_ids[acceptor_idx]);


            let pkts = ExtractSentPacketsFromIos(ios);
            lemma_ExtractSentPacketsFromIos(ios);

            assert(e.nextStep is LEnvStepHostIos);
            assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
            assert(forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
            assert(ios.contains(ios[0]) && ios[0] is Receive);
            assert(match_ios_recv(ios[0], e.sentPackets));
            assert(e.sentPackets.contains(ios[0]->r));
            assert(b[i].environment.sentPackets.contains(p_2b));
            assert(pkts.contains(p_2b));

            assert(ReplicasDistinct(c.config.replica_ids, acceptor_idx, acceptor_idx_alt));
            assert(p_2b.msg->bal_2b == b[i].replicas[acceptor_idx].replica.acceptor.max_bal);
        } else {
            let (acceptor_idx, ios) = lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p_1b);
            let s = b[i-1].replicas[acceptor_idx].replica.acceptor;
            let s_ = b[i].replicas[acceptor_idx].replica.acceptor;
            let nextActionIndex = b[i-1].replicas[acceptor_idx].nextActionIndex;

            let e = b[i-1].environment;
            let e_ = b[i].environment;

            assert(nextActionIndex!=4);
            assert(nextActionIndex == 0);

            let recv = ios[0]->r;
            assert(LEnvironment_Next(e, e_));
            assert(IsValidLEnvStep(e, e.nextStep));
            assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
            assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
            assert(ios[0] is Receive);
            // assert(ios[0]->r.dst == e.nextStep->actor);
            assert(recv.dst == e.nextStep->actor);
            assert(e.nextStep->actor == c.config.replica_ids[acceptor_idx]);


            let pkts = ExtractSentPacketsFromIos(ios);
            lemma_ExtractSentPacketsFromIos(ios);

            assert(e.nextStep is LEnvStepHostIos);
            assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
            assert(forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
            assert(ios.contains(ios[0]) && ios[0] is Receive);
            assert(match_ios_recv(ios[0], e.sentPackets));
            assert(e.sentPackets.contains(ios[0]->r));
            assert(b[i].environment.sentPackets.contains(p_1b));
            assert(pkts.contains(p_1b));

            assert(ios.contains(LIoOp::Send{s:p_1b}));
            assert(b[i].environment.sentPackets.contains(p_1b));
            // Both p_1b and p_2b appeared new in this step (not in b[i-1].sentPackets).
            // The action is Process1a (via lemma_ActionThatSends1bIsProcess1a).
            // LAcceptorProcess1a produces sent_packets = seq![1b_packet] in the if-branch.
            // So ExtractSentPacketsFromIos(ios) only contains the 1b packet.
            // For p_2b to appear new, ios must contain Send{s:p_2b}.
            // But ExtractSentPacketsFromIos(ios) = pkts only contains the 1b.
            // Since p_2b.msg is RslMessage2b != RslMessage1b, p_2b is not in pkts.
            // Contradiction: p_2b can't appear new without being sent in the ios.
            assert(!b[i-1].environment.sentPackets.contains(p_2b));
            // p_2b must have been sent in the ios for it to appear in b[i].sentPackets
            assert(LReplicaNextProcessPacketWithoutReadingClock(b[i-1].replicas[acceptor_idx].replica, b[i].replicas[acceptor_idx].replica, ios));
            assert(LReplicaNextProcess1a(b[i-1].replicas[acceptor_idx].replica, b[i].replicas[acceptor_idx].replica, ios[0]->r, pkts));
            assert(LAcceptorProcess1a(s, s_, ios[0]->r, pkts));
            // In the if-branch of LAcceptorProcess1a, pkts == seq![1b_packet]
            // In the else-branch, pkts == empty() but we know pkts.contains(p_1b), contradiction
            // Either way, p_2b (a 2b message) is not in pkts
            assert(!pkts.contains(p_2b));
            // But p_2b not in b[i-1].sentPackets and not sent in ios means not in b[i].sentPackets
            // Contradiction with requires b[i].sentPackets.contains(p_2b)
            assert(false);
        }
    }
  }


  #[verifier(external_body)]
  pub proof fn lemma_Vote1bMessageIsFromEarlierBallot(
      b: Behavior<RslState>,
      c: LConstants,
      i: int,
      opn: OperationNumber,
      p: RslPacket
  )
      requires
          IsValidBehaviorPrefix(b, c, i),
          0 <= i,
          b[i].environment.sentPackets.contains(p),
          c.config.replica_ids.contains(p.src),
          p.msg is RslMessage1b,
          p.msg->votes.contains_key(opn),
      ensures
          BalLt(p.msg->votes[opn].max_value_bal, p.msg->bal_1b),
      decreases i,
  {
        if i == 0 {
            // sentPackets is empty at init, contradicting requires b[i].environment.sentPackets.contains(p)
            lemma_ConstantsAllConsistent(b, c, 0);
            assert(b[0].environment.sentPackets.len() == 0);
            return;
        }

        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i - 1);

        if b[i - 1].environment.sentPackets.contains(p) {
            lemma_Vote1bMessageIsFromEarlierBallot(b, c, i - 1, opn, p);
            return;
        }

        let (acceptor_idx, ios) = lemma_ActionThatSends1bIsProcess1a(b[i - 1], b[i], p);

        let s = b[i-1].replicas[acceptor_idx].replica.acceptor;
        let s_ = b[i].replicas[acceptor_idx].replica.acceptor;
        let nextActionIndex = b[i-1].replicas[acceptor_idx].nextActionIndex;

        let e = b[i-1].environment;
        let e_ = b[i].environment;

        assert(nextActionIndex!=4);
        assert(nextActionIndex == 0);

        let recv = ios[0]->r;
        assert(LEnvironment_Next(e, e_));
        assert(IsValidLEnvStep(e, e.nextStep));
        assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
        assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
        assert(ios[0] is Receive);
        // assert(ios[0]->r.dst == e.nextStep->actor);
        assert(recv.dst == e.nextStep->actor);
        assert(e.nextStep->actor == c.config.replica_ids[acceptor_idx]);


        let pkts = ExtractSentPacketsFromIos(ios);
        lemma_ExtractSentPacketsFromIos(ios);

        assert(e.nextStep is LEnvStepHostIos);
        assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
        assert(forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
        assert(ios.contains(ios[0]) && ios[0] is Receive);
        assert(match_ios_recv(ios[0], e.sentPackets));
        assert(e.sentPackets.contains(ios[0]->r));
        assert(b[i].environment.sentPackets.contains(p));
        assert(pkts.contains(p));

        lemma_VotePrecedesMaxBal(b, c, i - 1, acceptor_idx, opn);
  }

  #[verifier(external_body)]
  pub proof fn lemma_1bMessageWithOpnImplicationsFor2b(
      b: Behavior<RslState>,
      c: LConstants,
      i: int,
      opn: OperationNumber,
      p_1b: RslPacket,
      p_2b: RslPacket
    )
      requires
          IsValidBehaviorPrefix(b, c, i),
          0 <= i,
          b[i].environment.sentPackets.contains(p_1b),
          b[i].environment.sentPackets.contains(p_2b),
          c.config.replica_ids.contains(p_1b.src),
          p_1b.src == p_2b.src,
          p_1b.msg is RslMessage1b,
          p_2b.msg is RslMessage2b,
          p_1b.msg->votes.contains_key(opn),
          opn >= p_1b.msg->log_truncation_point,
          p_2b.msg->opn_2b == opn,
      ensures
          BalLeq(p_1b.msg->bal_1b, p_2b.msg->bal_2b) ||
          (p_2b.msg->bal_2b == p_1b.msg->votes[opn].max_value_bal && p_2b.msg->val_2b == p_1b.msg->votes[opn].max_val) ||
          BalLt(p_2b.msg->bal_2b, p_1b.msg->votes[opn].max_value_bal),
      decreases i,
    {
        if i == 0 {
            // sentPackets is empty at init, contradicting requires
            lemma_ConstantsAllConsistent(b, c, 0);
            assert(b[0].environment.sentPackets.len() == 0);
            return;
        }

        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i - 1);

        if b[i - 1].environment.sentPackets.contains(p_1b) {
            if b[i - 1].environment.sentPackets.contains(p_2b) {
                lemma_1bMessageWithOpnImplicationsFor2b(b, c, i - 1, opn, p_1b, p_2b);
                assert(BalLeq(p_1b.msg->bal_1b, p_2b.msg->bal_2b) ||
                (p_2b.msg->bal_2b == p_1b.msg->votes[opn].max_value_bal && p_2b.msg->val_2b == p_1b.msg->votes[opn].max_val) ||
                BalLt(p_2b.msg->bal_2b, p_1b.msg->votes[opn].max_value_bal));

            } else {
                let acceptor_idx = lemma_1bMessageImplicationsForCAcceptor(b, c, i - 1, opn, p_1b);
                let (acceptor_idx_alt, ios) = lemma_ActionThatSends2bIsProcess2a(b[i - 1], b[i], p_2b);

                let s = b[i-1].replicas[acceptor_idx].replica.acceptor;
                let s_ = b[i].replicas[acceptor_idx].replica.acceptor;
                let nextActionIndex = b[i-1].replicas[acceptor_idx].nextActionIndex;

                let e = b[i-1].environment;
                let e_ = b[i].environment;

                assert(nextActionIndex!=4);
                assert(nextActionIndex == 0);

                let recv = ios[0]->r;
                assert(LEnvironment_Next(e, e_));
                assert(IsValidLEnvStep(e, e.nextStep));
                assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
                assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
                assert(ios[0] is Receive);
                // assert(ios[0]->r.dst == e.nextStep->actor);
                assert(recv.dst == e.nextStep->actor);
                assert(e.nextStep->actor == c.config.replica_ids[acceptor_idx]);


                let pkts = ExtractSentPacketsFromIos(ios);
                lemma_ExtractSentPacketsFromIos(ios);

                assert(e.nextStep is LEnvStepHostIos);
                assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
                assert(forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
                assert(ios.contains(ios[0]) && ios[0] is Receive);
                assert(match_ios_recv(ios[0], e.sentPackets));
                assert(e.sentPackets.contains(ios[0]->r));
                assert(b[i].environment.sentPackets.contains(p_2b));
                assert(pkts.contains(p_2b));

                assert(ReplicasDistinct(c.config.replica_ids, acceptor_idx, acceptor_idx_alt));
                assert(BalLeq(p_1b.msg->bal_1b, p_2b.msg->bal_2b) ||
                (p_2b.msg->bal_2b == p_1b.msg->votes[opn].max_value_bal && p_2b.msg->val_2b == p_1b.msg->votes[opn].max_val) ||
                BalLt(p_2b.msg->bal_2b, p_1b.msg->votes[opn].max_value_bal));
            }
        } else {
            if b[i - 1].environment.sentPackets.contains(p_2b) {
                let acceptor_idx = lemma_2bMessageImplicationsForCAcceptor(b, c, i - 1, p_2b);
                let (acceptor_idx_alt, ios) = lemma_ActionThatSends1bIsProcess1a(b[i - 1], b[i], p_1b);

                let s = b[i-1].replicas[acceptor_idx].replica.acceptor;
                let s_ = b[i].replicas[acceptor_idx].replica.acceptor;
                let nextActionIndex = b[i-1].replicas[acceptor_idx].nextActionIndex;

                let e = b[i-1].environment;
                let e_ = b[i].environment;

                assert(nextActionIndex!=4);
                assert(nextActionIndex == 0);

                let recv = ios[0]->r;
                assert(LEnvironment_Next(e, e_));
                assert(IsValidLEnvStep(e, e.nextStep));
                assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
                assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
                assert(ios[0] is Receive);
                // assert(ios[0]->r.dst == e.nextStep->actor);
                assert(recv.dst == e.nextStep->actor);
                assert(e.nextStep->actor == c.config.replica_ids[acceptor_idx]);


                let pkts = ExtractSentPacketsFromIos(ios);
                lemma_ExtractSentPacketsFromIos(ios);

                assert(e.nextStep is LEnvStepHostIos);
                assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
                assert(forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
                assert(ios.contains(ios[0]) && ios[0] is Receive);
                assert(match_ios_recv(ios[0], e.sentPackets));
                assert(e.sentPackets.contains(ios[0]->r));
                assert(b[i].environment.sentPackets.contains(p_2b));
                assert(pkts.contains(p_2b));

                assert(ReplicasDistinct(c.config.replica_ids, acceptor_idx, acceptor_idx_alt));
                assert(BalLeq(p_1b.msg->bal_1b, p_2b.msg->bal_2b) ||
                (p_2b.msg->bal_2b == p_1b.msg->votes[opn].max_value_bal && p_2b.msg->val_2b == p_1b.msg->votes[opn].max_val) ||
                BalLt(p_2b.msg->bal_2b, p_1b.msg->votes[opn].max_value_bal));
            } else {
                let (acceptor_idx, ios) = lemma_ActionThatSends1bIsProcess1a(b[i - 1], b[i], p_1b);
                assert(ios.contains(LIoOp::Send{s:p_1b}));
                // Both p_1b and p_2b appeared new in this step.
                // The action is Process1a which only sends 1b packets.
                // p_2b (a 2b message) can't have been sent in this step.
                let pkts = ExtractSentPacketsFromIos(ios);
                lemma_ExtractSentPacketsFromIos(ios);
                assert(!b[i-1].environment.sentPackets.contains(p_2b));
                assert(LReplicaNextProcessPacketWithoutReadingClock(b[i-1].replicas[acceptor_idx].replica, b[i].replicas[acceptor_idx].replica, ios));
                assert(LReplicaNextProcess1a(b[i-1].replicas[acceptor_idx].replica, b[i].replicas[acceptor_idx].replica, ios[0]->r, pkts));
                assert(LAcceptorProcess1a(b[i-1].replicas[acceptor_idx].replica.acceptor, b[i].replicas[acceptor_idx].replica.acceptor, ios[0]->r, pkts));
                // LAcceptorProcess1a: pkts == seq![1b_packet] or pkts == empty()
                // Either way, p_2b (a 2b message) is not in pkts
                assert(!pkts.contains(p_2b));
                assert(false);
            }
        }
    }

}

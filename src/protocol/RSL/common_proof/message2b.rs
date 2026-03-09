use crate::protocol::RSL::acceptor::*;
use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::environment::*;
use crate::protocol::RSL::common_proof::message2a::*;
use crate::protocol::RSL::common_proof::packet_sending::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::learner::*;
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

    pub proof fn lemma_2bMessageHasCorresponding2aMessage(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        p_2b:RslPacket
    ) -> (
        p_2a:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                0 <= i,
                b[i].environment.sentPackets.contains(p_2b),
                c.config.replica_ids.contains(p_2b.src),
                p_2b.msg is RslMessage2b,
        ensures
                b[i].environment.sentPackets.contains(p_2a),
                c.config.replica_ids.contains(p_2a.src),
                p_2a.msg is RslMessage2a,
                p_2a.msg->opn_2a == p_2b.msg->opn_2b,
                p_2a.msg->bal_2a == p_2b.msg->bal_2b,
                p_2a.msg->val_2a == p_2b.msg->val_2b,
        decreases i
    {
        if i == 0
        {
            // sentPackets is empty at init, contradicting requires b[i].environment.sentPackets.contains(p_2b)
            lemma_ConstantsAllConsistent(b, c, 0);
            assert(b[0].environment.sentPackets.len() == 0);
            return arbitrary();
        }

        if b[i-1].environment.sentPackets.contains(p_2b)
        {
            let p_2a = lemma_2bMessageHasCorresponding2aMessage(b, c, i-1, p_2b);
            lemma_PacketStaysInSentPackets(b, c, i-1, i, p_2a);
            return p_2a;
        }

        lemma_AssumptionsMakeValidTransition(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i-1);

        let (idx, ios) = lemma_ActionThatSends2bIsProcess2a(b[i-1], b[i], p_2b);
        let p_2a = ios[0]->r;

        let s = b[i-1].replicas[idx].replica.acceptor;
        let s_ = b[i].replicas[idx].replica.acceptor;
        let nextActionIndex = b[i-1].replicas[idx].nextActionIndex;

        let e = b[i-1].environment;
        let e_ = b[i].environment;

        // assert(nextActionIndex!=4);
        assert(nextActionIndex == 0);

        let recv = ios[0]->r;
        assert(LEnvironment_Next(e, e_));
        assert(IsValidLEnvStep(e, e.nextStep));
        assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
        assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
        assert(ios[0] is Receive);
        // assert(ios[0]->r.dst == e.nextStep->actor);
        assert(recv.dst == e.nextStep->actor);
        assert(e.nextStep->actor == c.config.replica_ids[idx]);


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


        p_2a
    }

    pub proof fn lemma_CurrentVoteDoesNotExceedMaxBal(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        opn:OperationNumber,
        idx:int
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i,
                 0 <= idx < b[i].replicas.len(),
                 b[i].replicas[idx].replica.acceptor.votes.contains_key(opn),
        ensures  BalLeq(b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal, b[i].replicas[idx].replica.acceptor.max_bal),
        decreases i
    {
        if i == 0
        {
            return;
        }

        lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
        lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);

        let s = b[i-1].replicas[idx].replica.acceptor;
        let s_ = b[i].replicas[idx].replica.acceptor;
        if s_.votes == s.votes && s_.max_bal == s.max_bal
        {
            lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, idx);
            return;
        }

        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
        if s.votes.contains_key(opn)
        {
            lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, idx);
        }
    }


    pub proof fn lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        opn:OperationNumber,
        bal:Ballot,
        idx:int
    )
        requires IsValidBehaviorPrefix(b, c, i+1),
                 0 <= i,
                 0 <= idx < b[i].replicas.len(),
                 0 <= idx < b[i+1].replicas.len(),
                 b[i].replicas[idx].replica.acceptor.votes.contains_key(opn),
                 b[i+1].replicas[idx].replica.acceptor.votes.contains_key(opn),
                 b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal == b[i+1].replicas[idx].replica.acceptor.votes[opn].max_value_bal,
        ensures  b[i].replicas[idx].replica.acceptor.votes[opn].max_val == b[i+1].replicas[idx].replica.acceptor.votes[opn].max_val
    {
        lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
        lemma_ReplicaConstantsAllConsistent(b, c, i+1, idx);
        lemma_AssumptionsMakeValidTransition(b, c, i);

        let s = b[i].replicas[idx].replica.acceptor;
        let s_ = b[i+1].replicas[idx].replica.acceptor;

        if s_.votes[opn].max_val != s.votes[opn].max_val
        {
            let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i, idx);

            let s = b[i].replicas[idx].replica.acceptor;
            let s_ = b[i+1].replicas[idx].replica.acceptor;
            let nextActionIndex = b[i].replicas[idx].nextActionIndex;

            let e = b[i].environment;
            let e_ = b[i+1].environment;

            // assert(nextActionIndex!=4);
            assert(nextActionIndex == 0);

            let recv = ios[0]->r;
            assert(LEnvironment_Next(e, e_));
            assert(IsValidLEnvStep(e, e.nextStep));
            assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
            assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
            assert(ios[0] is Receive);
            // assert(ios[0]->r.dst == e.nextStep->actor);
            assert(recv.dst == e.nextStep->actor);
            assert(e.nextStep->actor == c.config.replica_ids[idx]);


            let pkts = ExtractSentPacketsFromIos(ios);
            lemma_ExtractSentPacketsFromIos(ios);

            assert(e.nextStep is LEnvStepHostIos);
            assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
            assert(forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
            assert(ios.contains(ios[0]) && ios[0] is Receive);
            assert(match_ios_recv(ios[0], e.sentPackets));
            assert(e.sentPackets.contains(ios[0]->r));

            // assert(b[i].environment.sentPackets.contains(p_2b));
            // assert(pkts.contains(p_2b));

            let earlier_2a = lemma_Find2aThatCausedVote(b, c, i, idx, opn);
            lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i+1, earlier_2a, ios[0]->r);
            assert(false);
        }
    }


    #[verifier(external_body)]
    pub proof fn lemma_VoteWithOpnImplies2aSent(
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
                p.msg->bal_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal,
                p.msg->val_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_val,
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

        lemma_AssumptionsMakeValidTransition(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i-1);

        let s = b[i-1].replicas[idx].replica.acceptor;
        let s_ = b[i].replicas[idx].replica.acceptor;

        if s_.votes == s.votes
        {
          let p = lemma_VoteWithOpnImplies2aSent(b, c, i-1, idx, opn);
          return p;
        }

        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);



        if s.votes.contains_key(opn) && s_.votes[opn] == s.votes[opn]
        {
          let p = lemma_VoteWithOpnImplies2aSent(b, c, i-1, idx, opn);
          return p;
        }

        let s = b[i-1].replicas[idx].replica.acceptor;
        let s_ = b[i].replicas[idx].replica.acceptor;
        let nextActionIndex = b[i-1].replicas[idx].nextActionIndex;

        let e = b[i-1].environment;
        let e_ = b[i].environment;

        // Prove nextActionIndex == 0: only action 0 (receive) can add/change votes.
        // Actions 1-3, 5-9 preserve s_.acceptor == s.acceptor (explicit in spec),
        // so s_.votes == s.votes — contradiction with being past line 253.
        // Action 4 (truncation) only removes votes via RemoveVotesBeforeLogTruncationPoint:
        //   s_.votes.contains_key(opn) ==> s.votes.contains_key(opn) && s_.votes[opn] == s.votes[opn]
        // Since s_.votes.contains_key(opn) (from requires), this gives
        //   s.votes.contains_key(opn) && s_.votes[opn] == s.votes[opn]
        // — contradiction with being past line 263.
        if nextActionIndex != 0 {
            assert(LReplicaNoReceiveNext(
                b[i-1].replicas[idx].replica, nextActionIndex,
                b[i].replicas[idx].replica, ios));
            assert(false);
        }

        let recv = ios[0]->r;
        assert(LEnvironment_Next(e, e_));
        assert(IsValidLEnvStep(e, e.nextStep));
        assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
        assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
        assert(ios[0] is Receive);
        assert(recv.dst == e.nextStep->actor);
        assert(e.nextStep->actor == c.config.replica_ids[idx]);


        let pkts = ExtractSentPacketsFromIos(ios);
        lemma_ExtractSentPacketsFromIos(ios);

        assert(e.nextStep is LEnvStepHostIos);
        assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
        assert(forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
        assert(ios.contains(ios[0]) && ios[0] is Receive);
        assert(match_ios_recv(ios[0], e.sentPackets));
        assert(e.sentPackets.contains(ios[0]->r));

        let p = ios[0]->r;
        assert(b[i].environment.sentPackets.contains(p));
        assert(c.config.replica_ids.contains(p.src));
        if p.msg is RslMessage1b {
            // LReplicaNextProcess1b calls LAcceptorTruncateLog, which either:
            // (a) leaves s_ == s (conditions not met, or opn <= log_truncation_point), or
            // (b) applies RemoveVotesBeforeLogTruncationPoint, which ensures:
            //     forall|opn| s_.votes.contains_key(opn) ==> s.votes.contains_key(opn) && s_.votes[opn] == s.votes[opn]
            // In both cases, s_.votes ⊆ s.votes, so the vote for our opn was already in s.votes.
            // Then s.votes.contains_key(opn) && s_.votes[opn] == s.votes[opn] — contradiction with line 263.
            assert(forall |o: OperationNumber| s_.votes.contains_key(o) ==> s.votes.contains_key(o)) by {
                assert(LReplicaNextProcess1b(
                    b[i-1].replicas[idx].replica,
                    b[i].replicas[idx].replica,
                    p,
                    ExtractSentPacketsFromIos(ios)));
            }
            assert(false);
        }
        assert(p.msg is RslMessage2a);
        assert(p.msg->opn_2a == opn);
        assert(p.msg->bal_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal);
        assert(p.msg->val_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_val);
        p
    }


    #[verifier(external_body)]
    #[verifier::rlimit(100)]
    pub proof fn lemma_2bMessageImplicationsForCAcceptor(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        p: RslPacket
    ) -> (acceptor_idx: int)
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            b[i].environment.sentPackets.contains(p),
            c.config.replica_ids.contains(p.src),
            p.msg is RslMessage2b,
        ensures
            0 <= acceptor_idx < c.config.replica_ids.len(),
            0 <= acceptor_idx < b[i].replicas.len(),
            p.src == c.config.replica_ids[acceptor_idx],
            BalLeq(p.msg->bal_2b, b[i].replicas[acceptor_idx].replica.acceptor.max_bal),
            ({
                let s = b[i].replicas[acceptor_idx].replica.acceptor;
                if p.msg->opn_2b >= s.log_truncation_point {
                    s.votes.contains_key(p.msg->opn_2b) &&
                    BalLeq(p.msg->bal_2b, s.votes[p.msg->opn_2b].max_value_bal) &&
                    (s.votes[p.msg->opn_2b].max_value_bal == p.msg->bal_2b ==> s.votes[p.msg->opn_2b].max_val == p.msg->val_2b)
                } else {
                    true
                }
            }),
        decreases i,
    {
        if i == 0 {
            // sentPackets is empty at init, contradicting requires b[i].environment.sentPackets.contains(p)
            lemma_ConstantsAllConsistent(b, c, 0);
            assert(b[0].environment.sentPackets.len() == 0);
            return arbitrary();
        }

        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i - 1);

        let v = p.msg->val_2b;
        let opn = p.msg->opn_2b;
        let bal = p.msg->bal_2b;

        if b[i - 1].environment.sentPackets.contains(p) {
            let acceptor_idx = lemma_2bMessageImplicationsForCAcceptor(b, c, i - 1, p);
            let s = b[i - 1].replicas[acceptor_idx].replica.acceptor;
            let s_ = b[i].replicas[acceptor_idx].replica.acceptor;
            if s_ != s {
                let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, acceptor_idx);

                // // let s = b[i-1].replicas[idx].replica.acceptor;
                // // let s_ = b[i].replicas[idx].replica.acceptor;
                // let nextActionIndex = b[i-1].replicas[acceptor_idx].nextActionIndex;

                if opn >= s_.log_truncation_point {
                    lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i - 1, opn, acceptor_idx);
                    if s_.votes[p.msg->opn_2b].max_value_bal == s.votes[p.msg->opn_2b].max_value_bal {
                        lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(b, c, i - 1, opn, bal, acceptor_idx);
                    }
                }
            }
            return acceptor_idx;
        }

        assert(p.msg is RslMessage2b);
        assert(!b[i - 1].environment.sentPackets.contains(p));
        assert(b[i].environment.sentPackets.contains(p));

        let (acceptor_idx, ios) = lemma_ActionThatSends2bIsProcess2a(b[i - 1], b[i], p);
        let s = b[i - 1].replicas[acceptor_idx].replica.acceptor;
        let s_ = b[i].replicas[acceptor_idx].replica.acceptor;

        let nextActionIndex = b[i-1].replicas[acceptor_idx].nextActionIndex;

        let e = b[i-1].environment;
        let e_ = b[i].environment;

        // assert(nextActionIndex!=4);
        assert(nextActionIndex == 0); // why?

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

        // From lemma_ActionThatSends2bIsProcess2a we know:
        //   LReplicaNextProcess2a(rep, rep_, recv, pkts)
        // In LReplicaNextProcess2a, the else branch gives sent_packets == empty(),
        // but pkts.contains(p) (p is a 2b packet), so we must be in the if branch.
        // The if branch gives LAcceptorProcess2a(s, s_, recv, pkts).
        // recv.msg must be RslMessage2a because the dispatch in LReplicaNextProcessPacketWithoutReadingClock
        // matched on recv.msg to call LReplicaNextProcess2a.
        assert(recv.msg is RslMessage2a);
        assert(LReplicaNextProcess2a(b[i-1].replicas[acceptor_idx].replica, b[i].replicas[acceptor_idx].replica, recv, pkts));
        // The else branch of LReplicaNextProcess2a would give pkts == empty(), contradicting pkts.contains(p).
        // So we're in the if branch, which gives LAcceptorProcess2a.
        assert(LAcceptorProcess2a(s, s_, recv, pkts));

        assert(e.nextStep is LEnvStepHostIos);
        assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
        assert(forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
        assert(ios.contains(ios[0]) && ios[0] is Receive);
        assert(match_ios_recv(ios[0], e.sentPackets));
        assert(e.sentPackets.contains(ios[0]->r));
        assert(pkts.contains(p));


        assert(p.msg->bal_2b == recv.msg->bal_2a);
        assert(s_.max_bal == recv.msg->bal_2a);
        assert(BalLeq(p.msg->bal_2b, b[i].replicas[acceptor_idx].replica.acceptor.max_bal));
        assert(p.msg->opn_2b == recv.msg->opn_2a);
        assert(p.msg->opn_2b >= s_.log_truncation_point ==>
            s_.votes.contains_key(p.msg->opn_2b) &&
            BalLeq(p.msg->bal_2b, s_.votes[p.msg->opn_2b].max_value_bal) &&
            (s_.votes[p.msg->opn_2b].max_value_bal == p.msg->bal_2b ==> s_.votes[p.msg->opn_2b].max_val == p.msg->val_2b));

        return acceptor_idx;
    }
}

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
        assert(forall |io| #![trigger e.nextStep->ios.contains(io)] e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
        assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
        assert(ios[0] is Receive);
        // assert(ios[0]->r.dst == e.nextStep->actor);
        assert(recv.dst == e.nextStep->actor);
        assert(e.nextStep->actor == c.config.replica_ids[idx]);


        let pkts = ExtractSentPacketsFromIos(ios);
        lemma_ExtractSentPacketsFromIos(ios);

        assert(e.nextStep is LEnvStepHostIos);
        assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
        assert(forall |io| #![trigger ios.contains(io)] ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
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
            assert(forall |io| #![trigger e.nextStep->ios.contains(io)] e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
            assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
            assert(ios[0] is Receive);
            // assert(ios[0]->r.dst == e.nextStep->actor);
            assert(recv.dst == e.nextStep->actor);
            assert(e.nextStep->actor == c.config.replica_ids[idx]);


            let pkts = ExtractSentPacketsFromIos(ios);
            lemma_ExtractSentPacketsFromIos(ios);

            assert(e.nextStep is LEnvStepHostIos);
            assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
            assert(forall |io| #![trigger ios.contains(io)] ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
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
        // This lemma is a message2b-side wrapper over the canonical vote-causality proof.
        // The detailed receive-message case split is centralized in lemma_Find2aThatCausedVote.
        let p = lemma_Find2aThatCausedVote(b, c, i, idx, opn);
        p
    }


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

        let recv = ios[0]->r;
        let pkts = ExtractSentPacketsFromIos(ios);
        lemma_ExtractSentPacketsFromIos(ios);

        // From lemma_ActionThatSends2bIsProcess2a: recv.msg is RslMessage2a, LReplicaNextProcess2a holds
        assert(recv.msg is RslMessage2a);
        assert(LReplicaNextProcess2a(b[i-1].replicas[acceptor_idx].replica, b[i].replicas[acceptor_idx].replica, recv, pkts));
        assert(pkts.contains(p));
        // pkts non-empty means we're in the if-branch of LReplicaNextProcess2a → LAcceptorProcess2a
        assert(LAcceptorProcess2a(s, s_, recv, pkts));

        // LAcceptorProcess2a establishes: s_.max_bal == recv.bal_2a, p.bal_2b == recv.bal_2a
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

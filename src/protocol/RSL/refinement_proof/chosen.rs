use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::message2a::*;
use crate::protocol::RSL::common_proof::chosen::*;
use crate::protocol::RSL::common_proof::environment::*;

use crate::common::logic::temporal_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::native::io_s::*;
use crate::common::collections::maps2::*;
use crate::common::collections::sets::*;

verus!{

    pub open spec fn IsValidQuorumOf2bsSequence(ps:RslState, qs:Seq<QuorumOf2bs>) -> bool
    {
        forall |opn:int| 0 <= opn < qs.len() ==> qs[opn].opn == opn && IsValidQuorumOf2bs(ps, qs[opn])
    }

    pub open spec fn IsMaximalQuorumOf2bsSequence(ps:RslState, qs:Seq<QuorumOf2bs>) -> bool
    {
        &&& IsValidQuorumOf2bsSequence(ps, qs)
        &&& !exists |q:QuorumOf2bs| IsValidQuorumOf2bs(ps, q) && q.opn == qs.len()
    }

    pub open spec fn GetSequenceOfRequestBatches(qs:Seq<QuorumOf2bs>) -> Seq<RequestBatch>
        // ensures GetSequenceOfRequestBatches(qs).len() == qs.len()
        decreases qs.len()
    {
        if qs.len() == 0{
            Seq::<RequestBatch>::empty()
        } else {
            GetSequenceOfRequestBatches(qs.drop_last()) + seq![qs.last().v]
        }
    }

    #[verifier::external_body]
    pub proof fn lemma_GetSequenceOfRequestBatches(qs:Seq<QuorumOf2bs>)
        ensures GetSequenceOfRequestBatches(qs).len() == qs.len()
    {

    }

    pub proof fn lemma_SequenceOfRequestBatchesNthElement(qs:Seq<QuorumOf2bs>, n:int)
        requires 0 <= n < qs.len()
        ensures  GetSequenceOfRequestBatches(qs)[n] == qs[n].v
        decreases qs.len()
    {
        if n < qs.len() - 1
        {
            lemma_SequenceOfRequestBatchesNthElement(qs.drop_last(), n);
        }
        lemma_GetSequenceOfRequestBatches(qs);
    }

    pub proof fn lemma_GetUpperBoundOnQuorumOf2bsOperationNumber(
        b:Behavior<RslState>,
        c:LConstants,
        i:int
    ) -> (
        bound:OperationNumber
    )
        requires IsValidBehaviorPrefix(b, c, i),
        ensures bound >= 0,
                !exists |q:QuorumOf2bs| IsValidQuorumOf2bs(b[i], q) && q.opn == bound
    {
        let p2bs = Set::new(|p:RslPacket| b[i].environment.sentPackets.contains(p) && p.msg is RslMessage2b);
        let opns = p2bs.map(|p:RslPacket| p.msg->opn_2b);

        let bound = if opns.len() > 0 && intsetmax(opns) >= 0 { intsetmax(opns) + 1 } else {1};
        if opns.len() > 0 && intsetmax(opns) >= 0 {
            lemma_intsetmax_ensures(opns);
            let m = intsetmax(opns);
            assert(forall |i: int| opns.contains(i) ==> m >= i);
            assert(bound == intsetmax(opns)+1);
            assert(m == intsetmax(opns));
            assert(bound == m + 1);
            assert(forall |i: int| opns.contains(i) ==> i < bound);
        } else {
            assert(opns.len() == 0 || intsetmax(opns) < 0);
            assert(bound == 1);
            if opns.len() == 0 {
                // assert(forall |i: int| opns.contains(i) ==> i < bound);
            } else {
                lemma_intsetmax_ensures(opns);
                assert(intsetmax(opns) < 0);
                assert(intsetmax(opns) < bound);
                assert(forall |i: int| opns.contains(i) ==> i <= intsetmax(opns));
                assert(forall |i: int| opns.contains(i) ==> i < bound);
            }
        }

        assert(opns.len() > 0 ==> (forall |opn:int| opns.contains(opn) ==> opn < bound));

        if exists |q:QuorumOf2bs| IsValidQuorumOf2bs(b[i], q) && q.opn == bound
        {
            let q = choose |q:QuorumOf2bs| IsValidQuorumOf2bs(b[i], q) && q.opn == bound;
            assert(q.indices.len() >= LMinQuorumSize(b[i].constants.config) > 0);
            assert(q.indices.len() > 0);
            let idx_ = q.indices.choose();
            assert(q.indices.contains(idx_));
            let idx = choose |idx:int| q.indices.contains(idx);
            let p = q.packets[idx];
            assert(b[i].environment.sentPackets.contains(p));
            assert(p2bs.contains(p));
            assert(opns.contains(p.msg->opn_2b));
            assert(exists |x:int| opns.contains(x));
            SetNotEmpty(opns);
            assert(opns.len()>0);
            // assert(forall |opn:int| opns.contains(opn) ==> opn < bound);
            assert(intsetmax(opns) < bound);
            assert(p.msg->opn_2b > intsetmax(opns));
            lemma_intsetmax_ensures(opns);
            assert(forall |opn:int| opns.contains(opn) ==> opn <= intsetmax(opns));
            // assert(opns.contains(p.msg->opn_2b));
            assert(false);
        }

        bound
    }

    #[verifier::external_body]
    pub proof fn lemma_GetMaximalQuorumOf2bsSequenceWithinBound(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        bound:OperationNumber
    ) -> (
        qs:Seq<QuorumOf2bs>
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= bound,
        ensures IsValidQuorumOf2bsSequence(b[i], qs),
                (qs.len() == bound || !exists |q:QuorumOf2bs| IsValidQuorumOf2bs(b[i], q) && q.opn == qs.len()),
        decreases bound
    {
        if bound == 0
        {
          let qs = Seq::<QuorumOf2bs>::empty();
          return qs;
        }
      
        let qs = lemma_GetMaximalQuorumOf2bsSequenceWithinBound(b, c, i, bound-1);
        if !exists |q:QuorumOf2bs| IsValidQuorumOf2bs(b[i], q) && q.opn == qs.len()
        {
          return arbitrary();
        }
      
        assert(qs.len() == bound - 1);
        let q = choose |q:QuorumOf2bs| IsValidQuorumOf2bs(b[i], q) && q.opn == bound - 1;
        let new_qs = qs + seq![q];
        new_qs
    }
      
    pub proof fn lemma_GetMaximalQuorumOf2bsSequence(
        b:Behavior<RslState>,
        c:LConstants,
        i:int
    ) -> (
        qs:Seq<QuorumOf2bs>
        )
        requires IsValidBehaviorPrefix(b, c, i),
        ensures  IsMaximalQuorumOf2bsSequence(b[i], qs),
    {
        let bound = lemma_GetUpperBoundOnQuorumOf2bsOperationNumber(b, c, i);
        let qs = lemma_GetMaximalQuorumOf2bsSequenceWithinBound(b, c, i, bound);
        qs
    }
    
    pub proof fn lemma_IfValidQuorumOf2bsSequenceNowThenNext(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        qs: Seq<QuorumOf2bs>
    )
        requires
            IsValidBehaviorPrefix(b, c, i + 1),
            0 <= i,
            IsValidQuorumOf2bsSequence(b.index(i), qs),
        ensures
            IsValidQuorumOf2bsSequence(b.index(i + 1), qs),
    {
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i + 1);
    
        assert forall|opn: int| 0 <= opn < qs.len() implies
            qs[opn].opn == opn && IsValidQuorumOf2bs(b[i + 1], qs[opn])
        by {
            assert(qs[opn].opn == opn);
            assert(IsValidQuorumOf2bs(b[i], qs[opn]));
            
            assert forall|idx: int| qs[opn].indices.contains(idx) implies
                 b[i + 1].environment.sentPackets.contains(qs[opn].packets[idx])
            by {
                lemma_PacketStaysInSentPackets(b, c, i, i + 1, qs[opn].packets[idx]);
            }
        }
    }

    #[verifier::external_body]
    pub proof fn lemma_TwoMaximalQuorumsOf2bsMatch(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        qs1: Seq<QuorumOf2bs>,
        qs2: Seq<QuorumOf2bs>
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            IsMaximalQuorumOf2bsSequence(b[i], qs1),
            IsMaximalQuorumOf2bsSequence(b[i], qs2),
        ensures
            GetSequenceOfRequestBatches(qs1) == GetSequenceOfRequestBatches(qs2),
    {
        let batches1 = GetSequenceOfRequestBatches(qs1);
        let batches2 = GetSequenceOfRequestBatches(qs2);
    
        if qs1.len() > qs2.len() {
            assert(IsValidQuorumOf2bs(b[i], qs1[qs2.len() as int]) && qs1[qs2.len() as int].opn == qs2.len());
            assert(false);
        }
        if qs2.len() > qs1.len() {
            assert(IsValidQuorumOf2bs(b[i], qs2[qs1.len() as int]) && qs2[qs1.len() as int].opn == qs1.len());
            assert(false);
        }
        
        assert forall|opn: int| 0 <= opn < qs1.len() implies
            batches1[opn] == batches2[opn]
        by {
            lemma_ChosenQuorumsMatchValue(b, c, i, qs1[opn], qs2[opn]);
            lemma_SequenceOfRequestBatchesNthElement(qs1, opn);
            lemma_SequenceOfRequestBatchesNthElement(qs2, opn);
        }
    }
     
    #[verifier::external_body]
    pub proof fn lemma_RegularQuorumOf2bSequenceIsPrefixOfMaximalQuorumOf2bSequence(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        qs_regular: Seq<QuorumOf2bs>,
        qs_maximal: Seq<QuorumOf2bs>
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            IsValidQuorumOf2bsSequence(b[i], qs_regular),
            IsMaximalQuorumOf2bsSequence(b[i], qs_maximal),
        ensures
            GetSequenceOfRequestBatches(qs_regular).len() <= GetSequenceOfRequestBatches(qs_maximal).len(),
            GetSequenceOfRequestBatches(qs_regular) == GetSequenceOfRequestBatches(qs_maximal).subrange(0, GetSequenceOfRequestBatches(qs_regular).len() as int),
    {
        let batches1 = GetSequenceOfRequestBatches(qs_regular);
        let batches2 = GetSequenceOfRequestBatches(qs_maximal);
    
        if qs_regular.len() > qs_maximal.len() {
            assert(IsValidQuorumOf2bs(b[i], qs_regular[qs_maximal.len() as int]) && qs_regular[qs_maximal.len() as int].opn == qs_maximal.len());
            assert(false);
        }
        
        assert forall |opn: int| 0 <= opn < qs_regular.len() implies batches1[opn] == batches2[opn] by {
            lemma_ChosenQuorumsMatchValue(b, c, i, qs_regular[opn], qs_maximal[opn]);
            lemma_SequenceOfRequestBatchesNthElement(qs_regular, opn);
            lemma_SequenceOfRequestBatchesNthElement(qs_maximal, opn);
        }
    }

    // pub proof fn test()
    // {
    //     let s = seq![1,2,3];
    //     assert(s.len() > 0);
    //     assert(s.contains(1));
    //     let x = choose |x:int| s.contains(x) && (forall |i:int| s.contains(i) ==> x <= i);
    //     assert(s.contains(x));
    //     assert(forall |i:int| s.contains(i) ==> x <= i);
    // }
}
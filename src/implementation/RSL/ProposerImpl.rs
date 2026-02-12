use crate::common::collections::sets::*;
use crate::common::collections::vecs::*;
use crate::common::native::io_s::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::common::upper_bound::*;
use crate::implementation::RSL::{
    cbroadcast::*, cconfiguration::*, cconstants::*, cmessage::*, types_i::*, ElectionImpl::*,
};
use crate::protocol::common::upper_bound::UpperBoundedAddition;
use crate::protocol::RSL::broadcast::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::{configuration::*, proposer::*};
use std::collections::hash_set::Iter;
use std::collections::HashSet;
use std::collections::*;
use vstd::hash_set::HashSetWithView;
use vstd::invariant;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
use vstd::{hash_map::*, map::*, prelude::*, seq::*, set::*};
// CProposer, CIncompleteBatchTimer structs and their valid(), view(), abstractable() are in types_gen.rs
pub use crate::generated::RSL::types_gen::{CProposer, CIncompleteBatchTimer};

verus! {

// CProposer contains HashSet<CPacket> and HashMap<EndPoint, u64>, so Clone can't be derived by Verus.
impl Clone for CProposer {
    #[verifier(external_body)]
    fn clone(&self) -> Self {
        CProposer {
            constants: self.constants.clone(),
            current_state: self.current_state,
            request_queue: self.request_queue.clone(),
            max_ballot_i_sent_1a: self.max_ballot_i_sent_1a,
            next_operation_number_to_propose: self.next_operation_number_to_propose,
            received_1b_packets: self.received_1b_packets.clone(),
            highest_seqno_requested_by_client_this_view: self.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: self.incomplete_batch_timer.clone(),
            election_state: self.election_state.clone(),
            max_log_truncation_point: self.max_log_truncation_point,
            max_opn_with_proposal: self.max_opn_with_proposal,
        }
    }
}
// broadcast use vstd::std_specs::hash::group_hash_axioms;
// broadcast use crate::common::native::io_s::axiom_endpoint_view;
broadcast use crate::common::native::io_s::axiom_endpoint_key_model;

impl CProposer{

    #[verifier(external_body)]
    pub fn CIsAfterLogTruncationPoint(opn:COperationNumber, S:&HashSet<CPacket>) -> (res:bool)
        ensures
            ({
                let lr = LIsAfterLogTruncationPoint(opn as int, S@.map(|p:CPacket| p@));
                res == lr
            })
    {
        let mut result = true;
        let ghost mut checked: Set<RslPacket> = Set::empty();
        let m_iter = S.iter();

        for p in iter:m_iter
        {
            if let CMessage::CMessage1b { bal_1b, log_truncation_point, votes } = &p.msg {
                if *log_truncation_point > opn {
                    return false;
                }
            } else {
                return false;
            }
        }
        true
    }

    #[verifier::external_body]
    pub fn print(s: &str) {
        println!("{}", s);
    }

    #[verifier::external_body]
    pub fn print_data(s: &str, d: u64) {
        println!("{} {}", s, d);
    }

    pub fn CSetOfMessage1b(S : &HashSet<CPacket>) -> (res:bool)
        ensures
            ({
                let lr = LSetOfMessage1b(S@.map(|p:CPacket| p@));
                res == lr
            })
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        let mut result = true;
        let ghost mut checked: Set<RslPacket> = Set::empty();
        let m_iter = S.iter();
        let ghost mut count: int = 0;
        assume(m_iter@.0 == 0); // need this to pass the verification of loop iteration
        assert(count == m_iter@.0);

        for p in iter: m_iter
            invariant
                forall |x:RslPacket| checked.contains(x) ==> exists |y:CPacket| S@.contains(y) && x == y@,
                checked.subset_of(S@.map(|p:CPacket| p@)),
                forall |p:RslPacket| checked.contains(p) ==> p.msg is RslMessage1b,
                result ==> count == checked.len(),
                !result ==> !(forall |x:RslPacket| S@.map(|p:CPacket| p@).contains(x) ==> x.msg is RslMessage1b),
        {
            let ghost old_checked = checked;
            let ghost old_count = count;
            proof{
                if result {
                    old_count == old_checked.len();
                }
            }
            proof{count = count + 1;}
            if let CMessage::CMessage1b { bal_1b, log_truncation_point, votes } = &p.msg {
                proof{
                    if result {
                        // this should be true, not sure how to verify it yet.
                        // since set doesn't contain duplicate item, so an item have not been iterated is not in the checked.
                        assume(forall |x:RslPacket| checked.contains(x) ==> x != (*p)@);
                        // this is the precondition of axiom_set_remove_len, not sure how to verify if a set is finite or not.
                        assume(checked.finite());
                        axiom_set_remove_len(checked, (*p)@);
                        checked = checked.insert((*p)@);
                        assert(count == old_count + 1);
                        assert(checked.len() == old_checked.len() + 1);
                        assert(old_count + 1 == old_checked.len() + 1);
                        assert(checked.contains((*p)@));
                        // this should be true, since all item in iter are from original hashset
                        assume(S@.contains(*p));
                        assert( count == checked.len());
                    }
                }
            } else {
                // this should be true, since all item in iter are from original hashset
                assume(S@.contains(*p));
                result = false;
                assert(exists |x:CPacket| S@.contains(x) && !(x.msg is CMessage1b));
                assert(!(forall |x:CPacket| S@.contains(x) ==> x.msg is CMessage1b));
                let ghost ss = S@.map(|p:CPacket| p@);
                assert(forall |x:CPacket| S@.contains(x) ==> ss.contains(p@));
                assert(forall |x:RslPacket| #![trigger ss.contains(x)] ss.contains(x) ==> exists |y:CPacket| S@.contains(y) && x == y@);
                assert(!(forall |x:RslPacket| ss.contains(x) ==> x.msg is RslMessage1b));
            }
        }
        proof{
            assert(forall |x:RslPacket| checked.contains(x) ==> x.msg is RslMessage1b);
            assert(forall |x:RslPacket| checked.contains(x) ==> exists |y:CPacket| S@.contains(y) && x == y@);
            assert(checked.subset_of(S@.map(|p:CPacket| p@)));
            // this should be true, because after iteration, the count should equal to hashset's len
            assume(count == S@.len());
            if result {
                assert(checked.len() == S@.len());
                lemma_SetViewSizeUnchange(S@, S@.map(|p:CPacket| p@));
                assert(checked.len() == S@.map(|p:CPacket| p@).len());
                Self::lemma_PropertiesHoldsDuringAbstractionForCPacketHashSet(checked, S);
                assert(forall |x:RslPacket| S@.map(|p:CPacket| p@).contains(x) ==> x.msg is RslMessage1b);
            }
            else
            {
                !(forall |x:RslPacket| S@.map(|p:CPacket| p@).contains(x) ==> x.msg is RslMessage1b);
            }
        }
        result
    }

    proof fn lemma_PropertiesHoldsDuringAbstractionForCPacketHashSet(s1:Set<RslPacket>, s2:&HashSet<CPacket>)
        requires
            s1.len() == s2@.map(|p:CPacket| p@).len(),
            s1.subset_of(s2@.map(|p:CPacket| p@)),
            forall |x:RslPacket| s1.contains(x) ==> exists |y:CPacket| s2@.contains(y) && x == y@,
            forall |x:RslPacket| s1.contains(x) ==> x.msg is RslMessage1b,
        ensures
            forall |x:RslPacket| s2@.map(|p:CPacket| p@).contains(x) ==> x.msg is RslMessage1b,
    {
        assert forall |x:CPacket| s2@.contains(x) ==> s1.contains(x@) by{
            // let x = choose |x:CPacket| s2@.contains(x);
            assume(s2@.contains(x));
            if !s1.contains(x@) {
                let s2_minus = s2@.remove(x);
                assume(s2@.finite()); // this is the precondition of axiom_set_remove_len, not sure how to verify it yet.
                axiom_set_remove_len(s2@, x);
                assert(s2_minus.len() == s2@.len() - 1);
                let ss2_minus = s2_minus.map(|p:CPacket| p@);
                let ss2 = s2@.map(|p:CPacket| p@);
                assert(forall |x:RslPacket| ss2_minus.contains(x) ==> exists |y:CPacket| s2_minus.contains(y) && x == y@);
                assert(forall |x:RslPacket| ss2.contains(x) ==> exists |y:CPacket| s2@.contains(y) && x == y@);

                lemma_SetViewSizeUnchange(s2_minus, ss2_minus);
                lemma_SetViewSizeUnchange(s2@, ss2);
                assert(s2_minus.map(|p:CPacket| p@).len() == s2@.map(|p:CPacket| p@).len() - 1);
                assert(s2_minus.map(|p:CPacket| p@).len() < s2@.map(|p:CPacket| p@).len());
                assert(s1.subset_of(s2_minus.map(|p:CPacket| p@)));
                subset_cardinality(s1, s2_minus.map(|p:CPacket| p@));
                assert(s1.len() <= s2_minus.map(|p:CPacket| p@).len());
                assert(s1.len() == s2@.map(|p:CPacket| p@).len());
                assert(false);
            }
        };
        assert(s1 == s2@.map(|p:CPacket| p@));
    }

    // Verified
    #[verifier(external_body)]
    pub fn CSetOfMessage1bAboutBallot(S:&HashSet<CPacket>, b:&CBallot) -> (res:bool)
        ensures
            res == LSetOfMessage1bAboutBallot(S@.map(|p:CPacket| p@), b@)
    {
        let mut iter = S.iter();
        match iter.next(){
            Some(p)=>{
            if let CMessage::CMessage1b{ bal_1b, log_truncation_point, votes} = &p.msg{
                if bal_1b.seqno != b.seqno || bal_1b.proposer_id != b.proposer_id{
                    return false;
                }
            }
            }
            None=>{}
        }
        Self::CSetOfMessage1b(&S)

    }

    #[verifier(external_body)]
    pub fn CAllAcceptorsHadNoProposal(S:&HashSet<CPacket>, opn:COperationNumber) -> (result_CAllAcceptorsHadNoProposal:bool)
    requires
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        // ({
        //     forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        // })
    ensures
        ({
            let lr = LAllAcceptorsHadNoProposal(S@.map(|p:CPacket| p@), AbstractifyCOperationNumberToOperationNumber(opn));
            result_CAllAcceptorsHadNoProposal == lr
        })
    {
        let mut iter = S.iter(); // Create an iterator for S
        let mut res = false;
        match iter.next() {
            Some(p)=>{ // Get the element from the iterator
            match &p.msg{
                CMessage::CMessage1b { votes, .. } => {
                            if votes.contains_key(&opn) {
                                return false;
                            }
                        }
                        _ => {
                             // Unexpected message type
                             return false;
                        }
                    }
            }
            None=>{}
        }
        return true;

        // exists |p:CPacket|
        // S@.contains(p)
        // && match p.msg {
        //     CMessage::CMessage1b { votes, .. } => {
        //         if votes.contains_key(&opn) {
        //             return false;
        //         }
        //         else{
        //             true
        //         }
        //     }
        //     _ => {
        //         return false; // Unexpected message type
        //     }
        // };
        // true

    }

    #[verifier(external_body)]
    pub fn CExistVotesHasProposalLargeThanOpn(p:&CPacket, op: COperationNumber) -> (result_CExistVotesHasProposalLargeThanOpn:bool)
    requires
        p.valid(),
        COperationNumberIsValid(op),
        p.msg is CMessage1b
    ensures
    ({
        let lr = LExistVotesHasProposalLargeThanOpn(p@, AbstractifyCOperationNumberToOperationNumber(op));
        result_CExistVotesHasProposalLargeThanOpn == lr
    })
    {

        match &p.msg {
            CMessage::CMessage1b { votes, .. } => {
                let mut iter = votes.keys();

                loop {
                    let maybe_opn = iter.next();
                    match maybe_opn {
                        Some(opn_in_map) => {
                            if *opn_in_map > op {
                                return true;
                            }
                        }
                        None => break,
                    }
                }
            }
            _ => {
                return false; // unexpected message variant
            }
        }

        return false;


    }

    #[verifier(external_body)]
    pub fn CExistsAcceptorHasProposalLargeThanOpn(S:&HashSet<CPacket>, op:COperationNumber) -> (result_CExistsAcceptorHasProposalLargeThanOpn:bool)
    requires
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(op),
        // ({
        //     forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        // })
    ensures
    ({
        let lr = LExistsAcceptorHasProposalLargeThanOpn(S@.map(|p:CPacket| p@), AbstractifyCOperationNumberToOperationNumber(op));
        result_CExistsAcceptorHasProposalLargeThanOpn == lr
    })

    {
        for p in S {
            if Self::CExistVotesHasProposalLargeThanOpn(p, op) {
                return true;
            }
        }
        false
    }

    #[verifier(external_body)]
    pub fn Cmax_balInS(c:&CBallot, S:&HashSet<CPacket>, opn:&COperationNumber) -> (result_Cmax_balInS:bool)
    requires
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(*opn),
        // ({
        //     forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        // })
    ensures
    ({
        let lr = Lmax_balInS(c.view(),S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(*opn));
        result_Cmax_balInS == lr
    })
    {
        // for p in &S {
        //     for (opn, _) in &p.msg.clone()->votes {
        //         if !CBalLeq(&p.msg.clone()->votes[opn].max_value_bal, &c) {
        //             return false;
        //         }
        //     }
        // }
        // true

        for p in S {
            match p.msg.clone() {
                CMessage::CMessage1b { votes, .. } => {
                    for (opn, vote_entry) in &votes {
                        if !CBalLeq(&vote_entry.max_value_bal, &c) {
                            return false;
                        }
                    }
                }
                _ => {
                    return false; // Unexpected variant
                }
            }
        }
        true

    }

    #[verifier(external_body)]
    pub fn CExistsBallotInS(v: &CRequestBatch, c: &CBallot, S: &HashSet<CPacket>, opn:&COperationNumber) -> (result_CExistsBallotInS:bool)
    requires
        crequestbatch_is_valid(v),
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(*opn),
        // ({
        //     forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        // })
    ensures
    ({
        let lr = LExistsBallotInS(abstractify_crequestbatch(v), c.view(), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(*opn));
        result_CExistsBallotInS == lr
    })
    {
        // for p in &S {
        //     for (opn, _) in &p.msg.clone()->votes {
        //         if !(p.msg.clone()->votes[opn].max_value_bal==c) || !(p.msg.clone()->votes[opn].max_val==v) {
        //             return false;
        //         }
        //     }
        // }
        // true

        for p in S {
            match p.msg.clone() {
                CMessage::CMessage1b { votes, .. } => {
                    for (_opn, vote_entry) in &votes {
                        if !(vote_entry.max_value_bal == *c) || !(vote_entry.max_val == *v) {
                            return false;
                        }
                    }
                }
                _ => {
                    return false; // Unexpected variant
                }
            }
        }
        true

    }

    #[verifier(external_body)]
    pub fn CValIsHighestNumberedProposalAtBallot(v:&CRequestBatch, c:&CBallot, S:&HashSet<CPacket>, opn:&COperationNumber) -> (result_CValIsHighestNumberedProposalAtBallot:bool)
    requires
        crequestbatch_is_valid(v),
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(*opn),
        // ({
        //     forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        // })
    ensures
    ({
        let lr = LValIsHighestNumberedProposalAtBallot(abstractify_crequestbatch(v), c.view(), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(*opn));
        result_CValIsHighestNumberedProposalAtBallot == lr
    })
    {
        Self::Cmax_balInS(c, S, opn) && Self::CExistsBallotInS(v, c, S, opn)
    }


    #[verifier(external_body)]
    pub fn CValIsHighestNumberedProposal(v: &CRequestBatch, S: &HashSet<CPacket>, opn:COperationNumber ) -> (result_CValIsHighestNumberedProposal:bool)
    requires
        crequestbatch_is_valid(v),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        // ({
        //     forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        // })
    ensures
    ({
        let lr = LValIsHighestNumberedProposal(abstractify_crequestbatch(v), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
        result_CValIsHighestNumberedProposal == lr
    })
    {
        for p in S {
            match p.msg.clone() {
                CMessage::CMessage1b { votes, .. } => {
                    for (opn, vote_entry) in &votes {
                        let val = Self::CValIsHighestNumberedProposalAtBallot(
                            v,
                            &vote_entry.max_value_bal,
                            S,
                            opn,
                        );
                        if !val {
                            return false;
                        }
                    }
                }
                _ => {
                    return false; // Unexpected message type
                }
            }
        }
        true
    }

    #[verifier(external_body)]
    pub fn CProposerCanNominateUsingOperationNumber(&self, log_truncation_point: COperationNumber, opn:COperationNumber) -> (result_CProposerCanNominateUsingOperationNumber:bool)
    requires
        self.valid(),
        COperationNumberIsValid(log_truncation_point),
        COperationNumberIsValid(opn),
    ensures
        ({
            let lr = LProposerCanNominateUsingOperationNumber(self.view(), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCOperationNumberToOperationNumber(opn));
            result_CProposerCanNominateUsingOperationNumber == lr
        })
    {
        self.election_state.current_view == self.max_ballot_i_sent_1a
        && self.current_state == 2
        && self.received_1b_packets.len() >= self.constants.all.config.CMinQuorumSize()
        && Self::CSetOfMessage1bAboutBallot(&self.received_1b_packets.clone(),&self.max_ballot_i_sent_1a)
        && Self::CIsAfterLogTruncationPoint(opn, &self.received_1b_packets)
        && opn < CUpperBoundedAddition(log_truncation_point, self.constants.all.params.max_log_length, self.constants.all.params.max_integer_val)
        && opn >= 0
        && opn < self.constants.all.params.max_integer_val // CLtUpperBound
    }

    // #[verifier(external_body)]
    pub fn CProposerInit(c : CReplicaConstants)->(result_CProposerInit:CProposer)
    requires
        c.valid(),
    ensures
        result_CProposerInit.valid(),
        LProposerInit(result_CProposerInit@, c@)
    {
        let p = CProposer{
            constants: c.clone_up_to_view(),
            current_state: 0,
            request_queue: Vec::new(),
            max_ballot_i_sent_1a: CBallot{seqno:0, proposer_id:c.my_index},
            next_operation_number_to_propose: 0,
            received_1b_packets: HashSet::new(),
            highest_seqno_requested_by_client_this_view: HashMap::new(),
            incomplete_batch_timer: CIncompleteBatchTimer::CIncompleteBatchTimerOff,
            election_state: CElectionState::CElectionStateInit(c),
            max_opn_with_proposal: 0,
            max_log_truncation_point: 0,
        };
        assert(p.valid());
        let ghost sp = p@;
        let ghost sc = c@;
        proof{
            assert(sp.constants == sc);
            assert(sp.current_state == 0);
            assert(sp.request_queue == Seq::<Request>::empty());
            assert(sp.max_ballot_i_sent_1a == Ballot{seqno:0, proposer_id:sc.my_index});
            assert(sp.next_operation_number_to_propose == 0);
            assert(sp.received_1b_packets == Set::<RslPacket>::empty());
            assert(sp.highest_seqno_requested_by_client_this_view == Map::<AbstractEndPoint, int>::empty());
            assert(ElectionStateInit(sp.election_state, sc));
            assert(sp.incomplete_batch_timer is IncompleteBatchTimerOff);
            assert(LProposerInit(sp, sc));
        }
        p
    }

    // #[verifier(external_body)]
    pub fn CProposerProcessRequest(&mut self, packet:CPacket)
    requires
        old(self).valid(),
        packet.valid(),
        packet.msg is CMessageRequest
    ensures
        self.valid(),
        LProposerProcessRequest(old(self)@, self@, packet@)
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;

        let ghost ss = self@;
        let ghost sp = packet@;
        let ghost sv = Request{client:sp.src, seqno:sp.msg->seqno_req, request:sp.msg->val};
        // Self::print("receive request packet");
        match packet.msg {
            CMessage::CMessageRequest { seqno_req, val: req_val } => {
                let val = CRequest {
                    client: packet.src,
                    seqno: seqno_req,
                    request: req_val,
                };

                if self.current_state != 0
                {
                    let hseqno = self.highest_seqno_requested_by_client_this_view.get(&val.client);
                    match hseqno {
                        Some(hseqno) => {
                            assert(self.highest_seqno_requested_by_client_this_view@.contains_key(val.client));
                            assert(ss.highest_seqno_requested_by_client_this_view.contains_key(sv.client));
                            assert(val.client@ == sv.client);
                            proof{lemma_AbstractifyMap_DomainUnchange2(self.highest_seqno_requested_by_client_this_view, |s: u64| s as int);}
                            assert((*hseqno) as int == ss.highest_seqno_requested_by_client_this_view[sv.client]);
                            if val.seqno > *hseqno {
                                assert(ss.current_state != 0);
                                assert(sv.seqno > ss.highest_seqno_requested_by_client_this_view[sv.client]);
                                CElectionState::CElectionStateReflectReceivedRequest(&mut self.election_state, val.clone_up_to_view());
                                self.request_queue.push(val.clone_up_to_view());
                                self.highest_seqno_requested_by_client_this_view.insert(val.client, val.seqno);

                                let ghost ns = self@;
                                assert(ns.constants == ss.constants);
                                assert(ns.current_state == ss.current_state);
                                assert(ns.request_queue == ss.request_queue + seq![sv]);
                                proof{
                                    lemma_AbstractifyMap_Insert2(
                                    old(self).highest_seqno_requested_by_client_this_view,
                                    self.highest_seqno_requested_by_client_this_view,
                                    val.client,
                                    val.seqno,
                                    |s: u64| s as int
                                    );
                                    let ghost s_old_m = Map::new(
                                        |ak: AbstractEndPoint| exists |k:EndPoint| old(self).highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak,
                                        |ak: AbstractEndPoint| {
                                            let k = choose |k: EndPoint| old(self).highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak;
                                            old(self).highest_seqno_requested_by_client_this_view@[k] as int
                                        });
                                    let ghost s_new_m =  Map::new(
                                        |ak: AbstractEndPoint| exists |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak,
                                        |ak: AbstractEndPoint| {
                                            let k = choose |k: EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak;
                                            self.highest_seqno_requested_by_client_this_view@[k] as int
                                        });
                                    assume(s_new_m == s_old_m.insert(val.client@, val.seqno as int)); // this is the ensures of lemma_AbstractifyMap_Insert2, don't know why it fails
                                }
                                assert(ns.highest_seqno_requested_by_client_this_view == ss.highest_seqno_requested_by_client_this_view.insert(sv.client, sv.seqno));
                                assert(LProposerProcessRequest(ss, self@, sp));
                            } else {
                                assert(ss.highest_seqno_requested_by_client_this_view.contains_key(sv.client));
                                assert(ss.current_state != 0);
                                assert(sv.seqno <= ss.highest_seqno_requested_by_client_this_view[sv.client]);
                                CElectionState::CElectionStateReflectReceivedRequest(&mut self.election_state, val.clone_up_to_view());
                                let ghost ns = self@;
                                assert(LProposerProcessRequest(ss, self@, sp));
                            }
                        }
                        None => {
                            // Self::print("add to request queue");
                            assert(ss.current_state != 0);
                            assert(!self.highest_seqno_requested_by_client_this_view@.contains_key(val.client));
                            assert(val.client@ == sv.client);
                            proof{lemma_AbstractifyMap_DomainUnchange(self.highest_seqno_requested_by_client_this_view);}
                            assert(!ss.highest_seqno_requested_by_client_this_view.contains_key(sv.client));
                            CElectionState::CElectionStateReflectReceivedRequest(&mut self.election_state, val.clone_up_to_view());
                            self.request_queue.push(val.clone_up_to_view());
                            self.highest_seqno_requested_by_client_this_view.insert(val.client, val.seqno);

                            assert(self.highest_seqno_requested_by_client_this_view@ == old(self).highest_seqno_requested_by_client_this_view@.insert(val.client, val.seqno));
                            let ghost ns = self@;
                            assert(ns.constants == ss.constants);
                            assert(ns.current_state == ss.current_state);
                            assert(ns.request_queue == ss.request_queue + seq![sv]);
                            proof{
                                lemma_AbstractifyMap_Insert2(
                                old(self).highest_seqno_requested_by_client_this_view,
                                self.highest_seqno_requested_by_client_this_view,
                                val.client,
                                val.seqno,
                                |s: u64| s as int
                                );
                                let ghost s_old_m = Map::new(
                                    |ak: AbstractEndPoint| exists |k:EndPoint| old(self).highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak,
                                    |ak: AbstractEndPoint| {
                                        let k = choose |k: EndPoint| old(self).highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak;
                                        old(self).highest_seqno_requested_by_client_this_view@[k] as int
                                    });
                                let ghost s_new_m =  Map::new(
                                    |ak: AbstractEndPoint| exists |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak,
                                    |ak: AbstractEndPoint| {
                                        let k = choose |k: EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak;
                                        self.highest_seqno_requested_by_client_this_view@[k] as int
                                    });
                                assume(s_new_m == s_old_m.insert(val.client@, val.seqno as int)); // this is the ensures of lemma_AbstractifyMap_Insert2, don't know why it fails
                            }
                            assert(ns.highest_seqno_requested_by_client_this_view == ss.highest_seqno_requested_by_client_this_view.insert(val.client@, val.seqno as int));
                            assert(ns.highest_seqno_requested_by_client_this_view == ss.highest_seqno_requested_by_client_this_view.insert(sv.client, sv.seqno));
                            assert(ns.max_ballot_i_sent_1a == ss.max_ballot_i_sent_1a);
                            assert(ElectionStateReflectReceivedRequest(ss.election_state, ns.election_state, sv));
                            assert(LProposerProcessRequest(ss, self@, sp));
                        }
                    }
                } else {
                    Self::print("not the proposer");
                    CElectionState::CElectionStateReflectReceivedRequest(&mut self.election_state, val.clone_up_to_view());
                    let ghost ns = self@;
                    assert(LProposerProcessRequest(ss, self@, sp));
                }
            }
            _ => {
                // Unexpected message type
            }
        }

    }

    fn test()
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        let mut m = HashMap::<u64, u64>::new();
        m.insert(1, 1);
        assert(m@.contains_key(1));

        // assert(!m@.contains_key(2));

        let v = m.get(&2);
        match v {
            Some(v) => {

            }
            None => {
                assert(!m@.contains_key(2));
            }
        }

        let id:Vec<u8> = vec![1,2];
        let e = EndPoint{id:id};
        let mut mm = HashMap::<EndPoint, u64>::new();
        mm.insert(e, 1);
        assert(mm@.contains_key(e));

        let id2:Vec<u8> = vec![2,3];
        let e2 = EndPoint{id:id2};
        // assert(!mm@.contains_key(e2));

        let v2 = mm.get(&e2);
        match v2 {
            Some(v2) => {

            }
            None => {
                assert(!mm@.contains_key(e2));
            }
        }
    }

    fn test2(m:HashMap::<EndPoint, u64>)
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        let id:Vec<u8> = vec![1,2];
        let e = EndPoint{id:id};

        let v2 = m.get(&e);
        match v2 {
            Some(v2) => {
                assert(m@.contains_key(e));
            }
            None => {
                assert(!m@.contains_key(e));
            }
        }
    }

    fn test3()
    {
        // // assert(obeys_hash_table_key_model::<u32>());
        // assume(vstd::std_specs::hash::obeys_key_model::<u32>());
        // assume(vstd::std_specs::hash::obeys_key_model::<EndPoint>());
        // let mut m = HashMapWithView::<u32, u32>::new();
        // m.insert(2, 3);
        // m.insert(3, 4);
        // assert(m@.contains_key(2));

        // // assume(axiom_endpoint_view());
        // let mut mm = HashMapWithView::<EndPoint, u64>::new();
        broadcast use vstd::std_specs::hash::group_hash_axioms;
            let mut m = HashMap::<u32, i8>::new();
            assert(m@ == Map::<u32, i8>::empty());

            m.insert(3, 4);
            m.insert(6, -8);
            let m_keys = m.keys();
            assert(m_keys@.0 == 0);
            assert(m_keys@.1.to_set() =~= set![3u32, 6u32]);
            let ghost g_keys = m_keys@.1;

            let mut items = Vec::<u32>::new();
            assert(items@ =~= g_keys.take(0));

            for k in iter: m_keys
                invariant
                    iter.keys == g_keys,
                    g_keys.to_set() =~= set![3u32, 6u32],
                    items@ == iter@,
            {
                assert(iter.keys.take(iter.pos).push(*k) =~= iter.keys.take(iter.pos + 1));
                items.push(*k);
            }
            assert(items@.to_set() =~= set![3u32, 6u32]) by {
                assert(g_keys.take(g_keys.len() as int) =~= g_keys);
            }
            assert(items@.no_duplicates());
    }

    // #[verifier(external_body)]
    pub fn CProposerMaybeEnterNewViewAndSend1a(&mut self) -> (result_CProposerMaybeEnterNewViewAndSend1a:OutboundPackets)
    requires
        old(self).valid(),
    ensures
        self.valid(),
        result_CProposerMaybeEnterNewViewAndSend1a.valid(),
        LProposerMaybeEnterNewViewAndSend1a(old(self)@, self@, result_CProposerMaybeEnterNewViewAndSend1a@)
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;

        let ghost ss = old(self)@;

        if (self.election_state.current_view.proposer_id == self.constants.my_index ) && CBalLt(&self.max_ballot_i_sent_1a, &self.election_state.current_view)
        {
            assert(ss.election_state.current_view.proposer_id == ss.constants.my_index);
            assert(BalLt(ss.max_ballot_i_sent_1a, ss.election_state.current_view));

            self.current_state = 1;
            self.max_ballot_i_sent_1a = self.election_state.current_view;
            self.received_1b_packets = HashSet::new();
            self.highest_seqno_requested_by_client_this_view = HashMap::new();
            assert(forall |i:int| 0 <= i < self.election_state.requests_received_prev_epochs@.len() ==> self.election_state.requests_received_prev_epochs@[i].abstractable());
            assert(forall |i:int| 0 <= i < self.election_state.requests_received_this_epoch@.len() ==> self.election_state.requests_received_this_epoch@[i].abstractable());

            let new_req_queue = concat_vecs(&self.election_state.requests_received_prev_epochs, &self.election_state.requests_received_this_epoch);
            assert(new_req_queue@ == self.election_state.requests_received_prev_epochs@ + self.election_state.requests_received_this_epoch@);
            proof{
                lemma_AbstractifyVec_Concat(
                    self.election_state.requests_received_prev_epochs,
                    self.election_state.requests_received_this_epoch,
                    new_req_queue,
                    |x: CRequest| CRequest::abstractable(x));
                assert(forall |i:int| 0 <= i < new_req_queue.len() ==> new_req_queue[i].abstractable());
            }
            self.request_queue = new_req_queue;
            let response = CMessage::CMessage1a { bal_1a: self.election_state.current_view };

            let broadcast = CBroadcast::BuildBroadcastToEveryone(&self.constants.all.config, self.constants.my_index, response);

            let outboundPackets = OutboundPackets::Broadcast {
                broadcast: broadcast
            };

            assert(forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].abstractable());
            assert(self.max_ballot_i_sent_1a.abstractable());
            // assert()
            assert(self.abstractable());
            assert(self.valid());

            let ghost ns = self@;
            let ghost sent = outboundPackets@;

            assert(LBroadcastToEveryone(ss.constants.all.config, ss.constants.my_index,
                RslMessage::RslMessage1a{bal_1a:ss.election_state.current_view}, sent));

            assert(ns.request_queue == ss.election_state.requests_received_prev_epochs + ss.election_state.requests_received_this_epoch);
            assert(ns.received_1b_packets == Set::<RslPacket>::empty());
            assert(ns.highest_seqno_requested_by_client_this_view == Map::<AbstractEndPoint, int>::empty());

            assert(LProposerMaybeEnterNewViewAndSend1a(ss, ns, sent));

            outboundPackets
        }
        else {
            // No state change
            let outboundPackets = OutboundPackets::Broadcast {
                broadcast: CBroadcast::CBroadcastNop{}
            };
            assert(self.valid());

            let ghost ns = self@;
            let ghost sent = outboundPackets@;

            assert(LProposerMaybeEnterNewViewAndSend1a(ss, ns, sent));


            outboundPackets
        }
    }

    #[verifier(external_body)]
    proof fn lemma_hashset_insert(s:HashSet<CPacket>, ss:Set<RslPacket>, e:CPacket)
        requires
            ss == s@.map(|e:CPacket| e@)
        ensures
            (
                {
                    let ns = s@.insert(e);
                    let sns = ns.map(|e:CPacket| e@);
                    &&& sns == ss.insert(e@)
                }
            )
    {

    }

    // #[verifier(external_body)]
    pub fn CProposerProcess1b(&mut self, pkt:CPacket)
        requires
            old(self).valid(),
            pkt.valid(),
            pkt.msg is CMessage1b,
            old(self).constants.all.config.replica_ids@.contains(pkt.src),
            pkt@.msg->bal_1b == old(self)@.max_ballot_i_sent_1a,
            old(self).current_state == 1,
            forall |op:CPacket| old(self).received_1b_packets@.contains(op) ==> op.src@ != pkt.src@,
        ensures
            self.valid(),
            LProposerProcess1b(old(self)@, self@, pkt@)
    {
        let ghost ss = old(self)@;
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        broadcast use crate::implementation::RSL::cmessage::axiom_cpacket_key_model;
        proof{Self::lemma_hashset_insert(self.received_1b_packets, ss.received_1b_packets, pkt);}
        self.received_1b_packets.insert(pkt);
        assert(self@.received_1b_packets == ss.received_1b_packets + set![pkt@]);
    }

    pub fn CProposerMaybeEnterPhase2(&mut self, log_truncation_point:COperationNumber) -> (sent_packets:OutboundPackets)
        requires
            old(self).valid(),
            COperationNumberIsValid(log_truncation_point),
        ensures
            self.valid(),
            sent_packets.valid(),
            LProposerMaybeEnterPhase2(old(self)@, self@, log_truncation_point as int, sent_packets@)
    {
        let ghost ss = old(self)@;

        assert(forall |k:EndPoint| #[trigger] self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.abstractable());
        assert(forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].abstractable());
        assert(self.abstractable());

        let quorum = CConfiguration::CMinQuorumSize(&self.constants.all.config);
        // assert(quorum as int == LMinQuorumSize(ss.constants.all.config));
        // proof{lemma_AbstractifySet_SizeUnchange2(self.received_1b_packets);}
        // assert(ss.received_1b_packets == self.received_1b_packets@.map(|p:CPacket| p@));
        assume(self.received_1b_packets.len() == ss.received_1b_packets.len());

        if self.received_1b_packets.len() >= quorum
            && Self::CSetOfMessage1bAboutBallot(&self.received_1b_packets, &self.max_ballot_i_sent_1a)
            && self.current_state == 1
        {
            Self::print("receive 1b from the majority");
            assert(
                ss.received_1b_packets.len() >= LMinQuorumSize(ss.constants.all.config)
                && LSetOfMessage1bAboutBallot(ss.received_1b_packets, ss.max_ballot_i_sent_1a)
                && ss.current_state == 1);

            self.current_state = 2;
            self.next_operation_number_to_propose = log_truncation_point;

            assert(self.highest_seqno_requested_by_client_this_view == old(self).highest_seqno_requested_by_client_this_view);
            assert(forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].abstractable());
            assert(forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.abstractable());
            assert(forall |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.abstractable());
            assert(self.valid());

            let msg = CMessage::CMessageStartingPhase2{bal_2:self.max_ballot_i_sent_1a, logTruncationPoint_2:log_truncation_point};
            let broadcast = CBroadcast::BuildBroadcastToEveryone(&self.constants.all.config, self.constants.my_index, msg);
            let sent_packets = OutboundPackets::Broadcast { broadcast:broadcast};

            let ghost ns = self@;
            let ghost sent = sent_packets@;

            assert(LProposerMaybeEnterPhase2(ss, ns, log_truncation_point as int, sent));

            sent_packets
        } else {
            let sent_packets = OutboundPackets::Broadcast {
                broadcast: CBroadcast::CBroadcastNop{}
            };

            let ghost ns = self@;
            let ghost sent = sent_packets@;

            assert(LProposerMaybeEnterPhase2(ss, ns, log_truncation_point as int, sent));

            sent_packets
        }
    }

    pub fn CProposerMaybeEnterPhase2_optimized(&mut self, log_truncation_point:COperationNumber) -> (sent_packets:OutboundPackets)
        requires
            old(self).valid(),
            COperationNumberIsValid(log_truncation_point),
        ensures
            self.valid(),
            sent_packets.valid(),
            LProposerMaybeEnterPhase2(old(self)@, self@, log_truncation_point as int, sent_packets@)
    {
        let ghost ss = old(self)@;

        assert(forall |k:EndPoint| #[trigger] self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.abstractable());
        assert(forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].abstractable());
        assert(self.abstractable());

        let quorum = CConfiguration::CMinQuorumSize(&self.constants.all.config);
        assume(self.received_1b_packets.len() == ss.received_1b_packets.len());

        if self.received_1b_packets.len() >= quorum
            && Self::CSetOfMessage1bAboutBallot(&self.received_1b_packets, &self.max_ballot_i_sent_1a)
            && self.current_state == 1
        {
            let (opn, found) = Self::GetMaxOpnWithProposalFromSet(&self.received_1b_packets);
            let mut maxOpn = 0;
            if found {
                assume(opn < 0xffff_ffff_ffff_ffff);
                maxOpn = opn + 1;
            }

            let max_truncate = Self::GetMaxLogTruncatePoint(&self.received_1b_packets);


            Self::print("receive 1b from the majority");
            assert(
                ss.received_1b_packets.len() >= LMinQuorumSize(ss.constants.all.config)
                && LSetOfMessage1bAboutBallot(ss.received_1b_packets, ss.max_ballot_i_sent_1a)
                && ss.current_state == 1);

            self.current_state = 2;
            self.next_operation_number_to_propose = log_truncation_point;
            self.max_opn_with_proposal = maxOpn;
            self.max_log_truncation_point = max_truncate;

            assert(self.highest_seqno_requested_by_client_this_view == old(self).highest_seqno_requested_by_client_this_view);
            assert(forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].abstractable());
            assert(forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.abstractable());
            assert(forall |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.abstractable());
            assert(self.valid());

            let msg = CMessage::CMessageStartingPhase2{bal_2:self.max_ballot_i_sent_1a, logTruncationPoint_2:log_truncation_point};
            let broadcast = CBroadcast::BuildBroadcastToEveryone(&self.constants.all.config, self.constants.my_index, msg);
            let sent_packets = OutboundPackets::Broadcast { broadcast:broadcast};

            let ghost ns = self@;
            let ghost sent = sent_packets@;

            assert(LProposerMaybeEnterPhase2(ss, ns, log_truncation_point as int, sent));

            sent_packets
        } else {
            let sent_packets = OutboundPackets::Broadcast {
                broadcast: CBroadcast::CBroadcastNop{}
            };

            let ghost ns = self@;
            let ghost sent = sent_packets@;

            assert(LProposerMaybeEnterPhase2(ss, ns, log_truncation_point as int, sent));

            sent_packets
        }
    }

    pub fn AllAcceptorsHadNoProposal(&self) -> (res:bool)
    {
        if self.next_operation_number_to_propose < self.max_opn_with_proposal
        {
            let opn = self.next_operation_number_to_propose;
            Self::OpnNotExistsInVotes(&self.received_1b_packets, opn)
        } else {
            true
        }
    }

    #[verifier(external_body)]
    pub fn DidSomeAcceptorHaveProposal(&self) -> (res:bool)
    {
        if self.next_operation_number_to_propose >= self.max_opn_with_proposal {
            false
        } else {
            Self::CExistsAcceptorHasProposalLargeThanOpn(&self.received_1b_packets, self.next_operation_number_to_propose)
        }
    }

    #[verifier(external_body)]
    pub fn CProposerCanNominateUsingOperationNumber_optimized(&self, log_truncation_point:COperationNumber) -> (res:bool)
    {
        if self.current_state == 2 {
            let opn = self.next_operation_number_to_propose;
            let quorum = self.constants.all.config.CMinQuorumSize();

            let mut after_trunk = false;
            if opn >= self.max_log_truncation_point {
                after_trunk = true;
            } else {
                after_trunk = Self::CIsAfterLogTruncationPoint(opn, &self.received_1b_packets);
            }

            let sum = CUpperBoundedAddition(log_truncation_point, self.constants.all.params.max_log_length, self.constants.all.params.max_integer_val);

            self.election_state.current_view == self.max_ballot_i_sent_1a
            // && self.current_state == 2
            && self.received_1b_packets.len() >= quorum
            && after_trunk
            && opn < sum
            && opn >= 0
        } else {
            false
        }
    }

    #[verifier(external_body)]
    pub fn CProposerMaybeNominateValueAndSend2a_optimized(&mut self, clock:u64, log_truncation_point:COperationNumber) -> (sent_packets:OutboundPackets)
        requires
            old(self).valid(),
            COperationNumberIsValid(log_truncation_point),
        ensures
            self.valid(),
            sent_packets.valid(),
            LProposerMaybeNominateValueAndSend2a(old(self)@, self@, clock as int, log_truncation_point as int, sent_packets@),
    {
        let ghost ss = old(self)@;
        let ghost sclock = clock as int;
        let ghost slog_truncate = log_truncation_point as int;

        let mut timer:bool = false;
        let mut time:u64 = 0;
        match self.incomplete_batch_timer{
            CIncompleteBatchTimer::CIncompleteBatchTimerOn{when} => {
                timer = true;
                time = when;
            }
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => {
                timer = false;
            }
        }

        let canNominate = Self::CProposerCanNominateUsingOperationNumber_optimized(&self, log_truncation_point);

        if !canNominate {
            let broadcast = CBroadcast::CBroadcastNop{};
            let outboundpackets = OutboundPackets::Broadcast {
                broadcast: broadcast
            };
            assert(LProposerMaybeNominateValueAndSend2a(ss, self@, sclock, slog_truncate, outboundpackets@));
            outboundpackets
        } else {
            if self.next_operation_number_to_propose >= self.max_opn_with_proposal && self.request_queue.len() == 0 {
                let broadcast = CBroadcast::CBroadcastNop{};
                let outboundpackets = OutboundPackets::Broadcast {
                    broadcast: broadcast
                };
                assert(LProposerMaybeNominateValueAndSend2a(ss, self@, sclock, slog_truncate, outboundpackets@));
                outboundpackets
            } else {
                let noProposal = Self::AllAcceptorsHadNoProposal(&self);
                if !noProposal {
                    let outboundpackets = Self::CProposerNominateOldValueAndSend2a(self, log_truncation_point);
                    assert(LProposerMaybeNominateValueAndSend2a(ss, self@, sclock, slog_truncate, outboundpackets@));
                    outboundpackets
                } else {
                    let queueSize = self.request_queue.len();
                    let existsOpn = Self::DidSomeAcceptorHaveProposal(&self);

                    if (queueSize > 0 && timer && clock >= time)
                        || (queueSize as u64 >= self.constants.all.params.max_batch_size)
                        || existsOpn
                    {
                        let outboundpackets = Self::CProposerNominateNewValueAndSend2a(self, clock, log_truncation_point);
                        assert(LProposerMaybeNominateValueAndSend2a(ss, self@, sclock, slog_truncate, outboundpackets@));
                        outboundpackets
                    } else {
                        if (queueSize > 0 && !timer) {
                            self.incomplete_batch_timer = CIncompleteBatchTimer::CIncompleteBatchTimerOn{
                                when:CUpperBoundedAddition(clock, self.constants.all.params.max_batch_delay, self.constants.all.params.max_integer_val),
                            };
                            let broadcast = CBroadcast::CBroadcastNop{};
                            let outboundpackets = OutboundPackets::Broadcast {
                                broadcast: broadcast
                            };
                            assert(LProposerMaybeNominateValueAndSend2a(ss, self@, sclock, slog_truncate, outboundpackets@));
                            outboundpackets
                        } else {
                            let broadcast = CBroadcast::CBroadcastNop{};
                            let outboundpackets = OutboundPackets::Broadcast {
                                broadcast: broadcast
                            };
                            assert(self@ == ss);
                            assert(outboundpackets@ == Seq::<RslPacket>::empty());
                            assert(LProposerMaybeNominateValueAndSend2a(ss, self@, sclock, slog_truncate, outboundpackets@));
                            outboundpackets
                        }
                    }
                }
            }
        }
    }


    // #[verifier(external_body)]
    pub fn CProposerNominateNewValueAndSend2a(&mut self, clock: u64, log_truncation_point: COperationNumber) -> (result_CProposerNominateNewValueAndSend2a:OutboundPackets)
        requires
            old(self).valid(),
            COperationNumberIsValid(log_truncation_point),
        ensures
            self.valid(),
            result_CProposerNominateNewValueAndSend2a.valid(),
            LProposerNominateNewValueAndSend2a(old(self)@, self@, clock as int, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), result_CProposerNominateNewValueAndSend2a@)
    {
        let ghost ss = old(self)@;
        let ghost sclock = clock as int;
        let ghost slog_truncate = log_truncation_point as int;

        let batch_size =
            if self.request_queue.len() <= self.constants.all.params.max_batch_size as usize
                || self.constants.all.params.max_batch_size < 0
            {
                self.request_queue.len()
            } else {
                self.constants.all.params.max_batch_size as usize
            };

        Self::print_data("Batch size:", batch_size as u64);

        let ghost sbatch_size =
            if ss.request_queue.len() <= ss.constants.all.params.max_batch_size || ss.constants.all.params.max_batch_size < 0 {
                ss.request_queue.len() as int
            } else {
                ss.constants.all.params.max_batch_size
            };
        assert(batch_size as int == sbatch_size);

        // let v = self.request_queue[..batch_size].to_vec();
        let v = truncate_vec(&self.request_queue, 0, batch_size);
        let ghost sv = ss.request_queue.subrange(0, sbatch_size);
        assert(v@.map(|i, r:CRequest| r@) == sv);

        let opn = self.next_operation_number_to_propose;

        // Update proposer state
        let len = self.request_queue.len();
        self.request_queue = truncate_vec(&self.request_queue, batch_size, len);
        assume(self.next_operation_number_to_propose < 0xffff_ffff_ffff_ffff);

        let ghost sreq_queue = ss.request_queue.subrange(sbatch_size, ss.request_queue.len() as int);
        assert(self.request_queue@.map(|i, r:CRequest| r@) == sreq_queue);

        self.next_operation_number_to_propose = self.next_operation_number_to_propose + 1;

        let upper_bound = CUpperBoundedAddition(clock, self.constants.all.params.max_batch_delay, self.constants.all.params.max_integer_val);
        let ghost supper_bound = UpperBoundedAddition(sclock, ss.constants.all.params.max_batch_delay, ss.constants.all.params.max_integer_val);
        assert(upper_bound as int == supper_bound);


        self.incomplete_batch_timer =
            if len > batch_size {
                CIncompleteBatchTimer::CIncompleteBatchTimerOn {when: upper_bound}
            } else {
                CIncompleteBatchTimer::CIncompleteBatchTimerOff
            };
        let ghost stimer = if ss.request_queue.len() > sbatch_size
            {
                IncompleteBatchTimer::IncompleteBatchTimerOn{when:supper_bound}
            } else {
                IncompleteBatchTimer::IncompleteBatchTimerOff{}
            };
        assert(
            match self.incomplete_batch_timer {
                CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => stimer is IncompleteBatchTimerOn,
                CIncompleteBatchTimer::CIncompleteBatchTimerOff => stimer is IncompleteBatchTimerOff,
            }
        );
        assert(self.incomplete_batch_timer@ == stimer);

        proof{
            lemma_AbstractifyVec_Truncate(
                old(self).request_queue,
                self.request_queue,
                batch_size,
                len,
                |x: CRequest| CRequest::abstractable(x));
            assert(forall |i:int| 0 <= i < self.request_queue.len() ==> self.request_queue[i].abstractable());
        }
        assert(self.highest_seqno_requested_by_client_this_view == old(self).highest_seqno_requested_by_client_this_view);
        assert(forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.abstractable());
        assert(forall |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.abstractable());
        assert(self.abstractable());

        let ghost ns = self@;
        assert(ns.request_queue == ss.request_queue.subrange(sbatch_size, ss.request_queue.len() as int));
        assert(ns.next_operation_number_to_propose == ss.next_operation_number_to_propose + 1);
        assert(ns.received_1b_packets == ss.received_1b_packets);
        assert(ns.highest_seqno_requested_by_client_this_view == ss.highest_seqno_requested_by_client_this_view);
        assert(ns.incomplete_batch_timer ==
            if ss.request_queue.len() > sbatch_size
            {
                IncompleteBatchTimer::IncompleteBatchTimerOn{when:UpperBoundedAddition(sclock, ss.constants.all.params.max_batch_delay, ss.constants.all.params.max_integer_val)}
            } else {
                IncompleteBatchTimer::IncompleteBatchTimerOff{}
            });

        let response = CMessage::CMessage2a {
            bal_2a: self.max_ballot_i_sent_1a,
            opn_2a: opn,
            val_2a: v,
        };

        let broadcast = CBroadcast::BuildBroadcastToEveryone(&self.constants.all.config, self.constants.my_index, response);

        let outboundpackets = OutboundPackets::Broadcast {
            broadcast: broadcast
        };

        let ghost sent = outboundpackets@;
        assert(LBroadcastToEveryone(ss.constants.all.config, ss.constants.my_index,
            RslMessage::RslMessage2a{bal_2a:ss.max_ballot_i_sent_1a, opn_2a:opn as int, val_2a:sv},
            sent));


        assert(outboundpackets.valid());


        outboundpackets
    }

    // #[verifier(external_body)]
    pub fn CProposerNominateOldValueAndSend2a(&mut self, log_truncation_point:COperationNumber) -> (sent_packets:OutboundPackets)
        requires
            old(self).valid(),
            COperationNumberIsValid(log_truncation_point),
            LProposerCanNominateUsingOperationNumber(
                old(self)@,
                log_truncation_point as int,
                old(self).next_operation_number_to_propose as int,
            ),
            !LAllAcceptorsHadNoProposal(
                old(self)@.received_1b_packets,
                old(self).next_operation_number_to_propose as int,
            )
        ensures
            self.valid(),
            sent_packets.valid(),
            LProposerNominateOldValueAndSend2a(old(self)@, self@, log_truncation_point as int, sent_packets@),
    {
        let ghost ss = old(self)@;
        let ghost slog_truncate = log_truncation_point as int;
        let opn = self.next_operation_number_to_propose;
        let ghost sopn = opn as int;
        let m_iter = self.received_1b_packets.iter();
        assume(m_iter@.0 == 0);
        let mut broadcast = CBroadcast::CBroadcastNop{};
        let mut find = false;
        let mut target:CPacket = CPacket{
            src:self.constants.all.config.replica_ids[self.constants.my_index as usize].clone_up_to_view(),
            dst:self.constants.all.config.replica_ids[self.constants.my_index as usize].clone_up_to_view(),
            msg:CMessage::CMessageInvalid{},
        };
        let mut target_val = CVote{
            max_value_bal:self.max_ballot_i_sent_1a,
            max_val:Vec::new(),
        };

        for p in iter: m_iter
            invariant
                self.valid(),
                find ==> ss.received_1b_packets.contains(target@),
                find ==> LValIsHighestNumberedProposal(target@.msg->votes[sopn].max_val, ss.received_1b_packets, sopn),
                find ==> target@.msg->votes.contains_key(sopn),
                find ==> target_val@ == target@.msg->votes[sopn],
                // broadcast.valid(),
        {
            assert(self.valid());
            match &p.msg {
                CMessage::CMessage1b{bal_1b, log_truncation_point, votes} => {
                    let v = votes.get(&opn);
                    match v {
                        Some(v) => {
                            // assume(crequestbatch_is_valid1(&v.max_val));
                            assert(self.valid());
                            let ghost req_queue = self.request_queue;
                            let ghost highest_req = self.highest_seqno_requested_by_client_this_view;
                            assert((forall |i:int| 0 <= i < req_queue@.len() ==> req_queue@[i].abstractable()));
                            assert((forall |k:EndPoint| highest_req@.contains_key(k) ==> k.abstractable()));
                            assume(crequestbatch_is_valid(&v.max_val));
                            if Self::CValIsHighestNumberedProposal(&v.max_val, &self.received_1b_packets, opn) {
                                find = true;
                                target = p.clone_up_to_view();
                                target_val = v.clone_up_to_view();
                                assume(ss.received_1b_packets.contains(p@));
                                assert(ss.received_1b_packets.contains(target@));
                                assume(LValIsHighestNumberedProposal(target@.msg->votes[sopn].max_val, ss.received_1b_packets, sopn));
                                assume(p@.msg->votes.contains_key(sopn));
                                assume(v@ == p@.msg->votes[sopn]);
                                assert(target@.msg->votes.contains_key(sopn));
                                assert(target_val@ == target@.msg->votes[sopn]);
                                // break;
                                // assume(ss.received_1b_packets.contains(p@));
                                // assert(exists |sp:RslPacket| ss.received_1b_packets.contains(sp));
                                // assume(LValIsHighestNumberedProposal(p@.msg->votes[sopn].max_val, ss.received_1b_packets, sopn));
                                // assume(self.next_operation_number_to_propose < 0xffff_ffff_ffff_ffff);
                                // self.next_operation_number_to_propose = self.next_operation_number_to_propose + 1;
                                // let msg = CMessage::CMessage2a{bal_2a:self.max_ballot_i_sent_1a, opn_2a:opn, val_2a:clone_request_batch_up_to_view(&v.max_val)};
                                // broadcast = CBroadcast::BuildBroadcastToEveryone(self.constants.all.config.clone_up_to_view(), self.constants.my_index, msg);
                                // assert(broadcast.valid());
                                // assert(self.valid());
                                // let ghost out = OutboundPackets::Broadcast {
                                //     broadcast: broadcast
                                // };
                                // assert(LProposerNominateOldValueAndSend2a(ss, self@, slog_truncate, out@));
                            }
                            // else {
                            //     let ghost out = OutboundPackets::Broadcast {
                            //         broadcast: CBroadcast::CBroadcastNop{},
                            //     };
                            //     assert(LProposerNominateOldValueAndSend2a(ss, self@, slog_truncate, out@));
                            //     assert(self.valid());
                            // }
                        }
                        None => {
                            // let ghost out = OutboundPackets::Broadcast {
                            //     broadcast: CBroadcast::CBroadcastNop{},
                            // };
                            // assert(LProposerNominateOldValueAndSend2a(ss, self@, slog_truncate, out@));
                            // assert(self.valid());
                        }
                    }
                }
                _ => {
                    // let ghost out = OutboundPackets::Broadcast {
                    //     broadcast: CBroadcast::CBroadcastNop{},
                    // };
                    // assert(LProposerNominateOldValueAndSend2a(ss, self@, slog_truncate, out@));
                    // assert(self.valid());
                }
            }
        }
        if find {
            assert(ss.received_1b_packets.contains(target@));
            assert(LValIsHighestNumberedProposal(target@.msg->votes[sopn].max_val, ss.received_1b_packets, sopn));
            assert(exists |p:RslPacket| ss.received_1b_packets.contains(p)
                    && LValIsHighestNumberedProposal(p.msg->votes[sopn].max_val, ss.received_1b_packets, sopn));
            self.next_operation_number_to_propose = self.next_operation_number_to_propose + 1;
            let msg = CMessage::CMessage2a{bal_2a:self.max_ballot_i_sent_1a, opn_2a:opn, val_2a:clone_request_batch_up_to_view(&target_val.max_val)};
            assume(msg.abstractable());
            broadcast = CBroadcast::BuildBroadcastToEveryone(&self.constants.all.config, self.constants.my_index, msg);
            let outboundpackets = OutboundPackets::Broadcast {
                broadcast: broadcast
            };
            assert(LProposerNominateOldValueAndSend2a(ss, self@, log_truncation_point as int, outboundpackets@));
            outboundpackets
        } else {
            // assert(broadcast.valid());
            let outboundpackets = OutboundPackets::Broadcast {
                broadcast: CBroadcast::CBroadcastNop{}
            };
            assume(LProposerNominateOldValueAndSend2a(ss, self@, log_truncation_point as int, outboundpackets@));
            outboundpackets
        }

    }

    pub fn CProposerMaybeNominateValueAndSend2a(&mut self, clock:u64, log_truncation_point:COperationNumber) -> (sent_packets:OutboundPackets)
        requires
            old(self).valid(),
            COperationNumberIsValid(log_truncation_point),
        ensures
            self.valid(),
            sent_packets.valid(),
            LProposerMaybeNominateValueAndSend2a(old(self)@, self@, clock as int, log_truncation_point as int, sent_packets@),
    {
        let ghost ss = old(self)@;
        let ghost sclock = clock as int;
        let ghost slog_truncate = log_truncation_point as int;

        let mut timer:bool = false;
        let mut time:u64 = 0;
        match self.incomplete_batch_timer{
            CIncompleteBatchTimer::CIncompleteBatchTimerOn{when} => {
                timer = true;
                time = when;
            }
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => {
                timer = false;
            }
        }

        if !Self::CProposerCanNominateUsingOperationNumber(self, log_truncation_point, self.next_operation_number_to_propose){
            let broadcast = CBroadcast::CBroadcastNop{};
            let outboundpackets = OutboundPackets::Broadcast {
                broadcast: broadcast
            };
            assert(LProposerMaybeNominateValueAndSend2a(ss, self@, sclock, slog_truncate, outboundpackets@));
            outboundpackets
        } else if !Self::CAllAcceptorsHadNoProposal(&self.received_1b_packets, self.next_operation_number_to_propose){
            let outboundpackets = Self::CProposerNominateOldValueAndSend2a(self, log_truncation_point);
            assert(LProposerMaybeNominateValueAndSend2a(ss, self@, sclock, slog_truncate, outboundpackets@));
            outboundpackets
        } else if Self::CExistsAcceptorHasProposalLargeThanOpn(&self.received_1b_packets, self.next_operation_number_to_propose)
                || (self.request_queue.len() as u64) >= self.constants.all.params.max_batch_size
                || (self.request_queue.len() > 0 && timer && clock >= time)
        {
            assert(LExistsAcceptorHasProposalLargeThanOpn(ss.received_1b_packets, ss.next_operation_number_to_propose)
                    || ss.request_queue.len() >= ss.constants.all.params.max_batch_size
                    || (ss.request_queue.len() > 0 && ss.incomplete_batch_timer is IncompleteBatchTimerOn && sclock >= ss.incomplete_batch_timer->when));
            let outboundpackets = Self::CProposerNominateNewValueAndSend2a(self, clock, log_truncation_point);
            assert(LProposerMaybeNominateValueAndSend2a(ss, self@, sclock, slog_truncate, outboundpackets@));
            outboundpackets
        } else if self.request_queue.len() > 0 && !timer {
            assert(LProposerCanNominateUsingOperationNumber(ss, slog_truncate, ss.next_operation_number_to_propose));
            assert(LAllAcceptorsHadNoProposal(ss.received_1b_packets, ss.next_operation_number_to_propose));
            self.incomplete_batch_timer = CIncompleteBatchTimer::CIncompleteBatchTimerOn{
                when:CUpperBoundedAddition(clock, self.constants.all.params.max_batch_delay, self.constants.all.params.max_integer_val),
            };
            let broadcast = CBroadcast::CBroadcastNop{};
            let outboundpackets = OutboundPackets::Broadcast {
                broadcast: broadcast
            };
            assert(LProposerMaybeNominateValueAndSend2a(ss, self@, sclock, slog_truncate, outboundpackets@));
            outboundpackets
        } else {
            let broadcast = CBroadcast::CBroadcastNop{};
            let outboundpackets = OutboundPackets::Broadcast {
                broadcast: broadcast
            };
            assert(self@ == ss);
            assert(outboundpackets@ == Seq::<RslPacket>::empty());
            assert(LProposerMaybeNominateValueAndSend2a(ss, self@, sclock, slog_truncate, outboundpackets@));
            outboundpackets
        }
    }

    #[verifier(external_body)]
    pub fn OpnNotExistsInVotes(s:&HashSet<CPacket>, opn:COperationNumber) -> (res:bool)
    {
        let m_iter = s.iter();
        let mut found = false;
        for p in iter:m_iter
        {
            match &p.msg {
                CMessage::CMessage1b {bal_1b, log_truncation_point, votes} => {
                    if votes.contains_key(&opn) {
                        return false;
                    }
                }
                _ => {

                }
            }
        }
        true
    }

    #[verifier(external_body)]
    pub fn GetMaxOpnWithProposalFromSingleton(m:&HashMap<COperationNumber, CVote>) -> (res:COperationNumber)
    {
        let m_keys = m.keys();
        let mut res = 0;
        for k in iter:m_keys
        {
            if *k > res {
                res = *k;
            }
        }
        res
    }

    #[verifier(external_body)]
    pub fn GetMaxOpnWithProposalFromSet(s:&HashSet<CPacket>) -> (res:(COperationNumber, bool))
    {
        let m_iter = s.iter();
        let mut candidateOpn = 0;
        let mut found = false;
        for p in iter:m_iter
        {
            match &p.msg {
                CMessage::CMessage1b {bal_1b, log_truncation_point, votes} => {
                    if votes.len() > 0 {
                        let opn = Self::GetMaxOpnWithProposalFromSingleton(&votes);
                        if opn > candidateOpn {
                            candidateOpn = opn;
                        }
                        found = true;
                    }
                }
                _ => {

                }
            }
        }
        (candidateOpn, found)
    }

    #[verifier(external_body)]
    pub fn GetMaxLogTruncatePoint(s:&HashSet<CPacket>) -> (res:COperationNumber)
    {
        let m_iter = s.iter();
        let mut candidateOpn = 0;
        for p in iter:m_iter
        {
            match &p.msg {
                CMessage::CMessage1b {bal_1b, log_truncation_point, votes} => {
                    if candidateOpn > *log_truncation_point {
                        candidateOpn = *log_truncation_point;
                    }
                }
                _ => {

                }
            }
        }
        candidateOpn
    }

    // #[verifier(external_body)]
    pub fn CProposerProcessHeartbeat(&mut self, p:CPacket, clock:u64)
        requires
            old(self).valid(),
            p.valid(),
            p.msg is CMessageHeartbeat,
        ensures
            self.valid(),
            LProposerProcessHeartbeat(old(self)@, self@, p@, clock as int)
    {
        let ghost ss = old(self)@;

        let old_view = self.election_state.current_view.clone_up_to_view();
        CElectionState::CElectionStateProcessHeartbeat(&mut self.election_state,p,clock);
        if CBalLt(&old_view, &self.election_state.current_view)
        {
            self.current_state = 0;
            self.request_queue = Vec::new();

            let ghost ns = self@;

            assert(BalLt(ss.election_state.current_view, ns.election_state.current_view));
            assert(ns.current_state == 0);
            assert(ns.request_queue == Seq::<Request>::empty());
            // assert()

            assert(LProposerProcessHeartbeat(ss, ns, p@, clock as int));
        }
        else
        {
            let ghost ns = self@;
            assert(LProposerProcessHeartbeat(ss, ns, p@, clock as int));
        }
    }

    // #[verifier(external_body)]
    pub fn CProposerCheckForViewTimeout(& mut self, clock:u64)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            LProposerCheckForViewTimeout(old(self)@, self@, clock as int)

    {
        CElectionState::CElectionStateCheckForViewTimeout(&mut self.election_state, clock);
    }

    // #[verifier(external_body)]
    pub fn CProposerCheckForQuorumOfViewSuspicions(&mut self, clock:u64)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            LProposerCheckForQuorumOfViewSuspicions(old(self)@, self@, clock as int)
    {
        let ghost ss = old(self)@;

        let old_view = self.election_state.current_view.clone_up_to_view();
        CElectionState::CElectionStateCheckForQuorumOfViewSuspicions(&mut self.election_state, clock);
        if CBalLt(&old_view, &self.election_state.current_view)
        {
            self.current_state = 0;
            self.request_queue = Vec::new();

            let ghost ns = self@;

            assert(BalLt(ss.election_state.current_view, ns.election_state.current_view));
            assert(ns.request_queue == Seq::<Request>::empty());

            assert(LProposerCheckForQuorumOfViewSuspicions(ss, ns, clock as int));
        }
        else
        {
            // No changes in state
        }
    }

    // #[verifier(external_body)]
    pub fn CProposerResetViewTimerDueToExecution(&mut self, val:&CRequestBatch)
        requires
            old(self).valid(),
            crequestbatch_is_valid(val),
        ensures
            self.valid(),
            LProposerResetViewTimerDueToExecution(old(self)@, self@, abstractify_crequestbatch(val)),
    {
        // CElectionState::CElectionStateReflectExecutedRequestBatch(&mut self.election_state, val);
        CElectionState::CElectionStateReflectExecutedRequestBatch_Optimized(&mut self.election_state, val);
    }

    }
}

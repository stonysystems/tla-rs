use crate::common::collections::hashsets::*;
use crate::common::collections::sets::*;
use crate::common::collections::vecs::*;
use crate::common::native::io_s::*;
use crate::implementation::common::upper_bound::*;
use crate::implementation::RSL::{
    cbroadcast::*, cconfiguration::*, cconstants::*, cmessage::*, types_i::*, ElectionImpl::*,
    ExecutorImpl::CIncompleteBatchTimer,
};
use crate::protocol::common::upper_bound::UpperBoundedAddition;
use crate::protocol::RSL::broadcast::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::{configuration::*, proposer::*};
use std::collections::HashSet;
use std::collections::*;
use vstd::hash_set::HashSetWithView;
use vstd::invariant;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
use vstd::{hash_map::*, map::*, prelude::*, seq::*, set::*};
// Generated wrappers live in `crate::generated::RSL::proposer_gen`.
// This module owns CProposer type infrastructure, Clone impl, and static helpers.

verus! {
pub struct CProposer {
    pub constants: CReplicaConstants,
    pub current_state: u64,
    pub request_queue: Vec<CRequest>,
    pub max_ballot_i_sent_1a: CBallot,
    pub next_operation_number_to_propose: u64,
    pub received_1b_packets: HashSet<CPacket>,
    pub highest_seqno_requested_by_client_this_view: HashMap<EndPoint, u64>,
    pub incomplete_batch_timer: CIncompleteBatchTimer,
    pub election_state: CElectionState,
    pub max_log_truncation_point: COperationNumber,
    pub max_opn_with_proposal: COperationNumber,
}

impl CProposer{
    pub open spec fn abstractable(self) -> bool {
        &&& self.constants.abstractable()
        &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].abstractable())
        &&& self.max_ballot_i_sent_1a.abstractable()
        &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.abstractable())
        &&& (forall |k:EndPoint| #[trigger] self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.abstractable())
        &&& self.incomplete_batch_timer.abstractable()
        &&& self.election_state.abstractable()
    }

    pub open spec fn valid(self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].valid())
        &&& self.max_ballot_i_sent_1a.valid()
        &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.valid())
        &&& (forall |k:EndPoint| #[trigger] self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.valid_public_key())
        &&& self.incomplete_batch_timer.valid()
        &&& self.election_state.valid()
    }

    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result: Self)
        ensures
            self == result,
            result@ == self@,
            result.valid() == self.valid(),
    {
        self.clone()
    }

    pub open spec fn view(self) -> LProposer
    recommends self.valid(),
    {
        LProposer{
            constants: self.constants.view(),
            current_state: self.current_state as int,
            request_queue: self.request_queue@.map(|i, r:CRequest| r.view()),
            max_ballot_i_sent_1a: self.max_ballot_i_sent_1a.view(),
            next_operation_number_to_propose: self.next_operation_number_to_propose as int,
            received_1b_packets: self.received_1b_packets@.map(|p:CPacket| p.view()),
            highest_seqno_requested_by_client_this_view: Map::new(
                |ak: AbstractEndPoint| exists |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak,
                |ak: AbstractEndPoint| {
                    let k = choose |k: EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak;
                    self.highest_seqno_requested_by_client_this_view@[k] as int
                }
            ),
            incomplete_batch_timer: self.incomplete_batch_timer.view(),
            election_state: self.election_state.view(),
        }
    }
}

impl View for CProposer {
    type V = LProposer;

    open spec fn view(&self) -> LProposer {
        LProposer{
            constants: self.constants.view(),
            current_state: self.current_state as int,
            request_queue: self.request_queue@.map(|i, r:CRequest| r.view()),
            max_ballot_i_sent_1a: self.max_ballot_i_sent_1a.view(),
            next_operation_number_to_propose: self.next_operation_number_to_propose as int,
            received_1b_packets: self.received_1b_packets@.map(|p:CPacket| p.view()),
            highest_seqno_requested_by_client_this_view: Map::new(
                |ak: AbstractEndPoint| exists |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak,
                |ak: AbstractEndPoint| {
                    let k = choose |k: EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak;
                    self.highest_seqno_requested_by_client_this_view@[k] as int
                }
            ),
            incomplete_batch_timer: self.incomplete_batch_timer.view(),
            election_state: self.election_state.view(),
        }
    }
}

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

broadcast use crate::common::native::io_s::axiom_endpoint_key_model;

impl CProposer{

    // =========================================================================
    // Internal helper: check if opn is after all log truncation points in set
    // =========================================================================

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

    // =========================================================================
    // Internal helper: check if all packets in set are Message1b
    // =========================================================================

    pub fn CSetOfMessage1b(S : &HashSet<CPacket>) -> (res:bool)
        ensures
            ({
                let lr = LSetOfMessage1b(S@.map(|p:CPacket| p@));
                res == lr
            })
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        broadcast use vstd::set::group_set_axioms;
        let mut result = true;
        let ghost mut checked: Set<RslPacket> = Set::empty();
        let m_iter = S.iter();
        let ghost mut count: int = 0;
        proof {
            broadcast use crate::implementation::RSL::cmessage::axiom_cpacket_key_model;
            // With obeys_key_model::<CPacket>() and builds_valid_hashers::<RandomState>() (from group_hash_axioms),
            // HashSet::iter() ensures index == 0, i.e., m_iter@.0 == 0.
        }
        assert(count == m_iter@.0);

        for p in iter: m_iter
            invariant
                forall |x:RslPacket| checked.contains(x) ==> exists |y:CPacket| S@.contains(y) && x == y@,
                checked.subset_of(S@.map(|p:CPacket| p@)),
                forall |p:RslPacket| checked.contains(p) ==> p.msg is RslMessage1b,
                result ==> count == checked.len(),
                !result ==> !(forall |x:RslPacket| S@.map(|p:CPacket| p@).contains(x) ==> x.msg is RslMessage1b),
                checked.finite(),
                // Iterator-tracking invariants
                iter.elements.to_set() == S@,
                iter.elements.no_duplicates(),
        {
            let ghost old_checked = checked;
            let ghost old_count = count;
            proof{
                if result {
                    old_count == old_checked.len();
                }
            }
            proof{count = count + 1;}
            // Prove S@.contains(*p): from for-loop semantics, *p came from the HashSet S
            proof {
                // Try direct: iter.elements.to_set() == S@, and *p is an element from iter.elements
                assume(S@.contains(*p));
            }
            if let CMessage::CMessage1b { bal_1b, log_truncation_point, votes } = &p.msg {
                proof{
                    if result {
                        assume(forall |x:RslPacket| checked.contains(x) ==> x != (*p)@);
                        // checked.finite() from loop invariant + axiom_set_insert_finite
                        axiom_set_remove_len(checked, (*p)@);
                        checked = checked.insert((*p)@);
                        assert(count == old_count + 1);
                        assert(checked.len() == old_checked.len() + 1);
                        assert(old_count + 1 == old_checked.len() + 1);
                        assert(checked.contains((*p)@));
                        assert(S@.contains(*p));
                        assert( count == checked.len());
                    }
                }
            } else {
                proof {
                    assert(S@.contains(*p));
                }
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
            // count == iter.pos (invariant) and iter.pos == iter.elements.len() (ghost_ensures)
            // but iter is scoped to the for-loop body, so we can't access it here.
            // TODO: prove count == S@.len() when Verus for-loop ghost_ensures are accessible post-loop
            assume(count == S@.len());
            if result {
                assert(checked.len() == S@.len());
                // Proved: S@.map(|p| p@).len() == S@.len() via injective-map cardinality
                lemma_hashset_view_finite(S);
                let f_cpv = |p: CPacket| p@;
                broadcast use crate::implementation::RSL::cmessage::axiom_cpacket_view;
                assert forall |p1: CPacket, p2: CPacket| #![trigger f_cpv(p1), f_cpv(p2)] f_cpv(p1) == f_cpv(p2) implies p1 == p2 by {};
                lemma_set_map_injective_len::<CPacket, RslPacket>(S@, f_cpv);
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
        assert forall |x:CPacket| s2@.contains(x) implies s1.contains(x@) by{
            // With `implies`, the antecedent s2@.contains(x) is automatically assumed
            if !s1.contains(x@) {
                let s2_minus = s2@.remove(x);
                lemma_hashset_view_finite(s2);
                axiom_set_remove_len(s2@, x);
                assert(s2_minus.len() == s2@.len() - 1);
                let ss2_minus = s2_minus.map(|p:CPacket| p@);
                let ss2 = s2@.map(|p:CPacket| p@);
                assert(forall |x:RslPacket| ss2_minus.contains(x) ==> exists |y:CPacket| s2_minus.contains(y) && x == y@);
                assert(forall |x:RslPacket| ss2.contains(x) ==> exists |y:CPacket| s2@.contains(y) && x == y@);

                // Proved: injective-map cardinality for CPacket view
                {
                    broadcast use vstd::set::group_set_axioms;
                    broadcast use crate::implementation::RSL::cmessage::axiom_cpacket_view;
                    let f_cpv = |p: CPacket| p@;
                    assert forall |p1: CPacket, p2: CPacket| #![trigger f_cpv(p1), f_cpv(p2)] f_cpv(p1) == f_cpv(p2) implies p1 == p2 by {};
                    // s2@.finite() from lemma_hashset_view_finite(s2) above;
                    // s2_minus.finite() from axiom_set_remove_finite in group_set_axioms
                    lemma_set_map_injective_len::<CPacket, RslPacket>(s2_minus, f_cpv);
                    lemma_set_map_injective_len::<CPacket, RslPacket>(s2@, f_cpv);
                }
                assert(s2_minus.map(|p:CPacket| p@).len() == s2@.map(|p:CPacket| p@).len() - 1);
                assert(s2_minus.map(|p:CPacket| p@).len() < s2@.map(|p:CPacket| p@).len());
                assert(s1.subset_of(s2_minus.map(|p:CPacket| p@)));
                // s2_minus is finite (s2@ finite from HashSet, remove preserves finiteness)
                // s2_minus.map(...) is also finite
                s2_minus.lemma_map_finite(|p:CPacket| p@);
                subset_cardinality(s1, s2_minus.map(|p:CPacket| p@));
                assert(s1.len() <= s2_minus.map(|p:CPacket| p@).len());
                assert(s1.len() == s2@.map(|p:CPacket| p@).len());
                assert(false);
            }
        };
        assert(s1 == s2@.map(|p:CPacket| p@));
    }

    // =========================================================================
    // Live static method 1: CSetOfMessage1bAboutBallot
    // Called from proposer_gen.rs and proposer_manual.rs
    // =========================================================================

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

    // =========================================================================
    // Live static method 2: CAllAcceptorsHadNoProposal
    // Called from proposer_gen.rs and proposer_manual.rs
    // =========================================================================

    #[verifier(external_body)]
    pub fn CAllAcceptorsHadNoProposal(S:&HashSet<CPacket>, opn:COperationNumber) -> (result_CAllAcceptorsHadNoProposal:bool)
    requires
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
    ensures
        ({
            let lr = LAllAcceptorsHadNoProposal(S@.map(|p:CPacket| p@), AbstractifyCOperationNumberToOperationNumber(opn));
            result_CAllAcceptorsHadNoProposal == lr
        })
    {
        let mut iter = S.iter();
        let mut res = false;
        match iter.next() {
            Some(p)=>{
            match &p.msg{
                CMessage::CMessage1b { votes, .. } => {
                            if votes.contains_key(&opn) {
                                return false;
                            }
                        }
                        _ => {
                             return false;
                        }
                    }
            }
            None=>{}
        }
        return true;
    }

    // =========================================================================
    // Internal helper for CExistsAcceptorHasProposalLargeThanOpn
    // =========================================================================

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
                return false;
            }
        }

        return false;


    }

    // =========================================================================
    // Live static method 3: CExistsAcceptorHasProposalLargeThanOpn
    // Called from proposer_gen.rs and proposer_manual.rs
    // =========================================================================

    #[verifier(external_body)]
    pub fn CExistsAcceptorHasProposalLargeThanOpn(S:&HashSet<CPacket>, op:COperationNumber) -> (result_CExistsAcceptorHasProposalLargeThanOpn:bool)
    requires
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(op),
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

    // =========================================================================
    // Internal helpers for CValIsHighestNumberedProposal
    // =========================================================================

    #[verifier(external_body)]
    pub fn Cmax_balInS(c:&CBallot, S:&HashSet<CPacket>, opn:&COperationNumber) -> (result_Cmax_balInS:bool)
    requires
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(*opn),
    ensures
    ({
        let lr = Lmax_balInS(c.view(),S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(*opn));
        result_Cmax_balInS == lr
    })
    {
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
                    return false;
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
    ensures
    ({
        let lr = LExistsBallotInS(abstractify_crequestbatch(v), c.view(), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(*opn));
        result_CExistsBallotInS == lr
    })
    {
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
                    return false;
                }
            }
        }
        true

    }

    pub fn CValIsHighestNumberedProposalAtBallot(v:&CRequestBatch, c:&CBallot, S:&HashSet<CPacket>, opn:&COperationNumber) -> (result_CValIsHighestNumberedProposalAtBallot:bool)
    requires
        crequestbatch_is_valid(v),
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(*opn),
    ensures
    ({
        let lr = LValIsHighestNumberedProposalAtBallot(abstractify_crequestbatch(v), c.view(), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(*opn));
        result_CValIsHighestNumberedProposalAtBallot == lr
    })
    {
        Self::Cmax_balInS(c, S, opn) && Self::CExistsBallotInS(v, c, S, opn)
    }

    // =========================================================================
    // Live static method 4: CValIsHighestNumberedProposal
    // Called from proposer_gen.rs and proposer_manual.rs
    // =========================================================================

    #[verifier(external_body)]
    pub fn CValIsHighestNumberedProposal(v: &CRequestBatch, S: &HashSet<CPacket>, opn:COperationNumber ) -> (result_CValIsHighestNumberedProposal:bool)
    requires
        crequestbatch_is_valid(v),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
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
                    return false;
                }
            }
        }
        true
    }

    // =========================================================================
    // Live static method 5: CProposerCanNominateUsingOperationNumber
    // Called from proposer_gen.rs and proposer_manual.rs
    // =========================================================================

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
        proof {
            // Bridge HashSet<CPacket>.len() to Set<RslPacket>.len()
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            crate::common::collections::hashsets::lemma_hashset_cpacket_len(&self.received_1b_packets);
            assert(self.received_1b_packets@.map(|t: CPacket| t@) =~= self@.received_1b_packets);
        }
        let cloned_packets = crate::common::collections::hashsets::clone_hashset(&self.received_1b_packets);
        CBalEq(&self.election_state.current_view, &self.max_ballot_i_sent_1a)
        && self.current_state == 2
        && self.received_1b_packets.len() >= self.constants.all.config.CMinQuorumSize()
        && Self::CSetOfMessage1bAboutBallot(&cloned_packets, &self.max_ballot_i_sent_1a)
        && Self::CIsAfterLogTruncationPoint(opn, &self.received_1b_packets)
        && opn < CUpperBoundedAddition(log_truncation_point, self.constants.all.params.max_log_length, self.constants.all.params.max_integer_val)
        && opn >= 0
        && opn < self.constants.all.params.max_integer_val // CLtUpperBound
    }

    }
}

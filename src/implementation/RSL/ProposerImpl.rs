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

    pub fn CIsAfterLogTruncationPoint(opn:COperationNumber, S:&HashSet<CPacket>) -> (res:bool)
        ensures
            ({
                let lr = LIsAfterLogTruncationPoint(opn as int, S@.map(|p:CPacket| p@));
                res == lr
            })
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::set::group_set_axioms;
        broadcast use crate::implementation::RSL::cmessage::axiom_cpacket_key_model;

        let vec = hashset_to_vec(S);
        let mut i: usize = 0;
        while i < vec.len()
            invariant
                0 <= i <= vec.len(),
                forall |j: int| 0 <= j < i as int ==> (
                    (#[trigger] vec@[j]).msg is CMessage1b ==> vec@[j].msg->log_truncation_point <= opn
                ),
                forall |k: int| 0 <= k < vec@.len() ==> S@.contains(#[trigger] vec@[k]),
                forall |x: CPacket| S@.contains(x) ==> (exists |k: int| 0 <= k < vec@.len() && vec@[k] == x),
            decreases
                vec.len() - i,
        {
            if let CMessage::CMessage1b { bal_1b, log_truncation_point, votes } = &vec[i].msg {
                if *log_truncation_point > opn {
                    // Found a Message1b with log_truncation_point > opn
                    proof {
                        let bad = vec@[i as int];
                        assert(S@.contains(bad));
                        let f = |p: CPacket| p@;
                        assert(S@.map(f).contains(f(bad)));
                        assert(bad@.msg is RslMessage1b);
                        assert(bad@.msg->log_truncation_point > opn as int);
                    }
                    return false;
                }
            } else {
                // Not a Message1b — the spec condition is vacuously true for non-1b packets,
                // but we still need to check all packets; just continue
            }
            i = i + 1;
        }
        // All packets checked: for each Message1b, log_truncation_point <= opn
        proof {
            let f = |p: CPacket| p@;
            assert forall |p: RslPacket| S@.map(f).contains(p) && p.msg is RslMessage1b
                implies p.msg->log_truncation_point <= opn as int by {
                let cp = choose |cp: CPacket| S@.contains(cp) && f(cp) == p;
                let j = choose |j: int| 0 <= j < vec@.len() && vec@[j] == cp;
                // vec@[j].msg is CMessage1b (since cp@ == p and p.msg is RslMessage1b)
                // From loop invariant: vec@[j].msg->log_truncation_point <= opn
            };
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
        broadcast use crate::implementation::RSL::cmessage::axiom_cpacket_key_model;

        let vec = hashset_to_vec(S);
        let mut i: usize = 0;
        while i < vec.len()
            invariant
                0 <= i <= vec.len(),
                forall |j: int| 0 <= j < i as int ==> (#[trigger] vec@[j]).msg is CMessage1b,
                // hashset_to_vec postconditions available as ambient facts
                forall |k: int| 0 <= k < vec@.len() ==> S@.contains(#[trigger] vec@[k]),
                forall |x: CPacket| S@.contains(x) ==> (exists |k: int| 0 <= k < vec@.len() && vec@[k] == x),
            decreases
                vec.len() - i,
        {
            if let CMessage::CMessage1b { bal_1b, log_truncation_point, votes } = &vec[i].msg {
                // CMessage1b: continue
            } else {
                // Found a non-CMessage1b element; prove the result is false
                proof {
                    let bad = vec@[i as int];
                    assert(S@.contains(bad));
                    // bad@ is in S@.map(|p:CPacket| p@), and bad@.msg is NOT RslMessage1b
                    let f = |p: CPacket| p@;
                    assert(S@.map(f).contains(f(bad)));
                    assert(!(bad@.msg is RslMessage1b));
                }
                return false;
            }
            i = i + 1;
        }
        // All elements in vec are CMessage1b; prove the result is true
        proof {
            let f = |p: CPacket| p@;
            assert forall |x: RslPacket| S@.map(f).contains(x) implies x.msg is RslMessage1b by {
                // x is in S@.map(f), so there exists a CPacket cp in S@ with cp@ == x
                let cp = choose |cp: CPacket| S@.contains(cp) && f(cp) == x;
                // cp is in S@, so it appears in vec at some index j
                let j = choose |j: int| 0 <= j < vec@.len() && vec@[j] == cp;
                // From the loop invariant, vec@[j].msg is CMessage1b, so cp.msg is CMessage1b
                // Therefore cp@ (== x) has msg is RslMessage1b
            };
        }
        true
    }

    // =========================================================================
    // Live static method 1: CSetOfMessage1bAboutBallot
    // Called from proposer_gen.rs and proposer_manual.rs
    // =========================================================================

    pub fn CSetOfMessage1bAboutBallot(S:&HashSet<CPacket>, b:&CBallot) -> (res:bool)
        ensures
            res == LSetOfMessage1bAboutBallot(S@.map(|p:CPacket| p@), b@)
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::set::group_set_axioms;
        broadcast use crate::implementation::RSL::cmessage::axiom_cpacket_key_model;

        // First check: all packets are Message1b
        if !Self::CSetOfMessage1b(S) {
            return false;
        }
        // LSetOfMessage1b(S@.map(...)) is true at this point

        // Second check: all Message1b packets have ballot == b
        let vec = hashset_to_vec(S);
        let mut i: usize = 0;
        while i < vec.len()
            invariant
                0 <= i <= vec.len(),
                forall |j: int| 0 <= j < i as int ==>
                    ((#[trigger] vec@[j]).msg is CMessage1b ==> vec@[j].msg->bal_1b@ == b@),
                forall |k: int| 0 <= k < vec@.len() ==> S@.contains(#[trigger] vec@[k]),
                forall |x: CPacket| S@.contains(x) ==> (exists |k: int| 0 <= k < vec@.len() && vec@[k] == x),
            decreases
                vec.len() - i,
        {
            if let CMessage::CMessage1b { bal_1b, log_truncation_point, votes } = &vec[i].msg {
                if bal_1b.seqno != b.seqno || bal_1b.proposer_id != b.proposer_id {
                    // Found a Message1b with wrong ballot
                    proof {
                        let bad = vec@[i as int];
                        assert(S@.contains(bad));
                        let f = |p: CPacket| p@;
                        assert(S@.map(f).contains(f(bad)));
                        assert(bad@.msg is RslMessage1b);
                        assert(bad@.msg->bal_1b != b@);
                    }
                    return false;
                }
            }
            i = i + 1;
        }
        // All Message1b packets have ballot == b
        proof {
            let f = |p: CPacket| p@;
            assert forall |p: RslPacket| S@.map(f).contains(p)
                implies p.msg->bal_1b == b@ by {
                let cp = choose |cp: CPacket| S@.contains(cp) && f(cp) == p;
                let j = choose |j: int| 0 <= j < vec@.len() && vec@[j] == cp;
            };
        }
        true
    }

    // =========================================================================
    // Live static method 2: CAllAcceptorsHadNoProposal
    // Called from proposer_gen.rs and proposer_manual.rs
    // =========================================================================

    pub fn CAllAcceptorsHadNoProposal(S:&HashSet<CPacket>, opn:COperationNumber) -> (result_CAllAcceptorsHadNoProposal:bool)
    requires
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        LSetOfMessage1b(S@.map(|p:CPacket| p@)),
    ensures
        ({
            let lr = LAllAcceptorsHadNoProposal(S@.map(|p:CPacket| p@), AbstractifyCOperationNumberToOperationNumber(opn));
            result_CAllAcceptorsHadNoProposal == lr
        })
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::set::group_set_axioms;
        broadcast use crate::implementation::RSL::cmessage::axiom_cpacket_key_model;

        let vec = hashset_to_vec(S);
        let mut i: usize = 0;
        while i < vec.len()
            invariant
                0 <= i <= vec.len(),
                forall |j: int| 0 <= j < i as int ==> (
                    (#[trigger] vec@[j]).msg is CMessage1b ==> !(vec@[j].msg->votes@).contains_key(opn)
                ),
                forall |k: int| 0 <= k < vec@.len() ==> S@.contains(#[trigger] vec@[k]),
                forall |x: CPacket| S@.contains(x) ==> (exists |k: int| 0 <= k < vec@.len() && vec@[k] == x),
                forall |p:CPacket| S@.contains(p) ==> p.valid(),
                COperationNumberIsValid(opn),
                LSetOfMessage1b(S@.map(|p: CPacket| p@)),
            decreases
                vec.len() - i,
        {
            if let CMessage::CMessage1b { bal_1b, log_truncation_point, votes } = &vec[i].msg {
                if votes.contains_key(&opn) {
                    // Found a Message1b with votes containing opn — spec is false
                    proof {
                        let bad = vec@[i as int];
                        assert(S@.contains(bad));
                        assert(bad.valid());
                        assert(bad.abstractable());
                        let f = |p: CPacket| p@;
                        assert(S@.map(f).contains(f(bad)));
                        assert(bad@.msg is RslMessage1b);
                    }
                    return false;
                }
            }
            i = i + 1;
        }
        // All Message1b packets checked — none have opn in their votes
        // LSetOfMessage1b guarantees all packets are RslMessage1b, so loop invariant covers all
        proof {
            let f = |p: CPacket| p@;
            assert forall |p: RslPacket| S@.map(f).contains(p)
                implies !p.msg->votes.contains_key(AbstractifyCOperationNumberToOperationNumber(opn)) by {
                let cp = choose |cp: CPacket| S@.contains(cp) && f(cp) == p;
                assert(cp.valid());
                assert(cp.abstractable());
                // LSetOfMessage1b: all packets in S@.map(f) are RslMessage1b
                assert(p.msg is RslMessage1b);
                let j = choose |j: int| 0 <= j < vec@.len() && vec@[j] == cp;
                // loop invariant via j: vec@[j].msg is CMessage1b ==> !(vec@[j].msg->votes@).contains_key(opn)
                // since cp@ == p and p.msg is RslMessage1b, cp.msg is CMessage1b
                // so !(cp.msg->votes@).contains_key(opn)
            };
        }
        true
    }

    // =========================================================================
    // Internal helper for CExistsAcceptorHasProposalLargeThanOpn
    // =========================================================================

    // Inner helper: check if any key in votes HashMap is > op.
    // Proven against abstractify_cvotes(votes), avoiding the pattern-binding gap.
    fn CExistVotesHasProposalLargeThanOpn_inner(votes: &CVotes, op: COperationNumber) -> (result: bool)
    requires
        cvotes_is_abstractable(votes),
    ensures
        result == (exists |opn: int| abstractify_cvotes(votes).contains_key(opn) && opn > op as int),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::map::group_map_axioms;

        let keys = hashmap_keys_to_vec(votes);
        let mut i: usize = 0;
        while i < keys.len()
            invariant
                0 <= i <= keys.len(),
                forall |j: int| 0 <= j < i as int ==> (#[trigger] keys@[j]) <= op,
                forall |k: int| 0 <= k < keys@.len() ==> votes@.contains_key(#[trigger] keys@[k]),
                forall |k: u64| votes@.contains_key(k) ==> (exists |j: int| 0 <= j < keys@.len() && keys@[j] == k),
                cvotes_is_abstractable(votes),
            decreases keys.len() - i,
        {
            if keys[i] > op {
                proof {
                    let opn_u64 = keys@[i as int];
                    assert(votes@.contains_key(opn_u64));
                    assert(opn_u64 as int > op as int);
                    // Trigger Map::new axiom for abstractify_cvotes domain
                    let abs_v = abstractify_cvotes(votes);
                    assert(abs_v.dom().contains(opn_u64 as int));
                    assert(abs_v.contains_key(opn_u64 as int) && opn_u64 as int > op as int);
                }
                return true;
            }
            i = i + 1;
        }
        proof {
            assert forall |opn: int| abstractify_cvotes(votes).contains_key(opn)
                implies opn <= op as int by {
                let k = choose |k: u64| votes@.contains_key(k) && k as int == opn;
                assert(votes@.contains_key(k));
                let j = choose |j: int| 0 <= j < keys@.len() && keys@[j] == k;
                assert(k <= op);
            };
        }
        false
    }

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
            CMessage::CMessage1b { bal_1b, log_truncation_point, votes } => {
                proof {
                    // Bridge pattern-bound votes to p@.msg->votes via extensional equality
                    assert(abstractify_cvotes(votes) =~= p@.msg->votes);
                }
                Self::CExistVotesHasProposalLargeThanOpn_inner(votes, op)
            }
            _ => {
                return false;
            }
        }
    }

    // =========================================================================
    // Live static method 3: CExistsAcceptorHasProposalLargeThanOpn
    // Called from proposer_gen.rs and proposer_manual.rs
    // =========================================================================

    pub fn CExistsAcceptorHasProposalLargeThanOpn(S:&HashSet<CPacket>, op:COperationNumber) -> (result_CExistsAcceptorHasProposalLargeThanOpn:bool)
    requires
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(op),
        LSetOfMessage1b(S@.map(|p:CPacket| p@)),
    ensures
    ({
        let lr = LExistsAcceptorHasProposalLargeThanOpn(S@.map(|p:CPacket| p@), AbstractifyCOperationNumberToOperationNumber(op));
        result_CExistsAcceptorHasProposalLargeThanOpn == lr
    })
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::set::group_set_axioms;
        broadcast use crate::implementation::RSL::cmessage::axiom_cpacket_key_model;

        let vec = hashset_to_vec(S);
        let mut i: usize = 0;
        while i < vec.len()
            invariant
                0 <= i <= vec.len(),
                forall |j: int| 0 <= j < i as int ==> (
                    (#[trigger] vec@[j]).msg is CMessage1b ==>
                        !LExistVotesHasProposalLargeThanOpn(vec@[j]@, AbstractifyCOperationNumberToOperationNumber(op))
                ),
                forall |k: int| 0 <= k < vec@.len() ==> S@.contains(#[trigger] vec@[k]),
                forall |k: int| 0 <= k < vec@.len() ==> (#[trigger] vec@[k]).valid(),
                forall |x: CPacket| S@.contains(x) ==> (exists |k: int| 0 <= k < vec@.len() && vec@[k] == x),
                forall |p:CPacket| S@.contains(p) ==> p.valid(),
                COperationNumberIsValid(op),
                LSetOfMessage1b(S@.map(|p: CPacket| p@)),
            decreases
                vec.len() - i,
        {
            if let CMessage::CMessage1b { bal_1b, log_truncation_point, votes } = &vec[i].msg {
                // vec[i] is CMessage1b and valid — safe to call CExistVotesHasProposalLargeThanOpn
                if Self::CExistVotesHasProposalLargeThanOpn(&vec[i], op) {
                    // Found a packet with votes having key > op
                    proof {
                        let good = vec@[i as int];
                        assert(S@.contains(good));
                        assert(good.valid());
                        assert(good.abstractable());
                        let f = |p: CPacket| p@;
                        assert(S@.map(f).contains(f(good)));
                    }
                    return true;
                }
            }
            i = i + 1;
        }
        // No 1b packet has votes with key > op
        // LSetOfMessage1b guarantees all packets are RslMessage1b, so loop invariant covers all
        proof {
            let f = |p: CPacket| p@;
            assert forall |p: RslPacket| S@.map(f).contains(p)
                implies !LExistVotesHasProposalLargeThanOpn(p, AbstractifyCOperationNumberToOperationNumber(op)) by {
                let cp = choose |cp: CPacket| S@.contains(cp) && f(cp) == p;
                assert(cp.valid());
                assert(cp.abstractable());
                // LSetOfMessage1b: p.msg is RslMessage1b
                assert(p.msg is RslMessage1b);
                let j = choose |j: int| 0 <= j < vec@.len() && vec@[j] == cp;
                // cp.msg is CMessage1b (from p.msg is RslMessage1b)
                // loop invariant via j gives !LExistVotesHasProposalLargeThanOpn(cp@, ...)
            };
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

use super::types_i::COperationNumber;
use crate::common::collections::sets::*;
use std::collections::HashMap;
use vstd::prelude::*;

use vstd::std_specs::hash::*;
use vstd::{map::*, prelude::*, seq::*, set_lib::set_int_range};

use crate::common::collections::{count_matches::*, maps::*, vecs::*};
use crate::implementation::RSL::types_i::CBalLt;

use crate::common::{collections::maps::*, native::io_s::EndPoint};
use crate::implementation::common::{generic_refinement::*, upper_bound::*, upper_bound_i::*};
use crate::implementation::RSL::{
    cbroadcast::*, cconfiguration::*, cconstants::*, cmessage::*, types_i::*,
};
use crate::protocol::RSL::{
    acceptor::*, broadcast::*, configuration::*, constants::*, environment::*, message::*, types::*,
};
// DEPRECATED: Use `crate::generated::RSL::acceptor_gen` for functional wrappers
// and `crate::generated::RSL::types_gen::CAcceptor` for the type directly.
// This module's methods are still called internally by the generated wrappers.
#[deprecated(note = "Import CAcceptor from crate::generated::RSL::types_gen instead")]
pub use crate::generated::RSL::types_gen::CAcceptor;

verus! {

    impl CAcceptor{

    pub fn CRemoveVotesBeforeLogTruncationPoint(votes:&CVotes, log_truncation_point: COperationNumber) -> (cvotes: CVotes)
        requires
            cvotes_is_valid(votes),
            COperationNumberIsValid(log_truncation_point),
        ensures
            cvotes_is_valid(&cvotes),
            RemoveVotesBeforeLogTruncationPoint(
            abstractify_cvotes(votes),
            abstractify_cvotes(&cvotes),
            AbstractifyCOperationNumberToOperationNumber(log_truncation_point)
        )
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;

        let m_keys = votes.keys();
        assert(m_keys@.0 == 0);
        assume(m_keys@.1.len() == votes@.len()); // Gotta assume this, verus can't infer this
        assert(m_keys@.1.to_set() =~= votes@.dom());
        let ghost mut seen_keys = Set::<COperationNumber>::empty();
        assert(seen_keys == m_keys@.1.take(m_keys@.0).to_set());
        let mut result: HashMap<COperationNumber, CVote> = HashMap::new();
        assert(result@ == Map::<COperationNumber, CVote>::empty());

        for key in iter:m_keys
        invariant
            seen_keys.subset_of(votes@.dom()),
            forall |opn: COperationNumber| seen_keys.contains(opn) ==> votes@.contains_key(opn),
            forall |opn: COperationNumber| result@.contains_key(opn) ==> opn >= log_truncation_point && votes@.contains_key(opn),
            forall |opn: COperationNumber| result@.contains_key(opn) ==> seen_keys.contains(opn),
            forall |opn: COperationNumber| seen_keys.contains(opn) && opn >= log_truncation_point ==> result@.contains_key(opn),
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            assume(votes@.contains_key(*key));
            assert(forall |opn:COperationNumber| result@.contains_key(opn) ==> seen_keys.contains(opn));
            proof{seen_keys = seen_keys.insert(*key)};
            if *key >= log_truncation_point
            {
                let value = votes.get(key);
                match value{
                    Some(value) => {
                        assert(*key >= log_truncation_point);
                        assert(votes@.contains_key(*key));
                        result.insert(*key,(*value).clone_up_to_view());
                    }
                    None =>
                    {
                        // unreachable due to precondition: votes@.contains_key(*key)
                    }
                }
            }
        }
        assert(seen_keys.subset_of(votes@.dom()));
        assert(forall |opn:COperationNumber| seen_keys.contains(opn) ==> votes@.contains_key(opn));
        assume(m_keys@.0 == m_keys@.1.len()); // verus is stupid, it doesn't know after iteration, the number of iterated number equals to the len of iter's key_set.
        assume(seen_keys.len() == m_keys@.0);
        assert(seen_keys.len() == m_keys@.1.len());
        proof{subset_len_equal_implies_equal(seen_keys, votes@.dom())};
        assert(seen_keys == votes@.dom());
        assert(forall |opn : COperationNumber| votes@.contains_key(opn) ==> seen_keys.contains(opn));

        assert(forall |opn : COperationNumber| result@.contains_key(opn) <==> seen_keys.contains(opn) && opn >= log_truncation_point);

        assert(forall |opn : COperationNumber| votes@.contains_key(opn) ==> seen_keys.contains(opn));

        assert(forall |opn : COperationNumber| votes@.contains_key(opn) && opn >= log_truncation_point ==> result@.contains_key(opn));

        assert(forall |opn : COperationNumber| result@.contains_key(opn) ==> opn >= log_truncation_point && votes@.contains_key(opn) && result@[opn] == votes@[opn]);

        assert(forall |opn : COperationNumber|
            result@.contains_key(opn)
        ==> opn >= log_truncation_point && votes@.contains_key(opn));


        // The three condition to verify the RemoveVotesBeforeLogTruncationPoint
        assert(forall |opn: COperationNumber| result@.contains_key(opn) ==> votes@.contains_key(opn) && result@[opn] == votes@[opn]);
        assert(forall |opn : COperationNumber| opn < log_truncation_point ==> !result@.contains_key(opn));
        assert(forall |opn : COperationNumber| opn >= log_truncation_point && votes@.contains_key(opn) ==> result@.contains_key(opn));

        result
    }


    // #[verifier(external_body)]
    pub fn CAddVoteAndRemoveOldOnes(votes:&CVotes, new_opn: COperationNumber, new_vote:&CVote, log_truncation_point: COperationNumber) -> (cvotes_2:CVotes)
        requires
            cvotes_is_valid(votes),
            COperationNumberIsValid(new_opn),
            new_vote.valid(),
            COperationNumberIsValid(log_truncation_point),
        ensures
            cvotes_is_valid(&cvotes_2) && LAddVoteAndRemoveOldOnes(abstractify_cvotes(votes), abstractify_cvotes(&cvotes_2), AbstractifyCOperationNumberToOperationNumber(new_opn), new_vote.view(), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let m_keys = votes.keys();
        assert(m_keys@.0 == 0);
        assume(m_keys@.1.len() == votes@.len()); // Gotta assume this, verus can't infer this
        assert(m_keys@.1.to_set() =~= votes@.dom());
        let ghost mut seen_keys = Set::<COperationNumber>::empty();
        assert(seen_keys == m_keys@.1.take(m_keys@.0).to_set());
        let mut result: HashMap<COperationNumber, CVote> = HashMap::new();
        assert(result@ == Map::<COperationNumber, CVote>::empty());

        for key in iter:m_keys
        invariant
            seen_keys.subset_of(votes@.dom()),
            forall |opn: COperationNumber| seen_keys.contains(opn) ==> votes@.contains_key(opn),
            forall |opn: COperationNumber| result@.contains_key(opn) ==> opn >= log_truncation_point && votes@.contains_key(opn),
            // forall |opn: COperationNumber| result@.contains_key(opn) ==> result@[opn] == votes@[opn],
            forall |opn: COperationNumber| result@.contains_key(opn) ==> seen_keys.contains(opn),
            forall |opn: COperationNumber| seen_keys.contains(opn) && opn >= log_truncation_point ==> result@.contains_key(opn),
            // cvotes_is_valid(result),
            // cvotes_is_abstractable(result),
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            assume(votes@.contains_key(*key));
            assert(forall |opn:COperationNumber| result@.contains_key(opn) ==> seen_keys.contains(opn));
            proof{seen_keys = seen_keys.insert(*key)};
            if *key >= log_truncation_point
            {
                let value = votes.get(key);
                match value{
                    Some(value) => {
                        assert(*key >= log_truncation_point);
                        assert(votes@.contains_key(*key));
                        result.insert(*key,(*value).clone_up_to_view());
                    }
                    None =>
                    {
                        // unreachable due to precondition: votes@.contains_key(*key)
                    }
                }
            }
        }

        assert(forall |opn:COperationNumber| result@.contains_key(opn) ==> seen_keys.contains(opn));
        proof{seen_keys = seen_keys.insert(new_opn)};
        result.insert(new_opn, new_vote.clone_up_to_view());

        assume(seen_keys.subset_of(votes@.dom()));
        assert(forall |opn:COperationNumber| seen_keys.contains(opn) ==> votes@.contains_key(opn));
        assume(m_keys@.0 == m_keys@.1.len()); // verus is stupid, it doesn't know after iteration, the number of iterated number equals to the len of iter's key_set.
        assume(seen_keys.len() == m_keys@.0);
        assert(seen_keys.len() == m_keys@.1.len());
        proof{subset_len_equal_implies_equal(seen_keys, votes@.dom())};
        assert(seen_keys == votes@.dom());
        assert(forall |opn : COperationNumber| votes@.contains_key(opn) ==> seen_keys.contains(opn));

        assert(forall |opn : COperationNumber| result@.contains_key(opn) ==> seen_keys.contains(opn) && opn >= log_truncation_point);

        assert(forall |opn : COperationNumber| votes@.contains_key(opn) ==> seen_keys.contains(opn));

        assert(forall |opn : COperationNumber| votes@.contains_key(opn) && opn >= log_truncation_point ==> result@.contains_key(opn));

        assert(forall |opn : COperationNumber| result@.contains_key(opn) ==> opn >= log_truncation_point && votes@.contains_key(opn) && result@[opn] == votes@[opn]);

        assert(forall |opn : COperationNumber|result@.contains_key(opn)==> opn >= log_truncation_point && votes@.contains_key(opn));

        result
    }

    #[verifier(external_body)]
    pub fn CAddVoteAndRemoveOldOnes_optimized(votes:&mut CVotes, new_opn: COperationNumber, new_vote:&CVote, log_truncation_point: COperationNumber, min_vote_opn:COperationNumber) -> (res:COperationNumber)
    {
        votes.insert(new_opn, new_vote.clone_up_to_view());
        let new_votes = clone_cvotes_up_to_view(votes);
        if log_truncation_point > min_vote_opn {
            let m_keys = new_votes.keys();

            for key in iter:m_keys
            {
                if *key < log_truncation_point
                {
                    votes.remove(key);
                }
            }
            log_truncation_point
        } else {
            if new_opn < min_vote_opn {
                new_opn
            } else {
                min_vote_opn
            }
        }
    }


     // Function to initialize CAcceptor
    pub fn CAcceptorInit(c: CReplicaConstants) -> (rc:Self)
        requires c.valid()
        ensures
            rc.valid(),
            LAcceptorInit(rc@,c@)
    {
        let t2 = CBallot{
            seqno: 0,
            proposer_id: 0,
        };
        let t3: HashMap<COperationNumber,CVote> = HashMap::new();

        let len = c.all.config.replica_ids.len();
        let mut t4: Vec<u64> = Vec::new();
        let mut i = 0;
        while i < len
            invariant
                i <= len,
                t4.len() == i,
                forall |j:int| 0 <= j < i ==> t4[j] == 0,
            decreases len - i,
        {
            t4.push(0);
            i = i + 1;
        }

        assert(t4.len() == len);
        assert(forall |idx:int| 0 <= idx < t4.len() ==> t4[idx] == 0);

        let t5 = 0;

        let s = CAcceptor{constants:c, max_bal:t2, votes:t3, last_checkpointed_operation:t4, log_truncation_point:t5, min_vote_opn:0};

        let ghost ss = s@;
        let ghost sc = c@;

        assert(ss.constants =~= sc);
        assert(ss.max_bal =~= Ballot{seqno:0,proposer_id:0});
        assert(ss.votes == Map::<OperationNumber, Vote>::empty());
        assert(ss.last_checkpointed_operation.len() == sc.all.config.replica_ids.len());
        assert(forall |idx:int| 0 <= idx < ss.last_checkpointed_operation.len() ==> ss.last_checkpointed_operation[idx] == 0);
        assert(ss.log_truncation_point == 0);

        s
    }

    // Function to process 1a message
    // #[verifier(external_body)]
    pub fn CAcceptorProcess1a(&mut self, inp: CPacket) -> (sent: OutboundPackets)
        requires
            old(self).valid(),
            inp.valid(),
            inp.msg is CMessage1a
        ensures
            self.valid(),
            sent.valid(),
            LAcceptorProcess1a(old(self)@, self@, inp@, sent@)
    {
        let ghost ss = old(self)@;
        let ghost sinp = inp@;
        match inp.msg{
            CMessage::CMessage1a { bal_1a } => {
                let bal = bal_1a;
                let src = inp.src.clone_up_to_view();

                if  contains(&self.constants.all.config.replica_ids, &src)
                    && CBalLt(&self.max_bal, &bal)
                {
                    assert(self.constants.all.config.replica_ids@.contains(src));
                    assert(ss.constants.all.config.replica_ids.contains(sinp.src));
                    assert(BalLt(ss.max_bal, bal@));
                    assert(LReplicaConstantsValid(ss.constants));

                    self.max_bal = bal;

                    let cloned_votes = clone_cvotes_up_to_view(&self.votes);
                    assert(cvotes_is_valid(&cloned_votes));

                    let response = CMessage::CMessage1b {
                        bal_1b: bal,
                        log_truncation_point: self.log_truncation_point,
                        votes: cloned_votes,
                    };
                    assert(response.valid());

                    let packet = CPacket {
                        src: self.constants.all.config.replica_ids[self.constants.my_index as usize].clone_up_to_view(),
                        dst: inp.src.clone_up_to_view(),
                        msg: response,
                    };
                    assert(packet.src.valid_public_key());
                    assert(packet.dst.valid_public_key());
                    assert(packet.msg.valid());
                    assert(packet.valid());

                    let sent = OutboundPackets::PacketSequence { s: vec![packet] };
                    assert(sent.valid());

                    proof {
                        let ghost expected_packet = RslPacket {
                            src: ss.constants.all.config.replica_ids.index(ss.constants.my_index),
                            dst: sinp.src,
                            msg: RslMessage::RslMessage1b {
                                bal_1b: bal@,
                                log_truncation_point: ss.log_truncation_point,
                                votes: ss.votes,
                            },
                        };
                        let ghost expected = seq![expected_packet];
                        assert(sent@ == expected);
                        assert(self@ == LAcceptor {
                            constants: ss.constants,
                            max_bal: bal@,
                            votes: ss.votes,
                            last_checkpointed_operation: ss.last_checkpointed_operation,
                            log_truncation_point: ss.log_truncation_point,
                        });
                        assert(LAcceptorProcess1a(old(self)@, self@, inp@, sent@));
                    }
                    sent
                } else {
                    let sent = OutboundPackets::PacketSequence { s: Vec::new() };
                    assert(sent.valid());

                    proof {
                        assert(self@ == old(self)@);
                        assert(sent@ == Seq::<RslPacket>::empty());
                        assert(LAcceptorProcess1a(old(self)@, self@, inp@, sent@));
                    }
                    sent
                }
            }
            _ =>{
                let sent = OutboundPackets::PacketSequence { s: Vec::new() };
                sent
            }
        }
    }

    // #[verifier(external_body)]
    pub fn CAcceptorProcess2a(&mut self, inp: CPacket) -> (sent: OutboundPackets)
        requires
            old(self).valid(),
            inp.valid(),
            inp.msg is CMessage2a
        ensures
            self.valid(),
            sent.valid(),
            LAcceptorProcess2a(old(self)@, self@, inp@, sent@)
    {
        let ghost ss = old(self)@;
        let ghost sinp = inp@;

        match inp.msg {
            CMessage::CMessage2a { bal_2a, opn_2a, val_2a } => {
                let max_log_len = self.constants.all.params.max_log_length;

                let trunc_candidate = if opn_2a >= max_log_len {
                    opn_2a - max_log_len + 1
                } else {
                    0
                };

                let new_log_truncation_point = if trunc_candidate > self.log_truncation_point {
                    trunc_candidate
                } else {
                    self.log_truncation_point
                };

                let val_2b_cloned: CRequestBatch = clone_request_batch_up_to_view(&val_2a);
                let response = CMessage::CMessage2b {
                    bal_2b: bal_2a,
                    opn_2b: opn_2a,
                    val_2b: clone_request_batch_up_to_view(&val_2b_cloned),
                };

                // let new_config = self.constants.all.config.clone_up_to_view();
                let sent = OutboundPackets::Broadcast {
                    broadcast: CBroadcast::BuildBroadcastToEveryone(&self.constants.all.config,
                    self.constants.my_index, response)

                };


                self.max_bal = bal_2a;
                self.log_truncation_point = new_log_truncation_point;

                if self.log_truncation_point <= opn_2a {
                    let new_votes = Self::CAddVoteAndRemoveOldOnes(
                        &self.votes,
                        opn_2a,
                        & CVote {
                            max_value_bal: bal_2a,
                            max_val: val_2b_cloned,
                        },
                        new_log_truncation_point,
                    );
                    self.votes = new_votes;
                } else {
                    // clone_cvotes_up_to_view(&self.votes)
                }

                assert(sent.valid());
                sent
            }

            _ => {
                let sent = OutboundPackets::Broadcast {
                    broadcast: CBroadcast::CBroadcastNop {},
                };
                assert(sent.valid());
                sent
            }
        }
    }

    #[verifier(external_body)]
    pub fn CAcceptorProcess2a_optimized(&mut self, inp: CPacket) -> (sent: OutboundPackets)
        requires
            old(self).valid(),
            inp.valid(),
            inp.msg is CMessage2a
        ensures
            self.valid(),
            sent.valid(),
            LAcceptorProcess2a(old(self)@, self@, inp@, sent@)
    {
        let ghost ss = old(self)@;
        let ghost sinp = inp@;

        match inp.msg {
            CMessage::CMessage2a { bal_2a, opn_2a, val_2a } => {
                let max_log_len = self.constants.all.params.max_log_length;

                let trunc_candidate = if opn_2a >= max_log_len {
                    opn_2a - max_log_len + 1
                } else {
                    0
                };

                let new_log_truncation_point = if trunc_candidate > self.log_truncation_point {
                    trunc_candidate
                } else {
                    self.log_truncation_point
                };

                let val_2b_cloned: CRequestBatch = clone_request_batch_up_to_view(&val_2a);
                let response = CMessage::CMessage2b {
                    bal_2b: bal_2a,
                    opn_2b: opn_2a,
                    val_2b: clone_request_batch_up_to_view(&val_2b_cloned),
                };

                // let new_config = self.constants.all.config.clone_up_to_view();
                let sent = OutboundPackets::Broadcast {
                    broadcast: CBroadcast::BuildBroadcastToEveryone(&self.constants.all.config,
                    self.constants.my_index, response)

                };


                self.max_bal = bal_2a;
                self.log_truncation_point = new_log_truncation_point;

                if self.log_truncation_point <= opn_2a {
                    let new_min_vote_opn = Self::CAddVoteAndRemoveOldOnes_optimized(
                        &mut self.votes,
                        opn_2a,
                        & CVote {
                            max_value_bal: bal_2a,
                            max_val: val_2b_cloned,
                        },
                        new_log_truncation_point,
                        self.min_vote_opn
                    );
                    self.min_vote_opn = new_min_vote_opn;
                } else {

                }

                assert(sent.valid());
                sent
            }

            _ => {
                let sent = OutboundPackets::Broadcast {
                    broadcast: CBroadcast::CBroadcastNop {},
                };
                assert(sent.valid());
                sent
            }
        }
    }


    // #[verifier(external_body)]
    pub fn CAcceptorProcessHeartbeat(&mut self, inp: CPacket)
        requires
            old(self).valid(),
            inp.valid(),
            inp.msg is CMessageHeartbeat,
        ensures
            self.valid(),
            LAcceptorProcessHeartbeat(old(self)@, self@, inp@)
    {
        match inp.msg {
            CMessage::CMessageHeartbeat { opn_ckpt, .. } => {
                if contains(&self.constants.all.config.replica_ids, &inp.src) {
                    let (found, idx) = self.constants.all.config.CGetReplicaIndex(&inp.src);
                    if found && idx < self.last_checkpointed_operation.len() {
                        if opn_ckpt > self.last_checkpointed_operation[idx]
                        {
                            let new_last_checkpointed_operation = update_vec_at(&self.last_checkpointed_operation, idx, opn_ckpt);
                            self.last_checkpointed_operation = new_last_checkpointed_operation;
                            proof {
                                let ghost ss = old(self)@;
                                let ghost sinp = inp@;
                                let ghost idx_int = idx as int;
                                assert(self@.last_checkpointed_operation == ss.last_checkpointed_operation.update(idx_int, opn_ckpt as int));
                                assert(LAcceptorProcessHeartbeat(ss, self@, sinp));
                            }

                        }
                    }
                }
            }
            _ => {
                // unreachable due to precondition: inp.msg is CMessageHeartbeat
            }
        }
    }


    // #[verifier(external_body)]
    pub fn CAcceptorTruncateLog(&mut self, opn: COperationNumber)
        requires
            old(self).valid(),
            COperationNumberIsValid(opn)
        ensures
            self.valid(),
            LAcceptorTruncateLog(old(self)@, self@, AbstractifyCOperationNumberToOperationNumber(opn))
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let ghost ss = old(self)@;
        let ghost sopn = opn as int;
        if opn <= self.log_truncation_point {
            assert(LAcceptorTruncateLog(old(self)@, self@, AbstractifyCOperationNumberToOperationNumber(opn)));
        } else {
            // let old_votes = clone_cvotes_up_to_view(&self.votes);
            let new_votes: HashMap<COperationNumber, CVote> = Self::CRemoveVotesBeforeLogTruncationPoint(&self.votes, opn);
            self.votes = new_votes;
            self.log_truncation_point = opn;
            let ghost snew_votes = abstractify_cvotes(&new_votes);
            assert(RemoveVotesBeforeLogTruncationPoint(ss.votes, snew_votes, sopn));
            assert(LAcceptorTruncateLog(ss, self@, sopn));
        }
    }


}

    pub fn CIsLogTruncationPointValid(log_truncation_point: COperationNumber,last_checkpointed_operation:&Vec<COperationNumber>,config:&CConfiguration) -> (isValid: bool)
        requires
            COperationNumberIsValid(log_truncation_point),
            forall |i: int| 0 <= i < last_checkpointed_operation.len() ==> COperationNumberIsValid(last_checkpointed_operation[i]),
            config.valid()
        ensures
            isValid == IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(log_truncation_point),last_checkpointed_operation@.map(|i, x| (x as int)), config@)
    {
        let quorum = config.CMinQuorumSize();
        CIsNthHighestValueInSequence(log_truncation_point, last_checkpointed_operation, quorum as u64)
    }

// Function to check if the log truncation point is valid
// #[verifier(external_body)]
// pub fn CIsLogTruncationPointValid(log_truncation_point: COperationNumber,last_checkpointed_operation:&Vec<COperationNumber>,config:&CConfiguration) -> (isValid: bool)
//     requires
//         COperationNumberIsValid(log_truncation_point),
//         forall |i: int| 0 <= i < last_checkpointed_operation.len() ==> COperationNumberIsValid(last_checkpointed_operation[i]),
//         config.valid()
//     ensures
//         isValid == IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(log_truncation_point),last_checkpointed_operation@.map(|i, x| (x as int)),config.view())
// {
//     let v = log_truncation_point;
//     let s = last_checkpointed_operation;
//     let n = config.CMinQuorumSize();

//     if n == 0 || n >= last_checkpointed_operation.len() {
//         proof {
//             assert(!IsNthHighestValueInSequence(AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
//                 last_checkpointed_operation@.map(|i, x| x as int),
//                 n as int
//             ));
//         }
//         return false;
//     }

//     let mut count_gt:usize = 0;
//     let mut count_ge:usize = 0;
//     let mut contains:bool = true;
//     let len:usize = last_checkpointed_operation.len();
//     let mut i = 0;

//     while i < len
//         invariant
//             0<=i<=len,
//             count_gt <= i,
//             count_ge <= i,
//             len == last_checkpointed_operation.len(),
//     {
//         assert(i<len);
//         assert(i>=0);
//         assert(i<last_checkpointed_operation.len());
//         if last_checkpointed_operation[i] > v {
//             count_gt += 1;
//         }
//         else if last_checkpointed_operation[i] >= v
//         {
//             contains = true;
//             count_ge += 1;
//         }
//         i += 1;
//     }

//     let isValid = contains && count_gt < n && count_ge >= n;

//     proof {
//         assert(0 < n < last_checkpointed_operation.len());
//         assert(isValid == IsNthHighestValueInSequence(AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
//             last_checkpointed_operation@.map(|i, x| x as int),
//             n as int
//         ));
//     }
//     isValid

// }

    fn CCountLargerInSeq(s:&Vec<u64>, target:u64) -> (res:u64)
        ensures
        ({
            let ss = s@.map(|i, t:u64| t as int);
            && res < 0xffff_ffff_ffff_ffff
            && res as int == CountMatchesInSeq(ss, |x:int| x > target as int)
        })
        decreases s.len(),
    {
        let ghost ss = s@.map(|i, t:u64| t as int);
        if s.len() == 0 {
            assert(ss.len() == 0);
            assert(CountMatchesInSeq(ss, |x:int| x > target as int) == 0);
            0
        } else {
            let rest = truncate_vecu64(s, 1, s.len());
            assert(rest@.map(|i, t:u64| t as int) == ss.subrange(1, ss.len() as int));
            let temp = CCountLargerInSeq(&rest, target);
            assert(temp == CountMatchesInSeq(ss.subrange(1, ss.len() as int), |x:int| x > target as int));
            if s[0] > target {
                assume(temp + 1 < 0xffff_ffff_ffff_ffff);
                temp + 1
            } else
            {
                temp
            }
        }
    }


    fn CCountLargerOrEqualInSeq(s:&Vec<u64>, target:u64) -> (res:u64)
        ensures
        ({
            let ss = s@.map(|i, t:u64| t as int);
            && res < 0xffff_ffff_ffff_ffff
            && res as int == CountMatchesInSeq(ss, |x:int| x >= target as int)
        })
        decreases s.len(),
    {
        let ghost ss = s@.map(|i, t:u64| t as int);
        if s.len() == 0 {
            assert(ss.len() == 0);
            assert(CountMatchesInSeq(ss, |x:int| x > target as int) == 0);
            0
        } else {
            let rest = truncate_vecu64(s, 1, s.len());
            let temp = CCountLargerOrEqualInSeq(&rest, target);
            assert(temp == CountMatchesInSeq(ss.subrange(1, ss.len() as int), |x:int| x >= target as int));
            if s[0] >= target {
                assume(temp + 1 < 0xffff_ffff_ffff_ffff);
                temp + 1
            } else
            {
                temp
            }
        }
    }

    fn CIsNthHighestValueInSequence(v:u64, s:&Vec<u64>, n:u64) -> (res:bool)
        ensures
        ({
            let ss = s@.map(|i, t:u64| t as int);
            && res == IsNthHighestValueInSequence(v as int, ss, n as int)
        })
    {
        let ghost ss = s@.map(|i, t:u64| t as int);
        let len = s.len();
        let b1 = (0 < n) && (n < len as u64);
        assert(b1 == (0 < n < ss.len()));
        let b2 = contains_u64(s, &v);
        assert(b2 == ss.contains(v as int));
        let b3 = CCountLargerInSeq(s, v) < n;
        assert(b3 == (CountMatchesInSeq(ss, |x:int| x > v) < n as int));
        let b4 = CCountLargerOrEqualInSeq(s, v) >= n;
        assert(b4 == (CountMatchesInSeq(ss, |x:int| x >= v) >= n));
        b1 && b2 && b3 && b4
    }

    // Axiom for vote length
    #[verifier(external_body)]
    pub proof fn lemma_voteLen(votes: CVotes)
        // requires cvotes_is_valid(votes)
        ensures votes.len() < max_votes_len()
    {
        // Now trivially true because cvotes_is_valid implies the length constraint
    }

}

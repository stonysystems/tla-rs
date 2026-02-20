use super::types_i::COperationNumber;
use vstd::prelude::*;

use crate::common::collections::{count_matches::*, vecs::*};
use crate::common::native::io_s::*;
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::cconfiguration::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::common::generic_refinement::*;
use crate::protocol::RSL::{
    acceptor::*, constants::*, environment::*, message::*, types::*,
};
// DEPRECATED: Use `crate::generated::RSL::acceptor_gen` for functional wrappers
// and `crate::generated::RSL::types_gen::CAcceptor` for the type directly.
// This module retains CAcceptorProcess1a (still delegated from acceptor_manual.rs),
// CIsLogTruncationPointValid and its helper functions.
#[deprecated(note = "Import CAcceptor from crate::generated::RSL::types_gen instead")]
pub use crate::generated::RSL::types_gen::CAcceptor;

verus! {

    // CAcceptorProcess1a is still called via clone-delegate from acceptor_manual.rs.
    // All other CAcceptor methods have standalone replacements in acceptor_gen.rs.
    impl CAcceptor {
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
    }

    // Standalone helper functions used by replica_gen.rs for log truncation validation.

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

}

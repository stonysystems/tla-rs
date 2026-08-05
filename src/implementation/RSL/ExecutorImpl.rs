use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::cbroadcast::OutboundPackets;
use crate::implementation::RSL::cbroadcast::OutboundPackets::PacketSequence;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::gen_helpers::{CGetPacketsFromReplies, CUpdateNewCache};
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::CStateMachine::*;
use crate::implementation::RSL::ElectionImpl::COutstandingOperation;
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::executor::*;
use crate::protocol::RSL::proposer::*;
use crate::protocol::RSL::state_machine::HandleRequestBatch;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::environment::RslPacket;
use crate::common::framework::environment_s::LPacket;
use crate::common::native::io_s::AbstractEndPoint;

use vstd::prelude::*;
// Generated wrappers live in `crate::generated::RSL::executor_gen`.
// This module owns CExecutor/CIncompleteBatchTimer type infrastructure
// and CExecutorExecute, which is still called from ReplicaImpl.rs.

verus! {
pub struct CExecutor {
    pub constants: CReplicaConstants,
    pub app: CAppState,
    pub ops_complete: u64,
    pub max_bal_reflected: CBallot,
    pub next_op_to_execute: COutstandingOperation,
    pub reply_cache: CReplyCache,
}

impl CExecutor {
    pub open spec fn valid(&self) -> bool {
        self.abstractable()
            && self.constants.valid()
            && CAppStateIsValid(&self.app)
            && self.max_bal_reflected.valid()
            && self.next_op_to_execute.valid()
            && creplycache_is_valid(&self.reply_cache)
    }

    pub open spec fn abstractable(&self) -> bool {
        self.constants.abstractable()
            && CAppStateIsAbstractable(&self.app)
            && self.max_bal_reflected.abstractable()
            && self.next_op_to_execute.abstractable()
            && creplycache_is_abstractable(&self.reply_cache)
    }

    pub open spec fn view(&self) -> LExecutor
        recommends
            self.abstractable(){
        let res = LExecutor {
            constants: self.constants.view(),
            app: self.app,
            ops_complete: self.ops_complete as int,
            max_bal_reflected: self.max_bal_reflected.view(),
            next_op_to_execute: self.next_op_to_execute.view(),
            reply_cache: abstractify_creplycache(&self.reply_cache),
        };
        res
    }

    pub fn clone_up_to_view(&self) -> (result: Self)
        ensures
            result@ == self@,
            result.valid() == self.valid(),
    {
        let constants_clone = self.constants.clone();
        // Clone impl ensures: constants_clone == *self.constants, constants_clone@ == self.constants@
        let reply_cache_clone = clone_creply_cache_up_to_view(&self.reply_cache);
        let next_op_clone = match &self.next_op_to_execute {
            COutstandingOperation::COutstandingOpKnown{v, bal} => {
                let v_clone = clone_request_batch_up_to_view(v);
                // ensures: v_clone@ == v@, element-wise valid() preserved
                COutstandingOperation::COutstandingOpKnown{v: v_clone, bal: *bal}
            }
            COutstandingOperation::COutstandingOpUnknown{} => {
                COutstandingOperation::COutstandingOpUnknown{}
            }
        };
        CExecutor {
            constants: constants_clone,
            app: self.app,
            ops_complete: self.ops_complete,
            max_bal_reflected: self.max_bal_reflected,
            next_op_to_execute: next_op_clone,
            reply_cache: reply_cache_clone,
        }
    }
}

impl Clone for CExecutor {
    fn clone(&self) -> (result: Self)
    ensures
        result@ == self@,
        result.valid() == self.valid(),
    {
        self.clone_up_to_view()
    }
}


impl View for CExecutor {
    type V = LExecutor;

    open spec fn view(&self) -> LExecutor {
        let res = LExecutor {
            constants: self.constants.view(),
            app: self.app,
            ops_complete: self.ops_complete as int,
            max_bal_reflected: self.max_bal_reflected.view(),
            next_op_to_execute: self.next_op_to_execute.view(),
            reply_cache: abstractify_creplycache(&self.reply_cache),
        };
        res
    }
}

#[derive(Clone, Copy)]
pub enum CIncompleteBatchTimer {
    CIncompleteBatchTimerOn {
        when: u64,
    },
    CIncompleteBatchTimerOff,
}

impl CIncompleteBatchTimer{
    pub open spec fn abstractable(self) -> bool {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => true,
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => true,
        }
    }

    pub open spec fn valid(self) -> bool {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => self.abstractable(),
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => self.abstractable(),
        }
    }

    pub open spec fn view(self) -> IncompleteBatchTimer
        recommends
        self.abstractable(),
    {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => IncompleteBatchTimer::IncompleteBatchTimerOn {when:when as int},
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => IncompleteBatchTimer::IncompleteBatchTimerOff{},
        }
    }
}

impl View for CIncompleteBatchTimer {
    type V = IncompleteBatchTimer;

    open spec fn view(&self) -> IncompleteBatchTimer {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => IncompleteBatchTimer::IncompleteBatchTimerOn {when:*when as int},
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => IncompleteBatchTimer::IncompleteBatchTimerOff{},
        }
    }
}

// Proves that GetPacketsFromReplies constructs packets with RslMessageReply messages.
proof fn lemma_replies_are_reply_type(me: AbstractEndPoint, requests: RequestBatch, replies: Seq<Reply>, packets: Seq<RslPacket>)
    requires
        packets == GetPacketsFromReplies(me, requests, replies),
        requests.len() == replies.len(),
    ensures
        RepliesAreReplyType(packets),
    decreases requests.len(),
{
    if requests.len() > 0 {
        let rest_packets = GetPacketsFromReplies(me, requests.drop_first(), replies.drop_first());
        lemma_replies_are_reply_type(me, requests.drop_first(), replies.drop_first(), rest_packets);
        let first = LPacket::<AbstractEndPoint, RslMessage>{
            dst: requests[0].client,
            src: me,
            msg: RslMessage::RslMessageReply{
                seqno_reply: requests[0].seqno,
                reply: replies[0].reply,
            },
        };
        assert(packets =~= seq![first] + rest_packets);
        assert forall |p: RslPacket| #![trigger packets.contains(p)] packets.contains(p) implies p.msg is RslMessageReply by {
            if rest_packets.contains(p) {
                // By induction: RepliesAreReplyType(rest_packets)
            } else {
                // p must be first, which has msg is RslMessageReply
            }
        };
    }
    // Base case: packets is empty, vacuously true
}

impl CExecutor{

    // Phase 25.6: removed external_body, added proof assertions
    pub fn CExecutorExecute(&mut self) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            old(self).next_op_to_execute is COutstandingOpKnown,
            LtUpperBound(old(self)@.ops_complete, old(self)@.constants.all.params.max_integer_val),
            LReplicaConstantsValid(old(self)@.constants)
        ensures
            self.valid(),
            res.valid(),
            LExecutorExecute(old(self)@,
                                self@,
                                res@)
    {
        let ghost ss = old(self)@;
        let ghost spec_batch = ss.next_op_to_execute->v;
        let ghost spec_temp = HandleRequestBatch(ss.app, spec_batch);
        let ghost spec_new_state = spec_temp.0[spec_temp.0.len()-1];
        let ghost spec_replies = spec_temp.1;

        match &self.next_op_to_execute {
            COutstandingOperation::COutstandingOpKnown{v, bal} => {
                let batch = clone_request_batch_up_to_view(&v);
                let x = bal.clone_up_to_view();
                let (new_states, replies) = CHandleRequestBatch(&self.app, &batch);

                proof {
                    // CHandleRequestBatch ensures the exec results map to spec HandleRequestBatch
                    assert((new_states@.map(|i, x: CAppState| x@), replies@.map(|i, x: CReply| x@))
                        == HandleRequestBatch(self.app@, batch@.map(|i, x: CRequest| x@)));
                    assert(batch@.map(|i, x: CRequest| x@) == spec_batch);
                    assert(self.app == ss.app);
                    // Length properties from CHandleRequestBatch ensures
                    assert(new_states.len() == batch.len() + 1);
                    assert(new_states.len() > 0);
                    assert(replies.len() == batch.len());
                    // Reply validity from CHandleRequestBatch ensures (proved via induction on batch)
                }

                let new_state = new_states[new_states.len()-1];

                let new_max_bal_reflected = if CBalLeq(&self.max_bal_reflected, &x) {
                    x
                } else {
                    self.max_bal_reflected
                };

                self.app = new_state;
                self.ops_complete = self.ops_complete + 1;
                self.max_bal_reflected = new_max_bal_reflected;
                self.next_op_to_execute = COutstandingOperation::COutstandingOpUnknown{};
                self.reply_cache = CUpdateNewCache(&self.reply_cache, &replies);
                let pkt_vec = CGetPacketsFromReplies(
                    &self.constants.all.config.replica_ids[self.constants.my_index as usize],
                    &batch,
                    &replies
                );
                assert(forall |i:int| #![trigger pkt_vec@[i]] 0 <= i < pkt_vec.len() ==> pkt_vec@[i].valid());
                let outpackets = PacketSequence{s: pkt_vec};

                proof {
                    let ghost sr = self@;
                    let ghost sp = outpackets@;

                    // Conjunct 1: constants unchanged
                    assert(sr.constants == ss.constants);
                    // Conjunct 2: app == new_state from HandleRequestBatch
                    assert(sr.app == spec_new_state) by {
                        assert(new_states@.map(|i, x: CAppState| x@) == spec_temp.0);
                    };
                    // Conjunct 3: ops_complete incremented
                    assert(sr.ops_complete == ss.ops_complete + 1);
                    // Conjunct 4: max_bal_reflected conditional
                    assert(sr.max_bal_reflected == if BalLeq(ss.max_bal_reflected, ss.next_op_to_execute->bal)
                        { ss.next_op_to_execute->bal } else { ss.max_bal_reflected });
                    // Conjunct 5: next_op reset to unknown
                    assert(sr.next_op_to_execute == OutstandingOperation::OutstandingOpUnknown{});
                    // Conjunct 6: reply cache updated
                    assert(UpdateNewCache(ss.reply_cache, sr.reply_cache, spec_replies));
                    // Conjunct 7: sent_packets match GetPacketsFromReplies
                    assert(sp == GetPacketsFromReplies(
                        ss.constants.all.config.replica_ids[ss.constants.my_index],
                        spec_batch,
                        spec_replies));
                    // Conjunct 8: RepliesAreReplyType — proved by induction on GetPacketsFromReplies
                    assert(spec_batch.len() == spec_replies.len());
                    lemma_replies_are_reply_type(
                        ss.constants.all.config.replica_ids[ss.constants.my_index],
                        spec_batch, spec_replies, sp);
                    assert(RepliesAreReplyType(sp));

                    assert(LExecutorExecute(ss, sr, sp));
                }

                outpackets
            }
            COutstandingOperation::COutstandingOpUnknown {  } => {
                proof { assert(false); }
                let mut pkt_vec: Vec<CPacket> = Vec::new();
                let outpackets = OutboundPackets::PacketSequence{
                    s:pkt_vec,
                };
                outpackets
            }
        }
    }

}

}

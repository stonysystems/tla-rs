use crate::generated::RSL::executor_gen::CGetPacketsFromReplies;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::cbroadcast::OutboundPackets;
use crate::implementation::RSL::cbroadcast::OutboundPackets::PacketSequence;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::gen_helpers::CUpdateNewCache;
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::CStateMachine::*;
use crate::implementation::RSL::ElectionImpl::COutstandingOperation;
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::executor::*;
use crate::protocol::RSL::proposer::*;
use crate::protocol::RSL::types::*;
use vstd::prelude::*;
// Generated wrappers live in `crate::generated::RSL::executor_gen`.
// This module owns CExecutor/CIncompleteBatchTimer type infrastructure
// and CExecutorExecute, which is still called from ReplicaImpl.rs.

verus! {
#[derive(Clone)]
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

    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result: Self)
        ensures
            result@ == self@,
            result.valid() == self.valid(),
    {
        self.clone()
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

#[derive(Clone)]
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

impl CExecutor{

    #[verifier(external_body)]
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
        match &self.next_op_to_execute {
            COutstandingOperation::COutstandingOpKnown{v, bal} => {
                let batch = clone_request_batch_up_to_view(&v);
                let x = bal.clone_up_to_view();
                let (new_states, replies) = CHandleRequestBatch(&self.app, &batch);
                let new_state = new_states[new_states.len()-1];

                let new_max_bal_reflected = if CBalLeq(&self.max_bal_reflected, &x) {
                    x
                } else {
                    self.max_bal_reflected
                };

                self.app= new_state;
                self.ops_complete = self.ops_complete + 1;
                self.max_bal_reflected = new_max_bal_reflected;
                self.next_op_to_execute = COutstandingOperation::COutstandingOpUnknown{};
                self.reply_cache = CUpdateNewCache(&self.reply_cache, &replies);
                let pkt_vec = CGetPacketsFromReplies(
                    &self.constants.all.config.replica_ids[self.constants.my_index as usize],
                    &batch,
                    &replies
                );
                assert(forall |i:int| 0 <= i < pkt_vec.len() ==> pkt_vec@[i].valid());
                let outpackets = PacketSequence{s: pkt_vec};
                outpackets
            }
            COutstandingOperation::COutstandingOpUnknown {  } => {
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

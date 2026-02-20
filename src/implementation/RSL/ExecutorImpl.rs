use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::cbroadcast::OutboundPackets;
use crate::implementation::RSL::cbroadcast::OutboundPackets::PacketSequence;
use crate::protocol::RSL::types::*;
use vstd::prelude::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::CStateMachine::*;
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::executor::*;
use crate::protocol::RSL::constants::*;
use crate::generated::RSL::executor_gen::{CGetPacketsFromReplies, CUpdateNewCache};
// DEPRECATED: Use `crate::generated::RSL::executor_gen` for functional wrappers
// and `crate::generated::RSL::types_gen::{CExecutor, COutstandingOperation}` for types directly.
// This module retains only CExecutorExecute (called from ReplicaImpl.rs).
#[deprecated(note = "Import CExecutor, COutstandingOperation from crate::generated::RSL::types_gen instead")]
pub use crate::generated::RSL::types_gen::{CExecutor, COutstandingOperation};

verus! {

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

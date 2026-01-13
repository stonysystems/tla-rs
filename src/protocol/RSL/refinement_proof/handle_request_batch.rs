use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::state_machine::*;

use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::native::io_s::*;
use crate::services::RSL::app_state_machine::*;

verus!{
    pub open spec fn GetAppStateFromRequestBatches(batches:Seq<RequestBatch>) -> AppState
        decreases batches.len()
    {
      if batches.len() == 0 {
        AppInitialize()
      } else {
        HandleRequestBatch(GetAppStateFromRequestBatches(batches.drop_last()), batches.last()).0.last()
      }
    }

    pub open spec fn GetReplyFromRequestBatches(batches:Seq<RequestBatch>, batch_num:int, req_num:int) -> Reply
        recommends 0 <= batch_num < batches.len(),
                 0 <= req_num < batches[batch_num].len(),
    {
        let prev_state = GetAppStateFromRequestBatches(batches.subrange(0,batch_num));
        let result = HandleRequestBatch(prev_state, batches[batch_num]);
        result.1[req_num]
    }
  
    pub proof fn lemma_GetReplyFromRequestBatchesMatchesInSubsequence(batches1:Seq<RequestBatch>, batches2:Seq<RequestBatch>, batch_num:int, req_num:int)
        requires 0 <= batch_num < batches1.len() <= batches2.len(),
                batches1 == batches2.subrange(0, batches1.len() as int),
                0 <= req_num < batches1[batch_num].len(),
        ensures  GetReplyFromRequestBatches(batches1, batch_num, req_num) == GetReplyFromRequestBatches(batches2, batch_num, req_num)
    {
        assert(batches1.subrange(0, batch_num) == batches2.subrange(0, batch_num));
        assert(batches1[batch_num] == batches2[batch_num]);
    }

}
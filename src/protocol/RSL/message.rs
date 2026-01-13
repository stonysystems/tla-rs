use builtin::*;
use builtin_macros::*;
use vstd::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;

verus! {
    pub enum RslMessage {
        RslMessageInvalid{},
        RslMessageRequest{
            seqno_req:int,
            val:AppMessage,
        },
        RslMessage1a{
            bal_1a:Ballot,
        },
        RslMessage1b{
            bal_1b:Ballot,
            log_truncation_point:OperationNumber,
            votes:Votes,
        },
        RslMessage2a{
            bal_2a:Ballot,
            opn_2a:OperationNumber,
            val_2a:RequestBatch,
        },
        RslMessage2b{
            bal_2b:Ballot,
            opn_2b:OperationNumber,
            val_2b:RequestBatch,
        },
        RslMessageHeartbeat{
            bal_heartbeat:Ballot,
            suspicious:bool,
            opn_ckpt:OperationNumber,
        },
        RslMessageReply{
            seqno_reply:int,
            reply:AppMessage,
        },
        RslMessageAppStateRequest{
            bal_state_req:Ballot,
            opn_state_req:OperationNumber,
        },
        RslMessageAppStateSupply{
            bal_state_supply:Ballot,
            opn_state_supply:OperationNumber,
            app_state:AppState,
            reply_cache:ReplyCache,
        },
        RslMessageStartingPhase2{
            bal_2:Ballot,
            logTruncationPoint_2:OperationNumber,
        },
    }
}
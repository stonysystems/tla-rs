use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::common::native::io_s::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::common::marshalling::*;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
use builtin::*;
use builtin_macros::*;
use std::collections::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use vstd::std_specs::hash::*;
use std::hash::{Hash, Hasher};
use std::mem;
use std::collections::hash_map::DefaultHasher;

verus! {

    // #[derive(Clone)]
    // pub enum CMessage {
    //     CMessageInvalid{},
    //     CMessageRequest{
    //         seqno_req:u64,
    //         val:CAppMessage,
    //     },
    //     CMessage1a{
    //         bal_1a:CBallot,
    //     },
    //     CMessage1b{
    //         bal_1b:CBallot,
    //         log_truncation_point:COperationNumber,
    //         votes:CVotes,
    //     },
    //     CMessage2a{
    //         bal_2a:CBallot,
    //         opn_2a:COperationNumber,
    //         val_2a:CRequestBatch,
    //     },
    //     CMessage2b{
    //         bal_2b:CBallot,
    //         opn_2b:COperationNumber,
    //         val_2b:CRequestBatch,
    //     },
    //     CMessageHeartbeat{
    //         bal_heartbeat:CBallot,
    //         suspicious:bool,
    //         opn_ckpt:COperationNumber,
    //     },
    //     CMessageReply{
    //         seqno_reply:u64,
    //         reply:CAppMessage,
    //     },
    //     CMessageAppStateRequest{
    //         bal_state_req:CBallot,
    //         opn_state_req:COperationNumber,
    //     },
    //     CMessageAppStateSupply{
    //         bal_state_supply:CBallot,
    //         opn_state_supply:COperationNumber,
    //         app_state:CAppState,
    //         reply_cache:CReplyCache,
    //     },
    //     CMessageStartingPhase2{
    //         bal_2:CBallot,
    //         logTruncationPoint_2:COperationNumber,
    //     },
    // }
    define_enum_and_derive_marshalable! {
        #[derive(Clone , Eq, /*Hash,*/ PartialEq)]
        #[verus::trusted]
        pub enum CMessage {
            #[tag = 0]
            CMessageInvalid{},
            #[tag = 1]
            CMessageRequest{
                #[o=o0] seqno_req:u64,
                #[o=o1] val:CAppMessage,
            },
            #[tag = 2]
            CMessage1a{
                #[o=o0] bal_1a:CBallot,
            },
            #[tag = 3]
            CMessage1b{
                #[o=o0] bal_1b:CBallot,
                #[o=o1] log_truncation_point:COperationNumber,
                #[o=o2] votes:CVotes,
            },
            #[tag = 4]
            CMessage2a{
                #[o=o0] bal_2a:CBallot,
                #[o=o1] opn_2a:COperationNumber,
                #[o=o2] val_2a:CRequestBatch,
            },
            #[tag = 5]
            CMessage2b{
                #[o=o0] bal_2b:CBallot,
                #[o=o1] opn_2b:COperationNumber,
                #[o=o2] val_2b:CRequestBatch,
            },
            #[tag = 6]
            CMessageHeartbeat{
                #[o=o0] bal_heartbeat:CBallot,
                #[o=o1] suspicious:bool,
                #[o=o2] opn_ckpt:COperationNumber,
            },
            #[tag = 7]
            CMessageReply{
                #[o=o0] seqno_reply:u64,
                #[o=o1] reply:CAppMessage,
            },
            #[tag = 8]
            CMessageAppStateRequest{
                #[o=o0] bal_state_req:CBallot,
                #[o=o1] opn_state_req:COperationNumber,
            },
            #[tag = 9]
            CMessageAppStateSupply{
                #[o=o0] bal_state_supply:CBallot,
                #[o=o1] opn_state_supply:COperationNumber,
                #[o=o2] app_state:CAppState,
                #[o=o3] reply_cache:CReplyCache,
            },
            #[tag = 10]
            CMessageStartingPhase2{
                #[o=o0] bal_2:CBallot,
                #[o=o1] logTruncationPoint_2:COperationNumber,
            },
        }
        [rlimit attr = verifier::rlimit(100)]
    }

    impl CMessage{

        pub fn clone_up_to_view(&self) -> (res: Self)
        ensures 
            // res.abstractable(),
            // res.valid(),
            res@ == self@
                
    {
        match self {
            CMessage::CMessageInvalid {} => CMessage::CMessageInvalid {},

            CMessage::CMessageRequest { seqno_req, val } =>
                CMessage::CMessageRequest {
                    seqno_req: *seqno_req,
                    val: val.clone_up_to_view(),
                },

            CMessage::CMessage1a { bal_1a } =>
                CMessage::CMessage1a {
                    bal_1a: bal_1a.clone_up_to_view(),
                },

            CMessage::CMessage1b { bal_1b, log_truncation_point, votes } =>
                CMessage::CMessage1b {
                    bal_1b: bal_1b.clone_up_to_view(),
                    log_truncation_point: *log_truncation_point,
                    votes: clone_cvotes_up_to_view(votes),
                },

            CMessage::CMessage2a { bal_2a, opn_2a, val_2a } =>
                CMessage::CMessage2a {
                    bal_2a: bal_2a.clone_up_to_view(),
                    opn_2a: *opn_2a,
                    val_2a: clone_request_batch_up_to_view(val_2a),
                },

            CMessage::CMessage2b { bal_2b, opn_2b, val_2b } =>
                CMessage::CMessage2b {
                    bal_2b: bal_2b.clone_up_to_view(),
                    opn_2b: *opn_2b,
                    val_2b: clone_request_batch_up_to_view(val_2b),
                },

            CMessage::CMessageHeartbeat { bal_heartbeat, suspicious, opn_ckpt } =>
                CMessage::CMessageHeartbeat {
                    bal_heartbeat: bal_heartbeat.clone_up_to_view(),
                    suspicious: *suspicious,
                    opn_ckpt: *opn_ckpt,
                },

            CMessage::CMessageReply { seqno_reply, reply } =>
                CMessage::CMessageReply {
                    seqno_reply: *seqno_reply,
                    reply: reply.clone_up_to_view(),
                },

            CMessage::CMessageAppStateRequest { bal_state_req, opn_state_req } =>
                CMessage::CMessageAppStateRequest {
                    bal_state_req: bal_state_req.clone_up_to_view(),
                    opn_state_req: *opn_state_req,
                },

            CMessage::CMessageAppStateSupply { bal_state_supply, opn_state_supply, app_state, reply_cache } =>
                CMessage::CMessageAppStateSupply {
                    bal_state_supply: bal_state_supply.clone_up_to_view(),
                    opn_state_supply: *opn_state_supply,
                    app_state: *app_state,
                    reply_cache: clone_creply_cache_up_to_view(reply_cache),
                },

            CMessage::CMessageStartingPhase2 { bal_2, logTruncationPoint_2 } =>
                CMessage::CMessageStartingPhase2 {
                    bal_2: bal_2.clone_up_to_view(),
                    logTruncationPoint_2: *logTruncationPoint_2,
                },
        }
    }

        pub open spec fn abstractable(self) -> bool
        {
            match self {
                CMessage::CMessageInvalid{} => true,
                CMessage::CMessageRequest{seqno_req, val} => self->val.abstractable(),
                CMessage::CMessage1a{bal_1a} => self->bal_1a.abstractable(),
                CMessage::CMessage1b{bal_1b, log_truncation_point, votes} => self->bal_1b.abstractable() && COperationNumberIsAbstractable(self->log_truncation_point) && cvotes_is_abstractable(&self->votes),
                CMessage::CMessage2a{bal_2a, opn_2a, val_2a} => self->bal_2a.abstractable() && COperationNumberIsAbstractable(self->opn_2a) && crequestbatch_is_abstractable(&self->val_2a),
                CMessage::CMessage2b{bal_2b, opn_2b, val_2b} => self->bal_2b.abstractable() && COperationNumberIsAbstractable(self->opn_2b) && crequestbatch_is_abstractable(&self->val_2b),
                CMessage::CMessageHeartbeat{bal_heartbeat, suspicious, opn_ckpt} => self->bal_heartbeat.abstractable() && COperationNumberIsAbstractable(self->opn_ckpt),
                CMessage::CMessageReply{seqno_reply, reply} => self->reply.abstractable(),
                CMessage::CMessageAppStateRequest{bal_state_req, opn_state_req} => self->bal_state_req.abstractable() && COperationNumberIsAbstractable(self->opn_state_req),
                CMessage::CMessageAppStateSupply{bal_state_supply, opn_state_supply, app_state, reply_cache} => self->bal_state_supply.abstractable() && COperationNumberIsAbstractable(self->opn_state_supply) && CAppStateIsAbstractable(&self->app_state) && creplycache_is_abstractable(&self->reply_cache),
                CMessage::CMessageStartingPhase2{bal_2, logTruncationPoint_2} => self->bal_2.abstractable() && COperationNumberIsAbstractable(self->logTruncationPoint_2),
            }
        }

        pub open spec fn valid(self) -> bool
        {
            &&& self.abstractable()
            &&& match self {
                CMessage::CMessageInvalid{} => true,
                CMessage::CMessageRequest{seqno_req, val} => self->val.valid(),
                CMessage::CMessage1a{bal_1a} => self->bal_1a.valid(),
                CMessage::CMessage1b{bal_1b, log_truncation_point, votes} => self->bal_1b.valid() && COperationNumberIsValid(self->log_truncation_point) && cvotes_is_valid(&self->votes),
                CMessage::CMessage2a{bal_2a, opn_2a, val_2a} => self->bal_2a.valid() && COperationNumberIsValid(self->opn_2a) && crequestbatch_is_valid(&self->val_2a),
                CMessage::CMessage2b{bal_2b, opn_2b, val_2b} => self->bal_2b.valid() && COperationNumberIsValid(self->opn_2b) && crequestbatch_is_valid(&self->val_2b),
                CMessage::CMessageHeartbeat{bal_heartbeat, suspicious, opn_ckpt} => self->bal_heartbeat.valid() && COperationNumberIsValid(self->opn_ckpt),
                CMessage::CMessageReply{seqno_reply, reply} => self->reply.valid(),
                CMessage::CMessageAppStateRequest{bal_state_req, opn_state_req} => self->bal_state_req.valid() && COperationNumberIsValid(self->opn_state_req),
                CMessage::CMessageAppStateSupply{bal_state_supply, opn_state_supply, app_state, reply_cache} => self->bal_state_supply.valid() && COperationNumberIsValid(self->opn_state_supply) && CAppStateIsValid(&self->app_state) && creplycache_is_valid(&self->reply_cache),
                CMessage::CMessageStartingPhase2{bal_2, logTruncationPoint_2} => self->bal_2.valid() && COperationNumberIsValid(self->logTruncationPoint_2),
            }
        }

        pub open spec fn view(self) -> RslMessage
            recommends self.abstractable()
        {
            match self {
                CMessage::CMessageInvalid{} => RslMessage::RslMessageInvalid{},
                CMessage::CMessageRequest{seqno_req, val} => RslMessage::RslMessageRequest{seqno_req: seqno_req as int, val: val@},
                CMessage::CMessage1a{bal_1a} => RslMessage::RslMessage1a{bal_1a: bal_1a@},
                CMessage::CMessage1b{bal_1b, log_truncation_point, votes} => RslMessage::RslMessage1b{bal_1b: bal_1b@, log_truncation_point: AbstractifyCOperationNumberToOperationNumber(log_truncation_point), votes: abstractify_cvotes(&votes)},
                CMessage::CMessage2a{bal_2a, opn_2a, val_2a} => RslMessage::RslMessage2a{bal_2a: bal_2a@, opn_2a: AbstractifyCOperationNumberToOperationNumber(opn_2a), val_2a: abstractify_crequestbatch(&val_2a)},
                CMessage::CMessage2b{bal_2b, opn_2b, val_2b} => RslMessage::RslMessage2b{bal_2b: bal_2b@, opn_2b: AbstractifyCOperationNumberToOperationNumber(opn_2b), val_2b: abstractify_crequestbatch(&val_2b)},
                CMessage::CMessageHeartbeat{bal_heartbeat, suspicious, opn_ckpt} => RslMessage::RslMessageHeartbeat{bal_heartbeat: bal_heartbeat@, suspicious: suspicious, opn_ckpt: AbstractifyCOperationNumberToOperationNumber(opn_ckpt)},
                CMessage::CMessageReply{seqno_reply, reply} => RslMessage::RslMessageReply{seqno_reply: seqno_reply as int, reply:reply@},
                CMessage::CMessageAppStateRequest{bal_state_req, opn_state_req} => RslMessage::RslMessageAppStateRequest{bal_state_req: bal_state_req@, opn_state_req: AbstractifyCOperationNumberToOperationNumber(opn_state_req)},
                CMessage::CMessageAppStateSupply{bal_state_supply, opn_state_supply, app_state, reply_cache} => RslMessage::RslMessageAppStateSupply{bal_state_supply: bal_state_supply@, opn_state_supply:AbstractifyCOperationNumberToOperationNumber(opn_state_supply), app_state:AbstractifyCAppStateToAppState(&app_state), reply_cache:abstractify_creplycache(&reply_cache)},
                CMessage::CMessageStartingPhase2{bal_2, logTruncationPoint_2} => RslMessage::RslMessageStartingPhase2{bal_2: bal_2@, logTruncationPoint_2: AbstractifyCOperationNumberToOperationNumber(logTruncationPoint_2)},
            }
        }

    }

    
    #[verifier(broadcast_forall)]
    #[verifier(external_body)]
    pub proof fn axiom_cmessage_view()
        ensures forall |p1:CMessage, p2:CMessage| p1@ == p2@ ==> p1 == p2
    {

    }

    #[verifier(broadcast_forall)]
    #[verifier(external_body)]
    pub proof fn axiom_cmessage_key_model()
        ensures #[trigger] obeys_key_model::<CMessage>()
    {
    }


    #[derive(Clone, Eq, Hash, PartialEq)]
    #[verus::trusted]
    pub struct CPacket{
        pub dst: EndPoint,
        pub src: EndPoint,
        pub msg: CMessage,
    }

    impl CPacket{

        pub fn clone_up_to_view(&self) -> (res: CPacket)
        ensures res@ == self@
        {
            CPacket{
                dst: self.dst.clone_up_to_view(),
                src: self.src.clone_up_to_view(),
                msg: self.msg.clone_up_to_view(),
            }
        }
        pub open spec fn abstractable(self) -> bool
        {
            &&& self.dst.abstractable()
            &&& self.src.abstractable()
            &&& self.msg.abstractable()
        }

        pub open spec fn valid(self) -> bool
        {
            &&& self.dst.valid_public_key()
            &&& self.src.valid_public_key()
            &&& self.msg.valid()
        }

        pub open spec fn view(self) -> RslPacket
            recommends self.abstractable()
        {
            LPacket{
                dst: self.dst@,
                src: self.src@,
                msg: self.msg@,
            }
        }
    }

    impl View for CPacket{
        type V = RslPacket;

        open spec fn view(&self) -> RslPacket {
            LPacket{
                dst: self.dst@,
                src: self.src@,
                msg: self.msg@,
            }
        }
    }

    // impl PartialEq for CPacket {
    //     #[verifier(external_body)]
    //     fn eq(&self, other: &Self) -> bool {
    //         self.dst == other.dst
    //          && self.src == other.src
    //          && self.msg == other.msg
    //     }
    // }

    // impl Hash for CPacket {
    //     fn hash<H: Hasher>(&self, state: &mut H) {
    //         self.dst.hash(state);
    //         self.src.hash(state);
    //         self.msg.hash(state);
    //     }
    // }

    #[verifier(broadcast_forall)]
    #[verifier(external_body)]
    pub proof fn axiom_cpacket_view()
        ensures forall |p1:CPacket, p2:CPacket| p1@ == p2@ ==> p1 == p2
    {

    }

    #[verifier(broadcast_forall)]
    #[verifier(external_body)]
    pub proof fn axiom_cpacket_key_model()
        ensures #[trigger] obeys_key_model::<CPacket>()
    {
    }
}

impl Hash for CMessage {
    fn hash<H: Hasher>(&self, state: &mut H) {
        mem::discriminant(self).hash(state);

        match self {
            CMessage::CMessageInvalid {} => {}

            CMessage::CMessageRequest { seqno_req, val } => {
                seqno_req.hash(state);
                val.hash(state);
            }

            CMessage::CMessage1a { bal_1a } => {
                bal_1a.hash(state);
            }

            CMessage::CMessage1b {
                bal_1b,
                log_truncation_point,
                votes,
            } => {
                bal_1b.hash(state);
                log_truncation_point.hash(state);

                // votes: HashMap<COperationNumber, CVote>
                let mut xor_hash: u64 = 0;
                for (k, v) in votes.iter() {
                    let mut h2 = DefaultHasher::new();
                    k.hash(&mut h2);
                    v.hash(&mut h2);
                    xor_hash ^= h2.finish();
                }
                xor_hash.hash(state);
            }

            CMessage::CMessage2a {
                bal_2a,
                opn_2a,
                val_2a,
            } => {
                bal_2a.hash(state);
                opn_2a.hash(state);
                val_2a.hash(state);
            }

            CMessage::CMessage2b {
                bal_2b,
                opn_2b,
                val_2b,
            } => {
                bal_2b.hash(state);
                opn_2b.hash(state);
                val_2b.hash(state);
            }

            CMessage::CMessageHeartbeat {
                bal_heartbeat,
                suspicious,
                opn_ckpt,
            } => {
                bal_heartbeat.hash(state);
                suspicious.hash(state);
                opn_ckpt.hash(state);
            }

            CMessage::CMessageReply {
                seqno_reply,
                reply,
            } => {
                seqno_reply.hash(state);
                reply.hash(state);
            }

            CMessage::CMessageAppStateRequest {
                bal_state_req,
                opn_state_req,
            } => {
                bal_state_req.hash(state);
                opn_state_req.hash(state);
            }

            CMessage::CMessageAppStateSupply {
                bal_state_supply,
                opn_state_supply,
                app_state,
                reply_cache,
            } => {
                bal_state_supply.hash(state);
                opn_state_supply.hash(state);
                app_state.hash(state);

                // reply_cache: HashMap<EndPoint, CReply>
                let mut xor_hash: u64 = 0;
                for (k, v) in reply_cache.iter() {
                    let mut h2 = DefaultHasher::new();
                    k.hash(&mut h2);
                    v.hash(&mut h2);
                    xor_hash ^= h2.finish();
                }
                xor_hash.hash(state);
            }

            CMessage::CMessageStartingPhase2 {
                bal_2,
                logTruncationPoint_2,
            } => {
                bal_2.hash(state);
                logTruncationPoint_2.hash(state);
            }
        }
    }
}

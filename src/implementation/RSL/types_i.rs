// Re-export all types and helpers from the generated module.
pub use crate::generated::RSL::types_gen::*;

// The 4 marshalable basic types must be defined here (not in types_gen.rs)
// because they need define_struct_and_derive_marshalable! macro for Marshalable trait.
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::implementation::common::marshalling::*;
use crate::implementation::RSL::appinterface::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
use vstd::prelude::*;

verus! {

    define_struct_and_derive_marshalable!{
        #[derive(Eq, Clone, Copy, PartialEq, Hash)]
        pub struct CBallot {
            pub seqno : u64,
            pub proposer_id : u64,
        }
    }

    impl CBallot {

        pub fn is_equal(&self, other: &CBallot) -> (result: bool)
            ensures
                result == (self@ == other@)
        {
            self.seqno == other.seqno && self.proposer_id == other.proposer_id
        }

        pub fn clone_up_to_view(&self) -> (res: CBallot)
        ensures res@ == self@
        {
            CBallot {
                seqno: self.seqno,
                proposer_id: self.proposer_id,
            }
        }

        pub open spec fn abstractable(self) -> bool
        {
            self.proposer_id < 0xFFFF_FFFF_FFFF_FFFF
        }

        pub open spec fn valid(self) -> bool
        {
            self.abstractable()
        }

        pub open spec fn view(self) -> Ballot
            recommends self.abstractable()
        {
            Ballot{seqno:self.seqno as int, proposer_id:self.proposer_id as int}
        }
    }

    impl View for CBallot {
        type V = Ballot;
        open spec fn view(&self) -> Ballot {
            Ballot{seqno:self.seqno as int, proposer_id:self.proposer_id as int}
        }
    }

    define_struct_and_derive_marshalable!{
        #[derive(Clone, PartialEq, Eq, Hash)]
        pub struct CRequest {
            pub client : EndPoint,
            pub seqno : u64,
            pub request : CAppMessage,
        }
    }

    impl View for CRequest {
        type V = Request;
        open spec fn view(&self) -> Request
        {
            Request{
                client : self.client@,
                seqno : self.seqno as int,
                request : self.request@,
            }
        }
    }

    impl CRequest {

    #[verifier(external_body)]
        pub fn clone_up_to_view(&self) -> (res: CRequest)
            ensures
            res@ == self@,
            res==self
        {
            CRequest {
                client: self.client.clone_up_to_view(),
                seqno: self.seqno,
                request: self.request.clone_up_to_view()
            }
        }

        pub open spec fn abstractable(self) -> bool {
            &&& self.client.abstractable()
            &&& self.request.abstractable()
        }

        pub open spec fn valid(self) -> bool {
            &&& self.abstractable()
            &&& self.request.valid()
        }
    }

    define_struct_and_derive_marshalable!{
        #[derive(Clone, Eq, PartialEq, Hash)]
        pub struct CReply {
            pub client : EndPoint,
            pub seqno : u64,
            pub reply : CAppMessage,
        }
    }

    impl CReply {

        pub fn clone_up_to_view(&self) -> (res: CReply)
            ensures res@ == self@
        {
            CReply {
                client: self.client.clone_up_to_view(),
                seqno: self.seqno,
                reply: self.reply.clone_up_to_view(),
            }
        }

        pub open spec fn abstractable(self) -> bool {
            &&& self.client.abstractable()
            &&& self.reply.abstractable()
        }

        pub open spec fn valid(self) -> bool {
            &&& self.abstractable()
            &&& self.client.valid_public_key()
            &&& self.reply.valid()
        }
    }

    impl View for CReply{
        type V = Reply;

        open spec fn view(&self) -> Reply
        {
            Reply{
                client : self.client@,
                seqno : self.seqno as int,
                reply : self.reply@,
            }
        }
    }

    define_struct_and_derive_marshalable!{
        #[derive(Clone, Eq, PartialEq, Hash)]
        pub struct CVote {
            pub max_value_bal : CBallot,
            pub max_val : CRequestBatch,
        }
    }

    impl CVote{

        pub fn clone_up_to_view(&self) -> (res: CVote)
        ensures res@ == self@
        {
            CVote {
                max_value_bal: self.max_value_bal.clone_up_to_view(),
                max_val: clone_request_batch_up_to_view(&self.max_val),
            }
        }

        pub open spec fn abstractable(self) -> bool{
            &&& self.max_value_bal.abstractable()
            &&& crequestbatch_is_abstractable(&self.max_val)
        }

        pub open spec fn valid(self) -> bool{
            &&& self.abstractable()
            &&& self.max_value_bal.valid()
            &&& crequestbatch_is_valid(&self.max_val)
        }

        pub open spec fn view(self) -> Vote
            recommends self.abstractable()
        {
            Vote{
                max_value_bal : self.max_value_bal@,
                max_val : abstractify_crequestbatch(&self.max_val),
            }
        }
    }

    impl View for CVote {
        type V = Vote;
        open spec fn view(&self) -> Vote {
            Vote{
                max_value_bal : self.max_value_bal@,
                max_val : abstractify_crequestbatch(&self.max_val),
            }
        }
    }

}

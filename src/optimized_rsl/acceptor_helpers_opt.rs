// Optimized acceptor helpers — P3.1 and P3.2: &mut CVotes API.
// Takes &mut CVotes instead of &CVotes → CVotes, avoiding an extra clone at the
// caller site. Internally delegates to the verified functional implementations.

use std::collections::HashMap;
use vstd::prelude::*;

use crate::common::collections::hashsets::hashmap_keys_to_vec;
use crate::generated::RSL::types_gen::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::acceptor::*;

verus! {
    // P3.2: In-place API for CRemoveVotesBeforeLogTruncationPoint.
    pub exec fn CRemoveVotesBeforeLogTruncationPoint_mut(votes: &mut CVotes, log_truncation_point: &u64)
    requires
        cvotes_is_valid(&*old(votes)),
    ensures
        cvotes_is_valid(votes),
        RemoveVotesBeforeLogTruncationPoint(abstractify_cvotes(&*old(votes)), abstractify_cvotes(votes), *log_truncation_point as int),
    {
        let result = crate::implementation::RSL::acceptor_helpers::CRemoveVotesBeforeLogTruncationPoint(votes, log_truncation_point);
        *votes = result;
    }

    // P3.1: In-place API for CAddVoteAndRemoveOldOnes.
    pub exec fn CAddVoteAndRemoveOldOnes_mut(votes: &mut CVotes, new_opn: &u64, new_vote: &CVote, log_truncation_point: &u64)
    requires
        cvotes_is_valid(&*old(votes)),
        new_vote.valid(),
    ensures
        cvotes_is_valid(votes),
        LAddVoteAndRemoveOldOnes(abstractify_cvotes(&*old(votes)), abstractify_cvotes(votes), *new_opn as int, new_vote@, *log_truncation_point as int),
    {
        let result = crate::implementation::RSL::acceptor_helpers::CAddVoteAndRemoveOldOnes(votes, new_opn, new_vote, log_truncation_point);
        *votes = result;
    }
}

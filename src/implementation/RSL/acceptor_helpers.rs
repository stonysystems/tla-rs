use std::collections::HashMap;
use vstd::prelude::*;

use crate::generated::RSL::types_gen::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::acceptor::*;

verus! {
    // External-body helper for HashMap filtering over votes.
    #[verifier(external_body)]
    pub exec fn CRemoveVotesBeforeLogTruncationPoint(votes: &CVotes, log_truncation_point: &u64) -> (result: CVotes)
    requires
        cvotes_is_valid(votes),
    ensures
        cvotes_is_valid(&result),
        RemoveVotesBeforeLogTruncationPoint(abstractify_cvotes(votes), abstractify_cvotes(&result), *log_truncation_point as int),
    {
        let mut result: HashMap<u64, CVote> = HashMap::new();
        for (key, value) in votes.iter() {
            if *key >= *log_truncation_point {
                result.insert(*key, value.clone());
            }
        }
        result
    }

    // External-body helper for HashMap insert+filter update.
    #[verifier(external_body)]
    pub exec fn CAddVoteAndRemoveOldOnes(votes: &CVotes, new_opn: &u64, new_vote: &CVote, log_truncation_point: &u64) -> (result: CVotes)
    requires
        cvotes_is_valid(votes),
        new_vote.valid(),
    ensures
        cvotes_is_valid(&result),
        LAddVoteAndRemoveOldOnes(abstractify_cvotes(votes), abstractify_cvotes(&result), *new_opn as int, new_vote@, *log_truncation_point as int),
    {
        let mut result: HashMap<u64, CVote> = HashMap::new();
        for (key, value) in votes.iter() {
            if *key >= *log_truncation_point {
                result.insert(*key, value.clone());
            }
        }
        result.insert(*new_opn, new_vote.clone());
        result
    }
}

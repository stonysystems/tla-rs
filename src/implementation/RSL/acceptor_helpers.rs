use std::collections::HashMap;
use vstd::prelude::*;

use crate::common::collections::{count_matches::*, vecs::*};
use crate::generated::RSL::types_gen::*;
use crate::implementation::RSL::cconfiguration::*;
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

    // Log-truncation validity helper logic, re-homed from acceptorimpl.rs.
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

    pub fn CCountLargerInSeq(s:&Vec<u64>, target:u64) -> (res:u64)
        ensures
        ({
            let ss = s@.map(|i, t:u64| t as int);
            && res as int <= s@.len()
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
                proof {
                    lemma_count_matches_le_len(ss.subrange(1, ss.len() as int), |x:int| x > target as int);
                    // temp as int <= rest@.len() == s@.len() - 1, so temp + 1 <= s@.len() <= usize::MAX
                }
                temp + 1
            } else
            {
                temp
            }
        }
    }

    pub fn CCountLargerOrEqualInSeq(s:&Vec<u64>, target:u64) -> (res:u64)
        ensures
        ({
            let ss = s@.map(|i, t:u64| t as int);
            && res as int <= s@.len()
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
                proof {
                    lemma_count_matches_le_len(ss.subrange(1, ss.len() as int), |x:int| x >= target as int);
                }
                temp + 1
            } else
            {
                temp
            }
        }
    }

    pub fn CIsNthHighestValueInSequence(v:u64, s:&Vec<u64>, n:u64) -> (res:bool)
        ensures
        ({
            let ss = s@.map(|i, t:u64| t as int);
            && res == IsNthHighestValueInSequence(v as int, ss, n as int)
        })
    {
        let ghost ss = s@.map(|i, t:u64| t as int);
        let len = s.len();
        let b1 = (0 < n) && (n <= len as u64);
        assert(b1 == (0 < n <= ss.len()));
        let b2 = contains_u64(s, &v);
        assert(b2 == ss.contains(v as int));
        let b3 = CCountLargerInSeq(s, v) < n;
        assert(b3 == (CountMatchesInSeq(ss, |x:int| x > v) < n as int));
        let b4 = CCountLargerOrEqualInSeq(s, v) >= n;
        assert(b4 == (CountMatchesInSeq(ss, |x:int| x >= v) >= n));
        b1 && b2 && b3 && b4
    }
}

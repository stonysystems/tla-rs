use std::collections::HashMap;
use vstd::prelude::*;

use crate::common::collections::{count_matches::*, hashsets::hashmap_keys_to_vec, vecs::*};
use crate::generated::RSL::types_gen::*;
use crate::implementation::RSL::cconfiguration::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::acceptor::*;

verus! {
    // Verified HashMap filtering: keep only entries with key >= log_truncation_point.
    pub exec fn CRemoveVotesBeforeLogTruncationPoint(votes: &CVotes, log_truncation_point: &u64) -> (result: CVotes)
    requires
        cvotes_is_valid(votes),
    ensures
        cvotes_is_valid(&result),
        RemoveVotesBeforeLogTruncationPoint(abstractify_cvotes(votes), abstractify_cvotes(&result), *log_truncation_point as int),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        broadcast use vstd::map::group_map_lemmas;

        let keys = hashmap_keys_to_vec(votes);
        let mut result: HashMap<u64, CVote> = HashMap::new();
        let mut i: usize = 0;
        while i < keys.len()
            invariant
                0 <= i <= keys.len(),
                // Keys in result are from votes and are >= log_truncation_point
                forall |k: u64| result@.contains_key(k) ==> votes@.contains_key(k) && k >= *log_truncation_point,
                // Values in result match votes at view level, and are valid
                forall |k: u64| result@.contains_key(k) ==> (#[trigger] result@[k])@ == votes@[k]@ && result@[k].valid(),
                // All eligible keys from keys[0..i] are in result
                forall |j: int| 0 <= j < i as int && (#[trigger] keys@[j]) >= *log_truncation_point ==> result@.contains_key(keys@[j]),
                // hashmap_keys_to_vec postconditions
                forall |k: int| 0 <= k < keys@.len() ==> votes@.contains_key(#[trigger] keys@[k]),
                forall |k: u64| votes@.contains_key(k) ==> (exists |j: int| 0 <= j < keys@.len() && keys@[j] == k),
                cvotes_is_valid(votes),
            decreases keys.len() - i,
        {
            if keys[i] >= *log_truncation_point {
                proof {
                    lemma_cvotes_valid_key(votes, keys@[i as int]);
                }
                let value = votes.get(&keys[i]).unwrap().clone_up_to_view();
                // value@ == votes@[keys[i]]@ and value.valid() == votes@[keys[i]].valid()
                let _ = result.insert(keys[i], value);
            }
            i = i + 1;
        }
        // Prove cvotes_is_valid(&result)
        proof {
            assert forall |k: u64| #![trigger COperationNumberIsValid(k)] result@.contains_key(k) implies
                COperationNumberIsValid(k) && result@[k].valid() by {
                assert(votes@.contains_key(k));
                lemma_cvotes_valid_key(votes, k);
            };
        }
        // Prove RemoveVotesBeforeLogTruncationPoint
        proof {
            let abs_votes = abstractify_cvotes(votes);
            let abs_result = abstractify_cvotes(&result);
            let ltp = *log_truncation_point as int;

            // Conjunct 1: result entries are from votes with same values
            assert forall |opn: int| #![trigger abs_result[opn]] #![trigger abs_votes[opn]] abs_result.contains_key(opn) implies
                abs_votes.contains_key(opn) && abs_result[opn] == abs_votes[opn] by {
                let k = choose |k: u64| result@.contains_key(k) && k as int == opn;
                assert(votes@.contains_key(k));
                assert(result@[k]@ == votes@[k]@);
            };

            // Conjunct 2: keys below log_truncation_point are not in result
            assert forall |opn: int| opn < ltp implies !abs_result.contains_key(opn) by {
                if abs_result.contains_key(opn) {
                    let k = choose |k: u64| result@.contains_key(k) && k as int == opn;
                    assert(k >= *log_truncation_point);
                    assert(k as int >= ltp);
                }
            };

            // Conjunct 3: eligible keys are preserved
            assert forall |opn: int| opn >= ltp && abs_votes.contains_key(opn)
                implies abs_result.contains_key(opn) by {
                let k = choose |k: u64| votes@.contains_key(k) && k as int == opn;
                assert(k as int >= ltp);
                assert(k >= *log_truncation_point);
                let j = choose |j: int| 0 <= j < keys@.len() && keys@[j] == k;
                assert(result@.contains_key(k));
            };
        }
        result
    }

    // Verified HashMap insert+filter: filter votes keeping key >= log_truncation_point, then insert new entry.
    pub exec fn CAddVoteAndRemoveOldOnes(votes: &CVotes, new_opn: &u64, new_vote: &CVote, log_truncation_point: &u64) -> (result: CVotes)
    requires
        cvotes_is_valid(votes),
        new_vote.valid(),
    ensures
        cvotes_is_valid(&result),
        LAddVoteAndRemoveOldOnes(abstractify_cvotes(votes), abstractify_cvotes(&result), *new_opn as int, new_vote@, *log_truncation_point as int),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        broadcast use vstd::map::group_map_lemmas;

        // Phase 1: Filter votes keeping only keys >= log_truncation_point
        let keys = hashmap_keys_to_vec(votes);
        let mut result: HashMap<u64, CVote> = HashMap::new();
        let mut i: usize = 0;
        while i < keys.len()
            invariant
                0 <= i <= keys.len(),
                forall |k: u64| result@.contains_key(k) ==> votes@.contains_key(k) && k >= *log_truncation_point,
                forall |k: u64| result@.contains_key(k) ==> (#[trigger] result@[k])@ == votes@[k]@ && result@[k].valid(),
                forall |j: int| 0 <= j < i as int && (#[trigger] keys@[j]) >= *log_truncation_point ==> result@.contains_key(keys@[j]),
                forall |k: int| 0 <= k < keys@.len() ==> votes@.contains_key(#[trigger] keys@[k]),
                forall |k: u64| votes@.contains_key(k) ==> (exists |j: int| 0 <= j < keys@.len() && keys@[j] == k),
                cvotes_is_valid(votes),
                new_vote.valid(),
            decreases keys.len() - i,
        {
            if keys[i] >= *log_truncation_point {
                proof {
                    lemma_cvotes_valid_key(votes, keys@[i as int]);
                }
                let value = votes.get(&keys[i]).unwrap().clone_up_to_view();
                let _ = result.insert(keys[i], value);
            }
            i = i + 1;
        }

        // Phase 2: Insert the new vote (only if new_opn >= ltp, matching spec domain)
        let ghost pre_insert = result@;
        if *new_opn >= *log_truncation_point {
            let new_vote_cloned = new_vote.clone_up_to_view();
            let _ = result.insert(*new_opn, new_vote_cloned);
        }

        // Prove cvotes_is_valid(&result)
        proof {
            assert forall |k: u64| #![trigger COperationNumberIsValid(k)] result@.contains_key(k) implies
                COperationNumberIsValid(k) && result@[k].valid() by {
                if k == *new_opn && *new_opn >= *log_truncation_point {
                    // new_vote_cloned.valid() == new_vote.valid() == true
                } else {
                    // k was in pre_insert, which came from votes
                    assert(pre_insert.contains_key(k));
                    assert(votes@.contains_key(k));
                    lemma_cvotes_valid_key(votes, k);
                }
            };
        }

        // Prove LAddVoteAndRemoveOldOnes
        proof {
            let abs_votes = abstractify_cvotes(votes);
            let abs_result = abstractify_cvotes(&result);
            let ltp = *log_truncation_point as int;
            let new_opn_int = *new_opn as int;

            // Conjunct 1a: forward — abs_result.dom ⊆ {opn >= ltp && (in votes || == new_opn)}
            assert forall |opn: int| abs_result.dom().contains(opn) implies
                (opn >= ltp && (abs_votes.dom().contains(opn) || opn == new_opn_int)) by {
                let k = choose |k: u64| result@.contains_key(k) && k as int == opn;
                if k == *new_opn && *new_opn >= *log_truncation_point {
                    // Inserted in phase 2; opn == new_opn_int >= ltp
                    assert(opn >= ltp);
                } else {
                    // k from filter phase (pre_insert)
                    assert(pre_insert.contains_key(k));
                    assert(votes@.contains_key(k));
                    assert(k >= *log_truncation_point);
                }
            };

            // Conjunct 1b: backward — {opn >= ltp && (in votes || == new_opn)} ⊆ abs_result.dom
            assert forall |opn: int| opn >= ltp && (abs_votes.dom().contains(opn) || opn == new_opn_int)
                implies abs_result.dom().contains(opn) by {
                if opn == new_opn_int {
                    // new_opn >= ltp (since opn >= ltp and opn == new_opn_int)
                    assert(*new_opn >= *log_truncation_point);
                    assert(result@.contains_key(*new_opn));
                } else {
                    // opn in abs_votes, so exists concrete key k in votes@
                    let k = choose |k: u64| votes@.contains_key(k) && k as int == opn;
                    assert(k >= *log_truncation_point);
                    let j = choose |j: int| 0 <= j < keys@.len() && keys@[j] == k;
                    assert(pre_insert.contains_key(k));
                    assert(result@.contains_key(k));
                }
            };

            // Combine 1a+1b into the <==> needed by spec
            assert forall |opn: int| abs_result.dom().contains(opn) <==>
                (opn >= ltp && (abs_votes.dom().contains(opn) || opn == new_opn_int)) by {};

            // Conjunct 2: value characterization
            assert forall |opn: int| #![trigger abs_result[opn]] abs_result.dom().contains(opn) implies
                abs_result[opn] == (if opn == new_opn_int { new_vote@ } else { abs_votes[opn] }) by {
                let k = choose |k: u64| result@.contains_key(k) && k as int == opn;
                if opn == new_opn_int {
                    // k as int == new_opn_int, u64->int injective, so k == *new_opn
                    assert(*new_opn >= *log_truncation_point);
                } else {
                    // k != *new_opn, so result@[k] == pre_insert[k]
                    assert(pre_insert.contains_key(k));
                    assert(votes@.contains_key(k));
                }
            };
        }
        result
    }

    // Log-truncation validity helper logic, re-homed from acceptorimpl.rs.
    pub fn CIsLogTruncationPointValid(log_truncation_point: COperationNumber,last_checkpointed_operation:&Vec<COperationNumber>,config:&CConfiguration) -> (isValid: bool)
        requires
            COperationNumberIsValid(log_truncation_point),
            forall |i: int| #![trigger last_checkpointed_operation[i]] 0 <= i < last_checkpointed_operation.len() ==> COperationNumberIsValid(last_checkpointed_operation[i]),
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
            res == IsNthHighestValueInSequence(v as int, ss, n as int)
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

    // In-place (&mut) wrappers for &mut self acceptor methods (Phase 48.6.b).
    // Delegates to verified functional implementations above.

    pub exec fn CRemoveVotesBeforeLogTruncationPoint_mut(votes: &mut CVotes, log_truncation_point: &u64)
    requires
        cvotes_is_valid(&*old(votes)),
    ensures
        cvotes_is_valid(votes),
        RemoveVotesBeforeLogTruncationPoint(abstractify_cvotes(&*old(votes)), abstractify_cvotes(votes), *log_truncation_point as int),
    {
        let result = CRemoveVotesBeforeLogTruncationPoint(votes, log_truncation_point);
        *votes = result;
    }

    pub exec fn CAddVoteAndRemoveOldOnes_mut(votes: &mut CVotes, new_opn: &u64, new_vote: &CVote, log_truncation_point: &u64)
    requires
        cvotes_is_valid(&*old(votes)),
        new_vote.valid(),
    ensures
        cvotes_is_valid(votes),
        LAddVoteAndRemoveOldOnes(abstractify_cvotes(&*old(votes)), abstractify_cvotes(votes), *new_opn as int, new_vote@, *log_truncation_point as int),
    {
        let result = CAddVoteAndRemoveOldOnes(votes, new_opn, new_vote, log_truncation_point);
        *votes = result;
    }
}

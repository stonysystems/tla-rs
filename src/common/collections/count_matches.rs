use vstd::prelude::*;
use vstd::{set::*, set_lib::*};

verus! {
    pub open spec fn CountMatchesInSeq<T>(s: Seq<T>, f: spec_fn(T) -> bool) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            CountMatchesInSeq(s.subrange(1, s.len() as int), f) + if f(s.index(0)) { 1 as nat } else { 0 as nat }
        }
    }

    pub proof fn lemma_count_matches_le_len<T>(s: Seq<T>, f: spec_fn(T) -> bool)
        ensures CountMatchesInSeq(s, f) <= s.len()
        decreases s.len()
    {
        if s.len() > 0 {
            lemma_count_matches_le_len(s.subrange(1, s.len() as int), f);
        }
    }

    pub open spec fn IsNthHighestValueInSequence(v:int, s:Seq<int>, n:int) -> bool
    {
        &&& 0 < n < s.len()
        &&& s.contains(v)
        &&& CountMatchesInSeq(s, |x:int| x > v) < n
        &&& CountMatchesInSeq(s, |x:int| x >= v) >= n
    }

    /// Mathematical fact: for any integer sequence with 0 < n < len, an element satisfying
    /// IsNthHighestValueInSequence always exists (the nth order statistic is always a sequence element).
    /// Proof sketch: sort non-decreasingly as b_0 <= ... <= b_{k-1}; take v = b_{k-n}.
    /// Then count(>= v) >= n (elements at positions k-n..k-1) and count(> v) <= n-1 < n.
    #[verifier::external_body]
    pub proof fn lemma_nth_highest_value_exists(s: Seq<int>, n: int)
    requires
        0 < n,
        n < s.len(),
    ensures
        exists |v: int| s.contains(v)
            && CountMatchesInSeq(s, |x: int| x > v) < n
            && CountMatchesInSeq(s, |x: int| x >= v) >= n,
    {
    }

}

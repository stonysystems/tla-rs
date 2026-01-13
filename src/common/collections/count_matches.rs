use builtin::*;
use builtin_macros::*;
use vstd::seq::*;

use vstd::{set::*, set_lib::*};

verus! {
    // pub open spec fn CountMatchesInSeq<T, F: spec_fn(T) -> bool>(s: Seq<T>, f: F) -> nat
    // {
    //     if s.len() == 0 {
    //         0
    //     } else {
    //         CountMatchesInSeq(s.subrange(1, s.len() as int), f) + if f(s.index(0)) { 1 as nat } else { 0 as nat }
    //     }
    // }

    pub open spec fn CountMatchesInSeq<T>(s: Seq<T>, f: spec_fn(T) -> bool) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            CountMatchesInSeq(s.subrange(1, s.len() as int), f) + if f(s.index(0)) { 1 as nat } else { 0 as nat }
        }
    }

    pub open spec fn IsNthHighestValueInSequence(v:int, s:Seq<int>, n:int) -> bool
    {
        &&& 0 < n < s.len()
        &&& s.contains(v)
        &&& CountMatchesInSeq(s, |x:int| x > v) < n
        &&& CountMatchesInSeq(s, |x:int| x >= v) >= n
    }

}

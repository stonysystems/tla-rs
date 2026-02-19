use std::collections::*;
use vstd::prelude::*;

verus! {
    pub open spec fn FindIndexInSeq<T>(s: Seq<T>, v: T) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            -1
        } else if s[0] == v {
            0
        } else {
            let r = FindIndexInSeq(s.drop_first(), v);
            if r == -1 {
                -1
            } else {
                r + 1
            }
        }
    }



    #[verifier::external_body]
    pub proof fn lemma_FindIndexInSeq<T>(s:Seq<T>, v:T)
        ensures
            ({
                let idx = FindIndexInSeq(s, v);
                &&& if idx >= 0 {idx < s.len() && s[idx] == v} else {!s.contains(v)}
            })
    {

    }

    pub open spec fn ItemAtPositionInSeq<T>(s:Seq<T>, v:T, idx:int) -> bool
    {
        0 <= idx < s.len() && s[idx] == v
    }

}

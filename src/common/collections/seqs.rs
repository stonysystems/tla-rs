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



    pub proof fn lemma_FindIndexInSeq<T>(s:Seq<T>, v:T)
        ensures
            ({
                let idx = FindIndexInSeq(s, v);
                &&& if idx >= 0 {idx < s.len() && s[idx] == v} else {!s.contains(v)}
            })
        decreases s.len()
    {
        if s.len() == 0 {
            // idx = -1; empty seq contains nothing
        } else if s[0] == v {
            // idx = 0; s[0] == v and 0 < s.len()
        } else {
            lemma_FindIndexInSeq(s.drop_first(), v);
            // IH: if FindIndexInSeq(s.drop_first(), v) >= 0 then valid index+value;
            //      otherwise s.drop_first() does not contain v
            let r = FindIndexInSeq(s.drop_first(), v);
            if r >= 0 {
                // IH gives: r < s.drop_first().len() && s.drop_first()[r] == v
                // FindIndexInSeq(s, v) = r + 1
                // Need: r + 1 < s.len() && s[r + 1] == v
                assert(r < s.drop_first().len());
                assert(s.drop_first().len() == s.len() - 1);
                assert(s[r + 1] == s.drop_first()[r]);
            } else {
                // IH gives: !s.drop_first().contains(v)
                // Also s[0] != v, so !s.contains(v)
                // FindIndexInSeq(s, v) = -1 (since r < 0 means r == -1 from spec)
                assert forall |i: int| 0 <= i < s.len() implies s[i] != v by {
                    if i > 0 {
                        assert(s[i] == s.drop_first()[i - 1]);
                    }
                };
            }
        }
    }

    pub open spec fn ItemAtPositionInSeq<T>(s:Seq<T>, v:T, idx:int) -> bool
    {
        0 <= idx < s.len() && s[idx] == v
    }

}

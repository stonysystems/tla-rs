use builtin::*;
use builtin_macros::*;
use vstd::seq::*;
use std::collections::*;


verus! {
    // pub fn FindIndexInSeq<T>(s: Seq<T>, v: T) -> (r:int)    
    //     ensures
    //         if r >= 0 {
    //             r < s.len() && s.index(r) == v
    //         } else {
    //             !s.contains(v)
    //         }
    //     decreases s.len()  
    // {
    //     if s.len() == 0 {
    //         -1
    //     } else if s.index(0) == v {
    //         0
    //     } else {
    //         let r = FindIndexInSeq(s.subrange(1, s.len() as int), v);
    //         if r == -1 {
    //             -1
    //         } else {
    //             r + 1
    //         }
    //     }
    // }


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

    // pub proof fn lemma_subrange_excludes_first_element<T>(s: Seq<T>, v: T)
    //     ensures
    //         s.index(0) != v ==> (s.contains(v) == s.subrange(1, s.len() as int).contains(v))
    // {
    //     if s.len() > 0 {
    //         assert(s.contains(v) <==> (s.index(0) == v) || s.subrange(1, s.len() as int).contains(v));
    //     }
    // }

    // pub proof fn lemma_FindIndexInSeq<T>(s: Seq<T>, v: T)
    //     ensures
    //         if FindIndexInSeq(s, v) >= 0 {
    //             FindIndexInSeq(s, v) < s.len() && s.index(FindIndexInSeq(s, v)) == v
    //         } else {
    //             !s.contains(v)
    //         }
    // {
    //     reveal(FindIndexInSeq);
    //     if s.len() as int == 0 {
    //         assert(!s.contains(v));
    //     } else if s.index(0) == v {
    //         assert(FindIndexInSeq(s, v) == 0);
    //         assert(s.index(0) == v);
    //     } else {
    //         let r = FindIndexInSeq(s.subrange(1, s.len() as int), v);
    
    //         if r == -1 {
    //             // lemma_subrange_excludes_first_element(s, v);
    //             assert(!s.subrange(1, s.len() as int).contains(v));
    //             assert(!s.contains(v));
    //         } else {
    //             assert(0 <= r < s.subrange(1, s.len() as int).len());
    //             assert(s.subrange(1, s.len() as int).index(r) == v);

    //             assert(FindIndexInSeq(s, v) == r + 1);
    //             assert(s.index(FindIndexInSeq(s, v)) == v);
    //         }
    //     }
    // }
}
use vstd::prelude::*;
use vstd::seq::*;

verus! {
    #[verifier::opaque]
    pub open spec fn SeqIsUnique<T>(s: Seq<T>) -> bool {
        forall |i: int, j: int| #![trigger s[i], s[j]]
            0 <= i < s.len() && 0 <= j < s.len() && s[i] == s[j] ==> i == j
    }
}

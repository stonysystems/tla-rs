#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::set_lib::lemma_set_properties;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    pub open spec fn TLe(i:int, j:int) -> bool { i <= j }

    pub open spec fn imaptotal<KT, VT>(m:Map<KT, VT>) -> bool
    {
        forall |k:KT| #![trigger m[k]] m.contains_key(k)
    }
}

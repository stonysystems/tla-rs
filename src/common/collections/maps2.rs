#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::set_lib::group_set_properties;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    pub open spec fn TLe(i:int, j:int) -> bool { i <= j }

    pub open spec fn imaptotal<KT, VT>(m:IMap<KT, VT>) -> bool
    {
        forall |k:KT| #![trigger m[k]] m.contains_key(k)
    }
}

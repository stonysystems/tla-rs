use crate::implementation::common::function::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
// use crate::implementation::common::function::*;
use vstd::prelude::*;
use vstd::slice::*;

use crate::verus_extra::choose_v::*;
use crate::verus_extra::seq_lib_v;
use crate::verus_extra::seq_lib_v::*;

verus! {
    pub trait Comparable: PartialEq + Clone {
        // spec fn eq(&self, other: &Self) -> bool;

        exec fn equals(&self, other: &Self) -> (result: bool)
            ensures
                result == (*self == *other);
    }
}

#![allow(unused_imports)]
use std::net;
use vstd::prelude::*;

use std::collections::*;
use vstd::view::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {

    #[verifier::external_body]
    pub proof fn lemma_SetViewSizeUnchange<CT:vstd::view::View>(s:Set<CT>, ss:Set<CT::V>)
        requires
            forall |x:CT| s.contains(x) ==> ss.contains(x@),
            // forall |x:CT::V| ss.contains(x) ==> exists |y:CT| s.contains(y) &&  x == y@,
        ensures
            ss.len() == s.len()
    {

    }

}

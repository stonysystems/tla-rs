#![verus::trusted]

use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
    pub type AbstractArg = Seq<u8>;
    pub type AbstractArgs = Seq<AbstractArg>;

    pub type Arg = Vec<u8>;
    pub type Args = Vec<Arg>;

    pub fn clone_vec_u8(v: &Vec<u8>) -> (out: Vec<u8>)
    ensures
        out@ == v@
    {
        let mut out: Arg = Vec::with_capacity(v.len());
        let mut i = 0;
        while i < v.len()
            invariant
                i <= v.len(),
                i == out.len(),
                forall |j| #![auto] 0 <= j < i  ==> out@[j] == v@[j],
        {
            out.push(v[i]);
            i = i + 1;
        }
        proof {
            assert_seqs_equal!(out@, v@);
        }
        out
    }


    pub fn clone_arg(arg: &Arg) -> (out: Arg)
    ensures
        out@ == arg@
    {
        clone_vec_u8(arg)
    }

    pub open spec fn abstractify_args(args: Args) -> AbstractArgs
    {
        args@.map(|i, arg: Arg| arg@)
    }

}

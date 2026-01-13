use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq_lib::*;

use crate::common::framework::args_t::*;
use crate::common::native::io_s::*;

verus! {
    pub open spec fn parse_arg_as_end_point(arg: AbstractArg) -> AbstractEndPoint
    {
        AbstractEndPoint{id: arg}
    }

    pub open spec fn unchecked_parse_args(args: AbstractArgs) -> Seq<AbstractEndPoint>
    {
        args.map(|idx, arg: AbstractArg| parse_arg_as_end_point(arg))
    }

    pub open spec(checked) fn parse_args(args: AbstractArgs) -> Option<Seq<AbstractEndPoint>>
    {
        let end_points = unchecked_parse_args(args);
        if forall |i| #![auto] 0 <= i < end_points.len() ==> end_points[i].valid_physical_address() {
            Some(end_points)
        } else {
            None
        }
    }


    pub fn parse_end_point(arg: &Arg) -> (out: EndPoint)
    ensures
        out@ == parse_arg_as_end_point(arg@),
    {
        EndPoint{id: clone_arg(arg)}
    }


    pub fn parse_end_points(args: &Args) -> (out: Option<Vec<EndPoint>>)
    ensures
        match out {
            None => parse_args(abstractify_args(*args)) is None,
            Some(vec) => {
                &&& parse_args(abstractify_args(*args)) is Some
                &&& abstractify_end_points(vec) == parse_args(abstractify_args(*args)).unwrap()
                &&& forall |i: int| #![auto] 0 <= i < vec.len() ==> vec[i]@.valid_physical_address()
            },
        }
    {
        let mut end_points: Vec<EndPoint> = Vec::new();
        let mut i: usize = 0;

        while i<args.len()
        invariant
            i <= args.len(),
            end_points.len() == i,
            forall |j| #![auto] 0 <= j < i ==> parse_arg_as_end_point(abstractify_args(*args)[j]) == end_points@[j]@,
            forall |j| #![auto] 0 <= j < i ==> end_points@[j]@.valid_physical_address(),
        {
            let end_point = parse_end_point(&(*args)[i]);
            if !end_point.valid_physical_address() {
                assert(!unchecked_parse_args(abstractify_args(*args))[i as int].valid_physical_address()); // witness to !forall
                return None;
            }
            end_points.push(end_point);
            i = i + 1;
        }

        proof {
            assert_seqs_equal!(abstractify_end_points(end_points), unchecked_parse_args(abstractify_args(*args)));
        }
        Some(end_points)
    }
}

#![allow(unused_imports)]
use crate::common::collections::seq_is_unique_v::{get_host_index, seq_is_unique, test_unique};
use crate::common::framework::args_t::*;
use crate::common::logic::*;
use crate::common::native::io_s::*;
use crate::implementation::common::cmd_line_parser_i::*;
use crate::protocol::lock::node::{AbstractNode, NodeInit, NodeNext};
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

use super::host_i::HostState;
use super::node_i::Node;

verus! {
    pub fn parse_cmd_line(me: &EndPoint, args: &Args) -> (rc: (Option<(Vec<EndPoint>, usize)>))
        ensures ({
            let abstract_end_points = parse_args(abstractify_args(*args));
            &&& match rc {
                None => {
                    ||| abstract_end_points.is_None()
                    ||| abstract_end_points.unwrap().len()==0
                    ||| !seq_is_unique(abstract_end_points.unwrap())
                    ||| abstract_end_points.unwrap().len() > 0 && !abstract_end_points.unwrap().contains(me@)
                },
                Some(c) => {
                    let (end_points, my_index) = c;
                    let abstract_ret_endpoints = abstractify_end_points(end_points);

                    &&& abstract_ret_endpoints =~= abstract_end_points.unwrap()
                    &&& abstract_end_points.is_some()
                    &&& abstract_end_points.unwrap().len() > 0
                    &&& seq_is_unique(abstract_end_points.unwrap())
                    &&& abstract_end_points.unwrap().contains(me@)
                    &&& abstract_end_points.unwrap()[my_index as int] == me@
                    &&& 0 <= my_index < abstract_end_points.unwrap().len()
                    &&&  (forall |i: int| #![auto] 0 <= i < end_points.len() ==> end_points[i]@.valid_physical_address())
                },
            }
            // &&& rc is Some ==> parse_args(abstractify_args(*args)).is_some()
        })
    {
        let end_points = parse_end_points(args);
        if matches!(end_points, None) {
            return None;
        }

        let abstract_end_points:Ghost<Option<Seq<AbstractEndPoint>>> = Ghost(parse_args(abstractify_args(*args)));
        assert(abstract_end_points@.is_some());
        let end_points:Vec<EndPoint> = end_points.unwrap();
        if end_points.len()==0 { return None; }
        let unique = test_unique(&end_points);
        if !unique {
            return None;
        }

        let (present, my_index) = get_host_index(&end_points, me);
        if !present {
            assert(!abstractify_end_points(end_points).contains(me@));
            return None;
        }
        proof {
            assert(abstractify_end_points(end_points).contains(me@));
            assert(abstractify_end_points(end_points)[my_index as int] == me@);
        }
        return Some((end_points, my_index));
    }
}

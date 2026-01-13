use builtin::*;
use builtin_macros::*;
use crate::implementation::common::function::*;
use vstd::prelude::*;
use crate::common::collections::seq_is_unique_v::{get_host_index, seq_is_unique, test_unique};
use crate::common::framework::args_t::*;
use crate::common::logic::*;
use crate::common::native::io_s::*;
use crate::implementation::common::cmd_line_parser_i::*;
use crate::implementation::RSL::{
    cconfiguration::*,
    replicaimpl_class::*, 
    cmessage::*, cbroadcast::*, 
    replicaimpl_delivery::*, 
    netrsl_i::*, 
    ReplicaImpl::*,
    replicaimpl_read_clock::*,
    replicaimpl_process_packet_no_clock::*,
    replicaimpl_process_packet_x::*,
    replicaimpl_no_receive_clock::*,
    replicaimpl_no_receive_no_clock::*,
    replicaimpl_main::*,
};

verus!{
    #[verifier(external_body)]
    pub fn parse_cmd_line(me: &EndPoint, args: &Args) -> (rc: (Option<(CConfiguration, usize)>))
    {
        let end_points = parse_end_points(args);
        if matches!(end_points, None) {
            println!("parse endpoint fail2");
            return None;
        }

        // let abstract_end_points:Ghost<Option<Seq<AbstractEndPoint>>> = Ghost(parse_args(abstractify_args(*args)));
        // assert(abstract_end_points@.is_some());
        let end_points:Vec<EndPoint> = end_points.unwrap();
        if end_points.len()==0 { return None; }
        let unique = test_unique(&end_points);
        if !unique {
            println!("endpoint id duplicate");
            return None;
        }

        let config = CConfiguration{replica_ids:end_points};

        let (present, my_index) = config.CGetReplicaIndex(me);
        if !present {
            println!("me = {:?}", me);
            println!("cannot find myself");
            // assert(!abstractify_end_points(end_points).contains(me@));
            return None;
        }
        // proof {
        //     assert(abstractify_end_points(end_points).contains(me@));
        //     assert(abstractify_end_points(end_points)[my_index as int] == me@);
        // }
        return Some((config, my_index));
    }
}
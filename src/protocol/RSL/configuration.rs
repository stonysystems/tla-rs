use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::types::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::common::collections::seqs::*;

verus! {
    pub struct LConfiguration {
        pub clientIds:Set<AbstractEndPoint>,
        pub replica_ids:Seq<AbstractEndPoint>,
    }

    pub open spec fn LMinQuorumSize(c:LConfiguration) -> int
    {
        (c.replica_ids.len() as int)/2+1
    }

    pub open spec fn ReplicasDistinct(replica_ids:Seq<AbstractEndPoint>, i:int, j:int) -> bool
    {
        0 <= i < replica_ids.len() && 0 <= j < replica_ids.len() && replica_ids[i] == replica_ids[j] ==> i == j
    }

    pub open spec fn ReplicasIsUnique(replica_ids:Seq<AbstractEndPoint>) -> bool
    {
        forall |i:int, j:int| 0 <= i < replica_ids.len() && 0 <= j < replica_ids.len() && replica_ids[i] == replica_ids[j] ==> i == j
    }

    pub open spec fn WellFormedLConfiguration(c:LConfiguration) -> bool
    {
      &&& 0 < c.replica_ids.len()
      &&& (forall |i:int, j:int| ReplicasDistinct(c.replica_ids, i, j))
      &&& ReplicasIsUnique(c.replica_ids)
    }

    pub open spec fn IsReplicaIndex(idx:int, id:AbstractEndPoint, c:LConfiguration) -> bool
    {
        &&& 0 <= idx < c.replica_ids.len()
        &&& c.replica_ids[idx] == id
    }

    pub open spec fn GetReplicaIndex(id:AbstractEndPoint, c:LConfiguration) -> (idx:int)
        recommends
            c.replica_ids.contains(id)
        // ensures 
        //     // let idx = GetReplicaIndex(id, c);
        //     IsReplicaIndex(idx, id, c)
    {
        FindIndexInSeq(c.replica_ids, id)
    }
}
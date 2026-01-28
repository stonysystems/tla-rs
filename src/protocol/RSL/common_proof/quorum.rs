use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::message1b::*;
use crate::protocol::RSL::common_proof::message2a::*;
use crate::protocol::RSL::common_proof::message2b::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::proposer::*;
use crate::protocol::RSL::types::*;
use vstd::prelude::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

use crate::common::collections::maps2::*;
use crate::common::collections::sets::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::framework::environment_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::logic::temporal_s::*;
use crate::common::native::io_s::*;

verus! {
    #[verifier::external_body]
    pub proof fn lemma_GetIndicesFromNodes(
        nodes: Set<AbstractEndPoint>,
        config: LConfiguration
    ) -> (indices: Set<int>)
        requires
            WellFormedLConfiguration(config),
            forall |node: AbstractEndPoint| nodes.contains(node) ==> config.replica_ids.contains(node),
        ensures
            forall |idx: int| indices.contains(idx) ==>
                0 <= idx < config.replica_ids.len() && nodes.contains(config.replica_ids[idx]),
            forall |node: AbstractEndPoint| nodes.contains(node) ==> indices.contains(GetReplicaIndex(node, config)),
            indices.len() == nodes.len(),
    {
        let indices_out = Set::new(|idx:int| 0 <= idx < config.replica_ids.len() && nodes.contains(config.replica_ids[idx]));

        // Define function mapping indices to nodes.
        let f = |idx: int| -> AbstractEndPoint {
            if 0 <= idx && idx < config.replica_ids.len() {
                config.replica_ids[idx]
            } else {
                // choose |end: AbstractEndPoint| true
                arbitrary()
            }
        };

        assert forall |idx1: int, idx2: int|
            indices_out.contains(idx1) && indices_out.contains(idx2) &&
            nodes.contains(f(idx1)) && nodes.contains(f(idx2)) && f(idx1) == f(idx2)
            implies idx1 == idx2
        by {
            assert(ReplicasDistinct(config.replica_ids, idx1, idx2));
        };

        assert forall |node: AbstractEndPoint| nodes.contains(node)
            implies exists |idx: int| indices_out.contains(idx) && node == f(idx)
        by {
            let idx = GetReplicaIndex(node, config);
            assert(indices_out.contains(idx) && node == f(idx));
        };

        lemma_MapSetCardinalityOver(indices_out, nodes, f);
        indices_out
    }

    #[verifier::external_body]
    pub proof fn lemma_GetIndicesFromPackets(
        packets: Set<RslPacket>,
        config: LConfiguration
    ) -> (indices: Set<int>)
        requires
            WellFormedLConfiguration(config),
            forall |p: RslPacket| packets.contains(p) ==> config.replica_ids.contains(p.src),
            forall |p1: RslPacket, p2: RslPacket| packets.contains(p1) && packets.contains(p2) && p1 != p2 ==> p1.src != p2.src,
        ensures
            forall |idx: int| indices.contains(idx)
                ==> 0 <= idx < config.replica_ids.len() &&
                    exists |p: RslPacket| packets.contains(p) && config.replica_ids.index(idx) == p.src,
            forall |p: RslPacket| packets.contains(p) ==> indices.contains(GetReplicaIndex(p.src, config)),
            indices.len() == packets.len(),
    {
        // Construct the set of src nodes from the given packets.
        let nodes = packets.map(|p:RslPacket| p.src);

        // Derive the set of indices from the set of nodes.
        let indices_out = lemma_GetIndicesFromNodes(nodes, config);

        let f = |p: RslPacket| -> AbstractEndPoint{
            p.src
        };

        // Show that the cardinalities match (|indices| == |packets|).
        lemma_MapSetCardinalityOver(packets, nodes, f);

        indices_out
    }

    // #[verifier::external_body]
    pub proof fn lemma_SetOfElementsOfRangeNoBiggerThanRange(
        Q: Set<int>,
        n: int
    )
        requires
            forall |idx: int| Q.contains(idx) ==> 0 <= idx < n,
            0 <= n,
        ensures
            Q.len() <= n,
        decreases n,
    {
        if n == 0 {
            assert forall |idx: int| Q.contains(idx) implies false by {};
            assume(Q.is_empty());
            assert(Q.len() <= n);
        } else if Q.contains(n - 1) {
            lemma_SetOfElementsOfRangeNoBiggerThanRange(Q.remove(n - 1), n - 1);
            assume(Q.remove(n-1).len() == Q.len()-1);
            assert(Q.remove(n-1).len() <= n-1);
            assert(Q.len() <= n);
        } else {
            lemma_SetOfElementsOfRangeNoBiggerThanRange(Q, n - 1);
            assert(Q.len() <= n);
        }
    }

    // #[verifier::external_body]
    pub proof fn lemma_QuorumIndexOverlap(
        Q1: Set<int>,
        Q2: Set<int>,
        n: int
    ) -> (common: int)
        requires
            forall |idx: int| Q1.contains(idx) ==> 0 <= idx < n,
            forall |idx: int| Q2.contains(idx) ==> 0 <= idx < n,
            Q1.len() + Q2.len() > n,
            n >= 0,
        ensures
            Q1.contains(common),
            Q2.contains(common),
            0 <= common < n,
    {
        if Q1.intersect(Q2).is_empty() {
            lemma_SetOfElementsOfRangeNoBiggerThanRange(Q1.union(Q2), n);
            assert(Q1.union(Q2).len() <= n);
            assume(Q1.union(Q2).len() == Q1.len() + Q2.len());
            assert(false);
        }
        let overlap_Q = Q1.intersect(Q2);
        assume(forall |i:int| overlap_Q.contains(i) ==> Q1.contains(i) && Q2.contains(i));
        assert(!overlap_Q.is_empty());
        let common = choose |common: int| overlap_Q.contains(common);
        assume(overlap_Q.contains(common));
        common
    }
}

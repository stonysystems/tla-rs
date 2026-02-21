use crate::common::collections::seq_is_unique_v::*;
use crate::common::collections::seqs::*;
use crate::common::native::io_s::{AbstractEndPoint, EndPoint};
use crate::protocol::RSL::configuration::*;
use vstd::prelude::*;

// Type definitions are now in types_gen.rs.
// This module keeps quorum/index helpers outside generated manual_code injection.
pub use crate::generated::RSL::types_gen::{CConfiguration, ReplicaIndexValid};

verus! {
impl CConfiguration {
    pub fn CMinQuorumSize(&self) -> (q:usize)
        requires
            self.valid()
        ensures
            q as int == LMinQuorumSize(self@)
    {
        self.replica_ids.len()/2 + 1
    }

    pub fn CGetReplicaIndex( &self, id:&EndPoint) -> (rc:(bool, usize))
        requires
            self.valid(),
            id.valid_public_key(),
        ensures
            ({
                let found = rc.0;
                let index = rc.1;
                &&& found ==> self.CIsReplicaIndex(index, *id)
                &&& found ==> GetReplicaIndex(id@, self@) == index as int /* refinement */
                &&& !found ==> !(self.replica_ids@.contains(*id))
                &&& !found ==> !(self@.replica_ids.contains(id@))
            })
    {
        let mut i = 0;
        assert(self.valid());

        while i < self.replica_ids.len()
            invariant
                i < self.replica_ids.len(),
                forall |j:int| 0 <= j < i ==> self.replica_ids[j] != id,
                self.valid()
            decreases self.replica_ids.len() - i,
        {
            if do_end_points_match(&id, &self.replica_ids[i]) {
                let found = true;
                let idx = i;

                assert(id@ == self.replica_ids[i as int]@);

                let ghost sid = id@;
                let ghost sreplicas = self@.replica_ids;
                assert(sid == sreplicas[i as int]);
                assert(0 <= idx < sreplicas.len());
                assert(sreplicas[idx as int] == sid);
                assert(ItemAtPositionInSeq(sreplicas, sid, idx as int));
                assert(self.valid());
                assert(self.abstractable());
                assert(seq_is_unique(self.replica_ids@));

                assert(self.replica_ids[i as int] == id);
                assert(forall |j:int| 0 <= j < self.replica_ids.len() && j != i as int ==> self.replica_ids[j] != id);

                proof {
                    lemma_AbstractifyEndpoints_properties(self.replica_ids);
                }

                assert(seq_is_unique(sreplicas));
                assert(sreplicas[i as int] == sid);
                assert(forall |j:int| 0 <= j < sreplicas.len() && j != i as int ==> sreplicas[j] != sid);

                proof {
                    lemma_FindIndexInSeq(sreplicas, sid);
                }
                assert(idx >= 0 && sreplicas[idx as int] == sid);
                assert(FindIndexInSeq(sreplicas, sid) == idx as int);
                return (found, idx);
            }

            if i == self.replica_ids.len() - 1 {
                let found = false;
                let idx = 0;
                assert(!self.replica_ids@.contains(*id));
                proof {
                    lemma_AbstractifyEndpoints_properties(self.replica_ids);
                }
                return (found, idx);
            }
            i = i + 1;
        }

        (false, 0)
    }
}

#[verifier::external_body]
pub proof fn lemma_AbstractifyEndpoints_properties(s:Vec<EndPoint>)
    requires
        seq_is_unique(s@),
        (forall |i:int| 0 <= i < s.len() ==> s[i].abstractable()),
    ensures
        ({
            let ss = s@.map(|i, e:EndPoint| e@);
            &&& s.len() ==  ss.len()
            &&& (forall |i:int| 0 <= i < s.len() ==> ss[i] == s[i]@)
            &&& (forall |i:AbstractEndPoint| ss.contains(i) ==> exists |x:int| 0 <= x < s.len() && i == s[x]@)
            &&& (forall |i:EndPoint| ss.contains(i@) ==> exists |x:int| 0 <= x < s.len() && i == s[x])
            &&& seq_is_unique(ss) /* this one cannot be verified */
        })
{
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
}

#[verifier::external_body]
pub proof fn lemma_AbstractifyEndPointToNodeIdentity_injective(x:EndPoint, y:EndPoint)
    requires
        x@ == y@
    ensures
        x == y
{

}

pub proof fn lemma_AbstractifyEndPointToNodeIdentity_injective_forall()
    ensures forall |e1:EndPoint, e2:EndPoint| #![trigger e1@, e2@] e1@ == e2@ ==> e1 == e2
{
    assert forall |e1:EndPoint, e2:EndPoint| #![trigger e1@, e2@] e1@ == e2@ implies e1 == e2 by
    {
        lemma_AbstractifyEndPointToNodeIdentity_injective(e1, e2);
    }
}

pub fn CFindIndexInSeq(s:Vec<EndPoint>, v:EndPoint, start:usize) -> (rc:(bool, usize))
    requires s.len() < 0xffff_ffff_ffff_ffff
    decreases s.len() - start,
{
    if start >= s.len() {
        (false, 0)
    } else if do_end_points_match(&v, &s[start]) {
        (true, start)
    } else {
        CFindIndexInSeq(s, v, start+1)
    }
}
}

use crate::common::collections::seq_is_unique_v::*;
use crate::common::collections::seqs::*;
use crate::common::native::io_s::{AbstractEndPoint, EndPoint};
use crate::protocol::RSL::configuration::*;
use vstd::prelude::*;

verus! {
#[derive(Clone)]
pub struct CConfiguration {
    pub replica_ids: Vec<EndPoint>,
}

impl CConfiguration {
    pub fn clone_up_to_view(&self) -> (res:CConfiguration)
    ensures
        self@ == res@,
        res.valid() == self.valid(),
        self.replica_ids.len() == res.replica_ids.len(),
    {
        let mut newVec:Vec<EndPoint> = Vec::new();
        let mut i = 0;
        let len = self.replica_ids.len();
        while i < len
            invariant
                0 <= i <= len,
                len == self.replica_ids.len(),
                newVec.len() == i,
                newVec@ =~= self.replica_ids@.take(i as int),
                forall |j: int| 0 <= j < i ==> newVec@[j] == self.replica_ids@[j],
            decreases len - i,
        {
            let ep = self.replica_ids[i].clone_up_to_view();
            proof {
                broadcast use crate::common::native::io_s::axiom_endpoint_view;
            }
            // ep@ == self.replica_ids[i]@ from clone_up_to_view
            // axiom_endpoint_view: ep@ == self.replica_ids[i]@ ==> ep == self.replica_ids[i]
            assert(ep == self.replica_ids[i as int]);
            newVec.push(ep);
            i += 1;
            assert(newVec@ =~= self.replica_ids@.take(i as int));
        }
        assert(newVec@ =~= self.replica_ids@);
        CConfiguration {
            replica_ids: newVec,
        }
    }

    pub open spec fn abstractable(self) -> bool
    {
        &&& (forall |i:int| 0 <= i < self.replica_ids.len() ==> self.replica_ids[i].abstractable())
        &&& seq_is_unique(self.replica_ids@)
    }

    pub open spec fn valid(self) -> bool
    {
        &&& self.abstractable()
        &&& (forall |i:int| 0 <= i < self.replica_ids.len() ==> self.replica_ids[i].abstractable() && self.replica_ids[i].valid_public_key())
        &&& (0 < self.replica_ids.len() < 0xffff_ffff_ffff_ffff)
    }

    pub open spec fn view(self) -> LConfiguration
    {
        LConfiguration{
            clientIds: Set::<AbstractEndPoint>::empty(),
            replica_ids: self.replica_ids@.map(|i, e:EndPoint| e@)
        }
    }

    pub open spec fn CReplicaDistinct(&self, i:int, j:int) -> bool
    {
        &&& 0 <= i < self.replica_ids.len()
        &&& 0 <= j < self.replica_ids.len()
        &&& self.replica_ids[i] == self.replica_ids[j] ==> i == j
    }

    pub open spec fn CReplicasIsUnique(&self) -> bool
    {
        forall |i:int, j:int| 0 <= i < self.replica_ids.len() && 0 <= j < self.replica_ids.len() && self.replica_ids[i] == self.replica_ids[j] ==> i == j
    }

    pub open spec fn CWellFormedCConfiguration(&self) -> bool
    {
        &&& 0 < self.replica_ids.len()
        &&& (forall |i:int, j:int| self.CReplicaDistinct(i, j))
        &&& self.CReplicasIsUnique()
    }

    pub open spec fn CIsReplicaIndex(&self, idx:usize, id:EndPoint) -> bool
    {
        &&& 0 <= idx < self.replica_ids.len()
        &&& self.replica_ids[idx as int] == id
    }

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

impl View for CConfiguration {
    type V = LConfiguration;

    open spec fn view(&self) -> LConfiguration {
        LConfiguration {
            clientIds: Set::<AbstractEndPoint>::empty(),
            replica_ids: self.replica_ids@.map(|i, e:EndPoint| e@),
        }
    }
}

pub open spec fn ReplicaIndexValid(index:u64, config:CConfiguration) -> bool
{
    0 <= index < config.replica_ids.len()
}

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
            &&& seq_is_unique(ss)
        })
{
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    let ss = s@.map(|i, e:EndPoint| e@);

    // seq_is_unique(ss): if ss[i] == ss[j] then s@[i]@ == s@[j]@,
    // by endpoint injectivity s@[i] == s@[j], by seq_is_unique(s@) i == j.
    assert forall |i: int, j: int|
        #![trigger ss[i], ss[j]]
        0 <= i < ss.len() && 0 <= j < ss.len() && ss[i] == ss[j] implies i == j
    by {
        // ss[i] == s@[i]@ and ss[j] == s@[j]@ (by Seq::map)
        assert(ss[i] == s@[i]@);
        assert(ss[j] == s@[j]@);
        // s@[i]@ == s@[j]@ implies s@[i] == s@[j] by endpoint injectivity
        // seq_is_unique(s@) with s@[i] == s@[j] gives i == j
    };
}

pub proof fn lemma_AbstractifyEndPointToNodeIdentity_injective(x:EndPoint, y:EndPoint)
    requires
        x@ == y@
    ensures
        x == y
{
    broadcast use crate::common::native::io_s::axiom_endpoint_view;
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

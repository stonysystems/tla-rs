//! A returned proposal snapshot can omit the later agreeing process whose flag
//! appears in the returned check snapshot. Figure 5 then indexes a null entry.
//! This theorem identifies that missing definition; it does not invent the
//! implementation's behavior when it encounters null.
use vstd::prelude::*;
use super::consensus as p;
verus! {
pub proof fn mixed_lookup_can_be_missing()
    ensures exists|h:p::History,c:p::Config|
        p::config_ok(c) && p::defined_execution(h,c)
        && p::decision(h,0,2,1) && p::saw_agree(h,0,0) && p::saw_disagree(h,0,0)
        && p::sees(h,(1int,0int,0int),2) && p::agrees(h,0,2)
        && !p::sees(h,(0int,0int,0int),2),
{
    let c=p::Config {processes:set![0int,1int,2int],witnesses:set![0int,1int,2int],
        quorums:set![set![0int,1int],set![0int,2int]]};
    let a=(0int,0int,0int);let u=(0int,0int,1int);let b=(0int,0int,2int);
    let ac=(1int,0int,0int);let bc=(1int,0int,2int);
    let q=set![0int,1int];let r=set![0int,2int];
    let h=p::History {
        inputs:Map::empty().insert(0int,1int).insert(1int,2int).insert(2int,1int),
        values:Map::empty().insert(a,1int).insert(u,2int).insert(b,1int).insert(ac,0int).insert(bc,1int),
        starts:Map::empty().insert(a,2int).insert(u,0int).insert(b,8int).insert(ac,6int).insert(bc,12int),
        processed:Map::empty().insert((1int,u),1int).insert((0int,a),3int).insert((1int,a),4int)
            .insert((1int,ac),7int).insert((0int,ac),16int).insert((0int,b),9int).insert((2int,b),10int)
            .insert((0int,bc),13int).insert((2int,bc),14int),
        quorums:Map::empty().insert(a,q).insert(ac,q).insert(b,r).insert(bc,r),
        finishes:Map::empty().insert(a,5int).insert(ac,17int).insert(b,11int).insert(bc,15int),
    };
    assert(c.processes.contains(0)); assert(c.processes!=Set::<int>::empty());
    assert forall|x:Set<int>| c.quorums.contains(x) implies x.subset_of(c.witnesses) && x!=Set::<int>::empty() by {
        assert(x.contains(0));
    }
    assert forall|x:Set<int>,y:Set<int>| c.quorums.contains(x) && c.quorums.contains(y)
        implies exists|w:int| x.contains(w) && y.contains(w) by { assert(x.contains(0) && y.contains(0)); }
    assert(p::config_ok(c));
    assert(p::sees(h,a,1)) by {
        assert(h.quorums[a].contains(1)); assert(h.processed[(1int,u)]<=h.processed[(1int,a)]);
    }
    assert(!p::uniform(h,0,0));
    assert forall|n:int| p::sees(h,b,n) implies n==0 || n==2 by {
        let w=choose|w:int| h.quorums[b].contains(w) && h.processed.dom().contains((w,(0int,0int,n)))
            && h.processed[(w,(0int,0int,n))]<=h.processed[(w,b)];
        assert(w==0 || w==2);
    }
    assert(p::uniform(h,0,2));
    assert(p::defined_execution(h,c));
    assert(p::sees(h,ac,2)) by { assert(h.quorums[ac].contains(0)); assert(h.processed[(0int,bc)]<=h.processed[(0int,ac)]); }
    assert(p::sees(h,ac,0)) by { assert(h.quorums[ac].contains(0)); }
    assert(p::issued(h,bc) && h.values[bc]==1);
    assert(p::agrees(h,0,2));
    assert(p::sees(h,ac,2) && p::agrees(h,0,2));
    assert(p::saw_agree(h,0,0));
    assert(p::sees(h,ac,0) && h.values[ac]==0);
    assert(p::saw_disagree(h,0,0));
    assert(!p::sees(h,a,2)) by {
        assert forall|w:int| h.quorums[a].contains(w) && h.processed.dom().contains((w,b))
            implies h.processed[(w,b)]>h.processed[(w,a)] by { assert(w==0); }
    }
    assert forall|n:int| p::sees(h,bc,n) implies n==2 by {
        let w=choose|w:int| h.quorums[bc].contains(w) && h.processed.dom().contains((w,(1int,0int,n)))
            && h.processed[(w,(1int,0int,n))]<=h.processed[(w,bc)];
        assert(w==0 || w==2);
    }
    assert(!p::saw_disagree(h,0,2));
    assert(p::decision(h,0,2,1));
}
} // verus!

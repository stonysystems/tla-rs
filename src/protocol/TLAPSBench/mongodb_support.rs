//! Active snapshot flags coincide with the shard's finite active-transaction set.
use vstd::prelude::*;
use super::mongodb::*;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn shard(s: LState,c: Constants,i: int) -> bool {
    s.shards[i].txns.dom() == c.txns && s.shards[i].active.to_iset().subset_of(c.txns)
    && forall |t: int| c.txns.contains(t) ==> (#[trigger] s.shards[i].active.contains(t) <==> s.shards[i].txns[t].snapshot.active)
}
pub open spec fn shape(s: LState,c: Constants) -> bool {
    valid_catalog(c,s.catalog) && s.routers.dom() == c.routers && s.shards.dom() == c.shards && s.ops.dom() == c.txns
    && (forall |r: int| c.routers.contains(r) ==> (#[trigger] s.routers[r]).dom() == c.txns)
    && forall |i: int| c.shards.contains(i) ==> #[trigger] shard(s,c,i)
}
pub proof fn initial_shape(c: Constants,catalog: IMap<int,int>)
    requires valid_catalog(c,catalog)
    ensures shape(initial(c,catalog),c)
{
    let s=initial(c,catalog); assert(s.routers.dom() =~= c.routers); assert(s.shards.dom() =~= c.shards); assert(s.ops.dom() =~= c.txns);
    assert forall |r: int| c.routers.contains(r) implies (#[trigger] s.routers[r]).dom() == c.txns by { assert(s.routers[r].dom() =~= c.txns); }
    assert forall |i: int| c.shards.contains(i) implies #[trigger] shard(s,c,i) by { assert(s.shards[i].txns.dom() =~= c.txns); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires shape(s,c),enabled(s,c,a)
    ensures shape(apply(s,c,a),c)
{
    reveal(enabled); reveal(apply); let u=apply(s,c,a);
    assert(u.catalog == s.catalog); assert(u.routers.dom() =~= c.routers); assert(u.shards.dom() =~= c.shards); assert(u.ops.dom() =~= c.txns);
    assert forall |r: int| c.routers.contains(r) implies (#[trigger] u.routers[r]).dom() == c.txns by {
        assert(s.routers[r].dom() == c.txns); assert(u.routers[r].dom() =~= c.txns);
    }
    assert forall |i: int| c.shards.contains(i) implies #[trigger] shard(u,c,i) by {
        assert(shard(s,c,i)); assert(u.shards[i].txns.dom() =~= c.txns);
        assert(u.shards[i].active.to_iset().subset_of(c.txns));
        assert forall |t: int| c.txns.contains(t) implies (#[trigger] u.shards[i].active.contains(t) <==> u.shards[i].txns[t].snapshot.active) by {
            assert(s.shards[i].active.contains(t) <==> s.shards[i].txns[t].snapshot.active);
        }
    }
}
pub open spec fn safety_spec(b: Behavior<LState>,c: Constants) -> bool {
    valid_constants(c) && valid_catalog(c,b[0].catalog) && b[0] == initial(c,b[0].catalog)
    && (forall |time: int| time >= 0 ==> b.dom().contains(time))
    && forall |time: int| time >= 0 ==> #[trigger] next(b[time],b[time+1],c)
}
pub proof fn step(b: Behavior<LState>,c: Constants,time: int) -> (a: Action)
    requires safety_spec(b,c),time >= 0
    ensures enabled(b[time],c,a),b[time+1] == apply(b[time],c,a)
{
    assert(next(b[time],b[time+1],c)); reveal(next); choose |a: Action| #[trigger] enabled(b[time],c,a) && b[time+1] == apply(b[time],c,a)
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires safety_spec(b,c),time >= 0
    ensures shape(b[time],c),b[time].catalog == b[0].catalog
    decreases time
{
    if time == 0 { initial_shape(c,b[0].catalog); }
    else { at(b,c,time-1); let a=step(b,c,time-1); preserve(b[time-1],c,a); reveal(apply); }
}
} // verus!

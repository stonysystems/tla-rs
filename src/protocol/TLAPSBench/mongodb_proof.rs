//! Initial SI and action witnesses. Snapshot-isolation preservation remains open.
use vstd::prelude::*;
use super::mongodb::*;
verus! {
pub proof fn initial_snapshot_isolation(c: Constants,catalog: IMap<int,int>)
    requires valid_constants(c),valid_catalog(c,catalog)
    ensures snapshot_isolation(initial(c,catalog),c),single_write_per_key(initial(c,catalog),c)
{
    let s=initial(c,catalog);
    assert(s.ops.dom() =~= c.txns);
    assert(c.txns.filter(|t: int| s.ops[t].len() > 0) =~= ISet::empty());
    assert(Seq::<int>::empty().to_set().to_iset() =~= ISet::empty());
    assert(si_order(s,c,Seq::empty()));
}
pub proof fn can_start(c: Constants,catalog: IMap<int,int>,r: int,t: int,ts: int)
    requires c.routers.contains(r),c.txns.contains(t),c.timestamps.contains(ts)
    ensures enabled(initial(c,catalog),c,Action::RouterStart { r,t,ts })
{ reveal(enabled); }
} // verus!

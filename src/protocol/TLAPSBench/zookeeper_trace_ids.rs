//! Name three servers by the benchmark's own CHOOSE-based election ranking.
use vstd::prelude::*;
use super::zk_election as fle;
verus! {
broadcast use vstd::set_lib::group_set_lib_default;
pub open spec fn servers() -> Set<int> { set![0int,1int,2int] }
pub open spec fn a() -> int { choose |i: int| servers().contains(i) }
pub open spec fn b() -> int { choose |i: int| servers().remove(a()).contains(i) }
pub open spec fn c() -> int { choose |i: int| servers().remove(a()).remove(b()).contains(i) }
pub proof fn geometry()
    ensures a() != b(),a() != c(),b() != c(),servers() == set![a(),b(),c()],servers().len() == 3,
        fle::ranks(servers())[a()] == 3,fle::ranks(servers())[b()] == 2,fle::ranks(servers())[c()] == 1
{
    let q=servers(); let aa=a(); let bb=b(); let cc=c();
    assert(q.len() == 3); assert(q.contains(0)); assert(exists |i: int| q.contains(i)); assert(q.contains(aa));
    assert(q.remove(aa).len() == 2); assert(q.remove(aa).contains(q.remove(aa).choose())); assert(exists |i: int| q.remove(aa).contains(i)); assert(q.remove(aa).contains(bb));
    assert(q.remove(aa).remove(bb).len() == 1); assert(q.remove(aa).remove(bb).contains(q.remove(aa).remove(bb).choose()));
    assert(exists |i: int| q.remove(aa).remove(bb).contains(i)); assert(q.remove(aa).remove(bb).contains(cc));
    assert(q.remove(aa).remove(bb) =~= set![cc]); assert(q =~= set![aa,bb,cc]);
    reveal_with_fuel(fle::ranks,4);
}
} // verus!

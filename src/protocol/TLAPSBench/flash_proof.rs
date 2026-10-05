use vstd::prelude::*;
use super::flash::*;
use super::temporal::Behavior;
verus! {
pub open spec fn proc_typed(p: Proc, c: Constants) -> bool {
    data_u(c, p.data) && (p.cache != Cache::I ==> c.data.contains(p.data))
}
pub open spec fn uni_typed(m: UniMsg, c: Constants) -> bool {
    node_u(c, m.node) && data_u(c, m.data)
    && (m.cmd == Uni::Put || m.cmd == Uni::PutX ==> c.data.contains(m.data))
}
pub open spec fn typed(s: LState, c: Constants) -> bool {
    type_ok(s, c)
    && (forall |p: int| c.nodes.contains(p) ==> proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c))
    && (s.wb.pending ==> c.data.contains(s.wb.data))
    && (s.shwb.cmd == Shared::ShWb ==> c.data.contains(s.shwb.data) && c.nodes.contains(s.shwb.node))
}
pub proof fn initial_typed(c: Constants, home: int, data: int)
    requires c.nodes.contains(home), c.data.contains(data)
    ensures typed(initial(c, home, data), c)
{}
pub proof fn preserve_typed(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a)
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
pub open spec fn behavior(b: Seq<LState>, c: Constants) -> bool {
    valid_constants(c) && b.len() > 0
    && c.nodes.contains(b[0].home) && c.data.contains(b[0].current)
    && b[0] == initial(c, b[0].home, b[0].current)
    && forall |i: int| 0 <= i < b.len()-1 ==> #[trigger] next(b[i], b[i+1], c)
}
pub proof fn type_correct(b: Seq<LState>, c: Constants, k: int)
    requires behavior(b, c), 0 <= k < b.len()
    ensures typed(b[k], c), type_ok(b[k], c)
    decreases k
{
    if k == 0 { initial_typed(c, b[0].home, b[0].current); }
    else {
        type_correct(b, c, k-1);
        let i = k-1;
        assert(next(b[i], b[i+1], c));
        reveal(next);
        let a = choose |a: Action| #[trigger] enabled(b[i], c, a) && b[i+1] == apply(b[i], c, a);
        preserve_typed(b[i], c, a);
    }
}
pub proof fn type_at(b: Behavior<LState>, c: Constants, k: int)
    requires super::flash_liveness::safety_spec(b, c), k >= 0
    ensures typed(b[k], c), type_ok(b[k], c)
    decreases k
{
    if k == 0 { initial_typed(c, b[0].home, b[0].current); }
    else {
        type_at(b, c, k-1);
        let i = k-1;
        assert(next(b[i], b[i+1], c));
        reveal(next);
        let a = choose |a: Action| #[trigger] enabled(b[i], c, a) && b[i+1] == apply(b[i], c, a);
        preserve_typed(b[i], c, a);
    }
}
pub proof fn type_correct_always(b: Behavior<LState>, c: Constants)
    requires super::flash_liveness::safety_spec(b, c)
    ensures forall |k: int| k >= 0 ==> #[trigger] type_ok(b[k], c)
{
    assert forall |k: int| k >= 0 implies #[trigger] type_ok(b[k], c) by { type_at(b, c, k); }
}
} // verus!

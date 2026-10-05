//! No insertion can occur when the source's probe limit is zero.
use vstd::prelude::*;
use super::open_addressing::*;
use super::open_addressing_proof as base;
use super::open_addressing_contents as contents;
use super::temporal::Behavior;
verus! {
pub open spec fn thread(t: LWriter) -> bool {
    t.index == 0 && t.pc != Pc::Cntns && t.pc != Pc::OnSnc
    && t.pc != Pc::IsMth && t.pc != Pc::Cas
    && (t.pc == Pc::NestedIns || t.pc == Pc::Set ==> t.lo == Cell::Empty)
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    contents::inductive(s,c) && s.history.is_empty()
    && s.external == Seq::<int>::empty() && s.newexternal == Seq::<int>::empty()
    && (forall |i: int| 1 <= i <= c.k ==> s.table[i] == Cell::Empty)
    && (forall |p: int| c.writers.contains(p) ==> #[trigger] thread(s.threads[p]))
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{ contents::initial_inductive(c); }
pub proof fn preserve_thread(s: LState,c: Constants,p: int,pick: int,q: int)
    requires valid_constants(c),c.limit == 0,inductive(s,c),enabled(s,c,Action::Writer { p,pick }),c.writers.contains(q)
    ensures thread(apply(s,c,Action::Writer { p,pick }).threads[q])
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    assert(thread(s.threads[p])); assert(thread(s.threads[q]));
    contents::wrap_range(s.threads[p].ei+1,c.k);
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires valid_constants(c),c.limit == 0,inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    contents::preserve_inductive(s,c,a); let u=apply(s,c,a);
    reveal(enabled); reveal(apply); reveal(compare);
    if let Action::Writer { p,pick } = a {
        let t=s.threads[p]; assert(thread(t));
        contents::wrap_range(t.ei,c.k);
        assert forall |q: int| c.writers.contains(q) implies #[trigger] thread(u.threads[q]) by { preserve_thread(s,c,p,pick,q); }
    }
}
pub proof fn goals(s: LState,c: Constants)
    requires valid_constants(c),inductive(s,c)
    ensures consistent(s,c),contains_goal(s,c),duplicates(s,c)
{
    assert forall |f: int| c.fps.contains(f) && !s.history.contains(f) implies !contains(s,c,f) by {
        if contains(s,c,f) { contents::no_spurious(s,c,f); }
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires base::safety_spec(b,c),c.limit == 0,k >= 0
    ensures inductive(b[k],c),consistent(b[k],c),contains_goal(b[k],c),duplicates(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c); }
    else {
        safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve(b[i],c,a);
    }
    goals(b[k],c);
}
} // verus!

//! Probe bounds and the table positions touched by collapsed-hash eviction.
use vstd::prelude::*;
use super::open_addressing::*;
use super::open_addressing_proof as base;
use super::open_addressing_contents as contents;
use super::open_addressing_lock as lock;
use super::open_addressing_hash as hash;
use super::temporal::Behavior;
verus! {
pub open spec fn moving(pc: Pc) -> bool { pc == Pc::NestedIns || pc == Pc::Set }
pub open spec fn hole(t: LWriter,c: Constants) -> int { wrap(t.ej+1,c.k) }
pub open spec fn in_block(c: Constants,i: int) -> bool { i == c.k || 1 <= i < c.limit }
pub open spec fn positive(x: Cell) -> bool { x is Value && value(x) > 0 }
pub open spec fn bounds(t: LWriter,c: Constants) -> bool {
    0 <= t.index <= c.limit
    && (t.pc == Pc::Cas || t.pc == Pc::IsMth ==> t.index < c.limit)
    && (t.pc == Pc::Cas ==> t.expected is Empty || marked(t.expected) && t.expected != Cell::Value(-t.fp))
    && (t.pc == Pc::ChkSnc || t.pc == Pc::Cntns || t.pc == Pc::OnSnc ==> 0 <= value(t.expected) <= c.limit)
}
pub open spec fn temporary(s: LState,c: Constants,p: int) -> bool {
    let t=s.threads[p];
    (t.pc == Pc::StrIns ==> t.ej == t.ei)
    && (moving(t.pc) ==> (if positive(t.lo) {
        s.table[hole(t,c)] is Value && in_block(c,hole(t,c))
    } else { t.ej == t.ei && s.table[hole(t,c)] == t.lo }))
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    contents::inductive(s,c) && lock::inductive(s,c)
    && (forall |i: int| #![trigger in_block(c,i)] 1 <= i <= c.k && s.table[i] is Value ==> in_block(c,i))
    && (forall |p: int| c.writers.contains(p) ==> #[trigger] bounds(s.threads[p],c))
    && (forall |p: int| c.writers.contains(p) ==> #[trigger] temporary(s,c,p))
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial(c),c)
{ contents::initial_inductive(c); lock::initial_inductive(c); }
pub proof fn compare_values(c: Constants,a: Cell,i: int,b: Cell,j: int)
    requires valid_constants(c),compare(c,a,i,b,j) <= -1
    ensures positive(a),positive(b)
{ reveal(compare); }
pub proof fn preserve_bounds(s: LState,c: Constants,p: int,pick: int,q: int)
    requires valid_constants(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),c.writers.contains(q)
    ensures bounds(apply(s,c,Action::Writer { p,pick }).threads[q],c)
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    assert(bounds(s.threads[p],c)); assert(bounds(s.threads[q],c));
    assert(lock::local(s,p));
}
pub proof fn preserve_temporary(s: LState,c: Constants,p: int,pick: int,q: int)
    requires valid_constants(c),c.limit > 0,inductive(s,c),enabled(s,c,Action::Writer { p,pick }),c.writers.contains(q)
    ensures temporary(apply(s,c,Action::Writer { p,pick }),c,q)
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    let t=s.threads[p]; assert(temporary(s,c,p)); assert(temporary(s,c,q));
    assert(lock::pair(s,q,p)); assert(lock::local(s,p));
    contents::wrap_range(t.ei+1,c.k); contents::wrap_range(t.ej,c.k);
    hash::adjacent_different(t.ej,c.k);
    if compare(c,t.lo,wrap(t.ei+1,c.k),s.table[wrap(t.ej,c.k)],wrap(t.ej,c.k)) <= -1 {
        compare_values(c,t.lo,wrap(t.ei+1,c.k),s.table[wrap(t.ej,c.k)],wrap(t.ej,c.k));
    }
}
pub proof fn preserve_block(s: LState,c: Constants,p: int,pick: int,i: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),
        1 <= i <= c.k,apply(s,c,Action::Writer { p,pick }).table[i] is Value
    ensures in_block(c,i)
{
    reveal(enabled); reveal(apply);
    let t=s.threads[p]; assert(bounds(t,c)); assert(temporary(s,c,p));
    if t.pc == Pc::Cas { hash::collapsed_slot(c,t.fp,t.index); }
    if t.pc == Pc::Set || t.pc == Pc::NestedIns {
        contents::wrap_range(t.ej+1,c.k);
        if compare(c,t.lo,wrap(t.ei+1,c.k),s.table[wrap(t.ej,c.k)],wrap(t.ej,c.k)) <= -1 {
            compare_values(c,t.lo,wrap(t.ei+1,c.k),s.table[wrap(t.ej,c.k)],wrap(t.ej,c.k));
        }
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    contents::preserve_inductive(s,c,a); lock::preserve(s,c,a); let u=apply(s,c,a);
    reveal(enabled); reveal(apply);
    if let Action::Writer { p,pick } = a {
        assert forall |q: int| c.writers.contains(q) implies #[trigger] bounds(u.threads[q],c) by { preserve_bounds(s,c,p,pick,q); }
        assert forall |q: int| c.writers.contains(q) implies #[trigger] temporary(u,c,q) by { preserve_temporary(s,c,p,pick,q); }
        assert forall |i: int| #![trigger in_block(c,i)] 1 <= i <= c.k && u.table[i] is Value implies in_block(c,i) by { preserve_block(s,c,p,pick,i); }
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires base::safety_spec(b,c),hash::collapsed(c),c.limit > 0,k >= 0
    ensures inductive(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c); }
    else {
        safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve(b[i],c,a);
    }
}
} // verus!

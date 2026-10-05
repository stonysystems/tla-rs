//! Preservation of fingerprints through insertion, shifting, and flushing.
use vstd::prelude::*;
use super::open_addressing::*;
use super::open_addressing_proof as base;
use super::open_addressing_contents as contents;
use super::open_addressing_lock as lock;
use super::open_addressing_hash as hash;
use super::open_addressing_shape as shape;
use super::open_addressing_external as external;
use super::temporal::Behavior;
verus! {
pub open spec fn visible(s: LState,c: Constants,i: int) -> bool {
    forall |p: int| c.writers.contains(p) && shape::moving(s.threads[p].pc) ==> shape::hole(s.threads[p],c) != i
}
pub open spec fn represented(s: LState,c: Constants,f: int) -> bool {
    s.external.contains(f)
    || (exists |i: int| 1 <= i <= c.k && visible(s,c,i) && matches(s.table[i],f))
    || (exists |p: int| c.writers.contains(p) && shape::moving(s.threads[p].pc) && s.threads[p].lo == Cell::Value(f))
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    shape::inductive(s,c) && external::inductive(s,c)
    && forall |f: int| s.history.contains(f) ==> #[trigger] represented(s,c,f)
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial(c),c)
{ shape::initial_inductive(c); external::initial_inductive(c); }
pub proof fn visibility(s: LState,c: Constants,p: int,i: int)
    requires lock::inductive(s,c),c.writers.contains(p),!lock::dormant(s.threads[p].pc)
    ensures visible(s,c,i) <==> (!shape::moving(s.threads[p].pc) || shape::hole(s.threads[p],c) != i)
{
    assert forall |q: int| c.writers.contains(q) && shape::moving(s.threads[q].pc) implies q == p by { assert(lock::pair(s,q,p)); }
}
pub proof fn preserve_carried(s: LState,c: Constants,p: int,pick: int,q: int,f: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),
        c.writers.contains(q),shape::moving(s.threads[q].pc),s.threads[q].lo == Cell::Value(f),f > 0
    ensures represented(apply(s,c,Action::Writer { p,pick }),c,f)
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    let u=apply(s,c,Action::Writer { p,pick }); let t=s.threads[p];
    assert(lock::pair(s,q,p)); lock::preserve(s,c,Action::Writer { p,pick });
    if p == q && t.pc == Pc::Set {
        contents::wrap_range(t.ej+1,c.k); visibility(u,c,p,shape::hole(t,c));
        assert(matches(u.table[shape::hole(t,c)],f));
    } else {
        assert(shape::moving(u.threads[q].pc) && u.threads[q].lo == Cell::Value(f));
    }
}
pub proof fn preserve_cell(s: LState,c: Constants,p: int,pick: int,i: int,f: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),
        1 <= i <= c.k,visible(s,c,i),matches(s.table[i],f),f > 0
    ensures represented(apply(s,c,Action::Writer { p,pick }),c,f)
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    let a=Action::Writer { p,pick }; let u=apply(s,c,a); let t=s.threads[p];
    lock::preserve(s,c,a); external::sequence_step(s,c,p,pick);
    assert(shape::bounds(t,c)); assert(shape::temporary(s,c,p)); assert(lock::local(s,p));
    if !lock::dormant(t.pc) {
        visibility(s,c,p,i);
        if !lock::dormant(u.threads[p].pc) { visibility(u,c,p,i); }
    }
    if t.pc == Pc::Cas && idx(c,t.fp,t.index) == i && s.table[i] == t.expected {
        external::insertion_has_no_pending_flush(s,c,p);
        assert(external::accounted(s.table[i],s.external,s.newexternal));
        assert(s.external.contains(f));
    } else if t.pc == Pc::StrIns && t.ei <= c.k+c.limit && shape::hole(t,c) == i {
        if s.table[i] == Cell::Value(f) {
            assert(u.threads[p].lo == Cell::Value(f));
        } else {
            external::moving_has_no_pending_flush(s,c,p);
            assert(external::accounted(s.table[i],s.external,s.newexternal));
            assert(s.external.contains(f));
        }
    } else if t.pc == Pc::NestedIns && compare(c,t.lo,wrap(t.ei+1,c.k),s.table[wrap(t.ej,c.k)],wrap(t.ej,c.k)) <= -1 && i == wrap(t.ej,c.k) {
        let j=shape::hole(t,c); contents::wrap_range(t.ej+1,c.k); hash::adjacent_different(t.ej,c.k);
        visibility(u,c,p,j); assert(visible(u,c,j) && matches(u.table[j],f));
    } else {
        if t.pc == Pc::Flush && i == wrap(t.ei,c.k) && flush_append(s,c,t) {
            contents::expose(s,c,p);
            if s.newexternal.len() > 0 { assert(s.newexternal.contains(s.newexternal.last())); }
            assert(largest(s.newexternal) >= 0);
        }
        assert(matches(u.table[i],f));
        assert forall |q: int| c.writers.contains(q) && shape::moving(u.threads[q].pc) implies shape::hole(u.threads[q],c) != i by {
            if q != p { assert(shape::hole(s.threads[q],c) != i); }
        }
        assert(visible(u,c,i));
    }
}
pub proof fn preserve_fingerprint(s: LState,c: Constants,p: int,pick: int,f: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),
        apply(s,c,Action::Writer { p,pick }).history.contains(f)
    ensures represented(apply(s,c,Action::Writer { p,pick }),c,f)
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    let a=Action::Writer { p,pick }; let u=apply(s,c,a); let t=s.threads[p];
    external::sequence_step(s,c,p,pick);
    if s.history.contains(f) {
        assert(represented(s,c,f)); assert(c.fps.contains(f));
        if !s.external.contains(f) {
            if exists |i: int| 1 <= i <= c.k && visible(s,c,i) && matches(s.table[i],f) {
                let i=choose |i: int| 1 <= i <= c.k && visible(s,c,i) && matches(s.table[i],f);
                preserve_cell(s,c,p,pick,i,f);
            } else {
                let q=choose |q: int| c.writers.contains(q) && shape::moving(s.threads[q].pc) && s.threads[q].lo == Cell::Value(f);
                preserve_carried(s,c,p,pick,q,f);
            }
        }
    } else {
        lock::preserve(s,c,a); contents::idx_range(c,t.fp,t.index);
        assert(t.pc == Pc::Cas && t.fp == f); let i=idx(c,f,t.index);
        visibility(u,c,p,i); assert(visible(u,c,i) && matches(u.table[i],f));
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    shape::preserve(s,c,a); external::preserve(s,c,a); let u=apply(s,c,a);
    reveal(enabled); reveal(apply);
    if let Action::Writer { p,pick } = a {
        assert forall |f: int| u.history.contains(f) implies #[trigger] represented(u,c,f) by { preserve_fingerprint(s,c,p,pick,f); }
    }
}
pub proof fn goal(s: LState,c: Constants)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c)
    ensures contains_goal(s,c)
{
    assert forall |f: int| s.history.contains(f) implies contains(s,c,f) by {
        assert(represented(s,c,f)); assert(c.fps.contains(f));
        if !s.external.contains(f) {
            if exists |i: int| 1 <= i <= c.k && visible(s,c,i) && matches(s.table[i],f) {
                let i=choose |i: int| 1 <= i <= c.k && visible(s,c,i) && matches(s.table[i],f);
                assert(shape::in_block(c,i)); let probe=if i == c.k { 0 } else { i };
                hash::collapsed_slot(c,f,probe); assert(matches(s.table[idx(c,f,probe)],f));
            } else {
                let p=choose |p: int| c.writers.contains(p) && shape::moving(s.threads[p].pc) && s.threads[p].lo == Cell::Value(f);
                assert(lock::local(s,p));
            }
        }
    }
    assert forall |f: int| c.fps.contains(f) && !s.history.contains(f) implies !contains(s,c,f) by {
        if contains(s,c,f) { contents::no_spurious(s,c,f); }
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires base::safety_spec(b,c),hash::collapsed(c),c.limit > 0,k >= 0
    ensures inductive(b[k],c),contains_goal(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c); }
    else {
        safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve(b[i],c,a);
    }
    goal(b[k],c);
}
pub proof fn benchmark_contains(b: Behavior<LState>,c: Constants)
    requires base::safety_spec(b,c)
    ensures forall |k: int| k >= 0 ==> #[trigger] contains_goal(b[k],c)
{
    hash::classify(c);
    assert forall |k: int| k >= 0 implies #[trigger] contains_goal(b[k],c) by {
        if c.limit == 0 { super::open_addressing_zero::safety_at(b,c,k); }
        else if hash::injective(c) { super::open_addressing_separate::safety_at(b,c,k); }
        else { safety_at(b,c,k); }
    }
}
} // verus!

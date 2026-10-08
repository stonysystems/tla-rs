//! Provenance of table, external-storage, and eviction-temporary contents.
use vstd::prelude::*;
use super::open_addressing::*;
use super::open_addressing_proof as base;
use super::temporal::Behavior;
verus! {
pub open spec fn known(x: Cell,h: Set<int>) -> bool {
    x is Empty || value(x) != 0 && h.contains(abs(value(x)))
}
pub open spec fn temporary(x: Cell,h: Set<int>) -> bool {
    x == Cell::Value(0) || known(x,h)
}
pub open spec fn writer_known(t: LWriter,h: Set<int>) -> bool {
    temporary(t.lo,h)
    && (t.pc == Pc::NestedIns || t.pc == Pc::Set ==> known(t.lo,h))
    && forall |i: int| 0 <= i < t.stack.len() ==> #[trigger] temporary(t.stack[i].lo,h)
}
pub open spec fn sequence_known(a: Seq<int>,h: Set<int>) -> bool {
    forall |x: int| #[trigger] a.contains(x) ==> x > 0 && h.contains(x)
}
pub open spec fn contents(s: LState,c: Constants) -> bool {
    s.table.dom() == ISet::new(|i: int| 1 <= i <= c.k)
    && (forall |i: int| 1 <= i <= c.k ==> #[trigger] known(s.table[i],s.history))
    && (forall |p: int| c.writers.contains(p) ==> #[trigger] writer_known(s.threads[p],s.history))
    && sequence_known(s.external,s.history) && sequence_known(s.newexternal,s.history)
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    base::completion_inv(s,c) && sorted(s) && contents(s,c)
}
pub proof fn wrap_range(i: int,k: int)
    requires k > 0
    ensures 1 <= wrap(i,k) <= k
{ vstd::arithmetic::div_mod::lemma_mod_bound(i,k); }
pub proof fn idx_range(c: Constants,fp: int,p: int)
    requires c.k > 0
    ensures 1 <= idx(c,fp,p) <= c.k
{
    reveal(idx);
    wrap_range(((c.k-1)/(maximum(c.fps)-minimum(c.fps)))*(fp-minimum(c.fps)+1)+p,c.k);
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{ base::initial_completion(c); base::initial_sorted(c); }
pub proof fn expose(s: LState,c: Constants,p: int)
    requires inductive(s,c),c.writers.contains(p),c.k > 0
    ensures writer_known(s.threads[p],s.history),base::writer_inv(s.threads[p],c),
        known(s.table[idx(c,s.threads[p].fp,s.threads[p].index)],s.history),
        known(s.table[wrap(s.threads[p].ei,c.k)],s.history),
        known(s.table[wrap(s.threads[p].ei+1,c.k)],s.history),
        known(s.table[wrap(s.threads[p].ej,c.k)],s.history)
{
    idx_range(c,s.threads[p].fp,s.threads[p].index);
    wrap_range(s.threads[p].ei,c.k); wrap_range(s.threads[p].ei+1,c.k); wrap_range(s.threads[p].ej,c.k);
}
pub proof fn preserve_writer(s: LState,c: Constants,a: Action,p: int)
    requires valid_constants(c),inductive(s,c),enabled(s,c,a),c.writers.contains(p)
    ensures writer_known(apply(s,c,a).threads[p],apply(s,c,a).history)
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    expose(s,c,p);
    if let Action::Writer { p: q,pick } = a { expose(s,c,q); }
    let t=s.threads[p]; let u=apply(s,c,a); let v=u.threads[p];
    assert(s.history.subset_of(u.history));
    assert forall |i: int| 0 <= i < v.stack.len() implies #[trigger] temporary(v.stack[i].lo,u.history) by {
        if let Action::Writer { p: q,pick } = a {
            if q == p && t.pc == Pc::WaitIns {
                if i > 0 { assert(temporary(t.stack[i-1].lo,s.history)); }
                else { assert(temporary(t.lo,s.history)); }
            }
            else if q == p && t.pc == Pc::Rtrn { assert(temporary(t.stack[i+1].lo,s.history)); }
            else { assert(temporary(t.stack[i].lo,s.history)); }
        } else { assert(temporary(t.stack[i].lo,s.history)); }
    }
    if t.pc == Pc::Rtrn { assert(temporary(t.stack[0].lo,s.history)); }
}
pub proof fn preserve_table(s: LState,c: Constants,a: Action,i: int)
    requires valid_constants(c),inductive(s,c),enabled(s,c,a),1 <= i <= c.k
    ensures known(apply(s,c,a).table[i],apply(s,c,a).history)
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    assert(known(s.table[i],s.history));
    if let Action::Writer { p,pick } = a { expose(s,c,p); }
}
pub proof fn preserve_sequences(s: LState,c: Constants,a: Action,x: int)
    requires valid_constants(c),inductive(s,c),enabled(s,c,a)
    ensures apply(s,c,a).external.contains(x) || apply(s,c,a).newexternal.contains(x) ==>
        x > 0 && apply(s,c,a).history.contains(x)
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    broadcast use vstd::seq_lib::group_filter_ensures;
    broadcast use vstd::seq_lib::group_seq_properties;
    assert(s.external.contains(x) ==> x > 0 && s.history.contains(x));
    assert(s.newexternal.contains(x) ==> x > 0 && s.history.contains(x));
    if let Action::Writer { p,pick } = a {
        expose(s,c,p); let t=s.threads[p];
        if smaller(s.external,s.newexternal,value(s.table[wrap(t.ei,c.k)])).contains(x) {
            s.external.lemma_filter_contains_rev(|v: int| largest(s.newexternal) < v && v < value(s.table[wrap(t.ei,c.k)]),x);
        }
        if s.external.filter(|v: int| largest(s.newexternal) < v).contains(x) {
            s.external.lemma_filter_contains_rev(|v: int| largest(s.newexternal) < v,x);
        }
        if s.newexternal.len() > 0 { assert(s.newexternal.contains(s.newexternal.last())); }
        assert(largest(s.newexternal) >= 0);
        if t.pc == Pc::Flush && t.ei <= c.k+c.limit && flush_append(s,c,t) {
            let z=value(s.table[wrap(t.ei,c.k)]);
            assert(z > 0 && s.history.contains(z));
        }
    }
}
pub proof fn preserve_inductive(s: LState,c: Constants,a: Action)
    requires valid_constants(c),inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    base::preserve_completion(s,c,a); base::preserve_sorted(s,c,a);
    let u=apply(s,c,a);
    assert forall |i: int| 1 <= i <= c.k implies #[trigger] known(u.table[i],u.history) by { preserve_table(s,c,a,i); }
    assert forall |p: int| c.writers.contains(p) implies #[trigger] writer_known(u.threads[p],u.history) by { preserve_writer(s,c,a,p); }
    assert forall |x: int| #[trigger] u.external.contains(x) implies x > 0 && u.history.contains(x) by { preserve_sequences(s,c,a,x); }
    assert forall |x: int| #[trigger] u.newexternal.contains(x) implies x > 0 && u.history.contains(x) by { preserve_sequences(s,c,a,x); }
    reveal(enabled); reveal(apply);
    if let Action::Writer { p,pick } = a {
        idx_range(c,s.threads[p].fp,s.threads[p].index);
        wrap_range(s.threads[p].ei,c.k); wrap_range(s.threads[p].ej+1,c.k);
    }
    assert(u.table.dom() =~= s.table.dom());
}
pub proof fn no_spurious(s: LState,c: Constants,f: int)
    requires valid_constants(c),inductive(s,c),c.fps.contains(f),contains(s,c,f)
    ensures s.history.contains(f)
{
    if exists |i: int| #![trigger idx(c,f,i)] 0 <= i <= c.limit && matches(s.table[idx(c,f,i)],f) {
        let i=choose |i: int| #![trigger idx(c,f,i)] 0 <= i <= c.limit && matches(s.table[idx(c,f,i)],f);
        idx_range(c,f,i); assert(known(s.table[idx(c,f,i)],s.history));
    } else if !s.external.contains(f) {
        let p=choose |p: int| #![trigger c.writers.contains(p)] c.writers.contains(p) && s.threads[p].lo == Cell::Value(f);
        assert(writer_known(s.threads[p],s.history));
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires base::safety_spec(b,c),k >= 0
    ensures inductive(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c); }
    else {
        safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve_inductive(b[i],c,a);
    }
}
} // verus!

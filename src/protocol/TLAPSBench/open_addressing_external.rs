//! External merging retains the old sequence and every newly marked value.
use vstd::prelude::*;
use super::open_addressing::*;
use super::open_addressing_contents as contents;
use super::open_addressing_lock as lock;
use super::open_addressing_shape as shape;
use super::open_addressing_proof as base;
use super::temporal::Behavior;
verus! {
pub open spec fn accounted(x: Cell,a: Seq<int>,b: Seq<int>) -> bool {
    marked(x) ==> a.contains(-value(x)) || b.contains(-value(x))
}
pub open spec fn merged_prefix(a: Seq<int>,b: Seq<int>) -> bool {
    forall |x: int| a.contains(x) && x <= largest(b) ==> b.contains(x)
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    contents::inductive(s,c) && lock::inductive(s,c)
    && merged_prefix(s.external,s.newexternal)
    && (s.newexternal.len() > 0 ==> exists |p: int| c.writers.contains(p) && s.threads[p].pc == Pc::Flush)
    && (forall |i: int| 1 <= i <= c.k ==> #[trigger] accounted(s.table[i],s.external,s.newexternal))
    && (forall |p: int| c.writers.contains(p) && shape::moving(s.threads[p].pc) ==> #[trigger] accounted(s.threads[p].lo,s.external,s.newexternal))
}
pub proof fn accumulate(a: Seq<int>,b: Seq<int>,z: int)
    requires merged_prefix(a,b),z > largest(b)
    ensures merged_prefix(a,(b+smaller(a,b,z)).push(z)),
        forall |x: int| b.contains(x) ==> (b+smaller(a,b,z)).push(z).contains(x)
{
    broadcast use vstd::seq_lib::group_seq_properties;
    broadcast use vstd::seq_lib::group_filter_ensures;
    let u=(b+smaller(a,b,z)).push(z);
    assert forall |x: int| a.contains(x) && x <= largest(u) implies u.contains(x) by {
        if x < z && x > largest(b) {
            let i=choose |i: int| 0 <= i < a.len() && a[i] == x;
            a.lemma_filter_contains(|v: int| largest(b) < v && v < z,i);
        }
    }
}
pub proof fn finish(a: Seq<int>,b: Seq<int>)
    requires merged_prefix(a,b)
    ensures forall |x: int| a.contains(x) || b.contains(x) ==> (b+larger(a,b)).contains(x)
{
    broadcast use vstd::seq_lib::group_seq_properties;
    broadcast use vstd::seq_lib::group_filter_ensures;
    assert forall |x: int| a.contains(x) || b.contains(x) implies (b+larger(a,b)).contains(x) by {
        if a.contains(x) && x > largest(b) && b.len() > 0 {
            let i=choose |i: int| 0 <= i < a.len() && a[i] == x;
            a.lemma_filter_contains(|v: int| largest(b) < v,i);
        }
    }
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{ contents::initial_inductive(c); lock::initial_inductive(c); }
pub proof fn sequence_step(s: LState,c: Constants,p: int,pick: int)
    requires valid_constants(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick })
    ensures merged_prefix(apply(s,c,Action::Writer { p,pick }).external,apply(s,c,Action::Writer { p,pick }).newexternal),
        forall |x: int| s.external.contains(x) ==> apply(s,c,Action::Writer { p,pick }).external.contains(x),
        forall |x: int| s.external.contains(x) || s.newexternal.contains(x) ==>
            apply(s,c,Action::Writer { p,pick }).external.contains(x) || apply(s,c,Action::Writer { p,pick }).newexternal.contains(x)
{
    reveal(apply); reveal(enabled); let t=s.threads[p]; contents::expose(s,c,p);
    if t.pc == Pc::Flush {
        if t.ei <= c.k+c.limit {
            if flush_append(s,c,t) { accumulate(s.external,s.newexternal,value(s.table[wrap(t.ei,c.k)])); }
        } else {
            finish(s.external,s.newexternal);
            contents::preserve_inductive(s,c,Action::Writer { p,pick });
        }
    }
}
pub proof fn table_step(s: LState,c: Constants,p: int,pick: int,i: int)
    requires valid_constants(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),1 <= i <= c.k
    ensures accounted(apply(s,c,Action::Writer { p,pick }).table[i],apply(s,c,Action::Writer { p,pick }).external,apply(s,c,Action::Writer { p,pick }).newexternal)
{
    sequence_step(s,c,p,pick); reveal(enabled); reveal(apply);
    broadcast use vstd::seq_lib::group_seq_properties;
    let t=s.threads[p]; contents::expose(s,c,p);
    assert(accounted(s.table[i],s.external,s.newexternal));
    if t.pc == Pc::NestedIns && compare(c,t.lo,wrap(t.ei+1,c.k),s.table[wrap(t.ej,c.k)],wrap(t.ej,c.k)) <= -1 {
        shape::compare_values(c,t.lo,wrap(t.ei+1,c.k),s.table[wrap(t.ej,c.k)],wrap(t.ej,c.k));
    }
    if t.pc == Pc::Set { assert(accounted(t.lo,s.external,s.newexternal)); }
    if t.pc == Pc::Flush && flush_append(s,c,t) {
        assert((s.newexternal+smaller(s.external,s.newexternal,value(s.table[wrap(t.ei,c.k)]))).push(value(s.table[wrap(t.ei,c.k)])).contains(value(s.table[wrap(t.ei,c.k)])));
    }
}
pub proof fn temporary_step(s: LState,c: Constants,p: int,pick: int,q: int)
    requires valid_constants(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),c.writers.contains(q),
        shape::moving(apply(s,c,Action::Writer { p,pick }).threads[q].pc)
    ensures accounted(apply(s,c,Action::Writer { p,pick }).threads[q].lo,apply(s,c,Action::Writer { p,pick }).external,apply(s,c,Action::Writer { p,pick }).newexternal)
{
    sequence_step(s,c,p,pick); reveal(enabled); reveal(apply); reveal(thread_step);
    let t=s.threads[p]; assert(lock::local(s,p));
    contents::wrap_range(t.ei+1,c.k);
    assert(accounted(s.table[wrap(t.ei+1,c.k)],s.external,s.newexternal));
    if shape::moving(s.threads[q].pc) { assert(accounted(s.threads[q].lo,s.external,s.newexternal)); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires valid_constants(c),inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    contents::preserve_inductive(s,c,a); lock::preserve(s,c,a); let u=apply(s,c,a);
    reveal(enabled); reveal(apply); reveal(thread_step);
    if let Action::Writer { p,pick } = a {
        sequence_step(s,c,p,pick);
        assert forall |i: int| 1 <= i <= c.k implies #[trigger] accounted(u.table[i],u.external,u.newexternal) by { table_step(s,c,p,pick,i); }
        assert forall |q: int| c.writers.contains(q) && shape::moving(u.threads[q].pc) implies #[trigger] accounted(u.threads[q].lo,u.external,u.newexternal) by { temporary_step(s,c,p,pick,q); }
        if u.newexternal.len() > 0 {
            if s.newexternal.len() > 0 {
                let q=choose |q: int| c.writers.contains(q) && s.threads[q].pc == Pc::Flush;
                assert(u.threads[q].pc == Pc::Flush);
            } else { assert(u.threads[p].pc == Pc::Flush); }
        }
    }
}
pub proof fn insertion_has_no_pending_flush(s: LState,c: Constants,p: int)
    requires inductive(s,c),c.writers.contains(p),s.threads[p].pc == Pc::Cas
    ensures s.newexternal.len() == 0
{
    if s.newexternal.len() > 0 {
        let q=choose |q: int| c.writers.contains(q) && s.threads[q].pc == Pc::Flush;
        assert(lock::pair(s,q,p));
    }
}
pub proof fn moving_has_no_pending_flush(s: LState,c: Constants,p: int)
    requires inductive(s,c),c.writers.contains(p),s.threads[p].pc == Pc::StrIns || shape::moving(s.threads[p].pc)
    ensures s.newexternal.len() == 0
{
    if s.newexternal.len() > 0 {
        let q=choose |q: int| c.writers.contains(q) && s.threads[q].pc == Pc::Flush;
        assert(lock::pair(s,q,p));
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
        let a=choose |a: Action| enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve(b[i],c,a);
    }
}
} // verus!

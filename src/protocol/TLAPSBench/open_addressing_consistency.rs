//! Positive entries remain absent from both external sequences until marked.
use vstd::prelude::*;
use super::open_addressing::*;
use super::open_addressing_contents as contents;
use super::open_addressing_lock as lock;
use super::open_addressing_hash as hash;
use super::open_addressing_shape as shape;
use super::open_addressing_contains as coverage;
use super::open_addressing_insertion::*;
verus! {
pub proof fn preserve_fresh(s: LState,c: Constants,p: int,pick: int,i: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),1 <= i <= c.k
    ensures fresh(apply(s,c,Action::Writer { p,pick }).table[i],apply(s,c,Action::Writer { p,pick }))
{
    reveal(enabled); reveal(apply);
    broadcast use vstd::seq_lib::group_seq_properties;
    broadcast use vstd::seq_lib::group_filter_ensures;
    let u=apply(s,c,Action::Writer { p,pick }); let t=s.threads[p];
    contents::expose(s,c,p);
    if s.newexternal.len() > 0 { assert(s.newexternal.contains(s.newexternal.last())); }
    assert(largest(s.newexternal) >= 0);
    assert(fresh(s.table[i],s)); assert(temporary(s,c,p));
    contents::wrap_range(t.ej,c.k); contents::wrap_range(t.ei,c.k);
    assert(fresh(s.table[wrap(t.ej,c.k)],s));
    if t.pc == Pc::Cas { assert(local(s,c,p)); no_pending_flush(s,c,p); }
    if t.pc == Pc::Flush && t.ei <= c.k+c.limit && flush_append(s,c,t) && shape::positive(u.table[i]) {
        let j=wrap(t.ei,c.k);
        coverage::visibility(s,c,p,i); coverage::visibility(s,c,p,j);
        if i != j { different_values(s,c,i,j); }
        assert(value(s.table[j]) != value(u.table[i]));
    }
    if shape::positive(u.table[i]) {
        assert(fresh(u.table[i],s));
        let x=value(u.table[i]); let z=value(s.table[wrap(t.ei,c.k)]);
        if smaller(s.external,s.newexternal,z).contains(x) {
            s.external.lemma_filter_contains_rev(|v: int| largest(s.newexternal) < v && v < z,x);
        }
        if s.external.filter(|v: int| largest(s.newexternal) < v).contains(x) {
            s.external.lemma_filter_contains_rev(|v: int| largest(s.newexternal) < v,x);
        }
        assert(!u.external.contains(x));
        assert(!u.newexternal.contains(x));
    }
}
pub proof fn preserve_temporary_fresh(s: LState,c: Constants,p: int,pick: int,q: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),c.writers.contains(q),
        shape::moving(apply(s,c,Action::Writer { p,pick }).threads[q].pc)
    ensures fresh(apply(s,c,Action::Writer { p,pick }).threads[q].lo,apply(s,c,Action::Writer { p,pick }))
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    let t=s.threads[p]; assert(temporary(s,c,q)); assert(lock::local(s,p)); assert(lock::pair(s,q,p));
    contents::wrap_range(t.ei+1,c.k); assert(fresh(s.table[wrap(t.ei+1,c.k)],s));
}
} // verus!

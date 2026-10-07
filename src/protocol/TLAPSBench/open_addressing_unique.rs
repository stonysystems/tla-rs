//! Shifting moves a value into the hole and makes its old slot the new hole.
use vstd::prelude::*;
use super::open_addressing::*;
use super::open_addressing_contents as contents;
use super::open_addressing_lock as lock;
use super::open_addressing_hash as hash;
use super::open_addressing_shape as shape;
use super::open_addressing_contains as coverage;
use super::open_addressing_insertion::*;
verus! {
pub proof fn same_visibility(s: LState,c: Constants,p: int,pick: int,i: int)
    requires shape::moving(s.threads[p].pc) == shape::moving(thread_step(s,c,p,pick).pc),
        shape::moving(s.threads[p].pc) ==> shape::hole(s.threads[p],c) == shape::hole(thread_step(s,c,p,pick),c)
    ensures coverage::visible(s,c,i) == coverage::visible(apply(s,c,Action::Writer { p,pick }),c,i)
{
    reveal(apply);
    let u=apply(s,c,Action::Writer { p,pick });
    assert forall |q: int| c.writers.contains(q) && shape::moving(u.threads[q].pc) implies shape::moving(s.threads[q].pc) && shape::hole(u.threads[q],c) == shape::hole(s.threads[q],c) by {}
    assert forall |q: int| c.writers.contains(q) && shape::moving(s.threads[q].pc) implies shape::moving(u.threads[q].pc) && shape::hole(u.threads[q],c) == shape::hole(s.threads[q],c) by {}
}
pub proof fn occupancy(s: LState,c: Constants,p: int,pick: int,i: int)
    requires valid_constants(c),c.limit > 0,shape::inductive(s,c),enabled(s,c,Action::Writer { p,pick }),s.threads[p].pc != Pc::Cas,1 <= i <= c.k
    ensures (apply(s,c,Action::Writer { p,pick }).table[i] is Value) == (s.table[i] is Value)
{
    reveal(enabled); reveal(apply); let t=s.threads[p]; assert(shape::temporary(s,c,p));
    if t.pc == Pc::NestedIns && compare(c,t.lo,wrap(t.ei+1,c.k),s.table[wrap(t.ej,c.k)],wrap(t.ej,c.k)) <= -1 {
        shape::compare_values(c,t.lo,wrap(t.ei+1,c.k),s.table[wrap(t.ej,c.k)],wrap(t.ej,c.k));
    }
}
pub proof fn preserve_prefix(s: LState,c: Constants,p: int,pick: int,r: int,q: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),
        0 <= r < q < c.limit,cell(apply(s,c,Action::Writer { p,pick }),c,q) is Value
    ensures cell(apply(s,c,Action::Writer { p,pick }),c,r) is Value
{
    reveal(enabled); reveal(apply); let t=s.threads[p];
    slot_range(c,r); slot_range(c,q);
    if t.pc == Pc::Cas {
        assert(shape::bounds(t,c)); assert(local(s,c,p)); hash::collapsed_slot(c,t.fp,t.index);
        if q != t.index { slot_distinct(c,q,t.index); }
        if cell(s,c,q) is Value { assert(cell(s,c,r) is Value); }
        else { assert(q == t.index); assert(shape::positive(cell(s,c,r))); }
    } else {
        occupancy(s,c,p,pick,hash::slot(c,r)); occupancy(s,c,p,pick,hash::slot(c,q));
        assert(cell(s,c,r) is Value);
    }
}
pub proof fn preserve_pair(s: LState,c: Constants,p: int,pick: int,i: int,j: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),
        1 <= i < j <= c.k,coverage::visible(apply(s,c,Action::Writer { p,pick }),c,i),coverage::visible(apply(s,c,Action::Writer { p,pick }),c,j),
        apply(s,c,Action::Writer { p,pick }).table[i] is Value,apply(s,c,Action::Writer { p,pick }).table[j] is Value
    ensures abs(value(apply(s,c,Action::Writer { p,pick }).table[i])) != abs(value(apply(s,c,Action::Writer { p,pick }).table[j]))
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    let a=Action::Writer { p,pick }; let u=apply(s,c,a); let t=s.threads[p];
    assert(temporary(s,c,p)); assert(shape::temporary(s,c,p)); assert(lock::local(s,p));
    lock::preserve(s,c,a);
    if t.pc == Pc::Cas {
        coverage::visibility(s,c,p,i); coverage::visibility(s,c,p,j);
        let z=idx(c,t.fp,t.index);
        if s.table[z] == t.expected && z == i { inserting_absent(s,c,p,j); }
        else if s.table[z] == t.expected && z == j { inserting_absent(s,c,p,i); }
        else { different_values(s,c,i,j); }
    } else if t.pc == Pc::StrIns {
        coverage::visibility(s,c,p,i); coverage::visibility(s,c,p,j); different_values(s,c,i,j);
    } else if t.pc == Pc::Set {
        let h=shape::hole(t,c);
        coverage::visibility(s,c,p,i); coverage::visibility(s,c,p,j);
        if h == i { assert(abs(value(t.lo)) != abs(value(s.table[j]))); }
        else if h == j { assert(abs(value(t.lo)) != abs(value(s.table[i]))); }
        else { different_values(s,c,i,j); }
    } else if t.pc == Pc::NestedIns && compare(c,t.lo,wrap(t.ei+1,c.k),s.table[wrap(t.ej,c.k)],wrap(t.ej,c.k)) <= -1 {
        let h=shape::hole(t,c); let g=wrap(t.ej,c.k);
        let ii=if i == h { g } else { i }; let jj=if j == h { g } else { j };
        hash::adjacent_different(t.ej,c.k); contents::wrap_range(t.ej,c.k);
        coverage::visibility(u,c,p,i); coverage::visibility(u,c,p,j);
        coverage::visibility(s,c,p,ii); coverage::visibility(s,c,p,jj);
        assert(ii != jj && coverage::visible(s,c,ii) && coverage::visible(s,c,jj));
        assert(u.table[i] == s.table[ii] && u.table[j] == s.table[jj]); different_values(s,c,ii,jj);
    } else {
        same_visibility(s,c,p,pick,i); same_visibility(s,c,p,pick,j);
        assert(abs(value(u.table[i])) == abs(value(s.table[i])));
        assert(abs(value(u.table[j])) == abs(value(s.table[j])));
        different_values(s,c,i,j);
    }
}
pub proof fn preserve_temporary_value(s: LState,c: Constants,p: int,pick: int,q: int,i: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),c.writers.contains(q),
        shape::moving(apply(s,c,Action::Writer { p,pick }).threads[q].pc),apply(s,c,Action::Writer { p,pick }).threads[q].lo is Value,
        1 <= i <= c.k,coverage::visible(apply(s,c,Action::Writer { p,pick }),c,i),apply(s,c,Action::Writer { p,pick }).table[i] is Value
    ensures abs(value(apply(s,c,Action::Writer { p,pick }).threads[q].lo)) != abs(value(apply(s,c,Action::Writer { p,pick }).table[i]))
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    let a=Action::Writer { p,pick }; let u=apply(s,c,a); let t=s.threads[p];
    assert(temporary(s,c,q)); assert(lock::local(s,p)); assert(lock::pair(s,q,p));
    lock::preserve(s,c,a);
    if p == q && t.pc == Pc::StrIns {
        let h=shape::hole(t,c); assert(shape::temporary(s,c,p));
        contents::wrap_range(t.ej+1,c.k);
        coverage::visibility(s,c,p,h); coverage::visibility(s,c,p,i); coverage::visibility(u,c,p,i);
        different_values(s,c,h,i);
    } else if p == q && t.pc == Pc::NestedIns && compare(c,t.lo,wrap(t.ei+1,c.k),s.table[wrap(t.ej,c.k)],wrap(t.ej,c.k)) <= -1 {
        let h=shape::hole(t,c); let g=wrap(t.ej,c.k); let ii=if i == h { g } else { i };
        hash::adjacent_different(t.ej,c.k); contents::wrap_range(t.ej,c.k);
        coverage::visibility(u,c,p,i); coverage::visibility(s,c,p,ii);
        assert(coverage::visible(s,c,ii) && u.table[i] == s.table[ii]);
        assert(abs(value(t.lo)) != abs(value(s.table[ii])));
    } else {
        same_visibility(s,c,p,pick,i); assert(coverage::visible(s,c,i));
        assert(abs(value(s.threads[q].lo)) != abs(value(s.table[i])));
    }
}
} // verus!

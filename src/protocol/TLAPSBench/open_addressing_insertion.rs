//! Shared-home insertion certificates and uniqueness during eviction.
use vstd::prelude::*;
use super::open_addressing::*;
use super::open_addressing_proof as base;
use super::open_addressing_contents as contents;
use super::open_addressing_lock as lock;
use super::open_addressing_hash as hash;
use super::open_addressing_shape as shape;
use super::open_addressing_external as external;
use super::open_addressing_contains as coverage;
use super::temporal::Behavior;
verus! {
pub open spec fn cell(s: LState,c: Constants,r: int) -> Cell { s.table[hash::slot(c,r)] }
pub open spec fn active(pc: Pc) -> bool {
    pc == Pc::ChkSnc || pc == Pc::Cntns || pc == Pc::OnSnc || inserting(pc)
}
pub open spec fn inserting(pc: Pc) -> bool { pc == Pc::Insrt || pc == Pc::IsMth || pc == Pc::Cas }
pub open spec fn passed(s: LState,c: Constants,f: int,n: int) -> bool {
    forall |r: int| #![trigger cell(s,c,r)] 0 <= r < n ==> shape::positive(cell(s,c,r)) && cell(s,c,r) != Cell::Value(f)
}
pub open spec fn before(s: LState,c: Constants,n: int) -> bool {
    forall |r: int| 0 <= r < n ==> #[trigger] shape::positive(cell(s,c,r))
}
pub open spec fn placement(s: LState,c: Constants,f: int,n: int) -> bool {
    forall |r: int| 0 <= r < n && cell(s,c,r) == Cell::Value(f) ==> #[trigger] before(s,c,r)
}
pub open spec fn prefix(s: LState,c: Constants) -> bool {
    forall |r: int,q: int| 0 <= r < q < c.limit && cell(s,c,q) is Value ==> cell(s,c,r) is Value
}
pub open spec fn fresh(x: Cell,s: LState) -> bool {
    shape::positive(x) ==> !s.external.contains(value(x)) && !s.newexternal.contains(value(x))
}
pub open spec fn unique(s: LState,c: Constants) -> bool {
    forall |i: int,j: int| #![trigger coverage::visible(s,c,i), coverage::visible(s,c,j)] 1 <= i < j <= c.k && coverage::visible(s,c,i) && coverage::visible(s,c,j)
        && s.table[i] is Value && s.table[j] is Value ==> abs(value(s.table[i])) != abs(value(s.table[j]))
}
pub open spec fn temporary(s: LState,c: Constants,p: int) -> bool {
    let t=s.threads[p];
    shape::moving(t.pc) ==> fresh(t.lo,s) && (forall |i: int| #![trigger coverage::visible(s,c,i)] 1 <= i <= c.k && coverage::visible(s,c,i)
        && t.lo is Value && s.table[i] is Value ==> abs(value(t.lo)) != abs(value(s.table[i])))
}
pub open spec fn local(s: LState,c: Constants,p: int) -> bool {
    let t=s.threads[p];
    (t.pc == Pc::ChkSnc ==> t.index == 0 && t.expected == Cell::Value(c.limit))
    && (t.pc == Pc::Cntns ==> passed(s,c,t.fp,if t.index < value(t.expected) { t.index } else { value(t.expected) }) && placement(s,c,t.fp,t.index))
    && (t.pc == Pc::OnSnc ==> passed(s,c,t.fp,value(t.expected)) && placement(s,c,t.fp,c.limit))
    && (inserting(t.pc) ==> passed(s,c,t.fp,t.index) && placement(s,c,t.fp,c.limit) && !s.external.contains(t.fp))
    && (t.pc == Pc::IsMth ==> shape::positive(cell(s,c,t.index)))
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    coverage::inductive(s,c) && prefix(s,c) && unique(s,c)
    && (forall |i: int| 1 <= i <= c.k ==> #[trigger] fresh(s.table[i],s))
    && (forall |p: int| c.writers.contains(p) ==> #[trigger] temporary(s,c,p))
    && (forall |p: int| c.writers.contains(p) ==> #[trigger] local(s,c,p))
}
pub proof fn slot_range(c: Constants,r: int)
    requires valid_constants(c),0 <= r < c.limit
    ensures 1 <= hash::slot(c,r) <= c.k
{}
pub proof fn slot_distinct(c: Constants,r: int,q: int)
    requires valid_constants(c),0 <= r < c.limit,0 <= q < c.limit,r != q
    ensures hash::slot(c,r) != hash::slot(c,q)
{}
pub proof fn no_pending_flush(s: LState,c: Constants,p: int)
    requires external::inductive(s,c),c.writers.contains(p),!lock::dormant(s.threads[p].pc),s.threads[p].pc != Pc::Flush
    ensures s.newexternal.len() == 0
{
    if s.newexternal.len() > 0 {
        let q=choose |q: int| #![trigger c.writers.contains(q)] c.writers.contains(q) && s.threads[q].pc == Pc::Flush;
        assert(lock::pair(s,q,p));
    }
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial(c),c)
{
    coverage::initial_inductive(c);
    assert forall |r: int,q: int| 0 <= r < q < c.limit && cell(initial(c),c,q) is Value implies cell(initial(c),c,r) is Value by { slot_range(c,q); }
}
pub proof fn different_values(s: LState,c: Constants,i: int,j: int)
    requires unique(s,c),1 <= i <= c.k,1 <= j <= c.k,i != j,
        coverage::visible(s,c,i),coverage::visible(s,c,j),s.table[i] is Value,s.table[j] is Value
    ensures abs(value(s.table[i])) != abs(value(s.table[j]))
{
    if i < j { assert(abs(value(s.table[i])) != abs(value(s.table[j]))); }
    else { assert(abs(value(s.table[j])) != abs(value(s.table[i]))); }
}
pub proof fn inserting_absent(s: LState,c: Constants,p: int,i: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),c.writers.contains(p),
        s.threads[p].pc == Pc::Cas,s.table[idx(c,s.threads[p].fp,s.threads[p].index)] == s.threads[p].expected,
        1 <= i <= c.k,s.table[i] is Value
    ensures abs(value(s.table[i])) != s.threads[p].fp
{
    let t=s.threads[p]; assert(local(s,c,p)); assert(shape::bounds(t,c));
    assert(base::writer_inv(t,c)); assert(c.fps.contains(t.fp));
    no_pending_flush(s,c,p); hash::collapsed_slot(c,t.fp,t.index);
    assert(shape::in_block(c,i)); let q=if i == c.k { 0 } else { i };
    assert(0 <= q < c.limit && hash::slot(c,q) == i);
    assert(external::accounted(s.table[i],s.external,s.newexternal));
    if s.table[i] == Cell::Value(t.fp) {
        if q < t.index { assert(cell(s,c,q) != Cell::Value(t.fp)); }
        else if q > t.index { assert(before(s,c,q)); assert(shape::positive(cell(s,c,t.index))); }
    }
}
pub proof fn empty_external_placement(s: LState,c: Constants,p: int)
    requires valid_constants(c),inductive(s,c),c.writers.contains(p),active(s.threads[p].pc),s.external.len() == 0
    ensures placement(s,c,s.threads[p].fp,c.limit)
{
    no_pending_flush(s,c,p);
    assert forall |q: int| 0 <= q < c.limit && cell(s,c,q) == Cell::Value(s.threads[p].fp) implies #[trigger] before(s,c,q) by {
        assert forall |r: int| 0 <= r < q implies #[trigger] shape::positive(cell(s,c,r)) by {
            slot_range(c,r); assert(cell(s,c,r) is Value);
            assert(external::accounted(cell(s,c,r),s.external,s.newexternal));
            assert(contents::known(cell(s,c,r),s.history));
        }
    }
}
pub proof fn active_other_step(s: LState,c: Constants,p: int,pick: int,q: int,r: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),
        c.writers.contains(q),active(s.threads[q].pc),p != q,0 <= r < c.limit
    ensures apply(s,c,Action::Writer { p,pick }).external == s.external,
        shape::positive(cell(s,c,r)) ==> cell(apply(s,c,Action::Writer { p,pick }),c,r) == cell(s,c,r)
{
    reveal(enabled); reveal(apply); assert(lock::pair(s,p,q)); assert(shape::bounds(s.threads[p],c));
}
} // verus!

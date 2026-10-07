//! Each thread's scan certificate survives concurrent insertions.
use vstd::prelude::*;
use super::open_addressing::*;
use super::open_addressing_proof as base;
use super::open_addressing_contents as contents;
use super::open_addressing_lock as lock;
use super::open_addressing_hash as hash;
use super::open_addressing_shape as shape;
use super::open_addressing_external as external;
use super::open_addressing_insertion::*;
verus! {
pub proof fn same_table(s: LState,u: LState,c: Constants,f: int,n: int)
    requires s.table == u.table
    ensures passed(s,c,f,n) == passed(u,c,f,n),placement(s,c,f,n) == placement(u,c,f,n),before(s,c,n) == before(u,c,n)
{
    assert forall |r: int| #[trigger] cell(s,c,r) == #[trigger] cell(u,c,r) by {}
    assert forall |q: int| #[trigger] before(s,c,q) == #[trigger] before(u,c,q) by {
        if before(s,c,q) {
            assert forall |r: int| 0 <= r < q implies #[trigger] shape::positive(cell(u,c,r)) by { assert(shape::positive(cell(s,c,r))); }
        }
        if before(u,c,q) {
            assert forall |r: int| 0 <= r < q implies #[trigger] shape::positive(cell(s,c,r)) by { assert(shape::positive(cell(u,c,r))); }
        }
    }
    if passed(s,c,f,n) {
        assert forall |r: int| 0 <= r < n implies shape::positive(cell(u,c,r)) && cell(u,c,r) != Cell::Value(f) by { assert(shape::positive(cell(s,c,r)) && cell(s,c,r) != Cell::Value(f)); }
    }
    if passed(u,c,f,n) {
        assert forall |r: int| 0 <= r < n implies shape::positive(cell(s,c,r)) && cell(s,c,r) != Cell::Value(f) by { assert(shape::positive(cell(u,c,r)) && cell(u,c,r) != Cell::Value(f)); }
    }
    if placement(s,c,f,n) {
        assert forall |r: int| 0 <= r < n && cell(u,c,r) == Cell::Value(f) implies #[trigger] before(u,c,r) by { assert(before(s,c,r)); }
    }
    if placement(u,c,f,n) {
        assert forall |r: int| 0 <= r < n && cell(s,c,r) == Cell::Value(f) implies #[trigger] before(s,c,r) by { assert(before(u,c,r)); }
    }
}
pub proof fn passed_other(s: LState,c: Constants,p: int,pick: int,q: int,f: int,n: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),
        c.writers.contains(q),active(s.threads[q].pc),p != q,0 <= n <= c.limit,passed(s,c,f,n)
    ensures passed(apply(s,c,Action::Writer { p,pick }),c,f,n)
{
    assert forall |r: int| 0 <= r < n implies shape::positive(cell(apply(s,c,Action::Writer { p,pick }),c,r)) && cell(apply(s,c,Action::Writer { p,pick }),c,r) != Cell::Value(f) by {
        active_other_step(s,c,p,pick,q,r); assert(shape::positive(cell(s,c,r)) && cell(s,c,r) != Cell::Value(f));
    }
}
pub proof fn placement_other(s: LState,c: Constants,p: int,pick: int,q: int,f: int,n: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),
        c.writers.contains(q),active(s.threads[q].pc),p != q,0 <= n <= c.limit,placement(s,c,f,n)
    ensures placement(apply(s,c,Action::Writer { p,pick }),c,f,n)
{
    reveal(enabled); reveal(apply); let u=apply(s,c,Action::Writer { p,pick }); let t=s.threads[p];
    assert(lock::pair(s,p,q)); assert(shape::bounds(t,c)); assert(local(s,c,p));
    assert forall |j: int| 0 <= j < n && cell(u,c,j) == Cell::Value(f) implies #[trigger] before(u,c,j) by {
        if cell(s,c,j) != Cell::Value(f) {
            assert(t.pc == Pc::Cas && t.fp == f && idx(c,t.fp,t.index) == hash::slot(c,j));
            hash::collapsed_slot(c,t.fp,t.index);
            if j != t.index { slot_distinct(c,j,t.index); }
            assert(j == t.index);
            assert(before(s,c,j)) by {
                assert forall |r: int| 0 <= r < j implies #[trigger] shape::positive(cell(s,c,r)) by { assert(shape::positive(cell(s,c,r)) && cell(s,c,r) != Cell::Value(t.fp)); }
            }
        } else { assert(before(s,c,j)); }
        assert forall |r: int| 0 <= r < j implies #[trigger] shape::positive(cell(u,c,r)) by { active_other_step(s,c,p,pick,q,r); }
    }
}
pub proof fn other_local(s: LState,c: Constants,p: int,pick: int,q: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),c.writers.contains(q),p != q
    ensures local(apply(s,c,Action::Writer { p,pick }),c,q)
{
    reveal(enabled); reveal(apply); let u=apply(s,c,Action::Writer { p,pick }); let t=s.threads[q];
    assert(local(s,c,q)); assert(shape::bounds(t,c));
    if active(t.pc) {
        active_other_step(s,c,p,pick,q,0);
        if t.pc == Pc::Cntns {
            let n=if t.index < value(t.expected) { t.index } else { value(t.expected) };
            passed_other(s,c,p,pick,q,t.fp,n); placement_other(s,c,p,pick,q,t.fp,t.index);
        } else if t.pc == Pc::OnSnc {
            passed_other(s,c,p,pick,q,t.fp,value(t.expected)); placement_other(s,c,p,pick,q,t.fp,c.limit);
        } else if inserting(t.pc) {
            passed_other(s,c,p,pick,q,t.fp,t.index); placement_other(s,c,p,pick,q,t.fp,c.limit);
            if t.pc == Pc::IsMth { active_other_step(s,c,p,pick,q,t.index); }
        }
    }
}
pub proof fn own_local(s: LState,c: Constants,p: int,pick: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick })
    ensures local(apply(s,c,Action::Writer { p,pick }),c,p)
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    let u=apply(s,c,Action::Writer { p,pick }); let t=s.threads[p]; let v=u.threads[p];
    assert(local(s,c,p)); assert(shape::bounds(t,c)); assert(lock::local(s,p)); assert(base::writer_inv(t,c));
    if t.pc == Pc::ChkSnc && s.external.len() == 0 { empty_external_placement(s,c,p); }
    if t.pc == Pc::Cntns {
        assert(u.table == s.table);
        hash::collapsed_slot(c,t.fp,t.index);
        let n=if t.index < value(t.expected) { t.index } else { value(t.expected) };
        assert(passed(s,c,t.fp,n)); assert(placement(s,c,t.fp,t.index));
        if t.index < c.limit {
            slot_range(c,t.index); assert(contents::known(cell(s,c,t.index),s.history));
            if cell(s,c,t.index) is Empty {
                assert(v.expected == Cell::Value(n));
                assert forall |q: int| 0 <= q < c.limit && cell(u,c,q) == Cell::Value(t.fp) implies #[trigger] before(u,c,q) by {
                    assert(cell(s,c,q) == Cell::Value(t.fp));
                    if q < t.index { assert(before(s,c,q)); }
                    else if q > t.index { assert(cell(s,c,t.index) is Value); }
                    assert forall |r: int| 0 <= r < q implies #[trigger] shape::positive(cell(u,c,r)) by { assert(shape::positive(cell(s,c,r))); }
                }
                assert forall |r: int| 0 <= r < value(v.expected) implies shape::positive(cell(u,c,r)) && cell(u,c,r) != Cell::Value(t.fp) by {
                    assert(shape::positive(cell(s,c,r)) && cell(s,c,r) != Cell::Value(t.fp));
                }
            } else if !matches(cell(s,c,t.index),t.fp) {
                let n2=if v.index < value(v.expected) { v.index } else { value(v.expected) };
                assert forall |r: int| 0 <= r < n2 implies shape::positive(cell(u,c,r)) && cell(u,c,r) != Cell::Value(t.fp) by {
                    if r < n { assert(shape::positive(cell(s,c,r)) && cell(s,c,r) != Cell::Value(t.fp)); }
                }
                assert forall |r: int| 0 <= r < v.index && cell(u,c,r) == Cell::Value(t.fp) implies #[trigger] before(u,c,r) by {
                    assert(cell(s,c,r) == Cell::Value(t.fp));
                    if r < t.index { assert(before(s,c,r)); same_table(s,u,c,t.fp,r); }
                }
            }
        }
    }
    if u.table == s.table {
        same_table(s,u,c,t.fp,c.limit); same_table(s,u,c,t.fp,v.index);
        same_table(s,u,c,t.fp,value(v.expected));
        same_table(s,u,c,t.fp,if v.index < value(v.expected) { v.index } else { value(v.expected) });
    }
    if t.pc == Pc::Insrt && t.index < c.limit {
        hash::collapsed_slot(c,t.fp,t.index); no_pending_flush(s,c,p); slot_range(c,t.index);
        assert(external::accounted(cell(s,c,t.index),s.external,s.newexternal));
        assert(contents::known(cell(s,c,t.index),s.history));
    }
    if t.pc == Pc::IsMth {
        hash::collapsed_slot(c,t.fp,t.index);
        if !matches(cell(s,c,t.index),t.fp) {
            assert forall |r: int| 0 <= r < t.index+1 implies shape::positive(cell(u,c,r)) && cell(u,c,r) != Cell::Value(t.fp) by {
                if r < t.index { assert(shape::positive(cell(s,c,r)) && cell(s,c,r) != Cell::Value(t.fp)); }
            }
        }
    }
    assert(v.pc == Pc::ChkSnc ==> v.index == 0 && v.expected == Cell::Value(c.limit));
    assert(v.pc == Pc::Cntns ==> passed(u,c,v.fp,if v.index < value(v.expected) { v.index } else { value(v.expected) }) && placement(u,c,v.fp,v.index));
    assert(v.pc == Pc::OnSnc ==> passed(u,c,v.fp,value(v.expected)) && placement(u,c,v.fp,c.limit));
    assert(inserting(v.pc) ==> passed(u,c,v.fp,v.index) && placement(u,c,v.fp,c.limit) && !u.external.contains(v.fp));
    assert(v.pc == Pc::IsMth ==> shape::positive(cell(u,c,v.index)));
}
pub proof fn preserve_local(s: LState,c: Constants,p: int,pick: int,q: int)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),c.writers.contains(q)
    ensures local(apply(s,c,Action::Writer { p,pick }),c,q)
{
    if p == q { own_local(s,c,p,pick); } else { other_local(s,c,p,pick,q); }
}
} // verus!

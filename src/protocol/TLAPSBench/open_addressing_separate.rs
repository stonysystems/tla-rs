//! All three remaining goals when the source hash has distinct home slots.
use vstd::prelude::*;
use super::open_addressing::*;
use super::open_addressing_proof as base;
use super::open_addressing_contents as contents;
use super::open_addressing_hash as hash;
use super::temporal::Behavior;
verus! {
pub open spec fn allowed(pc: Pc) -> bool {
    pc == Pc::Pick || pc == Pc::Put || pc == Pc::ChkSnc || pc == Pc::Insrt || pc == Pc::IsMth || pc == Pc::Cas || pc == Pc::Done
}
pub open spec fn thread(s: LState,c: Constants,p: int) -> bool {
    let t=s.threads[p];
    allowed(t.pc) && t.index == 0
    && (t.pc == Pc::Cas ==> t.expected == Cell::Empty)
    && (t.pc == Pc::IsMth ==> s.table[idx(c,t.fp,0)] == Cell::Value(t.fp))
}
pub open spec fn homes(s: LState,c: Constants) -> bool {
    forall |i: int| #![trigger s.table[i]] 1 <= i <= c.k && s.table[i] is Value ==>
        c.fps.contains(value(s.table[i])) && idx(c,value(s.table[i]),0) == i
}
pub open spec fn membership(s: LState,c: Constants) -> bool {
    forall |f: int| #![trigger c.fps.contains(f)] #![trigger s.history.contains(f)] c.fps.contains(f) ==> (s.history.contains(f) <==> s.table[idx(c,f,0)] == Cell::Value(f))
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    base::completion_inv(s,c) && s.table.dom() == ISet::new(|i: int| 1 <= i <= c.k)
    && !s.evict && s.external == Seq::<int>::empty() && s.newexternal == Seq::<int>::empty()
    && homes(s,c) && membership(s,c)
    && forall |p: int| c.writers.contains(p) ==> #[trigger] thread(s,c,p)
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial(c),c)
{
    base::initial_completion(c);
    assert forall |f: int| #![trigger c.fps.contains(f)] c.fps.contains(f) implies (initial(c).history.contains(f) <==> initial(c).table[idx(c,f,0)] == Cell::Value(f)) by {
        contents::idx_range(c,f,0);
    }
}
pub proof fn home_empty_or_self(s: LState,c: Constants,f: int)
    requires valid_constants(c),hash::injective(c),inductive(s,c),c.fps.contains(f)
    ensures s.table[idx(c,f,0)] == Cell::Empty || s.table[idx(c,f,0)] == Cell::Value(f)
{
    contents::idx_range(c,f,0); let x=s.table[idx(c,f,0)];
    if x is Value {
        let g=value(x); assert(c.fps.contains(g)); assert(idx(c,g,0) == idx(c,f,0));
    }
}
pub proof fn preserve_thread(s: LState,c: Constants,p: int,pick: int,q: int)
    requires valid_constants(c),c.limit > 0,hash::injective(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),c.writers.contains(q)
    ensures thread(apply(s,c,Action::Writer { p,pick }),c,q)
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    assert(thread(s,c,p)); assert(thread(s,c,q)); assert(base::writer_inv(s.threads[p],c));
    if s.threads[p].pc == Pc::Insrt { home_empty_or_self(s,c,s.threads[p].fp); }
}
pub proof fn preserve_home(s: LState,c: Constants,p: int,pick: int,i: int)
    requires valid_constants(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),1 <= i <= c.k,
        apply(s,c,Action::Writer { p,pick }).table[i] is Value
    ensures c.fps.contains(value(apply(s,c,Action::Writer { p,pick }).table[i])),
        idx(c,value(apply(s,c,Action::Writer { p,pick }).table[i]),0) == i
{
    reveal(enabled); reveal(apply); assert(thread(s,c,p)); assert(base::writer_inv(s.threads[p],c));
}
pub proof fn preserve_membership(s: LState,c: Constants,p: int,pick: int,f: int)
    requires valid_constants(c),hash::injective(c),inductive(s,c),enabled(s,c,Action::Writer { p,pick }),c.fps.contains(f)
    ensures apply(s,c,Action::Writer { p,pick }).history.contains(f) <==>
        apply(s,c,Action::Writer { p,pick }).table[idx(c,f,0)] == Cell::Value(f)
{
    reveal(enabled); reveal(apply); assert(thread(s,c,p)); assert(base::writer_inv(s.threads[p],c));
    assert(s.history.contains(f) <==> s.table[idx(c,f,0)] == Cell::Value(f));
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires valid_constants(c),c.limit > 0,hash::injective(c),inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    base::preserve_completion(s,c,a); let u=apply(s,c,a);
    reveal(apply); reveal(enabled);
    if let Action::Writer { p,pick } = a {
        assert(thread(s,c,p)); contents::idx_range(c,s.threads[p].fp,0);
        assert(u.table.dom() =~= s.table.dom());
        assert forall |q: int| c.writers.contains(q) implies #[trigger] thread(u,c,q) by { preserve_thread(s,c,p,pick,q); }
        assert forall |i: int| #![trigger u.table[i]] 1 <= i <= c.k && u.table[i] is Value implies c.fps.contains(value(u.table[i])) && idx(c,value(u.table[i]),0) == i by { preserve_home(s,c,p,pick,i); }
        assert forall |f: int| #![trigger c.fps.contains(f)] #![trigger u.history.contains(f)] c.fps.contains(f) implies (u.history.contains(f) <==> u.table[idx(c,f,0)] == Cell::Value(f)) by { preserve_membership(s,c,p,pick,f); }
    }
}
pub proof fn goals(s: LState,c: Constants)
    requires valid_constants(c),inductive(s,c)
    ensures consistent(s,c),contains_goal(s,c),duplicates(s,c)
{
    assert forall |f: int| #![trigger contains(s,c,f)] #![trigger contained_in_table(s,c,f)] s.history.contains(f) implies contains(s,c,f) && contained_in_table(s,c,f) by {
        assert(c.fps.contains(f)); assert(s.table[idx(c,f,0)] == Cell::Value(f));
    }
    assert forall |f: int| #![trigger contains(s,c,f)] c.fps.contains(f) && !s.history.contains(f) implies !contains(s,c,f) by {
        if contains(s,c,f) {
            let p=choose |p: int| #![trigger idx(c,f,p)] 0 <= p <= c.limit && matches(s.table[idx(c,f,p)],f);
            contents::idx_range(c,f,p); let x=s.table[idx(c,f,p)];
            assert(c.fps.contains(value(x))); assert(value(x) > 0); assert(value(x) == f);
            assert(idx(c,f,0) == idx(c,f,p));
        }
    }
    assert forall |f: int| s.history.contains(f) implies !contained_in_table(s,c,-f) by {
        if contained_in_table(s,c,-f) {
            let p=choose |p: int| 0 <= p <= c.limit && #[trigger] s.table[idx(c,abs(-f),p)] == Cell::Value(-f);
            contents::idx_range(c,abs(-f),p); assert(c.fps.contains(-f));
        }
    }
    assert forall |i: int,j: int| #![trigger s.table[i], s.table[j]] 1 <= i < j <= c.k && s.table[i] is Value && s.table[j] is Value
        implies abs(value(s.table[i])) != abs(value(s.table[j])) by {
        assert(c.fps.contains(value(s.table[i]))); assert(c.fps.contains(value(s.table[j])));
        assert(value(s.table[i]) > 0 && value(s.table[j]) > 0);
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires base::safety_spec(b,c),hash::injective(c),c.limit > 0,k >= 0
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

//! Exact waiter accounting and exclusive access during eviction.
use vstd::prelude::*;
use super::open_addressing::*;
use super::open_addressing_proof as base;
use super::temporal::Behavior;
verus! {
pub open spec fn waiting(pc: Pc) -> bool { pc == Pc::WaitEv || pc == Pc::EndWEv }
pub open spec fn dormant(pc: Pc) -> bool { waiting(pc) || pc == Pc::Put }
pub open spec fn owner(pc: Pc) -> bool { pc == Pc::WaitIns || base::in_evict(pc) || pc == Pc::EndEv }
pub open spec fn exclusive(pc: Pc) -> bool { base::in_evict(pc) || pc == Pc::EndEv }
pub open spec fn waiters(s: LState,c: Constants) -> Set<int> {
    c.writers.filter(|p: int| waiting(s.threads[p].pc))
}
pub open spec fn local(s: LState,p: int) -> bool {
    (owner(s.threads[p].pc) ==> s.evict)
    && (base::in_evict(s.threads[p].pc) ==> s.threads[p].stack.len() == 1 && s.threads[p].stack[0].pc == Pc::EndEv)
    && (!base::in_evict(s.threads[p].pc) ==> s.threads[p].stack.len() == 0)
}
pub open spec fn pair(s: LState,p: int,q: int) -> bool {
    (owner(s.threads[p].pc) && owner(s.threads[q].pc) ==> p == q)
    && (exclusive(s.threads[p].pc) && p != q ==> dormant(s.threads[q].pc))
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    base::completion_inv(s,c)
    && s.wait_count == waiters(s,c).len()
    && (forall |p: int| c.writers.contains(p) ==> #[trigger] local(s,p))
    && (forall |p: int,q: int| c.writers.contains(p) && c.writers.contains(q) ==> #[trigger] pair(s,p,q))
    && (s.evict ==> exists |p: int| c.writers.contains(p) && owner(s.threads[p].pc))
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{
    base::initial_completion(c);
    assert(waiters(initial(c),c) =~= Set::<int>::empty());
}
pub proof fn all_waiting(s: LState,c: Constants,p: int)
    requires inductive(s,c),c.writers.contains(p),s.threads[p].pc == Pc::WaitIns,
        s.wait_count == c.writers.len()-1+c.readers.len()
    ensures waiters(s,c) == c.writers.remove(p),c.readers.is_empty()
{
    let w=waiters(s,c); let others=c.writers.remove(p);
    assert(w.subset_of(others));
    vstd::set_lib::lemma_len_subset(w,others);
    assert(w.len() == others.len());
    vstd::set_lib::lemma_subset_equality(w,others);
    c.readers.lemma_len0_is_empty();
}
pub proof fn preserve_count(s: LState,c: Constants,p: int,pick: int)
    requires inductive(s,c),enabled(s,c,Action::Writer { p,pick })
    ensures apply(s,c,Action::Writer { p,pick }).wait_count == waiters(apply(s,c,Action::Writer { p,pick }),c).len()
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    let u=apply(s,c,Action::Writer { p,pick }); let w=waiters(s,c);
    assert(local(s,p));
    if s.threads[p].pc == Pc::Put && s.evict {
        assert(!w.contains(p)); assert(waiters(u,c) =~= w.insert(p));
    } else if s.threads[p].pc == Pc::EndWEv {
        assert(w.contains(p)); assert(waiters(u,c) =~= w.remove(p));
    } else { assert(waiters(u,c) =~= w); }
}
pub proof fn preserve_local(s: LState,c: Constants,p: int,pick: int,q: int)
    requires inductive(s,c),enabled(s,c,Action::Writer { p,pick }),c.writers.contains(q)
    ensures local(apply(s,c,Action::Writer { p,pick }),q)
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    assert(local(s,q)); assert(local(s,p)); assert(pair(s,p,q));
}
pub proof fn preserve_pair(s: LState,c: Constants,p: int,pick: int,q: int,r: int)
    requires inductive(s,c),enabled(s,c,Action::Writer { p,pick }),c.writers.contains(q),c.writers.contains(r)
    ensures pair(apply(s,c,Action::Writer { p,pick }),q,r)
{
    reveal(enabled); reveal(apply); reveal(thread_step);
    assert(local(s,p)); assert(local(s,q)); assert(local(s,r));
    assert(pair(s,p,q)); assert(pair(s,p,r)); assert(pair(s,q,p)); assert(pair(s,r,p)); assert(pair(s,q,r));
    if s.threads[p].pc == Pc::WaitIns { all_waiting(s,c,p); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    base::preserve_completion(s,c,a); let u=apply(s,c,a);
    reveal(apply); reveal(enabled);
    if let Action::Writer { p,pick } = a {
        preserve_count(s,c,p,pick);
        assert forall |q: int| c.writers.contains(q) implies #[trigger] local(u,q) by { preserve_local(s,c,p,pick,q); }
        assert forall |q: int,r: int| c.writers.contains(q) && c.writers.contains(r) implies #[trigger] pair(u,q,r) by { preserve_pair(s,c,p,pick,q,r); }
        if u.evict {
            reveal(thread_step); assert(local(s,p));
            if s.evict {
                let q=choose |q: int| c.writers.contains(q) && owner(s.threads[q].pc);
                assert(local(s,q)); assert(pair(s,p,q)); assert(owner(u.threads[q].pc));
            } else { assert(owner(u.threads[p].pc)); }
        }
    }
}
pub proof fn other_preserves_table(s: LState,c: Constants,p: int,a: Action)
    requires inductive(s,c),enabled(s,c,a),c.writers.contains(p),exclusive(s.threads[p].pc),
        match a { Action::Writer { p: q,.. } => q != p,_ => true }
    ensures apply(s,c,a).table == s.table,apply(s,c,a).external == s.external,
        apply(s,c,a).newexternal == s.newexternal,apply(s,c,a).history == s.history
{
    reveal(enabled); reveal(apply);
    if let Action::Writer { p: q,.. } = a { assert(pair(s,p,q)); }
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

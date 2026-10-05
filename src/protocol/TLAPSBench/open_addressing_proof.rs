use vstd::prelude::*;
use super::open_addressing::*;
use super::temporal::Behavior;

verus! {

pub open spec fn writer_inv(t: LWriter, c: Constants) -> bool {
    (t.pc != Pc::Pick && t.pc != Pc::Done ==> c.fps.contains(t.fp))
    && (forall |i: int| 0 <= i < t.stack.len() ==> t.stack[i].pc == Pc::EndEv)
    && (t.pc == Pc::Rtrn ==> t.stack.len() > 0)
}
pub open spec fn completion_inv(s: LState, c: Constants) -> bool {
    s.threads.dom() == c.writers && s.history.subset_of(c.fps)
    && (forall |p: int| c.writers.contains(p) ==> writer_inv(s.threads[p], c))
    && complete_as_safety(s, c)
    // The call stack is nonempty throughout the eviction subroutine.
    && (forall |p: int| c.writers.contains(p) && in_evict(s.threads[p].pc) ==> s.threads[p].stack.len() > 0)
}
pub open spec fn in_evict(pc: Pc) -> bool {
    pc == Pc::StrIns || pc == Pc::NestedIns || pc == Pc::Set || pc == Pc::Flush || pc == Pc::Rtrn
}
pub proof fn initial_completion(c: Constants)
    ensures completion_inv(initial(c), c)
{}

pub proof fn writer_preservation(s: LState, c: Constants, p: int, pick: int)
    requires writer_inv(s.threads[p], c),
        in_evict(s.threads[p].pc) ==> s.threads[p].stack.len() > 0,
        enabled(s, c, Action::Writer { p, pick })
    ensures writer_inv(thread_step(s, c, p, pick), c),
        in_evict(thread_step(s, c, p, pick).pc) ==> thread_step(s, c, p, pick).stack.len() > 0,
        thread_step(s, c, p, pick).pc == Pc::Done ==>
            s.threads[p].pc == Pc::Done || s.threads[p].pc == Pc::Pick && c.fps.difference(s.history).is_empty()
{
    reveal(enabled);
    reveal(thread_step);
    let t = s.threads[p];
    let t2 = thread_step(s, c, p, pick);
    assert forall |i: int| 0 <= i < t2.stack.len() implies t2.stack[i].pc == Pc::EndEv by {
        if t.pc == Pc::WaitIns && i > 0 { assert(t.stack[i - 1].pc == Pc::EndEv); }
        if t.pc == Pc::Rtrn { assert(t.stack[i + 1].pc == Pc::EndEv); }
    }
}

pub proof fn preserve_completion(s: LState, c: Constants, a: Action)
    requires completion_inv(s, c), enabled(s, c, a)
    ensures completion_inv(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    match a {
        Action::Stutter => { assert(apply(s, c, a) == s); assert(completion_inv(apply(s, c, a), c)); },
        Action::Writer { p, pick } => {
            let t = s.threads[p];
            let u = apply(s, c, a);
            let t2 = thread_step(s, c, p, pick);
            assert(writer_inv(t, c));
            writer_preservation(s, c, p, pick);
            assert(writer_inv(t2, c));
            if t.pc == Pc::Pick && t2.pc == Pc::Done {
                assert(c.fps.subset_of(s.history)) by {
                    assert forall |f: int| c.fps.contains(f) implies s.history.contains(f) by {
                        if !s.history.contains(f) { assert(c.fps.difference(s.history).contains(f)); }
                    }
                }
                assert(s.history =~= c.fps);
            }
            assert(s.history.subset_of(u.history));
            assert(u.history.subset_of(c.fps)) by {
                assert forall |f: int| u.history.contains(f) implies c.fps.contains(f) by {
                    if !s.history.contains(f) { assert(t.pc == Pc::Cas); assert(c.fps.contains(t.fp)); }
                }
            }
            assert forall |q: int| c.writers.contains(q) implies writer_inv(u.threads[q], c) by {
                if q != p { assert(writer_inv(s.threads[q], c)); }
            }
            assert forall |q: int| c.writers.contains(q) && in_evict(u.threads[q].pc)
                implies u.threads[q].stack.len() > 0 by {
                if q != p { assert(s.threads[q].stack.len() > 0); }
            }
            assert forall |q: int| c.writers.contains(q) && u.threads[q].pc == Pc::Done
                implies u.history == c.fps by {
                if q != p { assert(s.threads[q].pc == Pc::Done); }
                assert(s.history == c.fps);
                assert(u.history =~= c.fps);
            }
            assert(u.threads.dom() =~= c.writers);
            assert(complete_as_safety(u, c));
            assert(completion_inv(u, c));
        },
    }
}

pub proof fn ordered_prefix(a: Seq<int>)
    requires ordered(a), a.len() > 0
    ensures ordered(a.drop_last())
{}
pub proof fn ordered_push(a: Seq<int>, x: int)
    requires ordered(a), forall |i: int| 0 <= i < a.len() ==> a[i] < x
    ensures ordered(a.push(x))
{
    assert forall |i: int, j: int| 0 <= i < j < a.push(x).len() implies a.push(x)[i] < a.push(x)[j] by {
        if j < a.len() { assert(a[i] < a[j]); }
    }
}
pub proof fn ordered_filter(a: Seq<int>, pred: spec_fn(int) -> bool)
    requires ordered(a)
    ensures ordered(a.filter(pred))
    decreases a.len()
{
    if a.len() > 0 {
        let b = a.drop_last();
        ordered_prefix(a);
        ordered_filter(b, pred);
        reveal(Seq::filter);
        if pred(a.last()) {
            assert forall |i: int| 0 <= i < b.filter(pred).len() implies b.filter(pred)[i] < a.last() by {
                let x = b.filter(pred)[i];
                assert(b.filter(pred).contains(x));
                b.lemma_filter_contains_rev(pred, x);
                assert(b.contains(x));
                let j = choose |j: int| 0 <= j < b.len() && b[j] == x;
                assert(a[j] < a[a.len() - 1]);
            }
            ordered_push(b.filter(pred), a.last());
        }
    } else { reveal(Seq::filter); }
}
pub proof fn ordered_concat(a: Seq<int>, b: Seq<int>)
    requires ordered(a), ordered(b), forall |i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i] < b[j]
    ensures ordered(a + b)
{
    assert forall |i: int, j: int| 0 <= i < j < (a+b).len() implies (a+b)[i] < (a+b)[j] by {
        if j < a.len() { assert(a[i] < a[j]); }
        else if i < a.len() { assert(a[i] < b[j - a.len()]); }
        else { assert(b[i - a.len()] < b[j - a.len()]); }
    }
}
pub proof fn ordered_upper_bound(a: Seq<int>)
    requires ordered(a)
    ensures forall |i: int| 0 <= i < a.len() ==> a[i] <= largest(a)
{
    assert forall |i: int| 0 <= i < a.len() implies a[i] <= largest(a) by {
        if i < a.len() - 1 { assert(a[i] < a[a.len() - 1]); }
    }
}
pub proof fn merge_smaller(a: Seq<int>, b: Seq<int>, x: int)
    requires ordered(a), ordered(b), largest(b) < x
    ensures ordered((b + smaller(a, b, x)).push(x))
{
    let pred = |v: int| largest(b) < v && v < x;
    ordered_filter(a, pred);
    broadcast use vstd::seq_lib::group_filter_ensures;
    ordered_upper_bound(b);
    ordered_concat(b, smaller(a, b, x));
    let joined = b + smaller(a, b, x);
    assert forall |i: int| 0 <= i < joined.len() implies joined[i] < x by {
        if i >= b.len() { assert(pred(smaller(a, b, x)[i - b.len()])); }
    }
    ordered_push(joined, x);
}
pub proof fn merge_larger(a: Seq<int>, b: Seq<int>)
    requires ordered(a), ordered(b)
    ensures ordered(b + larger(a, b))
{
    if b.len() != 0 {
        let pred = |v: int| largest(b) < v;
        ordered_filter(a, pred);
        broadcast use vstd::seq_lib::group_filter_ensures;
        ordered_upper_bound(b);
        ordered_concat(b, larger(a, b));
    } else { assert(b + a =~= a); }
}
pub proof fn initial_sorted(c: Constants)
    ensures sorted(initial(c))
{}
pub proof fn preserve_sorted(s: LState, c: Constants, a: Action)
    requires sorted(s), enabled(s, c, a)
    ensures sorted(apply(s, c, a))
{
    reveal(apply);
    if let Action::Writer { p, pick } = a {
        let t = s.threads[p];
        if t.pc == Pc::Flush {
            if t.ei <= c.k + c.limit {
                if flush_append(s, c, t) {
                    merge_smaller(s.external, s.newexternal, value(s.table[wrap(t.ei, c.k)]));
                }
            } else { merge_larger(s.external, s.newexternal); }
        }
    }
}

pub open spec fn behavior(b: Seq<LState>, c: Constants) -> bool {
    valid_constants(c) && b.len() > 0 && b[0] == initial(c)
    && forall |i: int| 0 <= i < b.len()-1 ==> #[trigger] next(b[i], b[i+1], c)
}
// No bound on the length, key space, table size, or writer/reader counts.
pub proof fn benchmark_invariants(b: Seq<LState>, c: Constants, k: int)
    requires behavior(b, c), 0 <= k < b.len()
    ensures complete_as_safety(b[k], c), sorted(b[k]), completion_inv(b[k], c)
    decreases k
{
    if k == 0 { initial_completion(c); initial_sorted(c); }
    else {
        benchmark_invariants(b, c, k-1);
        let i = k - 1;
        assert(0 <= i < b.len() - 1);
        assert(next(b[i], b[i + 1], c));
        reveal(next);
        let a = choose |a: Action| #[trigger] enabled(b[k-1], c, a) && b[k] == apply(b[k-1], c, a);
        preserve_completion(b[k-1], c, a);
        preserve_sorted(b[k-1], c, a);
    }
}

pub open spec fn safety_spec(b: Behavior<LState>, c: Constants) -> bool {
    valid_constants(c) && b[0] == initial(c)
    && (forall |k: int| k >= 0 ==> b.dom().contains(k))
    && forall |k: int| k >= 0 ==> #[trigger] next(b[k], b[k+1], c)
}
pub proof fn safety_at(b: Behavior<LState>, c: Constants, k: int)
    requires safety_spec(b, c), k >= 0
    ensures completion_inv(b[k], c), sorted(b[k])
    decreases k
{
    if k == 0 { initial_completion(c); initial_sorted(c); }
    else {
        safety_at(b, c, k-1);
        let i = k-1;
        assert(next(b[i], b[i+1], c));
        reveal(next);
        let a = choose |a: Action| #[trigger] enabled(b[i], c, a) && b[i+1] == apply(b[i], c, a);
        preserve_completion(b[i], c, a);
        preserve_sorted(b[i], c, a);
    }
}
// Dropping Spec's writer fairness proves these safety goals for more behaviors.
pub proof fn benchmark_safety(b: Behavior<LState>, c: Constants)
    requires safety_spec(b, c)
    ensures
        forall |k: int| k >= 0 ==> #[trigger] complete_as_safety(b[k], c),
        forall |k: int| k >= 0 ==> #[trigger] sorted(b[k]),
{
    assert forall |k: int| k >= 0 implies #[trigger] complete_as_safety(b[k], c) by {
        safety_at(b, c, k);
    }
    assert forall |k: int| k >= 0 implies #[trigger] sorted(b[k]) by {
        safety_at(b, c, k);
    }
}
} // verus!

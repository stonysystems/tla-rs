//! Completion of the shared-home induction and the original three goals.
use vstd::prelude::*;
use super::open_addressing::*;
use super::open_addressing_proof as base;
use super::open_addressing_contents as contents;
use super::open_addressing_lock as lock;
use super::open_addressing_hash as hash;
use super::open_addressing_shape as shape;
use super::open_addressing_external as external;
use super::open_addressing_contains as coverage;
use super::open_addressing_insertion::*;
use super::open_addressing_unique as shifting;
use super::open_addressing_consistency as marking;
use super::temporal::Behavior;
verus! {
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    coverage::preserve(s,c,a); let u=apply(s,c,a); reveal(enabled); reveal(apply);
    if let Action::Writer { p,pick } = a {
        assert forall |r: int,q: int| 0 <= r < q < c.limit && cell(u,c,q) is Value implies cell(u,c,r) is Value by { shifting::preserve_prefix(s,c,p,pick,r,q); }
        assert forall |i: int,j: int| #![trigger coverage::visible(u,c,i), coverage::visible(u,c,j)] 1 <= i < j <= c.k && coverage::visible(u,c,i) && coverage::visible(u,c,j)
            && u.table[i] is Value && u.table[j] is Value implies abs(value(u.table[i])) != abs(value(u.table[j])) by { shifting::preserve_pair(s,c,p,pick,i,j); }
        assert forall |i: int| 1 <= i <= c.k implies #[trigger] fresh(u.table[i],u) by { marking::preserve_fresh(s,c,p,pick,i); }
        assert forall |q: int| c.writers.contains(q) implies #[trigger] temporary(u,c,q) by {
            if shape::moving(u.threads[q].pc) {
                marking::preserve_temporary_fresh(s,c,p,pick,q);
                assert forall |i: int| #![trigger coverage::visible(u,c,i)] 1 <= i <= c.k && coverage::visible(u,c,i) && u.threads[q].lo is Value && u.table[i] is Value
                    implies abs(value(u.threads[q].lo)) != abs(value(u.table[i])) by { shifting::preserve_temporary_value(s,c,p,pick,q,i); }
            }
        }
        assert forall |q: int| c.writers.contains(q) implies #[trigger] local(u,c,q) by { super::open_addressing_scanning::preserve_local(s,c,p,pick,q); }
    }
}
pub proof fn no_eviction(s: LState,c: Constants)
    requires inductive(s,c),!s.evict
    ensures s.newexternal.len() == 0,forall |i: int| #[trigger] coverage::visible(s,c,i),
        forall |p: int| #![trigger c.writers.contains(p)] c.writers.contains(p) ==> !shape::moving(s.threads[p].pc)
{
    assert forall |p: int| #![trigger c.writers.contains(p)] c.writers.contains(p) implies !shape::moving(s.threads[p].pc) && s.threads[p].pc != Pc::Flush by { assert(lock::local(s,p)); }
    if s.newexternal.len() > 0 {
        let p=choose |p: int| #![trigger c.writers.contains(p)] c.writers.contains(p) && s.threads[p].pc == Pc::Flush;
        assert(lock::local(s,p));
    }
}
pub proof fn goals(s: LState,c: Constants)
    requires valid_constants(c),c.limit > 0,hash::collapsed(c),inductive(s,c)
    ensures consistent(s,c),contains_goal(s,c),duplicates(s,c)
{
    coverage::goal(s,c);
    if !s.evict {
        no_eviction(s,c);
        assert forall |i: int,j: int| #![trigger s.table[i], s.table[j]] 1 <= i < j <= c.k && s.table[i] is Value && s.table[j] is Value
            implies abs(value(s.table[i])) != abs(value(s.table[j])) by { different_values(s,c,i,j); }
        assert forall |f: int| #![trigger s.external.contains(f)] s.history.contains(f) implies
            (contained_in_table(s,c,f) ==> !s.external.contains(f))
            && (contained_in_table(s,c,-f) ==> s.external.contains(f))
            && (!contained_in_table(s,c,f) ==> s.external.contains(f)) by {
            assert(c.fps.contains(f)); assert(coverage::represented(s,c,f));
            if contained_in_table(s,c,f) {
                let r=choose |r: int| 0 <= r <= c.limit && #[trigger] s.table[idx(c,abs(f),r)] == Cell::Value(f);
                contents::idx_range(c,abs(f),r); assert(fresh(s.table[idx(c,abs(f),r)],s));
            }
            if contained_in_table(s,c,-f) {
                let r=choose |r: int| 0 <= r <= c.limit && #[trigger] s.table[idx(c,abs(-f),r)] == Cell::Value(-f);
                contents::idx_range(c,abs(-f),r); assert(external::accounted(s.table[idx(c,abs(-f),r)],s.external,s.newexternal));
            }
            if !s.external.contains(f) {
                let i=choose |i: int| #![trigger coverage::visible(s,c,i)] 1 <= i <= c.k && coverage::visible(s,c,i) && matches(s.table[i],f);
                assert(external::accounted(s.table[i],s.external,s.newexternal));
                assert(s.table[i] == Cell::Value(f)); assert(shape::in_block(c,i));
                let r=if i == c.k { 0 } else { i }; hash::collapsed_slot(c,f,r);
                assert(contained_in_table(s,c,f));
            }
        }
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires base::safety_spec(b,c),hash::collapsed(c),c.limit > 0,k >= 0
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
pub proof fn all_cases(b: Behavior<LState>,c: Constants,k: int)
    requires base::safety_spec(b,c),k >= 0
    ensures consistent(b[k],c),contains_goal(b[k],c),duplicates(b[k],c)
{
    hash::classify(c);
    if c.limit == 0 { super::open_addressing_zero::safety_at(b,c,k); }
    else if hash::injective(c) { super::open_addressing_separate::safety_at(b,c,k); }
    else { safety_at(b,c,k); }
}
pub proof fn benchmark_safety(b: Behavior<LState>,c: Constants)
    requires base::safety_spec(b,c)
    ensures
        forall |k: int| k >= 0 ==> #[trigger] consistent(b[k],c),
        forall |k: int| k >= 0 ==> #[trigger] contains_goal(b[k],c),
        forall |k: int| k >= 0 ==> #[trigger] duplicates(b[k],c)
{
    assert forall |k: int| k >= 0 implies #[trigger] consistent(b[k],c) by { all_cases(b,c,k); }
    assert forall |k: int| k >= 0 implies #[trigger] contains_goal(b[k],c) by { all_cases(b,c,k); }
    assert forall |k: int| k >= 0 implies #[trigger] duplicates(b[k],c) by { all_cases(b,c,k); }
}
} // verus!

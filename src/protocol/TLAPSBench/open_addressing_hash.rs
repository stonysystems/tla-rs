//! The source's integer rescaling is either injective or collapses all homes.
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use super::open_addressing::*;
verus! {
pub open spec fn factor(c: Constants) -> int { (c.k-1)/(maximum(c.fps)-minimum(c.fps)) }
pub open spec fn injective(c: Constants) -> bool {
    forall |f: int,g: int| c.fps.contains(f) && c.fps.contains(g) && #[trigger] idx(c,f,0) == #[trigger] idx(c,g,0) ==> f == g
}
pub open spec fn collapsed(c: Constants) -> bool {
    forall |f: int,p: int| #[trigger] idx(c,f,p) == wrap(p,c.k)
}
pub proof fn extrema(q: Set<int>)
    requires !q.is_empty()
    ensures q.contains(minimum(q)),q.contains(maximum(q)),
        forall |x: int| q.contains(x) ==> minimum(q) <= x <= maximum(q)
    decreases q.len()
{
    let x=q.choose(); let r=q.remove(x);
    let lo; let hi;
    if r.is_empty() { lo=x; hi=x; }
    else {
        extrema(r);
        lo=if x < minimum(r) { x } else { minimum(r) };
        hi=if x > maximum(r) { x } else { maximum(r) };
    }
    assert(q.contains(lo) && q.contains(hi));
    assert forall |y: int| q.contains(y) implies lo <= y <= hi by { if y != x { assert(r.contains(y)); } }
    assert(exists |z: int| q.contains(z) && forall |y: int| q.contains(y) ==> z <= y);
    assert(exists |z: int| q.contains(z) && forall |y: int| q.contains(y) ==> z >= y);
}
pub proof fn factor_bounds(c: Constants)
    requires valid_constants(c)
    ensures maximum(c.fps) > minimum(c.fps),factor(c) >= 0,
        factor(c)*(maximum(c.fps)-minimum(c.fps)) <= c.k-1
{
    extrema(c.fps);
    let lo=minimum(c.fps); let hi=maximum(c.fps);
    if hi <= lo {
        assert(c.fps.subset_of(set![lo])); vstd::set_lib::lemma_len_subset(c.fps,set![lo]);
        assert(false);
    }
    lemma_div_pos_is_pos(c.k-1,hi-lo);
    lemma_mod_bound(c.k-1,hi-lo);
    lemma_fundamental_div_mod(c.k-1,hi-lo);
    let q=factor(c); let d=hi-lo; let r=(c.k-1)%d;
    assert(c.k-1 == d*q+r);
    assert(q*d <= c.k-1) by(nonlinear_arith)
        requires c.k-1 == d*q+r,r >= 0;
}
pub proof fn wrap_injective_near(a: int,b: int,k: int)
    requires k > 0,0 < b-a < k
    ensures wrap(a,k) != wrap(b,k)
{
    lemma_mod_bound(a,k); lemma_mod_bound(b,k);
    lemma_mod_equivalence(b,a,k); lemma_small_mod((b-a) as nat,k as nat);
}
pub proof fn distinct_homes(c: Constants,f: int,g: int)
    requires valid_constants(c),factor(c) > 0,c.fps.contains(f),c.fps.contains(g),f < g
    ensures idx(c,f,0) != idx(c,g,0)
{
    factor_bounds(c); extrema(c.fps);
    let q=factor(c); let lo=minimum(c.fps); let hi=maximum(c.fps);
    let a=q*(f-lo+1); let b=q*(g-lo+1);
    assert(lo <= f < g <= hi);
    assert(0 < b-a < c.k) by(nonlinear_arith)
        requires a == q*(f-lo+1),b == q*(g-lo+1),q > 0,
            lo <= f < g <= hi,q*(hi-lo) <= c.k-1;
    wrap_injective_near(a,b,c.k); reveal(idx);
}
pub proof fn classify(c: Constants)
    requires valid_constants(c)
    ensures injective(c) || collapsed(c)
{
    factor_bounds(c);
    if factor(c) == 0 {
        reveal(idx);
        assert forall |f: int,p: int| #[trigger] idx(c,f,p) == wrap(p,c.k) by {}
    } else {
        assert forall |f: int,g: int| c.fps.contains(f) && c.fps.contains(g) && #[trigger] idx(c,f,0) == #[trigger] idx(c,g,0) implies f == g by {
            if f < g { distinct_homes(c,f,g); } else if g < f { distinct_homes(c,g,f); }
        }
    }
}
pub open spec fn slot(c: Constants,p: int) -> int { if p == 0 { c.k } else { p } }
pub proof fn collapsed_slot(c: Constants,f: int,p: int)
    requires valid_constants(c),collapsed(c),0 <= p <= c.limit,c.limit > 0
    ensures idx(c,f,p) == slot(c,p),1 <= slot(c,p) <= c.k
{
    lemma_small_mod(p as nat,c.k as nat);
}
pub proof fn adjacent_different(j: int,k: int)
    requires k >= 2
    ensures wrap(j,k) != wrap(j+1,k)
{ wrap_injective_near(j,j+1,k); }
} // verus!

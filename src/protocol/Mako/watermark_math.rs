//! Minimum reduction over every worker, including finite and INF endpoints.
use vstd::prelude::*;
use vstd::imap::IMap;
use super::model::*;

verus! {

pub open spec fn bmin(a: Bound, b: Bound) -> Bound {
    if bound_le(a, b) { a } else { b }
}
pub open spec fn bmax(a: Bound, b: Bound) -> Bound {
    if bound_le(a, b) { b } else { a }
}
pub open spec fn worker(e: nat, sh: int, w: int) -> Stream {
    Stream { epoch: e, shard: sh, worker: w }
}
pub open spec fn minimum(v: IMap<Stream, Bound>, e: nat, sh: int, count: nat) -> Bound
    decreases count
{
    if count == 0 { Bound::Infinity }
    else { bmin(minimum(v, e, sh, (count - 1) as nat), v[worker(e, sh, count as int - 1)]) }
}
pub proof fn order(a: Bound, b: Bound, d: Bound)
    ensures bound_le(a, a), bound_le(a, b) || bound_le(b, a),
        (bound_le(a, b) && bound_le(b, a)) ==> a == b,
        (bound_le(a, b) && bound_le(b, d)) ==> bound_le(a, d),
        bound_le(bmin(a, b), a), bound_le(bmin(a, b), b),
        bound_le(a, bmax(a, b)), bound_le(b, bmax(a, b)),
        (bound_le(a, d) && bound_le(b, d)) ==> bound_le(bmax(a, b), d),
        (bound_le(d, a) && bound_le(d, b)) ==> bound_le(d, bmin(a, b))
{ }
pub proof fn minimum_lower(v: IMap<Stream, Bound>, e: nat, sh: int, count: nat, w: int)
    requires 0 <= w < count
    ensures bound_le(minimum(v, e, sh, count), v[worker(e, sh, w)])
    decreases count
{
    if w < count - 1 {
        minimum_lower(v, e, sh, (count - 1) as nat, w);
        order(minimum(v, e, sh, (count - 1) as nat), v[worker(e, sh, count as int - 1)], v[worker(e, sh, w)]);
        order(minimum(v, e, sh, count), minimum(v, e, sh, (count - 1) as nat), v[worker(e, sh, w)]);
    } else {
        order(minimum(v, e, sh, (count - 1) as nat), v[worker(e, sh, w)], Bound::Infinity);
    }
}
pub proof fn minimum_greatest(v: IMap<Stream, Bound>, e: nat, sh: int, count: nat, b: Bound)
    requires forall|w: int| 0 <= w < count ==> bound_le(b, #[trigger] v[worker(e, sh, w)])
    ensures bound_le(b, minimum(v, e, sh, count))
    decreases count
{
    if count > 0 {
        minimum_greatest(v, e, sh, (count - 1) as nat, b);
        order(minimum(v, e, sh, (count - 1) as nat), v[worker(e, sh, count as int - 1)], b);
    }
}
pub proof fn minimum_mono(a: IMap<Stream, Bound>, b: IMap<Stream, Bound>, e: nat, sh: int, count: nat)
    requires forall|w: int| 0 <= w < count ==> bound_le(#[trigger] a[worker(e, sh, w)], b[worker(e, sh, w)])
    ensures bound_le(minimum(a, e, sh, count), minimum(b, e, sh, count))
{
    assert forall|w: int| 0 <= w < count implies bound_le(minimum(a, e, sh, count), #[trigger] b[worker(e, sh, w)]) by {
        minimum_lower(a, e, sh, count, w);
        order(minimum(a, e, sh, count), a[worker(e, sh, w)], b[worker(e, sh, w)]);
    }
    minimum_greatest(b, e, sh, count, minimum(a, e, sh, count));
}
pub proof fn minimum_equal(a: IMap<Stream, Bound>, b: IMap<Stream, Bound>, e: nat, sh: int, count: nat)
    requires forall|w: int| 0 <= w < count ==> #[trigger] a[worker(e, sh, w)] == b[worker(e, sh, w)]
    ensures minimum(a, e, sh, count) == minimum(b, e, sh, count)
    decreases count
{
    if count > 0 { minimum_equal(a, b, e, sh, (count - 1) as nat); }
}
} // verus!

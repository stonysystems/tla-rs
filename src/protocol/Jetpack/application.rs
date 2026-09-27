//! Deterministic application semantics, including returned values.
//! Independence requires both state commutation and preservation of outputs.
use vstd::prelude::*;
use super::recovery as r;

verus! {

#[verifier::reject_recursive_types(A)]
pub struct Machine<A, R> {
    pub initial: A,
    pub step: spec_fn(A, int) -> A,
    pub output: spec_fn(A, int) -> R,
}
pub struct Execution<A, R> { pub state: A, pub outputs: Map<int, R> }
pub open spec fn independent(c: r::Config, x: int, y: int) -> bool {
    x != y && !c.conflict.contains((x, y))
}
pub open spec fn machine_ok<A, R>(m: Machine<A, R>, c: r::Config) -> bool {
    forall|s: A, x: int, y: int| c.commands.contains(x) && c.commands.contains(y)
        && independent(c, x, y) ==> #[trigger] commutes_at(m, s, x, y)
}
pub open spec fn commutes_at<A, R>(m: Machine<A, R>, s: A, x: int, y: int) -> bool {
    (m.step)((m.step)(s, x), y) == (m.step)((m.step)(s, y), x)
        && (m.output)((m.step)(s, y), x) == (m.output)(s, x)
}
pub open spec fn advance<A, R>(m: Machine<A, R>, e: Execution<A, R>, x: int) -> Execution<A, R> {
    Execution { state: (m.step)(e.state, x), outputs: e.outputs.insert(x, (m.output)(e.state, x)) }
}
pub open spec fn fold<A, R>(m: Machine<A, R>, e: Execution<A, R>, h: Seq<int>) -> Execution<A, R>
    decreases h.len(),
{
    if h.len() == 0 { e }
    else { advance(m, fold(m, e, h.drop_last()), h.last()) }
}
pub open spec fn run<A, R>(m: Machine<A, R>, h: Seq<int>) -> Execution<A, R> {
    fold(m, Execution { state: m.initial, outputs: Map::<int, R>::empty() }, h)
}
pub open spec fn commands_ok(c: r::Config, h: Seq<int>) -> bool {
    h.to_set().subset_of(c.commands)
}
pub open spec fn remove_at(h: Seq<int>, i: int) -> Seq<int> {
    h.subrange(0, i) + h.subrange(i + 1, h.len() as int)
}

pub proof fn fold_push<A, R>(m: Machine<A, R>, e: Execution<A, R>, h: Seq<int>, x: int)
    ensures fold(m, e, h.push(x)) == advance(m, fold(m, e, h), x),
{
    assert(h.push(x).drop_last() =~= h);
}
pub proof fn fold_concat<A, R>(m: Machine<A, R>, e: Execution<A, R>, p: Seq<int>, q: Seq<int>)
    ensures fold(m, e, p + q) == fold(m, fold(m, e, p), q),
    decreases q.len(),
{
    if q.len() == 0 { assert(p + q =~= p); }
    else {
        assert((p + q).drop_last() =~= p + q.drop_last());
        fold_concat(m, e, p, q.drop_last());
        assert((p + q).last() == q.last());
    }
}
pub proof fn commute_steps<A, R>(m: Machine<A, R>, c: r::Config, e: Execution<A, R>, x: int, y: int)
    requires r::config_ok(c), machine_ok(m, c), c.commands.contains(x), c.commands.contains(y),
        independent(c, x, y),
    ensures advance(m, advance(m, e, x), y) == advance(m, advance(m, e, y), x),
{
    assert(independent(c, y, x));
    assert(commutes_at(m, e.state, x, y));
    assert(commutes_at(m, e.state, y, x));
    assert((m.step)((m.step)(e.state, x), y) == (m.step)((m.step)(e.state, y), x));
    assert((m.output)((m.step)(e.state, y), x) == (m.output)(e.state, x));
    assert((m.output)((m.step)(e.state, x), y) == (m.output)(e.state, y));
    assert(advance(m, advance(m, e, x), y).outputs =~= advance(m, advance(m, e, y), x).outputs);
}
// Move x left across independent commands, preserving every returned value.
pub proof fn move_left<A, R>(m: Machine<A, R>, c: r::Config, e: Execution<A, R>, h: Seq<int>, x: int)
    requires r::config_ok(c), machine_ok(m, c), commands_ok(c, h), c.commands.contains(x),
        forall|y: int| h.contains(y) ==> independent(c, x, y),
    ensures fold(m, e, h.push(x)) == fold(m, advance(m, e, x), h),
    decreases h.len(),
{
    fold_push(m, e, h, x);
    if h.len() > 0 {
        let rest = h.drop_last();
        let y = h.last();
        assert(h.contains(y));
        assert(commands_ok(c, rest));
        assert forall|z: int| rest.contains(z) implies independent(c, x, z) by {
            assert(h.contains(z));
        }
        move_left(m, c, e, rest, x);
        fold_push(m, e, rest, x);
        commute_steps(m, c, fold(m, e, rest), x, y);
    }
}
pub proof fn move_selected_left<A, R>(m: Machine<A, R>, c: r::Config,
                                     e: Execution<A, R>, h: Seq<int>, i: int)
    requires r::config_ok(c), machine_ok(m, c), commands_ok(c, h), 0 <= i < h.len(),
        forall|j: int| 0 <= j < i ==> independent(c, h[i], h[j]),
    ensures fold(m, e, h) == fold(m, advance(m, e, h[i]), remove_at(h, i)),
{
    let p = h.subrange(0, i);
    let q = h.subrange(i + 1, h.len() as int);
    assert(h =~= p.push(h[i]) + q);
    assert(commands_ok(c, p));
    assert(c.commands.contains(h[i]));
    assert forall|x: int| p.contains(x) implies independent(c, h[i], x) by {
        let j = choose|j: int| 0 <= j < p.len() && p[j] == x;
        assert(h[j] == x);
    }
    move_left(m, c, e, p, h[i]);
    fold_concat(m, e, p.push(h[i]), q);
    fold_concat(m, advance(m, e, h[i]), p, q);
}
pub proof fn untouched_output<A, R>(m: Machine<A, R>, e: Execution<A, R>, h: Seq<int>, x: int)
    requires !h.contains(x),
    ensures fold(m, e, h).outputs.dom().contains(x) == e.outputs.dom().contains(x),
        e.outputs.dom().contains(x) ==> fold(m, e, h).outputs[x] == e.outputs[x],
    decreases h.len(),
{
    if h.len() > 0 {
        assert(!h.drop_last().contains(x));
        assert(h.last() != x);
        untouched_output(m, e, h.drop_last(), x);
    }
}
pub proof fn output_domain<A, R>(m: Machine<A, R>, e: Execution<A, R>, h: Seq<int>)
    ensures fold(m, e, h).outputs.dom() == e.outputs.dom().union(h.to_set()),
    decreases h.len(),
{
    if h.len() == 0 { assert(h.to_set() =~= Set::<int>::empty()); }
    else {
        output_domain(m, e, h.drop_last());
        assert(h =~= h.drop_last().push(h.last()));
        h.drop_last().lemma_push_to_set_commute(h.last());
        assert(h.to_set() =~= h.drop_last().to_set().insert(h.last()));
        assert(fold(m, e, h).outputs.dom() =~= e.outputs.dom().union(h.to_set()));
    }
}

pub proof fn append_before_independent<A, R>(m: Machine<A, R>, c: r::Config,
                                           p: Seq<int>, q: Seq<int>, x: int)
    requires r::config_ok(c), machine_ok(m, c), commands_ok(c, q), c.commands.contains(x),
        forall|y: int| q.contains(y) ==> independent(c, x, y),
    ensures run(m, p.push(x) + q) == run(m, (p + q).push(x)),
        run(m, p.push(x) + q).outputs.dom().contains(x),
        run(m, p.push(x) + q).outputs[x] == (m.output)(run(m, p).state, x),
{
    let e = Execution { state: m.initial, outputs: Map::<int, R>::empty() };
    fold_concat(m, e, p, q.push(x));
    fold_concat(m, e, p.push(x), q);
    fold_push(m, e, p, x);
    move_left(m, c, run(m, p), q, x);
    assert(p + q.push(x) =~= (p + q).push(x));
    assert(!q.contains(x));
    untouched_output(m, advance(m, run(m, p), x), q, x);
}

pub proof fn prefix_output<A, R>(m: Machine<A, R>, h: Seq<int>, n: int, x: int)
    requires h.no_duplicates(), 0 <= n <= h.len(), h.subrange(0, n).contains(x),
    ensures run(m, h).outputs.dom().contains(x), run(m, h.subrange(0, n)).outputs.dom().contains(x),
        run(m, h).outputs[x] == run(m, h.subrange(0, n)).outputs[x],
{
    let p = h.subrange(0, n);
    let q = h.subrange(n, h.len() as int);
    assert(h =~= p + q);
    assert(!q.contains(x)) by {
        if q.contains(x) {
            let i = choose|i: int| 0 <= i < p.len() && p[i] == x;
            let j = choose|j: int| 0 <= j < q.len() && q[j] == x;
            assert(h[i] == h[n + j]);
            assert(false);
        }
    }
    let e = Execution { state: m.initial, outputs: Map::<int, R>::empty() };
    output_domain(m, e, p);
    fold_concat(m, e, p, q);
    untouched_output(m, run(m, p), q, x);
}

} // verus!

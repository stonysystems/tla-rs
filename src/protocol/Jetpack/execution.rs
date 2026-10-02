//! Client-history refinement of Jetpack composed with ordering.rs's host API.
//! The linearization witness is ghost state. It is constructed by transitions;
//! neither linearizability nor execution agreement is a protocol action guard.
use vstd::prelude::*;
use super::recovery as r;
use super::ordering as o;
use super::application as a;

verus! {

#[verifier::reject_recursive_types(A)]
pub struct State<A, R> {
    pub order: o::State,
    pub base: Seq<int>,
    pub pending: Seq<int>,
    pub linear: Seq<int>,
    pub available: Map<int, R>,
    pub calls: Map<int, nat>,
    pub points: Map<int, nat>,
    pub replies: Map<int, R>,
    pub returns: Map<int, nat>,
    pub clock: nat,
    pub application: a::Machine<A, R>,
}
pub open spec fn without(h: Seq<int>, x: int) -> Seq<int> {
    if h.contains(x) { a::remove_at(h, choose|i: int| 0 <= i < h.len() && h[i] == x) }
    else { h }
}
pub open spec fn structure<A, R>(s: State<A, R>, c: r::Config) -> bool {
    &&& o::inv(s.order, c)
    &&& s.order.calls == s.calls.dom()
    &&& s.order.base == s.base.to_set() && s.order.pending == s.pending.to_set()
    &&& s.base.no_duplicates() && s.pending.no_duplicates() && s.linear.no_duplicates()
    &&& (s.base + s.pending).no_duplicates()
    &&& s.linear.to_set() == s.base.to_set().union(s.pending.to_set())
    &&& s.available.dom() == s.linear.to_set() && s.points.dom() == s.linear.to_set()
}
pub open spec fn timing<A, R>(s: State<A, R>) -> bool {
    &&& forall|x: int| #![trigger s.calls.dom().contains(x)] s.calls.dom().contains(x) ==> s.calls[x] < s.clock
    &&& forall|x: int| s.points.dom().contains(x) ==> s.calls.dom().contains(x)
        && s.calls[x] < s.points[x] < s.clock
    &&& forall|i: int, j: int| #![trigger s.linear[i], s.linear[j]] 0 <= i < j < s.linear.len() ==> s.points[s.linear[i]] < s.points[s.linear[j]]
    &&& s.replies.dom() == s.returns.dom() && s.replies.dom().subset_of(s.available.dom())
    &&& forall|x: int| s.replies.dom().contains(x) ==> #[trigger] returned_ok(s, x)
}
pub open spec fn returned_ok<A, R>(s: State<A, R>, x: int) -> bool {
    s.replies[x] == s.available[x] && s.points.dom().contains(x)
        && s.points[x] < s.returns[x] < s.clock
}
pub open spec fn inv<A, R>(s: State<A, R>, c: r::Config) -> bool {
    &&& structure(s, c) && timing(s)
    &&& conflict_order(s, c)
    &&& a::run(s.application, s.base + s.pending) == a::run(s.application, s.linear)
    &&& s.available == a::run(s.application, s.linear).outputs
}
pub open spec fn conflict_order<A, R>(s: State<A, R>, c: r::Config) -> bool {
    &&& forall|i: int, j: int| 0 <= i < j < s.base.len() && c.conflict.contains((s.base[i], s.base[j]))
        ==> s.points[s.base[i]] < s.points[s.base[j]]
    &&& forall|x: int, y: int| s.pending.contains(x) && s.base.contains(y) && c.conflict.contains((y, x))
        ==> s.points[y] < s.points[x]
}
pub open spec fn init<A, R>(s: State<A, R>, c: r::Config, proposers: Set<int>, m: a::Machine<A, R>) -> bool {
    &&& o::init(s.order, c, proposers)
    &&& s.base == Seq::<int>::empty() && s.pending == Seq::<int>::empty() && s.linear == Seq::<int>::empty()
    &&& s.available == Map::<int, R>::empty() && s.calls == Map::<int, nat>::empty()
    &&& s.points == Map::<int, nat>::empty() && s.replies == Map::<int, R>::empty()
    &&& s.returns == Map::<int, nat>::empty() && s.clock == 0 && s.application == m
}
pub open spec fn protocol_step<A, R>(s: State<A, R>, t: State<A, R>, c: r::Config, action: o::Action) -> bool {
    &&& o::next(s.order, t.order, c, action)
    &&& match action {
        o::Action::Invoke { command } => t == State {
            order: t.order, clock: s.clock + 1, calls: s.calls.insert(command, s.clock), ..s
        },
        o::Action::Fast { command } => t == State {
            order: t.order, clock: s.clock + 1,
            pending: s.pending.push(command), linear: s.linear.push(command),
            points: s.points.insert(command, s.clock),
            available: s.available.insert(command, (s.application.output)(a::run(s.application, s.base).state, command)), ..s
        },
        o::Action::Commit { command, .. } => t == State {
            order: t.order, clock: s.clock + 1, base: s.base.push(command), pending: without(s.pending, command),
            linear: if s.pending.contains(command) { s.linear } else { s.linear.push(command) },
            points: if s.pending.contains(command) { s.points } else { s.points.insert(command, s.clock) },
            available: s.available.insert(command, (s.application.output)(a::run(s.application, s.base).state, command)), ..s
        },
        _ => t == State { order: t.order, clock: s.clock + 1, ..s },
    }
}
pub open spec fn reply<A, R>(s: State<A, R>, t: State<A, R>, x: int) -> bool {
    &&& s.available.dom().contains(x) && !s.replies.dom().contains(x)
    &&& t == State { clock: s.clock + 1, replies: s.replies.insert(x, s.available[x]),
                    returns: s.returns.insert(x, s.clock), ..s }
}
pub enum Action {
    Protocol { action: o::Action }, Reply { command: int },
}
pub open spec fn next<A, R>(s: State<A, R>, t: State<A, R>, c: r::Config, action: Action) -> bool {
    match action {
        Action::Protocol { action } => protocol_step(s, t, c, action),
        Action::Reply { command } => reply(s, t, command),
    }
}

pub proof fn init_inv<A, R>(s: State<A, R>, c: r::Config, proposers: Set<int>, m: a::Machine<A, R>)
    requires r::config_ok(c), init(s, c, proposers, m),
    ensures inv(s, c),
{
    o::init_inv(s.order, c, proposers);
    assert(o::init(s.order, c, proposers));
    assert(s.order.calls == s.calls.dom());
    assert(s.order.base == s.base.to_set());
    assert(s.order.pending == s.pending.to_set());
    assert(s.base + s.pending =~= Seq::<int>::empty());
    assert(s.linear.to_set() =~= Set::<int>::empty());
    assert(s.linear.to_set() =~= s.base.to_set().union(s.pending.to_set()));
    assert(structure(s, c));
    assert(timing(s));
    assert(s.available == a::run(m, s.linear).outputs);
}

// Sequence facts used by the transition proofs, separate from semantics.
pub proof fn append_structure(h: Seq<int>, x: int)
    requires h.no_duplicates(), !h.contains(x),
    ensures h.push(x).no_duplicates(), h.push(x).to_set() == h.to_set().insert(x),
{
    h.lemma_push_to_set_commute(x);
}
pub proof fn remove_structure(h: Seq<int>, x: int)
    requires h.no_duplicates(),
    ensures without(h, x).no_duplicates(), without(h, x).to_set() == h.to_set().remove(x),
        !without(h, x).contains(x),
{
    if h.contains(x) {
        let i = choose|i: int| 0 <= i < h.len() && h[i] == x;
        let rest = a::remove_at(h, i);
        assert forall|j: int| 0 <= j < rest.len() implies rest[j] == h[if j < i { j } else { j + 1 }] by {};
        assert(rest.no_duplicates());
        assert(rest.to_set() =~= h.to_set().remove(x)) by {
            assert forall|y: int| h.contains(y) && y != x implies rest.contains(y) by {
                let j = choose|j: int| 0 <= j < h.len() && h[j] == y;
                assert(j != i);
                assert(rest[if j < i { j } else { j - 1 }] == y);
            }
        }
    }
}
pub proof fn disjoint_concat(p: Seq<int>, q: Seq<int>)
    requires p.no_duplicates(), q.no_duplicates(), p.to_set().disjoint(q.to_set()),
    ensures (p + q).no_duplicates(), (p + q).to_set() == p.to_set().union(q.to_set()),
{
    vstd::seq_lib::seq_to_set_distributes_over_add(p, q);
    assert forall|i: int, j: int| 0 <= i < j < (p + q).len() implies (p + q)[i] != (p + q)[j] by {
        if i < p.len() && j >= p.len() {
            assert(p.to_set().contains(p[i]));
            assert(q.to_set().contains(q[j - p.len()]));
        }
    }
}

pub proof fn frame_timing<A, R>(s: State<A, R>, t: State<A, R>)
    requires timing(s), s.linear == t.linear, s.points == t.points, s.replies == t.replies,
        s.returns == t.returns, s.clock < t.clock,
        s.calls.dom().subset_of(t.calls.dom()),
        forall|x: int| #![trigger t.calls[x]] #![trigger s.calls[x]] s.calls.dom().contains(x) ==> t.calls[x] == s.calls[x],
        forall|x: int| #![trigger t.calls.dom().contains(x)] t.calls.dom().contains(x) ==> t.calls[x] < t.clock,
        s.available == t.available,
    ensures timing(t),
{
    assert forall|x: int| t.points.dom().contains(x) implies t.calls.dom().contains(x)
        && t.calls[x] < t.points[x] < t.clock by {
        assert(s.calls.dom().contains(x) && s.calls[x] < s.points[x] < s.clock);
    }
    assert forall|x: int| #![trigger t.replies[x]] #![trigger t.available[x]] t.replies.dom().contains(x) implies t.replies[x] == t.available[x]
        && t.points.dom().contains(x) && t.points[x] < t.returns[x] < t.clock by {
        assert(returned_ok(s, x));
        assert(s.points[x] < s.returns[x] < s.clock);
    }
}
pub proof fn append_timing<A, R>(s: State<A, R>, t: State<A, R>, x: int, result: R)
    requires timing(s), s.points.dom() == s.linear.to_set(), s.available.dom() == s.linear.to_set(),
        !s.linear.contains(x), s.calls.dom().contains(x), t.clock > s.clock,
        t.linear == s.linear.push(x), t.points == s.points.insert(x, s.clock),
        t.calls == s.calls, t.available == s.available.insert(x, result),
        t.replies == s.replies, t.returns == s.returns,
    ensures timing(t),
{
    assert forall|y: int| t.points.dom().contains(y) implies t.calls.dom().contains(y)
        && t.calls[y] < t.points[y] < t.clock by {
        if y != x { assert(s.calls.dom().contains(y) && s.calls[y] < s.points[y] < s.clock); }
    }
    assert forall|i: int, j: int| #![trigger t.linear[i], t.linear[j]] 0 <= i < j < t.linear.len()
        implies t.points[t.linear[i]] < t.points[t.linear[j]] by {
        assert(s.linear.contains(s.linear[i]));
        assert(s.points.dom().contains(s.linear[i]));
        if j < s.linear.len() {
            assert(s.points[s.linear[i]] < s.points[s.linear[j]]);
            assert(s.linear.contains(s.linear[j]));
        } else { assert(s.points[s.linear[i]] < s.clock); }
    }
    assert forall|y: int| #![trigger t.replies[y]] #![trigger t.available[y]] t.replies.dom().contains(y) implies t.replies[y] == t.available[y]
        && t.points.dom().contains(y) && t.points[y] < t.returns[y] < t.clock by {
        assert(s.available.dom().contains(y));
        assert(y != x);
        assert(returned_ok(s, y));
        assert(s.points[y] < s.returns[y] < s.clock);
    }
}

pub proof fn fast_preserves<A, R>(s: State<A, R>, t: State<A, R>, c: r::Config, x: int)
    requires r::config_ok(c), a::machine_ok(s.application, c), inv(s, c),
        protocol_step(s, t, c, o::Action::Fast { command: x }),
    ensures inv(t, c),
{
    o::fast_preserves(s.order, t.order, c, x);
    linear_membership(s, c, x);
    assert(o::fast(s.order, t.order, c, x));
    assert(!s.linear.contains(x));
    assert(c.commands.contains(x));
    assert(a::commands_ok(c, s.pending));
    assert forall|y: int| s.pending.contains(y) implies a::independent(c, x, y) by {
        assert(s.order.pending.contains(y));
    }
    a::append_before_independent(s.application, c, s.base, s.pending, x);
    let e = a::Execution { state: s.application.initial, outputs: Map::<int, R>::empty() };
    a::fold_push(s.application, e, s.linear, x);
    a::fold_push(s.application, e, s.base + s.pending, x);
    assert(s.base + s.pending.push(x) =~= (s.base + s.pending).push(x));
    assert(a::run(s.application, t.base + t.pending) == a::run(s.application, t.linear));
    assert(a::run(s.application, t.linear).outputs[x]
        == (s.application.output)(a::run(s.application, s.base).state, x));
    assert(t.available =~= a::run(s.application, t.linear).outputs);
    append_structure(s.pending, x);
    append_structure(s.linear, x);
    disjoint_concat(t.base, t.pending);
    assert(t.linear.to_set() =~= t.base.to_set().union(t.pending.to_set()));
    assert(t.points.dom() =~= t.linear.to_set());
    assert(t.available.dom() =~= t.linear.to_set());
    append_timing(s, t, x, (s.application.output)(a::run(s.application, s.base).state, x));
    fast_order(s, t, c, x);
}

pub proof fn commit_preserves<A, R>(s: State<A, R>, t: State<A, R>, c: r::Config, x: int, from_recovery: bool)
    requires r::config_ok(c), a::machine_ok(s.application, c), inv(s, c),
        protocol_step(s, t, c, o::Action::Commit { command: x, from_recovery }),
    ensures inv(t, c),
{
    assert(o::commit(s.order, t.order, c, x, from_recovery));
    assert(!s.order.base.contains(x));
    linear_membership(s, c, x);
    o::commit_respects_fast(s.order, t.order, c, x, from_recovery);
    o::growing_base_preserves(s.order, t.order, c);
    let m = s.application;
    let e = a::Execution { state: m.initial, outputs: Map::<int, R>::empty() };
    let result = (m.output)(a::run(m, s.base).state, x);
    assert(a::commands_ok(c, s.pending));
    assert(c.commands.contains(x));
    a::fold_push(m, e, s.base, x);
    if s.pending.contains(x) {
        let i = choose|i: int| 0 <= i < s.pending.len() && s.pending[i] == x;
        assert forall|j: int| #![trigger s.pending[j]] 0 <= j < i implies a::independent(c, s.pending[i], s.pending[j]) by {
            assert(s.pending[i] != s.pending[j]);
            assert(s.order.pending.contains(s.pending[i]) && s.order.pending.contains(s.pending[j]));
        }
        a::move_selected_left(m, c, a::run(m, s.base), s.pending, i);
        a::fold_concat(m, e, s.base, s.pending);
        a::fold_concat(m, e, t.base, t.pending);
        assert(a::run(m, t.base + t.pending) == a::run(m, s.linear));
        remove_structure(s.pending, x);
        a::untouched_output(m, a::run(m, t.base), t.pending, x);
        assert(s.available[x] == result);
        assert(t.available =~= s.available);
        frame_timing(s, t);
    } else {
        assert(!s.linear.contains(x));
        assert forall|y: int| s.pending.contains(y) implies a::independent(c, x, y) by {
            assert(s.order.pending.contains(y));
        }
        a::append_before_independent(m, c, s.base, s.pending, x);
        a::fold_push(m, e, s.linear, x);
        a::fold_push(m, e, s.base + s.pending, x);
        assert(a::run(m, t.base + t.pending) == a::run(m, t.linear));
        assert(a::run(m, t.linear).outputs[x] == result);
        assert(t.available =~= a::run(m, t.linear).outputs);
        append_structure(s.linear, x);
        append_timing(s, t, x, result);
    }
    append_structure(s.base, x);
    remove_structure(s.pending, x);
    disjoint_concat(t.base, t.pending);
    assert(t.linear.to_set() =~= t.base.to_set().union(t.pending.to_set()));
    assert(t.points.dom() =~= t.linear.to_set());
    assert(t.available.dom() =~= t.linear.to_set());
    commit_order(s, t, c, x, from_recovery);
}

pub proof fn protocol_preserves<A, R>(s: State<A, R>, t: State<A, R>, c: r::Config, action: o::Action)
    requires r::config_ok(c), a::machine_ok(s.application, c), inv(s, c), protocol_step(s, t, c, action),
    ensures inv(t, c), t.application == s.application,
{
    o::step_preserves(s.order, t.order, c, action);
    match action {
        o::Action::Fast { command } => fast_preserves(s, t, c, command),
        o::Action::Commit { command, from_recovery } => commit_preserves(s, t, c, command, from_recovery),
        o::Action::Invoke { command } => {
            assert(t.order.calls =~= t.calls.dom());
            assert forall|x: int| #![trigger t.calls.dom().contains(x)] t.calls.dom().contains(x) implies t.calls[x] < t.clock by {
                if x != command { assert(s.calls[x] < s.clock); }
            }
            frame_timing(s, t);
        },
        _ => { frame_timing(s, t); },
    }
}
pub proof fn reply_preserves<A, R>(s: State<A, R>, t: State<A, R>, c: r::Config, x: int)
    requires inv(s, c), reply(s, t, x),
    ensures inv(t, c),
{
    assert(t.replies.dom() =~= t.returns.dom());
    assert forall|y: int| #![trigger t.replies[y]] #![trigger t.available[y]] t.replies.dom().contains(y) implies t.replies[y] == t.available[y]
        && t.points.dom().contains(y) && t.points[y] < t.returns[y] < t.clock by {
        if y == x { assert(s.points.dom().contains(x)); assert(s.points[x] < s.clock); }
        else { assert(returned_ok(s, y)); assert(s.points[y] < s.returns[y] < s.clock); }
    }
}
pub proof fn step_preserves<A, R>(s: State<A, R>, t: State<A, R>, c: r::Config, action: Action)
    requires r::config_ok(c), a::machine_ok(s.application, c), inv(s, c), next(s, t, c, action),
    ensures inv(t, c), t.application == s.application,
{
    match action {
        Action::Protocol { action } => protocol_preserves(s, t, c, action),
        Action::Reply { command } => reply_preserves(s, t, c, command),
    }
}

// Standard finite-history linearizability: complete some pending invocations,
// then find a legal sequential execution containing every returned operation,
// with identical results and with response-before-invocation order preserved.
pub open spec fn linearization<A, R>(s: State<A, R>, h: Seq<int>) -> bool {
    &&& h.no_duplicates() && h.to_set().subset_of(s.calls.dom())
    &&& s.replies.dom().subset_of(h.to_set())
    &&& forall|x: int| #![trigger s.replies[x]] s.replies.dom().contains(x)
        ==> a::run(s.application, h).outputs.dom().contains(x)
            && a::run(s.application, h).outputs[x] == s.replies[x]
    &&& forall|i: int, j: int| #![trigger h[i], h[j]] 0 <= i < h.len() && 0 <= j < h.len()
        && s.returns.dom().contains(h[i]) && s.returns[h[i]] < s.calls[h[j]] ==> i < j
}
pub proof fn invariant_linearizes<A, R>(s: State<A, R>, c: r::Config)
    requires inv(s, c),
    ensures linearization(s, s.linear), exists|h: Seq<int>| linearization(s, h),
{
    assert(s.linear.to_set().subset_of(s.calls.dom()));
    assert forall|x: int| #![trigger s.replies[x]] s.replies.dom().contains(x) implies
        a::run(s.application, s.linear).outputs.dom().contains(x)
        && a::run(s.application, s.linear).outputs[x] == s.replies[x] by {
        assert(returned_ok(s, x));
    }
    assert forall|i: int, j: int| #![trigger s.linear[i], s.linear[j]] 0 <= i < s.linear.len() && 0 <= j < s.linear.len()
        && s.returns.dom().contains(s.linear[i]) && s.returns[s.linear[i]] < s.calls[s.linear[j]]
        implies i < j by {
        let x = s.linear[i]; let y = s.linear[j];
        assert(returned_ok(s, x));
        assert(s.points.dom().contains(x) && s.points.dom().contains(y));
        assert(s.points[x] < s.returns[x]);
        assert(s.calls[y] < s.points[y]);
        if j < i { assert(s.points[y] < s.points[x]); }
    }
    assert(linearization(s, s.linear));
}

pub open spec fn behavior<A, R>(states: Seq<State<A, R>>, actions: Seq<Action>, c: r::Config,
                                proposers: Set<int>, m: a::Machine<A, R>) -> bool {
    &&& states.len() == actions.len() + 1 && init(states[0], c, proposers, m)
    &&& forall|k: int| 0 <= k < actions.len() ==> #[trigger] next(states[k], states[k + 1], c, actions[k])
}
pub proof fn reachable_inv<A, R>(states: Seq<State<A, R>>, actions: Seq<Action>, c: r::Config,
                                proposers: Set<int>, m: a::Machine<A, R>, k: int)
    requires r::config_ok(c), a::machine_ok(m, c), behavior(states, actions, c, proposers, m),
        0 <= k < states.len(),
    ensures inv(states[k], c), states[k].application == m,
    decreases k,
{
    if k == 0 { init_inv(states[0], c, proposers, m); }
    else {
        reachable_inv(states, actions, c, proposers, m, k - 1);
        assert(next(states[k - 1], states[(k - 1) + 1], c, actions[k - 1]));
        step_preserves(states[k - 1], states[k], c, actions[k - 1]);
    }
}
pub proof fn history_linearizable<A, R>(states: Seq<State<A, R>>, actions: Seq<Action>, c: r::Config,
                                       proposers: Set<int>, m: a::Machine<A, R>, k: int)
    requires r::config_ok(c), a::machine_ok(m, c), behavior(states, actions, c, proposers, m),
        0 <= k < states.len(),
    ensures exists|h: Seq<int>| linearization(states[k], h),
{
    reachable_inv(states, actions, c, proposers, m, k);
    invariant_linearizes(states[k], c);
}

pub proof fn fast_order<A, R>(s: State<A, R>, t: State<A, R>, c: r::Config, x: int)
    requires inv(s, c), protocol_step(s, t, c, o::Action::Fast { command: x }),
    ensures conflict_order(t, c),
{
    assert(!s.base.contains(x));
    assert forall|i: int, j: int| 0 <= i < j < t.base.len() && c.conflict.contains((t.base[i], t.base[j]))
        implies t.points[t.base[i]] < t.points[t.base[j]] by {
        assert(s.points[s.base[i]] < s.points[s.base[j]]);
        assert(s.base.contains(s.base[i]) && s.base.contains(s.base[j]));
    }
    assert forall|y: int, z: int| t.pending.contains(y) && t.base.contains(z) && c.conflict.contains((z, y))
        implies t.points[z] < t.points[y] by {
        assert(z != x);
        if y == x {
            assert(s.points.dom().contains(z));
            assert(s.points[z] < s.clock);
        } else { assert(s.points[z] < s.points[y]); }
    }
}
pub proof fn commit_order<A, R>(s: State<A, R>, t: State<A, R>, c: r::Config, x: int, from_recovery: bool)
    requires r::config_ok(c), inv(s, c), protocol_step(s, t, c, o::Action::Commit { command: x, from_recovery }),
    ensures conflict_order(t, c),
{
    o::commit_respects_fast(s.order, t.order, c, x, from_recovery);
    remove_structure(s.pending, x);
    assert(!s.base.contains(x));
    assert forall|i: int, j: int| 0 <= i < j < t.base.len() && c.conflict.contains((t.base[i], t.base[j]))
        implies t.points[t.base[i]] < t.points[t.base[j]] by {
        assert(s.base.contains(s.base[i]));
        if j < s.base.len() {
            assert(s.base.contains(s.base[j]));
            assert(s.points[s.base[i]] < s.points[s.base[j]]);
        } else if s.pending.contains(x) {
            assert(s.points[s.base[i]] < s.points[x]);
        } else {
            assert(s.points.dom().contains(s.base[i]));
            assert(s.points[s.base[i]] < s.clock);
        }
    }
    assert forall|y: int, z: int| t.pending.contains(y) && t.base.contains(z) && c.conflict.contains((z, y))
        implies t.points[z] < t.points[y] by {
        assert(s.pending.contains(y) && y != x);
        if z == x {
            assert(a::independent(c, x, y));
            assert(false);
        } else { assert(s.points[z] < s.points[y]); }
    }
}

pub proof fn fast_base_order_agreement<A, R>(s: State<A, R>, c: r::Config,
                                           i: int, j: int, p: int, q: int)
    requires inv(s, c), 0 <= i < j < s.base.len(), c.conflict.contains((s.base[i], s.base[j])),
        0 <= p < s.linear.len(), 0 <= q < s.linear.len(),
        s.linear[p] == s.base[i], s.linear[q] == s.base[j],
    ensures p < q,
{
    assert(s.points[s.base[i]] < s.points[s.base[j]]);
    if q < p { assert(s.points[s.linear[q]] < s.points[s.linear[p]]); }
}
pub proof fn base_prefix_execution_consistent<A, R>(s: State<A, R>, c: r::Config, n: int, x: int)
    requires inv(s, c), 0 <= n <= s.base.len(), s.base.subrange(0, n).contains(x),
    ensures a::run(s.application, s.base.subrange(0, n)).outputs.dom().contains(x),
        s.available.dom().contains(x),
        a::run(s.application, s.base.subrange(0, n)).outputs[x] == s.available[x],
{
    assert((s.base + s.pending).subrange(0, n) =~= s.base.subrange(0, n));
    a::prefix_output(s.application, s.base + s.pending, n, x);
}
pub proof fn replica_execution_agreement<A, R>(s: State<A, R>, c: r::Config, n: int, k: int, x: int)
    requires inv(s, c), 0 <= n <= s.base.len(), 0 <= k <= s.base.len(),
        s.base.subrange(0, n).contains(x), s.base.subrange(0, k).contains(x),
    ensures a::run(s.application, s.base.subrange(0, n)).outputs[x]
            == a::run(s.application, s.base.subrange(0, k)).outputs[x],
        s.replies.dom().contains(x) ==> a::run(s.application, s.base.subrange(0, n)).outputs[x] == s.replies[x],
{
    base_prefix_execution_consistent(s, c, n, x);
    base_prefix_execution_consistent(s, c, k, x);
    if s.replies.dom().contains(x) { assert(returned_ok(s, x)); }
}
pub proof fn drained_state_agreement<A, R>(s: State<A, R>, c: r::Config)
    requires inv(s, c), s.pending.len() == 0,
    ensures a::run(s.application, s.base) == a::run(s.application, s.linear),
{
    assert(s.base + s.pending =~= s.base);
}

pub proof fn linear_membership<A, R>(s: State<A, R>, c: r::Config, x: int)
    requires structure(s, c),
    ensures s.linear.contains(x) == (s.order.base.contains(x) || s.order.pending.contains(x)),
        s.pending.contains(x) == s.order.pending.contains(x),
{
    s.linear.to_set_ensures();
    s.base.to_set_ensures();
    s.pending.to_set_ensures();
    assert(s.linear.to_set().contains(x) == s.linear.contains(x));
    assert(s.base.to_set().contains(x) == s.base.contains(x));
    assert(s.pending.to_set().contains(x) == s.pending.contains(x));
    assert(s.linear.to_set().contains(x) == (s.base.to_set().contains(x) || s.pending.to_set().contains(x)));
}

pub proof fn step_preserves_observations<A, R>(s: State<A, R>, t: State<A, R>, c: r::Config, action: Action)
    requires r::config_ok(c), a::machine_ok(s.application, c), inv(s, c), next(s, t, c, action),
    ensures inv(t, c), t.application == s.application, o::prefix(s.base, t.base),
        s.replies.dom().subset_of(t.replies.dom()),
        forall|x: int| #![trigger t.replies[x]] #![trigger s.replies[x]] s.replies.dom().contains(x) ==> t.replies[x] == s.replies[x],
{
    step_preserves(s, t, c, action);
    match action {
        Action::Protocol { action } => {
            match action {
                o::Action::Commit { .. } => {},
                _ => {},
            }
        },
        Action::Reply { command } => {
            assert forall|x: int| #![trigger t.replies[x]] #![trigger s.replies[x]] s.replies.dom().contains(x) implies t.replies[x] == s.replies[x] by {
                assert(x != command);
            }
        },
    }
}
pub proof fn observations_persist<A, R>(states: Seq<State<A, R>>, actions: Seq<Action>, c: r::Config,
                                       proposers: Set<int>, m: a::Machine<A, R>, i: int, j: int)
    requires r::config_ok(c), a::machine_ok(m, c), behavior(states, actions, c, proposers, m),
        0 <= i <= j < states.len(),
    ensures states[i].replies.dom().subset_of(states[j].replies.dom()),
        forall|x: int| #![trigger states[j].replies[x]] #![trigger states[i].replies[x]] states[i].replies.dom().contains(x) ==> states[j].replies[x] == states[i].replies[x],
        o::prefix(states[i].base, states[j].base),
    decreases j - i,
{
    if i < j {
        observations_persist(states, actions, c, proposers, m, i, j - 1);
        reachable_inv(states, actions, c, proposers, m, j - 1);
        assert(next(states[j - 1], states[(j - 1) + 1], c, actions[j - 1]));
        step_preserves_observations(states[j - 1], states[j], c, actions[j - 1]);
        assert forall|x: int| #![trigger states[j].replies[x]] #![trigger states[i].replies[x]] states[i].replies.dom().contains(x)
            implies states[j].replies[x] == states[i].replies[x] by {
            assert(states[j - 1].replies.dom().contains(x));
            assert(states[j - 1].replies[x] == states[i].replies[x]);
        }
        assert forall|n: int| 0 <= n < states[i].base.len()
            implies states[i].base[n] == states[j].base[n] by {
            assert(states[i].base[n] == states[j - 1].base[n]);
        }
    }
}
// A result returned on either path must match a replica executing this command
// later, including after any number of recovery attempts and normal views.
pub proof fn execution_consistency_over_time<A, R>(states: Seq<State<A, R>>, actions: Seq<Action>, c: r::Config,
                                                  proposers: Set<int>, m: a::Machine<A, R>,
                                                  i: int, j: int, n: int, x: int)
    requires r::config_ok(c), a::machine_ok(m, c), behavior(states, actions, c, proposers, m),
        0 <= i <= j < states.len(), states[i].replies.dom().contains(x),
        0 <= n <= states[j].base.len(), states[j].base.subrange(0, n).contains(x),
    ensures a::run(m, states[j].base.subrange(0, n)).outputs[x] == states[i].replies[x],
{
    observations_persist(states, actions, c, proposers, m, i, j);
    reachable_inv(states, actions, c, proposers, m, j);
    base_prefix_execution_consistent(states[j], c, n, x);
    assert(returned_ok(states[j], x));
}
pub proof fn reachable_order_agreement<A, R>(states: Seq<State<A, R>>, actions: Seq<Action>, c: r::Config,
                                            proposers: Set<int>, m: a::Machine<A, R>, k: int,
                                            i: int, j: int, p: int, q: int)
    requires r::config_ok(c), a::machine_ok(m, c), behavior(states, actions, c, proposers, m),
        0 <= k < states.len(), 0 <= i < j < states[k].base.len(),
        c.conflict.contains((states[k].base[i], states[k].base[j])),
        0 <= p < states[k].linear.len(), 0 <= q < states[k].linear.len(),
        states[k].linear[p] == states[k].base[i], states[k].linear[q] == states[k].base[j],
    ensures p < q,
{
    reachable_inv(states, actions, c, proposers, m, k);
    fast_base_order_agreement(states[k], c, i, j, p, q);
}

} // verus!

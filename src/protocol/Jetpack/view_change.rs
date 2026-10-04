//! Conditional composition with a durable base protocol, Jetpack Phase 3.
//! Committing a recovery batch and its marker is one abstract base operation.
//! Election targets may change repeatedly before a normal view is installed.
//! Original-path durability is an explicit contract of this model; base-log
//! recovery, within-view ordering, execution results and liveness are not proved.
use vstd::prelude::*;
use super::recovery as r;

verus! {

pub struct Certificate { pub ballot: int, pub value: Set<int> }
pub struct State {
    pub normal: int,
    pub target: int,
    pub layers: Map<int, r::State>,
    pub markers: Map<int, Certificate>,
    pub durable: Set<int>,
}

pub open spec fn inv(s: State, c: r::Config) -> bool {
    &&& 0 <= s.normal <= s.target
    &&& !s.markers.dom().contains(s.normal)
    &&& s.layers.dom() == s.markers.dom().insert(s.normal)
    &&& s.durable.subset_of(c.commands)
    &&& forall|v: int| #![trigger s.layers.dom().contains(v)] s.layers.dom().contains(v) ==> 0 <= v <= s.normal && r::inv(s.layers[v], c)
    &&& forall|v: int| #![trigger s.markers.dom().contains(v)] s.markers.dom().contains(v) ==>
        v < s.normal && s.markers[v].value.subset_of(s.durable)
        && r::chosen(s.layers[v], c, s.markers[v].ballot, s.markers[v].value)
}
pub open spec fn init(s: State, c: r::Config) -> bool {
    &&& s.normal == 0 && s.target == 0
    &&& s.layers.dom() == set![0int] && r::init(s.layers[0], c)
    &&& s.markers == Map::<int, Certificate>::empty()
    &&& s.durable == Set::<int>::empty()
}
pub open spec fn elect(s: State, t: State, target: int) -> bool {
    target > s.target && t == State { target, ..s }
}
pub open spec fn layer_step(s: State, t: State, c: r::Config,
                           view: int, after: r::State, action: r::Action) -> bool {
    &&& s.layers.dom().contains(view) && r::next(s.layers[view], after, c, action)
    &&& t == State { layers: s.layers.insert(view, after), ..s }
}
// Abstract completion of submitting the recovery batch through the base
// protocol. An empty batch still installs a marker, corresponding to the
// paper's no-op. There is no ordinary-admission path into the target view.
pub open spec fn commit_marker(s: State, t: State, c: r::Config,
                              b: int, value: Set<int>, fresh: r::State) -> bool {
    &&& s.target > s.normal && r::chosen(s.layers[s.normal], c, b, value)
    &&& r::init(fresh, c)
    &&& t == State {
        normal: s.target,
        layers: s.layers.insert(s.target, fresh),
        markers: s.markers.insert(s.normal, Certificate { ballot: b, value }),
        durable: s.durable.union(value), ..s
    }
}
pub open spec fn admit_command(s: State, t: State, c: r::Config, x: int) -> bool {
    &&& s.target == s.normal && c.commands.contains(x)
    &&& t == State { durable: s.durable.insert(x), ..s }
}
pub enum Action {
    Elect { target: int },
    Layer { view: int, after: r::State, action: r::Action },
    CommitMarker { ballot: int, value: Set<int>, fresh: r::State },
    Admit { command: int },
    Stutter,
}
pub open spec fn next(s: State, t: State, c: r::Config, action: Action) -> bool {
    match action {
        Action::Elect { target } => elect(s, t, target),
        Action::Layer { view, after, action } => layer_step(s, t, c, view, after, action),
        Action::CommitMarker { ballot, value, fresh } => commit_marker(s, t, c, ballot, value, fresh),
        Action::Admit { command } => admit_command(s, t, c, command),
        Action::Stutter => t == s,
    }
}

pub proof fn init_inv(s: State, c: r::Config)
    requires r::config_ok(c), init(s, c),
    ensures inv(s, c),
{
    r::init_inv(s.layers[0], c);
    assert(s.layers.dom() =~= s.markers.dom().insert(s.normal));
}
pub proof fn layer_preserves(s: State, t: State, c: r::Config,
                            view: int, after: r::State, action: r::Action)
    requires r::config_ok(c), inv(s, c), layer_step(s, t, c, view, after, action),
    ensures inv(t, c),
{
    r::step_preserves(s.layers[view], after, c, action);
    assert(t.layers.dom() =~= s.layers.dom());
    assert forall|v: int| #![trigger t.layers.dom().contains(v)] t.layers.dom().contains(v)
        implies 0 <= v <= t.normal && r::inv(t.layers[v], c) by {
        if v != view { assert(r::inv(s.layers[v], c)); }
    }
    assert forall|v: int| #![trigger t.markers.dom().contains(v)] t.markers.dom().contains(v) implies
        v < t.normal && t.markers[v].value.subset_of(t.durable)
        && r::chosen(t.layers[v], c, t.markers[v].ballot, t.markers[v].value) by {
        assert(r::chosen(s.layers[v], c, s.markers[v].ballot, s.markers[v].value));
        if v == view {
            r::certificates_monotone(s.layers[v], after, c,
                                     s.markers[v].ballot, s.markers[v].value, 0);
        }
    }
}
pub proof fn marker_preserves(s: State, t: State, c: r::Config,
                             b: int, value: Set<int>, fresh: r::State)
    requires r::config_ok(c), inv(s, c), commit_marker(s, t, c, b, value, fresh),
    ensures inv(t, c),
{
    r::init_inv(fresh, c);
    let q = choose|q: Set<int>| r::quorum(c, q)
        && forall|a: int| #![trigger q.contains(a)] q.contains(a) ==> r::voted(s.layers[s.normal], a, b, value);
    r::quorum_intersection(c, q, q);
    let a = choose|a: int| q.contains(a);
    assert(s.layers.dom().contains(s.normal));
    assert(r::inv(s.layers[s.normal], c));
    assert(r::voted(s.layers[s.normal], a, b, value));
    assert(s.layers[s.normal].proposals.dom().contains(b));
    assert(s.layers[s.normal].proposals[b] == value);
    assert(r::candidate(s.layers[s.normal], c, value));
    let origin = choose|q: Set<int>| #![trigger r::quorum(c, q)] r::quorum(c, q) && q.subset_of(s.layers[s.normal].frozen)
        && value == r::selected(c, s.layers[s.normal].logs, q);
    assert(value.subset_of(c.commands));
    assert(!s.layers.dom().contains(s.target));
    assert(t.layers.dom() =~= t.markers.dom().insert(t.normal));
    assert forall|v: int| #![trigger t.layers.dom().contains(v)] t.layers.dom().contains(v)
        implies 0 <= v <= t.normal && r::inv(t.layers[v], c) by {
        if v != s.target { assert(r::inv(s.layers[v], c)); }
    }
    assert forall|v: int| #![trigger t.markers.dom().contains(v)] t.markers.dom().contains(v) implies
        v < t.normal && t.markers[v].value.subset_of(t.durable)
        && r::chosen(t.layers[v], c, t.markers[v].ballot, t.markers[v].value) by {
        if v != s.normal {
            assert(s.markers[v].value.subset_of(s.durable));
            assert(r::chosen(s.layers[v], c, s.markers[v].ballot, s.markers[v].value));
        }
    }
}
pub proof fn step_preserves(s: State, t: State, c: r::Config, action: Action)
    requires r::config_ok(c), inv(s, c), next(s, t, c, action),
    ensures inv(t, c), s.durable.subset_of(t.durable), s.normal <= t.normal,
{
    match action {
        Action::Elect { target } => {},
        Action::Layer { view, after, action } => layer_preserves(s, t, c, view, after, action),
        Action::CommitMarker { ballot, value, fresh } => marker_preserves(s, t, c, ballot, value, fresh),
        Action::Admit { command } => {
            assert forall|v: int| #![trigger t.markers.dom().contains(v)] t.markers.dom().contains(v) implies
                v < t.normal && t.markers[v].value.subset_of(t.durable)
                && r::chosen(t.layers[v], c, t.markers[v].ballot, t.markers[v].value) by {
                assert(s.markers[v].value.subset_of(s.durable));
            }
        },
        Action::Stutter => {},
    }
}

// Old certificates can be delivered after a newer view is active. Their
// commands are already durable because each old instance retains its chosen
// recovery set, including throughout later elections and recovery retries.
pub proof fn prior_view_fast_is_durable(s: State, c: r::Config, view: int, x: int)
    requires r::config_ok(c), inv(s, c), s.layers.dom().contains(view), view < s.normal,
        r::fast_committed(s.layers[view], c, x),
    ensures s.durable.contains(x),
{
    assert(s.markers.dom().contains(view));
    let marker = s.markers[view];
    r::recovery_complete_and_safe(s.layers[view], c, marker.ballot, marker.value, x);
}
pub open spec fn behavior(states: Seq<State>, actions: Seq<Action>, c: r::Config) -> bool {
    &&& states.len() == actions.len() + 1 && init(states[0], c)
    &&& forall|k: int| 0 <= k < actions.len()
        ==> #[trigger] next(states[k], states[k + 1], c, actions[k])
}
pub proof fn reachable_inv(states: Seq<State>, actions: Seq<Action>, c: r::Config, k: int)
    requires r::config_ok(c), behavior(states, actions, c), 0 <= k < states.len(),
    ensures inv(states[k], c),
    decreases k,
{
    if k == 0 { init_inv(states[0], c); }
    else {
        reachable_inv(states, actions, c, k - 1);
        assert(next(states[k - 1], states[(k - 1) + 1], c, actions[k - 1]));
        step_preserves(states[k - 1], states[k], c, actions[k - 1]);
    }
}
pub proof fn admission_after_recovery(states: Seq<State>, actions: Seq<Action>, c: r::Config,
                                     k: int, old_view: int, old_command: int, new_command: int)
    requires r::config_ok(c), behavior(states, actions, c), 0 <= k < actions.len(),
        actions[k] == (Action::Admit { command: new_command }),
        states[k].layers.dom().contains(old_view), old_view < states[k].normal,
        r::fast_committed(states[k].layers[old_view], c, old_command),
    ensures states[k].durable.contains(old_command), states[k].target == states[k].normal,
{
    reachable_inv(states, actions, c, k);
    prior_view_fast_is_durable(states[k], c, old_view, old_command);
    assert(next(states[k], states[k + 1], c, actions[k]));
}

} // verus!

//! History-level model of van Renesse and Schneider, OSDI 2004, Section 3.1.
//! The master and its reconfiguration handshake are abstracted as atomic steps.
//! This is a specification and safety proof, not generated executable code.
use vstd::prelude::*;

verus! {

pub struct State {
    pub history: Seq<Seq<int>>,
    pub alive: Seq<bool>,
    // Fresh request identities, not application values. Equal values are allowed
    // when carried by different requests in an application refinement.
    pub submitted: Set<int>,
}

pub open spec fn prefix(a: Seq<int>, b: Seq<int>) -> bool {
    a.len() <= b.len()
        && forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] == b[k]
}

pub open spec fn committed(s: State) -> Seq<int> {
    s.history[s.history.len() - 1]
}

pub open spec fn inv(s: State) -> bool {
    &&& s.history.len() > 0
    &&& s.alive.len() == s.history.len()
    &&& forall|i: int, j: int| 0 <= i <= j < s.history.len()
        ==> #[trigger] prefix(s.history[j], s.history[i])
    &&& forall|i: int, k: int| 0 <= i < s.history.len()
        && 0 <= k < s.history[i].len()
        ==> s.submitted.contains(#[trigger] s.history[i][k])
    &&& forall|i: int, k: int, l: int| 0 <= i < s.history.len()
        && 0 <= k < l < s.history[i].len()
        ==> #[trigger] s.history[i][k] != #[trigger] s.history[i][l]
}

pub open spec fn init(s: State, n: nat) -> bool {
    &&& n > 0
    &&& s.history == Seq::new(n, |i: int| Seq::<int>::empty())
    &&& s.alive == Seq::new(n, |i: int| true)
    &&& s.submitted == Set::<int>::empty()
}

pub open spec fn write(s: State, t: State, request: int) -> bool {
    &&& s.history.len() > 0
    &&& s.alive.len() == s.history.len()
    &&& s.alive[0]
    &&& !s.submitted.contains(request)
    &&& t.history == s.history.update(0, s.history[0].push(request))
    &&& t.alive == s.alive
    &&& t.submitted == s.submitted.insert(request)
}

// One in-order delivery on the reliable FIFO channel from i-1 to i.
// The sender may already have failed after sending. Its immutable history
// records the payloads that could be in transit. Channels are abstracted here.
pub open spec fn forward(s: State, t: State, i: int) -> bool {
    &&& 0 < i < s.history.len()
    &&& s.alive.len() == s.history.len()
    &&& s.alive[i]
    &&& s.history[i].len() < s.history[i - 1].len()
    &&& t.history == s.history.update(i,
        s.history[i].push(s.history[i - 1][s.history[i].len() as int]))
    &&& t.alive == s.alive
    &&& t.submitted == s.submitted
}

pub open spec fn crash(s: State, t: State, i: int) -> bool {
    &&& 0 <= i < s.history.len()
    &&& s.alive.len() == s.history.len()
    &&& t.history == s.history
    &&& t.alive == s.alive.update(i, false)
    &&& t.submitted == s.submitted
}

pub open spec fn remove_index<A>(a: Seq<A>, i: int) -> Seq<A> {
    Seq::new((a.len() - 1) as nat, |j: int| a[if j < i { j } else { j + 1 }])
}

// One globally installed configuration, supplied by the paper's master.
// False suspicions, competing configurations and the notification handshake
// are not modeled by this atomic transition.
pub open spec fn remove_failed(s: State, t: State, i: int) -> bool {
    &&& s.history.len() > 1
    &&& s.alive.len() == s.history.len()
    &&& 0 <= i < s.history.len()
    &&& !s.alive[i]
    &&& t.history == remove_index(s.history, i)
    &&& t.alive == remove_index(s.alive, i)
    &&& t.submitted == s.submitted
}

// Atomic completion of transfer to a fresh tail, after it has caught up.
pub open spec fn extend(s: State, t: State) -> bool {
    &&& s.history.len() > 0
    &&& s.alive.len() == s.history.len()
    &&& s.alive[s.alive.len() - 1]
    &&& t.history == s.history.push(committed(s))
    &&& t.alive == s.alive.push(true)
    &&& t.submitted == s.submitted
}

pub enum Action {
    Write { request: int },
    Forward { node: int },
    Crash { node: int },
    Remove { node: int },
    Extend,
    Stutter,
}

pub open spec fn next(s: State, t: State, a: Action) -> bool {
    match a {
        Action::Write { request } => write(s, t, request),
        Action::Forward { node } => forward(s, t, node),
        Action::Crash { node } => crash(s, t, node),
        Action::Remove { node } => remove_failed(s, t, node),
        Action::Extend => extend(s, t),
        Action::Stutter => t == s,
    }
}

pub proof fn prefix_transitive(a: Seq<int>, b: Seq<int>, c: Seq<int>)
    requires prefix(a, b), prefix(b, c),
    ensures prefix(a, c),
{
    assert forall|k: int| 0 <= k < a.len() implies #[trigger] a[k] == c[k] by {
        assert(a[k] == b[k]);
    }
}

pub proof fn init_inv(s: State, n: nat)
    requires init(s, n),
    ensures inv(s),
{}

pub proof fn write_preserves(s: State, t: State, request: int)
    requires inv(s), write(s, t, request),
    ensures inv(t), prefix(committed(s), committed(t)),
{
    assert forall|i: int, j: int| 0 <= i <= j < t.history.len()
        implies #[trigger] prefix(t.history[j], t.history[i]) by {
        assert(prefix(s.history[j], s.history[i]));
        if i == 0 && j > 0 {
            assert forall|k: int| 0 <= k < t.history[j].len()
                implies #[trigger] t.history[j][k] == t.history[i][k] by {
                assert(s.history[j][k] == s.history[i][k]);
            }
        }
    }
    assert forall|i: int, k: int| 0 <= i < t.history.len()
        && 0 <= k < t.history[i].len()
        implies t.submitted.contains(#[trigger] t.history[i][k]) by {
        if i != 0 || k < s.history[0].len() {
            assert(s.submitted.contains(s.history[i][k]));
        }
    }
    assert forall|i: int, k: int, l: int| 0 <= i < t.history.len()
        && 0 <= k < l < t.history[i].len()
        implies #[trigger] t.history[i][k] != #[trigger] t.history[i][l] by {
        if i == 0 && l == s.history[0].len() {
            assert(s.submitted.contains(s.history[0][k]));
        } else {
            assert(s.history[i][k] != s.history[i][l]);
        }
    }
}

pub proof fn forward_preserves(s: State, t: State, node: int)
    requires inv(s), forward(s, t, node),
    ensures inv(t), prefix(committed(s), committed(t)),
{
    let old = s.history[node];
    let pred = s.history[node - 1];
    let new = t.history[node];
    assert(prefix(old, pred));
    assert(prefix(old, new));
    assert(prefix(new, pred)) by {
        assert forall|k: int| 0 <= k < new.len()
            implies #[trigger] new[k] == pred[k] by {
            if k < old.len() { assert(old[k] == pred[k]); }
        }
    }
    assert forall|i: int, j: int| 0 <= i <= j < t.history.len()
        implies #[trigger] prefix(t.history[j], t.history[i]) by {
        assert(prefix(s.history[j], s.history[i]));
        if j == node && i < node {
            assert(prefix(pred, s.history[i]));
            prefix_transitive(new, pred, s.history[i]);
        } else if i == node && j > node {
            prefix_transitive(s.history[j], old, new);
        }
    }
    assert forall|i: int, k: int| 0 <= i < t.history.len()
        && 0 <= k < t.history[i].len()
        implies t.submitted.contains(#[trigger] t.history[i][k]) by {
        if i == node {
            assert(new[k] == pred[k]);
            assert(s.submitted.contains(pred[k]));
        } else { assert(s.submitted.contains(s.history[i][k])); }
    }
    assert forall|i: int, k: int, l: int| 0 <= i < t.history.len()
        && 0 <= k < l < t.history[i].len()
        implies #[trigger] t.history[i][k] != #[trigger] t.history[i][l] by {
        if i == node {
            assert(new[k] == pred[k]);
            assert(new[l] == pred[l]);
            assert(pred[k] != pred[l]);
        } else { assert(s.history[i][k] != s.history[i][l]); }
    }
}

pub proof fn remove_preserves(s: State, t: State, node: int)
    requires inv(s), remove_failed(s, t, node),
    ensures inv(t), prefix(committed(s), committed(t)),
{
    assert forall|i: int, j: int| 0 <= i <= j < t.history.len()
        implies #[trigger] prefix(t.history[j], t.history[i]) by {
        let oi = if i < node { i } else { i + 1 };
        let oj = if j < node { j } else { j + 1 };
        assert(prefix(s.history[oj], s.history[oi]));
    }
    assert forall|i: int, k: int| 0 <= i < t.history.len()
        && 0 <= k < t.history[i].len()
        implies t.submitted.contains(#[trigger] t.history[i][k]) by {
        let oi = if i < node { i } else { i + 1 };
        assert(s.submitted.contains(s.history[oi][k]));
    }
    assert forall|i: int, k: int, l: int| 0 <= i < t.history.len()
        && 0 <= k < l < t.history[i].len()
        implies #[trigger] t.history[i][k] != #[trigger] t.history[i][l] by {
        let oi = if i < node { i } else { i + 1 };
        assert(s.history[oi][k] != s.history[oi][l]);
    }
    if node == s.history.len() - 1 {
        assert(prefix(s.history[s.history.len() - 1], s.history[s.history.len() - 2]));
    }
}

pub proof fn extend_preserves(s: State, t: State)
    requires inv(s), extend(s, t),
    ensures inv(t), committed(t) == committed(s),
{
    assert forall|i: int, j: int| 0 <= i <= j < t.history.len()
        implies #[trigger] prefix(t.history[j], t.history[i]) by {
        let oi = if i < s.history.len() { i } else { s.history.len() - 1 };
        let oj = if j < s.history.len() { j } else { s.history.len() - 1 };
        assert(prefix(s.history[oj], s.history[oi]));
    }
    assert forall|i: int, k: int| 0 <= i < t.history.len()
        && 0 <= k < t.history[i].len()
        implies t.submitted.contains(#[trigger] t.history[i][k]) by {
        let oi = if i < s.history.len() { i } else { s.history.len() - 1 };
        assert(s.submitted.contains(s.history[oi][k]));
    }
    assert forall|i: int, k: int, l: int| 0 <= i < t.history.len()
        && 0 <= k < l < t.history[i].len()
        implies #[trigger] t.history[i][k] != #[trigger] t.history[i][l] by {
        let oi = if i < s.history.len() { i } else { s.history.len() - 1 };
        assert(s.history[oi][k] != s.history[oi][l]);
    }
}

pub proof fn step_preserves(s: State, t: State, a: Action)
    requires inv(s), next(s, t, a),
    ensures inv(t), prefix(committed(s), committed(t)),
        s.submitted.subset_of(t.submitted),
{
    match a {
        Action::Write { request } => write_preserves(s, t, request),
        Action::Forward { node } => forward_preserves(s, t, node),
        Action::Remove { node } => remove_preserves(s, t, node),
        Action::Extend => extend_preserves(s, t),
        _ => {},
    }
}

pub open spec fn behavior(states: Seq<State>, actions: Seq<Action>, n: nat) -> bool {
    &&& states.len() == actions.len() + 1
    &&& init(states[0], n)
    &&& forall|k: int| 0 <= k < actions.len()
        ==> #[trigger] next(states[k], states[k + 1], actions[k])
}

// Arbitrary finite execution lengths and arbitrary nonempty initial chains.
pub proof fn reachable_inv(states: Seq<State>, actions: Seq<Action>, n: nat, k: int)
    requires behavior(states, actions, n), 0 <= k < states.len(),
    ensures inv(states[k]),
    decreases k,
{
    if k == 0 { init_inv(states[0], n); }
    else {
        reachable_inv(states, actions, n, k - 1);
        assert(next(states[k - 1], states[(k - 1) + 1], actions[k - 1]));
        step_preserves(states[k - 1], states[k], actions[k - 1]);
    }
}

pub proof fn completed_prefix_never_lost(
    states: Seq<State>, actions: Seq<Action>, n: nat, i: int, j: int,
)
    requires behavior(states, actions, n), 0 <= i <= j < states.len(),
    ensures prefix(committed(states[i]), committed(states[j])),
    decreases j - i,
{
    reachable_inv(states, actions, n, j);
    if i < j {
        completed_prefix_never_lost(states, actions, n, i, j - 1);
        reachable_inv(states, actions, n, j - 1);
        assert(next(states[j - 1], states[(j - 1) + 1], actions[j - 1]));
        step_preserves(states[j - 1], states[j], actions[j - 1]);
        prefix_transitive(committed(states[i]), committed(states[j - 1]), committed(states[j]));
    }
}

// Validity and at-most-once execution refer to request identities, not values.
pub proof fn committed_valid_and_unique(s: State)
    requires inv(s),
    ensures
        forall|k: int| 0 <= k < committed(s).len()
            ==> s.submitted.contains(#[trigger] committed(s)[k]),
        forall|k: int, l: int| 0 <= k < l < committed(s).len()
            ==> #[trigger] committed(s)[k] != #[trigger] committed(s)[l],
{}

}

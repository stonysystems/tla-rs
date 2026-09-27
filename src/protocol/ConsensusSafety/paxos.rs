//! Shared classic Paxos safety kernel, derived from the verified Mencius core.
//! Higher ballots may propose fresh values after empty Phase 1.
//! Phase 1 quorum collection is atomic; accept delivery is per replica.
//! This kernel alone is not evidence for any paper-specific protocol.
use vstd::prelude::*;

verus! {

pub struct Config {
    pub acceptors: Set<int>,
    pub quorums: Set<Set<int>>,
}

pub open spec fn config_ok(c: Config) -> bool {
    &&& c.acceptors != Set::<int>::empty()
    &&& c.quorums != Set::<Set<int>>::empty()
    &&& forall|q: Set<int>| c.quorums.contains(q)
        ==> q.subset_of(c.acceptors) && q != Set::<int>::empty()
    &&& forall|q: Set<int>, r: Set<int>| c.quorums.contains(q) && c.quorums.contains(r)
        ==> exists|a: int| q.contains(a) && r.contains(a)
}

pub struct State {
    pub promise: Map<int, int>,
    pub last_ballot: Map<int, int>,
    pub last_value: Map<int, int>,
    pub proposals: Map<int, int>,
    pub votes: Set<(int, int, int)>,
}

pub open spec fn voted(s: State, a: int, b: int, v: int) -> bool {
    s.votes.contains((a, b, v))
}

pub open spec fn blocked_or_same(s: State, a: int, b: int, v: int) -> bool {
    voted(s, a, b, v)
        || (s.promise[a] > b && forall|w: int| !voted(s, a, b, w))
}

pub open spec fn protected_at(s: State, c: Config, k: int, v: int) -> bool {
    exists|q: Set<int>| c.quorums.contains(q)
        && forall|a: int| q.contains(a) ==> blocked_or_same(s, a, k, v)
}

pub open spec fn safe_at(s: State, c: Config, b: int, v: int) -> bool {
    forall|k: int| 0 <= k < b ==> #[trigger] protected_at(s, c, k, v)
}

pub open spec fn inv(s: State, c: Config) -> bool {
    &&& s.promise.dom() == c.acceptors
    &&& s.last_ballot.dom() == c.acceptors
    &&& s.last_value.dom() == c.acceptors
    &&& forall|a: int| c.acceptors.contains(a) ==>
        0 <= s.promise[a] && -1 <= s.last_ballot[a] <= s.promise[a]
    &&& forall|a: int, b: int, v: int| voted(s, a, b, v) ==>
        c.acceptors.contains(a) && 0 <= b <= s.last_ballot[a]
        && s.proposals.dom().contains(b) && s.proposals[b] == v
    &&& forall|a: int| c.acceptors.contains(a) && s.last_ballot[a] >= 0
        ==> voted(s, a, s.last_ballot[a], s.last_value[a])
    &&& forall|b: int| s.proposals.dom().contains(b) ==>
        b >= 0 && safe_at(s, c, b, s.proposals[b])
}

pub open spec fn init(s: State, c: Config) -> bool {
    &&& s.promise == Map::new(c.acceptors, |a: int| 0)
    &&& s.last_ballot == Map::new(c.acceptors, |a: int| -1)
    &&& s.last_value == Map::new(c.acceptors, |a: int| 0)
    &&& s.proposals == Map::<int, int>::empty()
    &&& s.votes == Set::<(int, int, int)>::empty()
}

// The unique initial proposer owns ballot zero; later owners run Phase 1.
pub open spec fn suggest(s: State, t: State, v: int) -> bool {
    &&& !s.proposals.dom().contains(0)
    &&& t.proposals == s.proposals.insert(0, v)
    &&& t.promise == s.promise
    &&& t.last_ballot == s.last_ballot
    &&& t.last_value == s.last_value
    &&& t.votes == s.votes
}

// Atomic Phase 1 followed by selecting the Phase 2 value. The maximum is
// computed from actual accepted states, never from the desired safety result.
pub open spec fn prepared_promises(s: State, q: Set<int>, b: int) -> Map<int, int> {
    Map::new(s.promise.dom(), |a: int| if q.contains(a) { b } else { s.promise[a] })
}
pub open spec fn revoke(s: State, t: State, c: Config,
                       b: int, q: Set<int>, maximum: int, v: int) -> bool {
    &&& b > 0
    &&& c.quorums.contains(q)
    &&& !s.proposals.dom().contains(b)
    &&& forall|a: int| q.contains(a)
        ==> s.promise[a] < b && s.last_ballot[a] <= maximum
    &&& if maximum == -1 { true } else {
        maximum >= 0 && exists|a: int| q.contains(a)
            && s.last_ballot[a] == maximum && s.last_value[a] == v
    }
    &&& t.promise == prepared_promises(s, q, b)
    &&& t.proposals == s.proposals.insert(b, v)
    &&& t.last_ballot == s.last_ballot
    &&& t.last_value == s.last_value
    &&& t.votes == s.votes
}

pub open spec fn accept(s: State, t: State, c: Config, a: int, b: int) -> bool {
    &&& c.acceptors.contains(a)
    &&& s.proposals.dom().contains(b)
    &&& b >= s.promise[a]
    &&& t.promise == s.promise.insert(a, b)
    &&& t.last_ballot == s.last_ballot.insert(a, b)
    &&& t.last_value == s.last_value.insert(a, s.proposals[b])
    &&& t.votes == s.votes.insert((a, b, s.proposals[b]))
    &&& t.proposals == s.proposals
}

pub enum Action {
    Suggest { value: int },
    Revoke { ballot: int, quorum: Set<int>, maximum: int, value: int },
    Accept { acceptor: int, ballot: int },
    Stutter,
}

pub open spec fn next(s: State, t: State, c: Config, action: Action) -> bool {
    match action {
        Action::Suggest { value } => suggest(s, t, value),
        Action::Revoke { ballot, quorum, maximum, value }
            => revoke(s, t, c, ballot, quorum, maximum, value),
        Action::Accept { acceptor, ballot } => accept(s, t, c, acceptor, ballot),
        Action::Stutter => t == s,
    }
}

pub open spec fn quorum_chosen(s: State, c: Config, b: int, v: int) -> bool {
    exists|q: Set<int>| c.quorums.contains(q)
        && forall|a: int| q.contains(a) ==> voted(s, a, b, v)
}

// This is evidence permitting a learner to decide, not a new state guard.
pub open spec fn learned(s: State, c: Config, v: int) -> bool {
    exists|b: int| quorum_chosen(s, c, b, v)
}

pub proof fn init_inv(s: State, c: Config)
    requires init(s, c),
    ensures inv(s, c),
{}

pub proof fn safe_monotone_promises(s: State, t: State, c: Config, b: int, v: int)
    requires safe_at(s, c, b, v), t.votes == s.votes,
        s.promise.dom() == c.acceptors, t.promise.dom() == c.acceptors,
        forall|a: int| c.acceptors.contains(a) ==> t.promise[a] >= s.promise[a],
        config_ok(c),
    ensures safe_at(t, c, b, v),
{
    assert forall|k: int| 0 <= k < b implies #[trigger] protected_at(t, c, k, v) by {
        assert(protected_at(s, c, k, v));
        let q = choose|q: Set<int>| c.quorums.contains(q)
            && forall|a: int| q.contains(a) ==> blocked_or_same(s, a, k, v);
        assert(q.subset_of(c.acceptors));
        assert forall|a: int| q.contains(a) implies blocked_or_same(t, a, k, v) by {
            assert(c.acceptors.contains(a));
            assert(blocked_or_same(s, a, k, v));
            assert(t.promise[a] >= s.promise[a]);
            if !voted(s, a, k, v) {
                assert forall|w: int| !voted(t, a, k, w) by {
                    assert(!voted(s, a, k, w));
                }
            }
        }
        assert(c.quorums.contains(q)
            && forall|a: int| q.contains(a) ==> blocked_or_same(t, a, k, v));
    }
}

pub proof fn suggest_preserves(s: State, t: State, c: Config, v: int)
    requires config_ok(c), inv(s, c), suggest(s, t, v),
    ensures inv(t, c),
{
    assert forall|b: int| t.proposals.dom().contains(b) implies
        b >= 0 && safe_at(t, c, b, t.proposals[b]) by {
        if b != 0 { safe_monotone_promises(s, t, c, b, s.proposals[b]); }
    }
    assert forall|a: int, b: int, w: int| voted(t, a, b, w) implies
        c.acceptors.contains(a) && 0 <= b <= t.last_ballot[a]
        && t.proposals.dom().contains(b) && t.proposals[b] == w by {
        assert(voted(s, a, b, w));
        assert(s.proposals.dom().contains(b) && s.proposals[b] == w);
    }
}

pub proof fn revoke_preserves(s: State, t: State, c: Config,
                             b: int, q: Set<int>, maximum: int, v: int)
    requires config_ok(c), inv(s, c), revoke(s, t, c, b, q, maximum, v),
    ensures inv(t, c),
{
    assert(q.subset_of(c.acceptors));
    assert forall|a: int| c.acceptors.contains(a)
        implies t.promise[a] >= s.promise[a] by {};
    if maximum >= 0 {
        let witness = choose|a: int| q.contains(a)
            && s.last_ballot[a] == maximum && s.last_value[a] == v;
        assert(voted(s, witness, maximum, v));
        assert(s.proposals.dom().contains(maximum) && s.proposals[maximum] == v);
        assert(maximum <= s.promise[witness] < b);
    }
    assert(safe_at(t, c, b, v)) by {
        assert forall|k: int| 0 <= k < b implies #[trigger] protected_at(t, c, k, v) by {
            if k < maximum {
                assert(safe_at(s, c, maximum, v));
                safe_monotone_promises(s, t, c, maximum, v);
                assert(protected_at(t, c, k, v));
            } else {
                assert forall|a: int| q.contains(a) implies blocked_or_same(t, a, k, v) by {
                    assert(c.acceptors.contains(a));
                    if s.last_ballot[a] == k {
                        assert(k == maximum);
                        assert(voted(s, a, k, s.last_value[a]));
                        assert(s.proposals[k] == v);
                    } else {
                        assert(s.last_ballot[a] < k);
                        assert forall|w: int| !voted(t, a, k, w) by {
                            if voted(s, a, k, w) { assert(k <= s.last_ballot[a]); }
                        }
                    }
                }
                assert(c.quorums.contains(q)
                    && forall|a: int| q.contains(a) ==> blocked_or_same(t, a, k, v));
            }
        }
    }
    assert forall|k: int| t.proposals.dom().contains(k) implies
        k >= 0 && safe_at(t, c, k, t.proposals[k]) by {
        if k != b { safe_monotone_promises(s, t, c, k, s.proposals[k]); }
    }
    assert forall|a: int, k: int, w: int| voted(t, a, k, w) implies
        c.acceptors.contains(a) && 0 <= k <= t.last_ballot[a]
        && t.proposals.dom().contains(k) && t.proposals[k] == w by {
        assert(voted(s, a, k, w));
        assert(s.proposals.dom().contains(k) && s.proposals[k] == w);
    }
}

pub proof fn accept_preserves_safe(s: State, t: State, c: Config,
                                  a: int, b: int, k: int, v: int)
    requires config_ok(c), inv(s, c), accept(s, t, c, a, b), safe_at(s, c, k, v),
    ensures safe_at(t, c, k, v),
{
    assert forall|r: int| 0 <= r < k implies #[trigger] protected_at(t, c, r, v) by {
        assert(protected_at(s, c, r, v));
        let q = choose|q: Set<int>| c.quorums.contains(q)
            && forall|n: int| q.contains(n) ==> blocked_or_same(s, n, r, v);
        assert forall|n: int| q.contains(n) implies blocked_or_same(t, n, r, v) by {
            assert(blocked_or_same(s, n, r, v));
            if !voted(s, n, r, v) {
                if n == a { assert(b > r); }
                assert forall|w: int| !voted(t, n, r, w) by {
                    assert(!voted(s, n, r, w));
                }
            }
        }
        assert(c.quorums.contains(q)
            && forall|n: int| q.contains(n) ==> blocked_or_same(t, n, r, v));
    }
}

pub proof fn accept_preserves(s: State, t: State, c: Config, a: int, b: int)
    requires config_ok(c), inv(s, c), accept(s, t, c, a, b),
    ensures inv(t, c),
{
    assert(t.promise.dom() =~= c.acceptors);
    assert(t.last_ballot.dom() =~= c.acceptors);
    assert(t.last_value.dom() =~= c.acceptors);
    assert forall|n: int| c.acceptors.contains(n) implies
        0 <= t.promise[n] && -1 <= t.last_ballot[n] <= t.promise[n] by {
        assert(0 <= s.promise[n] && -1 <= s.last_ballot[n] <= s.promise[n]);
    }
    assert forall|n: int, k: int, v: int| voted(t, n, k, v) implies
        c.acceptors.contains(n) && 0 <= k <= t.last_ballot[n]
        && t.proposals.dom().contains(k) && t.proposals[k] == v by {
        if voted(s, n, k, v) {
            assert(k <= s.last_ballot[n] <= s.promise[n]);
        }
    }
    assert forall|k: int| t.proposals.dom().contains(k) implies
        k >= 0 && safe_at(t, c, k, t.proposals[k]) by {
        accept_preserves_safe(s, t, c, a, b, k, s.proposals[k]);
    }
    assert forall|n: int| c.acceptors.contains(n) && t.last_ballot[n] >= 0
        implies voted(t, n, t.last_ballot[n], t.last_value[n]) by {
        if n != a { assert(voted(s, n, s.last_ballot[n], s.last_value[n])); }
    }
}

pub proof fn step_preserves(s: State, t: State, c: Config, action: Action)
    requires config_ok(c), inv(s, c), next(s, t, c, action),
    ensures inv(t, c), s.votes.subset_of(t.votes),
        s.proposals.dom().subset_of(t.proposals.dom()),
        forall|b: int| s.proposals.dom().contains(b) ==> t.proposals[b] == s.proposals[b],
{
    match action {
        Action::Suggest { value } => suggest_preserves(s, t, c, value),
        Action::Revoke { ballot, quorum, maximum, value }
            => revoke_preserves(s, t, c, ballot, quorum, maximum, value),
        Action::Accept { acceptor, ballot } => accept_preserves(s, t, c, acceptor, ballot),
        Action::Stutter => {},
    }
}

pub proof fn quorum_agreement(s: State, c: Config, b: int, v: int, k: int, w: int)
    requires config_ok(c), inv(s, c),
        quorum_chosen(s, c, b, v), quorum_chosen(s, c, k, w), b <= k,
    ensures v == w,
{
    let q = choose|q: Set<int>| c.quorums.contains(q)
        && forall|a: int| q.contains(a) ==> voted(s, a, b, v);
    let r = choose|q: Set<int>| c.quorums.contains(q)
        && forall|a: int| q.contains(a) ==> voted(s, a, k, w);
    let a = choose|a: int| q.contains(a) && r.contains(a);
    assert(voted(s, a, b, v));
    assert(voted(s, a, k, w));
    if b < k {
        assert(safe_at(s, c, k, w));
        assert(protected_at(s, c, b, w));
        let blocker = choose|q: Set<int>| c.quorums.contains(q)
            && forall|a: int| q.contains(a) ==> blocked_or_same(s, a, b, w);
        let n = choose|a: int| q.contains(a) && blocker.contains(a);
        assert(voted(s, n, b, v));
        assert(blocked_or_same(s, n, b, w));
        assert(voted(s, n, b, w));
    }
}

pub proof fn learned_agreement(s: State, c: Config, v: int, w: int)
    requires config_ok(c), inv(s, c), learned(s, c, v), learned(s, c, w),
    ensures v == w,
{
    let b = choose|b: int| quorum_chosen(s, c, b, v);
    let k = choose|b: int| quorum_chosen(s, c, b, w);
    if b <= k { quorum_agreement(s, c, b, v, k, w); }
    else { quorum_agreement(s, c, k, w, b, v); }
}

pub open spec fn behavior(states: Seq<State>, actions: Seq<Action>, c: Config) -> bool {
    &&& states.len() == actions.len() + 1
    &&& init(states[0], c)
    &&& forall|k: int| 0 <= k < actions.len()
        ==> #[trigger] next(states[k], states[k + 1], c, actions[k])
}

pub proof fn reachable_inv(states: Seq<State>, actions: Seq<Action>, c: Config, k: int)
    requires config_ok(c), behavior(states, actions, c), 0 <= k < states.len(),
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

pub proof fn learned_preserved(s: State, t: State, c: Config, v: int)
    requires learned(s, c, v), s.votes.subset_of(t.votes),
        s.proposals.dom().subset_of(t.proposals.dom()),
        forall|b: int| s.proposals.dom().contains(b) ==> t.proposals[b] == s.proposals[b],
    ensures learned(t, c, v),
{
    {
        let b = choose|b: int| quorum_chosen(s, c, b, v);
        let q = choose|q: Set<int>| c.quorums.contains(q)
            && forall|a: int| q.contains(a) ==> voted(s, a, b, v);
        assert forall|a: int| q.contains(a) implies voted(t, a, b, v) by {
            assert(voted(s, a, b, v));
        }
        assert(c.quorums.contains(q)
            && forall|a: int| q.contains(a) ==> voted(t, a, b, v));
        assert(quorum_chosen(t, c, b, v));
    }
}

pub proof fn learned_persists(states: Seq<State>, actions: Seq<Action>, c: Config,
                             i: int, j: int, v: int)
    requires config_ok(c), behavior(states, actions, c),
        0 <= i <= j < states.len(), learned(states[i], c, v),
    ensures learned(states[j], c, v),
    decreases j - i,
{
    if i < j {
        learned_persists(states, actions, c, i, j - 1, v);
        reachable_inv(states, actions, c, j - 1);
        assert(next(states[j - 1], states[(j - 1) + 1], c, actions[j - 1]));
        step_preserves(states[j - 1], states[j], c, actions[j - 1]);
        learned_preserved(states[j - 1], states[j], c, v);
    }
}

pub proof fn behavior_agreement(states: Seq<State>, actions: Seq<Action>, c: Config,
                               i: int, j: int, v: int, w: int)
    requires config_ok(c), behavior(states, actions, c), 0 <= i <= j < states.len(),
        learned(states[i], c, v), learned(states[j], c, w),
    ensures v == w,
{
    reachable_inv(states, actions, c, j);
    learned_persists(states, actions, c, i, j, v);
    learned_agreement(states[j], c, v, w);
}

} // verus!

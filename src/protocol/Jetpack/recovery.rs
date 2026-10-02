//! Jetpack, OSDI 2026, Sections 4.3 and B.3: recovery of one normal view.
//! Global asynchronous safety model. Fast acknowledgments, freezing, prepare
//! replies, proposals and accepts are separate transitions. Replies and votes
//! are durable history, so delayed delivery and arbitrary recovery retries are
//! allowed. Membership is fixed within this recovery instance.
//! This proves recovery completeness, conflict exclusion and Paxos agreement;
//! it does not refine the authors' implementation or prove base-log ordering.
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub struct Config {
    pub nodes: Set<int>,
    pub commands: Set<int>,
    pub conflict: Set<(int, int)>,
    pub f: nat,
}

pub open spec fn config_ok(c: Config) -> bool {
    &&& c.nodes.len() == 2 * c.f + 1
    &&& forall|x: int, y: int| c.conflict.contains((x, y))
        ==> x != y && c.conflict.contains((y, x))
}

pub open spec fn threshold(c: Config) -> nat { (c.f + 1) / 2 + 1 }
pub open spec fn fast_size(c: Config) -> nat { c.f + threshold(c) }
pub open spec fn quorum(c: Config, q: Set<int>) -> bool {
    q.subset_of(c.nodes) && q.len() == c.f + 1
}

pub struct Snapshot {
    pub last: int,
    pub value: Set<int>,
    pub log: Set<int>,
}

pub struct State {
    pub logs: Map<int, Set<int>>,
    pub frozen: Set<int>,
    pub promise: Map<int, int>,
    pub last: Map<int, int>,
    pub value: Map<int, Set<int>>,
    // Key is (acceptor, ballot). A prepare reply is created only by Prepare.
    pub replies: Map<(int, int), Snapshot>,
    // A unique ballot owner sends at most one value in its ballot.
    pub proposals: Map<int, Set<int>>,
    pub votes: Set<(int, int, Set<int>)>,
}

pub open spec fn support(logs: Map<int, Set<int>>, q: Set<int>, x: int) -> Set<int> {
    q.filter(|a: int| logs[a].contains(x))
}
pub open spec fn selected(c: Config, logs: Map<int, Set<int>>, q: Set<int>) -> Set<int> {
    c.commands.filter(|x: int| support(logs, q, x).len() >= threshold(c))
}
pub open spec fn reply_logs(s: State, b: int, q: Set<int>) -> Map<int, Set<int>> {
    Map::new(q, |a: int| s.replies[(a, b)].log)
}
// No proposer condition is needed for this recovery theorem. Requiring all
// original-path proposers to acknowledge only narrows these certificates.
pub open spec fn fast_committed(s: State, c: Config, x: int) -> bool {
    c.commands.contains(x) && support(s.logs, c.nodes, x).len() >= fast_size(c)
}
pub open spec fn voted(s: State, a: int, b: int, v: Set<int>) -> bool {
    s.votes.contains((a, b, v))
}
pub open spec fn blocked_or_same(s: State, a: int, b: int, v: Set<int>) -> bool {
    voted(s, a, b, v)
        || (s.promise[a] > b && forall|w: Set<int>| !voted(s, a, b, w))
}
pub open spec fn protected_at(s: State, c: Config, b: int, v: Set<int>) -> bool {
    exists|q: Set<int>| quorum(c, q)
        && forall|a: int| #![trigger q.contains(a)] q.contains(a) ==> blocked_or_same(s, a, b, v)
}
pub open spec fn safe_at(s: State, c: Config, b: int, v: Set<int>) -> bool {
    forall|k: int| 0 <= k < b ==> #[trigger] protected_at(s, c, k, v)
}
// Each proposed value has an actual frozen-log quorum as its origin. This is
// an inductive invariant, not a condition on the protocol's Next relation.
pub open spec fn candidate(s: State, c: Config, v: Set<int>) -> bool {
    exists|q: Set<int>| #![trigger quorum(c, q)] quorum(c, q) && q.subset_of(s.frozen)
        && v == selected(c, s.logs, q)
}
pub open spec fn reply_ok(s: State, c: Config, a: int, b: int) -> bool {
    let r = s.replies[(a, b)];
    &&& c.nodes.contains(a) && s.frozen.contains(a)
    &&& 0 <= b <= s.promise[a]
    &&& -1 <= r.last < b
    &&& r.log == s.logs[a]
    &&& r.last >= 0 ==> voted(s, a, r.last, r.value)
    &&& forall|k: int, w: Set<int>| r.last < k < b ==> !voted(s, a, k, w)
}
pub open spec fn inv(s: State, c: Config) -> bool {
    &&& s.logs.dom() == c.nodes && s.frozen.subset_of(c.nodes)
    &&& s.promise.dom() == c.nodes && s.last.dom() == c.nodes && s.value.dom() == c.nodes
    &&& forall|a: int| #![trigger c.nodes.contains(a)] c.nodes.contains(a) ==> s.logs[a].subset_of(c.commands)
        && -1 <= s.last[a] <= s.promise[a]
    &&& forall|a: int, x: int, y: int| #![trigger c.nodes.contains(a), c.conflict.contains((x, y))] c.nodes.contains(a)
        && s.logs[a].contains(x) && s.logs[a].contains(y) ==> !c.conflict.contains((x, y))
    &&& forall|a: int, b: int, v: Set<int>| voted(s, a, b, v) ==>
        c.nodes.contains(a) && 0 <= b <= s.last[a]
        && s.proposals.dom().contains(b) && s.proposals[b] == v
    &&& forall|a: int| #![trigger c.nodes.contains(a)] c.nodes.contains(a) && s.last[a] >= 0
        ==> voted(s, a, s.last[a], s.value[a])
    &&& forall|a: int, b: int| #![trigger reply_ok(s, c, a, b)] s.replies.dom().contains((a, b)) ==> reply_ok(s, c, a, b)
    &&& forall|b: int| #![trigger s.proposals.dom().contains(b)] s.proposals.dom().contains(b) ==>
        b >= 0 && safe_at(s, c, b, s.proposals[b]) && candidate(s, c, s.proposals[b])
}
pub open spec fn init(s: State, c: Config) -> bool {
    &&& s.logs == Map::new(c.nodes, |a: int| Set::<int>::empty())
    &&& s.frozen == Set::<int>::empty()
    &&& s.promise == Map::new(c.nodes, |a: int| -1)
    &&& s.last == Map::new(c.nodes, |a: int| -1)
    &&& s.value == Map::new(c.nodes, |a: int| Set::<int>::empty())
    &&& s.replies == Map::<(int, int), Snapshot>::empty()
    &&& s.proposals == Map::<int, Set<int>>::empty()
    &&& s.votes == Set::<(int, int, Set<int>)>::empty()
}

pub open spec fn acknowledge(s: State, t: State, c: Config, a: int, x: int) -> bool {
    &&& c.nodes.contains(a) && c.commands.contains(x) && !s.frozen.contains(a)
    &&& forall|y: int| #![trigger s.logs[a].contains(y)] s.logs[a].contains(y) ==> !c.conflict.contains((x, y))
    &&& t == State { logs: s.logs.insert(a, s.logs[a].insert(x)), ..s }
}
pub open spec fn freeze(s: State, t: State, c: Config, a: int) -> bool {
    c.nodes.contains(a) && t == State { frozen: s.frozen.insert(a), ..s }
}
pub open spec fn prepare(s: State, t: State, c: Config, a: int, b: int) -> bool {
    &&& c.nodes.contains(a) && s.frozen.contains(a) && b >= 0 && b > s.promise[a]
    &&& t == State {
        promise: s.promise.insert(a, b),
        replies: s.replies.insert((a, b), Snapshot { last: s.last[a], value: s.value[a], log: s.logs[a] }),
        ..s
    }
}
pub open spec fn propose(s: State, t: State, c: Config,
                        b: int, q: Set<int>, maximum: int, v: Set<int>) -> bool {
    &&& b >= 0 && quorum(c, q) && !s.proposals.dom().contains(b)
    &&& forall|a: int| #![trigger q.contains(a)] q.contains(a) ==> s.replies.dom().contains((a, b))
        && s.replies[(a, b)].last <= maximum
    &&& if maximum == -1 {
        v == selected(c, reply_logs(s, b, q), q)
    } else {
        maximum >= 0 && exists|a: int| #![trigger q.contains(a)] q.contains(a)
            && s.replies[(a, b)].last == maximum && s.replies[(a, b)].value == v
    }
    &&& t == State { proposals: s.proposals.insert(b, v), ..s }
}
pub open spec fn accept(s: State, t: State, c: Config, a: int, b: int) -> bool {
    &&& c.nodes.contains(a) && s.proposals.dom().contains(b) && b >= s.promise[a]
    &&& t == State {
        promise: s.promise.insert(a, b), last: s.last.insert(a, b),
        value: s.value.insert(a, s.proposals[b]),
        votes: s.votes.insert((a, b, s.proposals[b])), ..s
    }
}
pub enum Action {
    Acknowledge { node: int, command: int },
    Freeze { node: int },
    Prepare { node: int, ballot: int },
    Propose { ballot: int, quorum: Set<int>, maximum: int, value: Set<int> },
    Accept { node: int, ballot: int },
    Stutter,
}
pub open spec fn next(s: State, t: State, c: Config, action: Action) -> bool {
    match action {
        Action::Acknowledge { node, command } => acknowledge(s, t, c, node, command),
        Action::Freeze { node } => freeze(s, t, c, node),
        Action::Prepare { node, ballot } => prepare(s, t, c, node, ballot),
        Action::Propose { ballot, quorum, maximum, value } => propose(s, t, c, ballot, quorum, maximum, value),
        Action::Accept { node, ballot } => accept(s, t, c, node, ballot),
        Action::Stutter => t == s,
    }
}
pub open spec fn chosen(s: State, c: Config, b: int, v: Set<int>) -> bool {
    exists|q: Set<int>| quorum(c, q) && forall|a: int| #![trigger q.contains(a)] q.contains(a) ==> voted(s, a, b, v)
}

pub proof fn intersection_bound(c: Config, p: Set<int>, q: Set<int>)
    requires config_ok(c), p.subset_of(c.nodes), q.subset_of(c.nodes),
    ensures p.intersect(q).len() + c.nodes.len() >= p.len() + q.len(),
{
    assert(p.union(q).subset_of(c.nodes));
    lemma_len_subset(p.union(q), c.nodes);
    lemma_set_intersect_union_lens(p, q);
}
pub proof fn quorum_intersection(c: Config, p: Set<int>, q: Set<int>)
    requires config_ok(c), quorum(c, p), quorum(c, q),
    ensures exists|a: int| p.contains(a) && q.contains(a),
{
    intersection_bound(c, p, q);
    assert(p.intersect(q).len() > 0);
    assert(p.intersect(q) != Set::<int>::empty());
    assert(exists|a: int| p.intersect(q).contains(a)) by {
        if !(exists|a: int| p.intersect(q).contains(a)) {
            assert(p.intersect(q) =~= Set::<int>::empty());
        }
    }
    let a = choose|a: int| p.intersect(q).contains(a);
    assert(p.contains(a) && q.contains(a));
}

// Paper Lemma 2, including certificates completed after recovery started.
pub proof fn selection_complete_and_safe(s: State, c: Config, q: Set<int>, x: int)
    requires config_ok(c), inv(s, c), quorum(c, q), fast_committed(s, c, x),
    ensures selected(c, s.logs, q).contains(x),
        forall|y: int| #![trigger selected(c, s.logs, q).contains(y)] selected(c, s.logs, q).contains(y) ==> !c.conflict.contains((x, y)),
{
    let p = support(s.logs, c.nodes, x);
    intersection_bound(c, p, q);
    assert(p.intersect(q) =~= support(s.logs, q, x));
    assert(support(s.logs, q, x).len() >= threshold(c));
    assert forall|y: int| #![trigger selected(c, s.logs, q).contains(y)] selected(c, s.logs, q).contains(y)
        implies !c.conflict.contains((x, y)) by {
        if c.conflict.contains((x, y)) {
            let r = support(s.logs, q, y);
            assert(r.subset_of(c.nodes));
            assert(p.intersect(r) =~= Set::<int>::empty()) by {
                assert forall|a: int| p.intersect(r).contains(a) implies false by {
                    assert(c.nodes.contains(a) && s.logs[a].contains(x) && s.logs[a].contains(y));
                }
            }
            intersection_bound(c, p, r);
            assert(2 * ((c.f + 1) / 2) >= c.f) by (nonlinear_arith);
            assert(false);
        }
    }
}

pub proof fn init_inv(s: State, c: Config)
    requires config_ok(c), init(s, c),
    ensures inv(s, c),
{}

pub proof fn candidate_stable(s: State, t: State, c: Config, v: Set<int>)
    requires candidate(s, c, v), s.frozen.subset_of(t.frozen),
        forall|a: int| #![trigger s.logs[a]] #![trigger t.logs[a]] s.frozen.contains(a) ==> s.logs[a] == t.logs[a],
    ensures candidate(t, c, v),
{
    let q = choose|q: Set<int>| #![trigger quorum(c, q)] quorum(c, q) && q.subset_of(s.frozen)
        && v == selected(c, s.logs, q);
    assert forall|x: int| c.commands.contains(x) implies
        support(s.logs, q, x) == support(t.logs, q, x) by {
        assert(support(s.logs, q, x) =~= support(t.logs, q, x));
    }
    assert(selected(c, s.logs, q) =~= selected(c, t.logs, q));
    assert(q.subset_of(t.frozen));
}

pub proof fn safe_monotone(s: State, t: State, c: Config, b: int, v: Set<int>)
    requires safe_at(s, c, b, v), t.votes == s.votes,
        forall|a: int| #![trigger c.nodes.contains(a)] c.nodes.contains(a) ==> t.promise[a] >= s.promise[a],
    ensures safe_at(t, c, b, v),
{
    assert forall|k: int| 0 <= k < b implies #[trigger] protected_at(t, c, k, v) by {
        assert(protected_at(s, c, k, v));
        let q = choose|q: Set<int>| quorum(c, q)
            && forall|a: int| #![trigger q.contains(a)] q.contains(a) ==> blocked_or_same(s, a, k, v);
        assert forall|a: int| #![trigger q.contains(a)] q.contains(a) implies blocked_or_same(t, a, k, v) by {
            assert(c.nodes.contains(a));
            assert(blocked_or_same(s, a, k, v));
            if !voted(s, a, k, v) {
                assert forall|w: Set<int>| !voted(t, a, k, w) by {
                    assert(!voted(s, a, k, w));
                }
            }
        }
        assert(quorum(c, q) && forall|a: int| #![trigger q.contains(a)] q.contains(a) ==> blocked_or_same(t, a, k, v));
    }
}

pub proof fn acknowledge_preserves(s: State, t: State, c: Config, a: int, x: int)
    requires config_ok(c), inv(s, c), acknowledge(s, t, c, a, x),
    ensures inv(t, c),
{
    votes_frame(s, t, c);
    assert(t.logs.dom() =~= c.nodes);
    assert forall|n: int| #![trigger c.nodes.contains(n)] c.nodes.contains(n) implies t.logs[n].subset_of(c.commands)
        && -1 <= t.last[n] <= t.promise[n] by {
        assert(s.logs[n].subset_of(c.commands));
    }
    assert forall|n: int, y: int, z: int| #![trigger c.nodes.contains(n), c.conflict.contains((y, z))] c.nodes.contains(n)
        && t.logs[n].contains(y) && t.logs[n].contains(z)
        implies !c.conflict.contains((y, z)) by {
        if n == a && y == x {
            if z == x { assert(!c.conflict.contains((x, x))); }
        } else if n == a && z == x {
            assert(!c.conflict.contains((x, y)));
        }
    }
    assert forall|n: int| #![trigger s.logs[n]] #![trigger t.logs[n]] s.frozen.contains(n) implies s.logs[n] == t.logs[n] by {};
    assert forall|b: int| #![trigger t.proposals.dom().contains(b)] t.proposals.dom().contains(b) implies
        b >= 0 && safe_at(t, c, b, t.proposals[b]) && candidate(t, c, t.proposals[b]) by {
        candidate_stable(s, t, c, s.proposals[b]);
        safe_monotone(s, t, c, b, s.proposals[b]);
    }
    assert forall|n: int, b: int| #![trigger reply_ok(t, c, n, b)] t.replies.dom().contains((n, b))
        implies reply_ok(t, c, n, b) by {
        assert(reply_ok(s, c, n, b));
        reply_frame(s, t, c, n, b);
    }
}

pub proof fn freeze_preserves(s: State, t: State, c: Config, a: int)
    requires config_ok(c), inv(s, c), freeze(s, t, c, a),
    ensures inv(t, c),
{
    votes_frame(s, t, c);
    assert forall|b: int| #![trigger t.proposals.dom().contains(b)] t.proposals.dom().contains(b) implies
        b >= 0 && safe_at(t, c, b, t.proposals[b]) && candidate(t, c, t.proposals[b]) by {
        candidate_stable(s, t, c, s.proposals[b]);
        safe_monotone(s, t, c, b, s.proposals[b]);
    }
    assert forall|n: int, b: int| #![trigger reply_ok(t, c, n, b)] t.replies.dom().contains((n, b))
        implies reply_ok(t, c, n, b) by {
        assert(reply_ok(s, c, n, b));
        reply_frame(s, t, c, n, b);
    }
}

pub proof fn prepare_preserves(s: State, t: State, c: Config, a: int, b: int)
    requires config_ok(c), inv(s, c), prepare(s, t, c, a, b),
    ensures inv(t, c),
{
    votes_frame(s, t, c);
    assert(t.promise.dom() =~= c.nodes);
    assert forall|n: int| #![trigger c.nodes.contains(n)] c.nodes.contains(n) implies t.logs[n].subset_of(c.commands)
        && -1 <= t.last[n] <= t.promise[n] by {
        assert(-1 <= s.last[n] <= s.promise[n]);
    }
    assert forall|n: int, k: int| #![trigger reply_ok(t, c, n, k)] t.replies.dom().contains((n, k))
        implies reply_ok(t, c, n, k) by {
        if n == a && k == b {
            assert forall|j: int, w: Set<int>| s.last[a] < j < b
                implies !voted(t, a, j, w) by {
                if voted(s, a, j, w) { assert(j <= s.last[a]); }
            }
        } else {
            assert(reply_ok(s, c, n, k));
            reply_frame(s, t, c, n, k);
        }
    }
    assert forall|k: int| #![trigger t.proposals.dom().contains(k)] t.proposals.dom().contains(k) implies
        k >= 0 && safe_at(t, c, k, t.proposals[k]) && candidate(t, c, t.proposals[k]) by {
        safe_monotone(s, t, c, k, s.proposals[k]);
        candidate_stable(s, t, c, s.proposals[k]);
    }
}

pub proof fn propose_preserves(s: State, t: State, c: Config,
                              b: int, q: Set<int>, maximum: int, v: Set<int>)
    requires config_ok(c), inv(s, c), propose(s, t, c, b, q, maximum, v),
    ensures inv(t, c),
{
    assert forall|a: int| #![trigger q.contains(a)] q.contains(a) implies reply_ok(s, c, a, b) by {};
    if maximum >= 0 {
        let a = choose|a: int| #![trigger q.contains(a)] q.contains(a)
            && s.replies[(a, b)].last == maximum && s.replies[(a, b)].value == v;
        assert(voted(s, a, maximum, v));
        assert(s.proposals.dom().contains(maximum) && s.proposals[maximum] == v);
        assert(maximum < b);
        candidate_stable(s, t, c, v);
    } else {
        assert(q.subset_of(s.frozen));
        assert forall|x: int| #![trigger c.commands.contains(x)] #![trigger support(s.logs, q, x)] c.commands.contains(x) implies
            support(reply_logs(s, b, q), q, x) == support(s.logs, q, x) by {
            assert(support(reply_logs(s, b, q), q, x) =~= support(s.logs, q, x));
        }
        assert(v =~= selected(c, s.logs, q));
        assert(candidate(s, c, v));
        candidate_stable(s, t, c, v);
    }
    assert(safe_at(t, c, b, v)) by {
        assert forall|k: int| 0 <= k < b implies #[trigger] protected_at(t, c, k, v) by {
            if k < maximum {
                assert(safe_at(s, c, maximum, v));
                safe_monotone(s, t, c, maximum, v);
                assert(protected_at(t, c, k, v));
            } else {
                assert forall|a: int| #![trigger q.contains(a)] q.contains(a) implies blocked_or_same(t, a, k, v) by {
                    let r = s.replies[(a, b)];
                    assert(reply_ok(s, c, a, b));
                    if r.last == k {
                        assert(k == maximum);
                        assert(voted(s, a, k, r.value));
                        assert(s.proposals[k] == v);
                    } else {
                        assert(r.last < k < b);
                        assert forall|w: Set<int>| !voted(t, a, k, w) by {
                            assert(!voted(s, a, k, w));
                        }
                    }
                }
                assert(quorum(c, q) && forall|a: int| #![trigger q.contains(a)] q.contains(a) ==> blocked_or_same(t, a, k, v));
            }
        }
    }
    assert forall|k: int| #![trigger t.proposals.dom().contains(k)] t.proposals.dom().contains(k) implies
        k >= 0 && safe_at(t, c, k, t.proposals[k]) && candidate(t, c, t.proposals[k]) by {
        if k != b {
            safe_monotone(s, t, c, k, s.proposals[k]);
            candidate_stable(s, t, c, s.proposals[k]);
        }
    }
    assert forall|a: int, k: int, w: Set<int>| voted(t, a, k, w) implies
        c.nodes.contains(a) && 0 <= k <= t.last[a]
        && t.proposals.dom().contains(k) && t.proposals[k] == w by {
        assert(voted(s, a, k, w));
        assert(s.proposals.dom().contains(k) && s.proposals[k] == w);
    }
    assert forall|a: int, k: int| #![trigger reply_ok(t, c, a, k)] t.replies.dom().contains((a, k))
        implies reply_ok(t, c, a, k) by {
        assert(reply_ok(s, c, a, k));
        reply_frame(s, t, c, a, k);
    }
    votes_frame(s, t, c);
}

pub proof fn accept_preserves_safe(s: State, t: State, c: Config,
                                  a: int, b: int, k: int, v: Set<int>)
    requires config_ok(c), inv(s, c), accept(s, t, c, a, b), safe_at(s, c, k, v),
    ensures safe_at(t, c, k, v),
{
    assert forall|r: int| 0 <= r < k implies #[trigger] protected_at(t, c, r, v) by {
        assert(protected_at(s, c, r, v));
        let q = choose|q: Set<int>| quorum(c, q)
            && forall|n: int| #![trigger q.contains(n)] q.contains(n) ==> blocked_or_same(s, n, r, v);
        assert forall|n: int| #![trigger q.contains(n)] q.contains(n) implies blocked_or_same(t, n, r, v) by {
            assert(blocked_or_same(s, n, r, v));
            if !voted(s, n, r, v) {
                if n == a { assert(b > r); }
                assert forall|w: Set<int>| !voted(t, n, r, w) by {
                    assert(!voted(s, n, r, w));
                }
            }
        }
        assert(quorum(c, q) && forall|n: int| #![trigger q.contains(n)] q.contains(n) ==> blocked_or_same(t, n, r, v));
    }
}

pub proof fn accept_preserves(s: State, t: State, c: Config, a: int, b: int)
    requires config_ok(c), inv(s, c), accept(s, t, c, a, b),
    ensures inv(t, c),
{
    assert(t.promise.dom() =~= c.nodes);
    assert(t.last.dom() =~= c.nodes);
    assert(t.value.dom() =~= c.nodes);
    assert forall|n: int| #![trigger c.nodes.contains(n)] c.nodes.contains(n) implies t.logs[n].subset_of(c.commands)
        && -1 <= t.last[n] <= t.promise[n] by {
        assert(-1 <= s.last[n] <= s.promise[n]);
    }
    assert forall|n: int, k: int, w: Set<int>| voted(t, n, k, w) implies
        c.nodes.contains(n) && 0 <= k <= t.last[n]
        && t.proposals.dom().contains(k) && t.proposals[k] == w by {
        if voted(s, n, k, w) { assert(k <= s.last[n] <= s.promise[n]); }
    }
    assert forall|n: int| #![trigger c.nodes.contains(n)] c.nodes.contains(n) && t.last[n] >= 0
        implies voted(t, n, t.last[n], t.value[n]) by {
        if n != a { assert(voted(s, n, s.last[n], s.value[n])); }
    }
    assert forall|n: int, k: int| #![trigger reply_ok(t, c, n, k)] t.replies.dom().contains((n, k))
        implies reply_ok(t, c, n, k) by {
        assert(reply_ok(s, c, n, k));
        let r = s.replies[(n, k)];
        assert forall|j: int, w: Set<int>| r.last < j < k
            implies !voted(t, n, j, w) by {
            assert(!voted(s, n, j, w));
            if n == a { assert(k <= s.promise[a] <= b); }
        }
    }
    assert forall|k: int| #![trigger t.proposals.dom().contains(k)] t.proposals.dom().contains(k) implies
        k >= 0 && safe_at(t, c, k, t.proposals[k]) && candidate(t, c, t.proposals[k]) by {
        accept_preserves_safe(s, t, c, a, b, k, s.proposals[k]);
        candidate_stable(s, t, c, s.proposals[k]);
    }
}

pub proof fn step_preserves(s: State, t: State, c: Config, action: Action)
    requires config_ok(c), inv(s, c), next(s, t, c, action),
    ensures inv(t, c), s.votes.subset_of(t.votes), s.frozen.subset_of(t.frozen),
        forall|a: int| #![trigger c.nodes.contains(a)] c.nodes.contains(a) ==> s.logs[a].subset_of(t.logs[a]),
{
    match action {
        Action::Acknowledge { node, command } => acknowledge_preserves(s, t, c, node, command),
        Action::Freeze { node } => freeze_preserves(s, t, c, node),
        Action::Prepare { node, ballot } => prepare_preserves(s, t, c, node, ballot),
        Action::Propose { ballot, quorum, maximum, value }
            => propose_preserves(s, t, c, ballot, quorum, maximum, value),
        Action::Accept { node, ballot } => accept_preserves(s, t, c, node, ballot),
        Action::Stutter => {},
    }
}

pub proof fn agreement(s: State, c: Config, b: int, v: Set<int>, k: int, w: Set<int>)
    requires config_ok(c), inv(s, c), chosen(s, c, b, v), chosen(s, c, k, w), b <= k,
    ensures v == w,
{
    let q = choose|q: Set<int>| quorum(c, q) && forall|a: int| #![trigger q.contains(a)] q.contains(a) ==> voted(s, a, b, v);
    let r = choose|q: Set<int>| quorum(c, q) && forall|a: int| #![trigger q.contains(a)] q.contains(a) ==> voted(s, a, k, w);
    quorum_intersection(c, q, r);
    let a = choose|a: int| q.contains(a) && r.contains(a);
    assert(voted(s, a, b, v));
    assert(voted(s, a, k, w));
    if b < k {
        assert(protected_at(s, c, b, w));
        let blocker = choose|q: Set<int>| quorum(c, q)
            && forall|a: int| #![trigger q.contains(a)] q.contains(a) ==> blocked_or_same(s, a, b, w);
        quorum_intersection(c, q, blocker);
        let n = choose|a: int| q.contains(a) && blocker.contains(a);
        assert(voted(s, n, b, v));
        assert(blocked_or_same(s, n, b, w));
        assert(voted(s, n, b, w));
    }
}

pub proof fn recovery_complete_and_safe(s: State, c: Config, b: int, v: Set<int>, x: int)
    requires config_ok(c), inv(s, c), chosen(s, c, b, v), fast_committed(s, c, x),
    ensures v.contains(x), forall|y: int| #![trigger v.contains(y)] v.contains(y) ==> !c.conflict.contains((x, y)),
{
    let voters = choose|q: Set<int>| quorum(c, q) && forall|a: int| #![trigger q.contains(a)] q.contains(a) ==> voted(s, a, b, v);
    quorum_intersection(c, voters, voters);
    let a = choose|a: int| voters.contains(a);
    assert(voted(s, a, b, v));
    assert(candidate(s, c, v));
    let q = choose|q: Set<int>| #![trigger quorum(c, q)] quorum(c, q) && q.subset_of(s.frozen) && v == selected(c, s.logs, q);
    selection_complete_and_safe(s, c, q, x);
}

pub open spec fn behavior(states: Seq<State>, actions: Seq<Action>, c: Config) -> bool {
    &&& states.len() == actions.len() + 1 && init(states[0], c)
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

pub proof fn reply_frame(s: State, t: State, c: Config, a: int, b: int)
    requires reply_ok(s, c, a, b), t.replies[(a, b)] == s.replies[(a, b)],
        t.logs[a] == s.logs[a], t.promise[a] >= s.promise[a],
        s.frozen.subset_of(t.frozen), t.votes == s.votes,
    ensures reply_ok(t, c, a, b),
{
    let r = s.replies[(a, b)];
    assert forall|k: int, w: Set<int>| r.last < k < b implies !voted(t, a, k, w) by {
        assert(!voted(s, a, k, w));
    }
}
pub proof fn votes_frame(s: State, t: State, c: Config)
    requires inv(s, c), t.votes == s.votes, t.last == s.last, t.value == s.value,
        s.proposals.dom().subset_of(t.proposals.dom()),
        forall|b: int| #![trigger t.proposals[b]] #![trigger s.proposals[b]] s.proposals.dom().contains(b) ==> t.proposals[b] == s.proposals[b],
    ensures
        forall|a: int, b: int, v: Set<int>| voted(t, a, b, v) ==>
            c.nodes.contains(a) && 0 <= b <= t.last[a]
            && t.proposals.dom().contains(b) && t.proposals[b] == v,
        forall|a: int| #![trigger c.nodes.contains(a)] c.nodes.contains(a) && t.last[a] >= 0
            ==> voted(t, a, t.last[a], t.value[a]),
{
    assert forall|a: int, b: int, v: Set<int>| voted(t, a, b, v) implies
        c.nodes.contains(a) && 0 <= b <= t.last[a]
        && t.proposals.dom().contains(b) && t.proposals[b] == v by {
        assert(voted(s, a, b, v));
        assert(s.proposals.dom().contains(b) && s.proposals[b] == v);
    }
    assert forall|a: int| #![trigger c.nodes.contains(a)] c.nodes.contains(a) && t.last[a] >= 0
        implies voted(t, a, t.last[a], t.value[a]) by {
        assert(voted(s, a, s.last[a], s.value[a]));
    }
}

pub proof fn history_monotone(states: Seq<State>, actions: Seq<Action>, c: Config, i: int, j: int)
    requires config_ok(c), behavior(states, actions, c), 0 <= i <= j < states.len(),
    ensures states[i].votes.subset_of(states[j].votes),
        forall|a: int| #![trigger c.nodes.contains(a)] c.nodes.contains(a) ==> states[i].logs[a].subset_of(states[j].logs[a]),
    decreases j - i,
{
    if i < j {
        history_monotone(states, actions, c, i, j - 1);
        reachable_inv(states, actions, c, j - 1);
        assert(next(states[j - 1], states[(j - 1) + 1], c, actions[j - 1]));
        step_preserves(states[j - 1], states[j], c, actions[j - 1]);
        assert forall|a: int| #![trigger c.nodes.contains(a)] c.nodes.contains(a)
            implies states[i].logs[a].subset_of(states[j].logs[a]) by {
            assert(states[i].logs[a].subset_of(states[j - 1].logs[a]));
            assert(states[j - 1].logs[a].subset_of(states[j].logs[a]));
        }
    }
}
pub proof fn certificates_monotone(s: State, t: State, c: Config, b: int, v: Set<int>, x: int)
    requires s.votes.subset_of(t.votes),
        forall|a: int| #![trigger c.nodes.contains(a)] c.nodes.contains(a) ==> s.logs[a].subset_of(t.logs[a]),
    ensures chosen(s, c, b, v) ==> chosen(t, c, b, v),
        fast_committed(s, c, x) ==> fast_committed(t, c, x),
{
    if chosen(s, c, b, v) {
        let q = choose|q: Set<int>| quorum(c, q)
            && forall|a: int| #![trigger q.contains(a)] q.contains(a) ==> voted(s, a, b, v);
        assert forall|a: int| #![trigger q.contains(a)] q.contains(a) implies voted(t, a, b, v) by {
            assert(voted(s, a, b, v));
        }
        assert(chosen(t, c, b, v));
    }
    assert(support(s.logs, c.nodes, x).subset_of(support(t.logs, c.nodes, x)));
    lemma_len_subset(support(s.logs, c.nodes, x), support(t.logs, c.nodes, x));
}
// The three observations can occur in ANY order. In particular a delayed fast
// certificate may finish after a recovery set was already chosen.
pub proof fn execution_safety(states: Seq<State>, actions: Seq<Action>, c: Config,
                             i: int, j: int, k: int, x: int,
                             b: int, v: Set<int>, d: int, w: Set<int>)
    requires config_ok(c), behavior(states, actions, c),
        0 <= i < states.len(), 0 <= j < states.len(), 0 <= k < states.len(),
        fast_committed(states[i], c, x), chosen(states[j], c, b, v), chosen(states[k], c, d, w),
    ensures v == w, v.contains(x),
        forall|y: int| #![trigger v.contains(y)] v.contains(y) ==> !c.conflict.contains((x, y)),
{
    let end = states.len() - 1;
    reachable_inv(states, actions, c, end);
    history_monotone(states, actions, c, i, end);
    history_monotone(states, actions, c, j, end);
    history_monotone(states, actions, c, k, end);
    certificates_monotone(states[i], states[end], c, b, v, x);
    certificates_monotone(states[j], states[end], c, b, v, x);
    certificates_monotone(states[k], states[end], c, d, w, x);
    if b <= d { agreement(states[end], c, b, v, d, w); }
    else { agreement(states[end], c, d, w, b, v); }
    recovery_complete_and_safe(states[end], c, b, v, x);
}

} // verus!

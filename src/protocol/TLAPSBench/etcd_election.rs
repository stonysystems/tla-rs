//! Election proof with a passive history of released positive vote responses.
use vstd::prelude::*;
use super::etcd::*;
use super::temporal::Behavior;
verus! {
pub open spec fn node_inv(s: LState, c: Constants, i: int) -> bool {
    let n = s.nodes[i];
    n.disk.term <= n.term
    && (n.term == n.disk.term && n.disk.voted_for is Some ==> n.voted_for == n.disk.voted_for)
    && (n.role != Role::Follower ==> n.voted_for == Some(i) && c.voters.contains(i))
    && n.granted.subset_of(c.voters)
    && (n.role == Role::Leader ==> quorum(n.granted, c))
    && (forall |v: int| n.role != Role::Follower && n.granted.contains(v) ==> s.votes.contains(Ballot { voter: v, term: n.term, candidate: i }))
}
pub open spec fn message_wf(m: Message, c: Constants) -> bool {
    c.servers.contains(m.source) && c.servers.contains(m.dest)
    && (m.body is VoteRequest || positive(m) ==> c.voters.contains(m.source) && c.voters.contains(m.dest))
}
pub open spec fn pending_inv(s: LState, c: Constants, m: Message) -> bool {
    message_wf(m, c) && (positive(m) ==> {
        let n = s.nodes[m.source];
        n.disk.term <= m.term <= n.term
        && (m.term == n.term ==> n.voted_for == Some(m.dest))
        && (m.term == n.disk.term && n.disk.voted_for is Some ==> n.disk.voted_for == Some(m.dest))
    })
}
pub open spec fn history_inv(s: LState, c: Constants, b: Ballot) -> bool {
    c.voters.contains(b.voter) && c.voters.contains(b.candidate) && c.servers.contains(b.voter)
    && b.term <= s.nodes[b.voter].disk.term
    && (b.term == s.nodes[b.voter].disk.term ==> s.nodes[b.voter].disk.voted_for == Some(b.candidate))
}
pub open spec fn compatible(a: Ballot, b: Ballot) -> bool {
    a.voter == b.voter && a.term == b.term ==> a.candidate == b.candidate
}
pub open spec fn inductive(s: LState, c: Constants) -> bool {
    s.nodes.dom() == c.servers
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] node_inv(s, c, i))
    && (forall |m: Message| #[trigger] s.pending.count(m) > 0 ==> pending_inv(s, c, m))
    && (forall |m: Message| #[trigger] s.messages.count(m) > 0 ==> message_wf(m, c) && (positive(m) ==> s.votes.contains(ballot(m))))
    && (forall |b: Ballot| s.votes.contains(b) ==> #[trigger] history_inv(s, c, b))
    && (forall |a: Ballot, b: Ballot| s.votes.contains(a) && s.votes.contains(b) ==> #[trigger] compatible(a, b))
    && (forall |a: Message, b: Message| #[trigger] s.pending.count(a) > 0 && #[trigger] s.pending.count(b) > 0 && positive(a) && positive(b) ==> compatible(ballot(a), ballot(b)))
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c), c)
{
    broadcast use vstd::multiset::group_multiset_axioms;
    assert(initial(c).nodes.dom() =~= c.servers);
}
pub proof fn pending_history_compatible(s: LState, c: Constants, m: Message, b: Ballot)
    requires inductive(s, c), s.pending.count(m) > 0, positive(m), s.votes.contains(b)
    ensures compatible(ballot(m), b)
{
    assert(pending_inv(s, c, m));
    assert(history_inv(s, c, b));
}
pub proof fn preserve_node(s: LState, c: Constants, a: Action, i: int)
    requires inductive(s, c), enabled(s, c, a), c.servers.contains(i)
    ensures node_inv(apply(s, c, a), c, i)
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    let u = apply(s, c, a);
    assert(node_inv(s, c, i));
    assert(s.votes.subset_of(u.votes));
    if let Action::Receive { m, how } = a {
        assert(s.messages.count(m) > 0);
        assert(message_wf(m, c));
        if i == m.dest && how == Receive::VoteResponse {
            assert(s.nodes[i].granted.subset_of(u.nodes[i].granted));
            vstd::set_lib::lemma_len_subset(s.nodes[i].granted, u.nodes[i].granted);
        }
    }
    assert forall |v: int| u.nodes[i].role != Role::Follower && u.nodes[i].granted.contains(v)
        implies u.votes.contains(Ballot { voter: v, term: u.nodes[i].term, candidate: i }) by {
        if s.nodes[i].role != Role::Follower && s.nodes[i].granted.contains(v) {
            assert(s.votes.contains(Ballot { voter: v, term: s.nodes[i].term, candidate: i }));
        }
    }
}
pub proof fn preserve_pending(s: LState, c: Constants, a: Action, m: Message)
    requires inductive(s, c), enabled(s, c, a), apply(s, c, a).pending.count(m) > 0
    ensures pending_inv(apply(s, c, a), c, m)
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    if s.pending.count(m) > 0 { assert(pending_inv(s, c, m)); }
    assert(c.servers.contains(m.source));
    assert(node_inv(s, c, m.source));
}
pub proof fn preserve_pending_pair(s: LState, c: Constants, a: Action, m: Message, n: Message)
    requires inductive(s, c), enabled(s, c, a), apply(s, c, a).pending.count(m) > 0,
        apply(s, c, a).pending.count(n) > 0, positive(m), positive(n)
    ensures compatible(ballot(m), ballot(n))
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    if s.pending.count(m) > 0 { assert(pending_inv(s, c, m)); }
    if s.pending.count(n) > 0 { assert(pending_inv(s, c, n)); }
    if s.pending.count(m) > 0 && s.pending.count(n) > 0 { assert(compatible(ballot(m), ballot(n))); }
    else if m.source == n.source && m.term == n.term {
        preserve_pending(s, c, a, m);
        preserve_pending(s, c, a, n);
        assert(m.term == apply(s, c, a).nodes[m.source].term);
    }
}
pub proof fn released_origin(s: LState, i: int, b: Ballot) -> (m: Message)
    requires released_votes(s, i).contains(b)
    ensures s.pending.count(m) > 0, m.source == i, positive(m), ballot(m) == b
{
    broadcast use {vstd::multiset::Multiset::dom_ensures, Set::lemma_map_contains};
    choose |m: Message| s.pending.dom().filter(|m: Message| m.source == i && positive(m)).contains(m) && ballot(m) == b
}
pub proof fn record_released(s: LState, i: int, m: Message)
    requires s.pending.count(m) > 0, m.source == i, positive(m)
    ensures released_votes(s, i).contains(ballot(m))
{
    broadcast use {vstd::multiset::Multiset::dom_ensures, Set::lemma_map_contains};
    assert(s.pending.dom().filter(|m: Message| m.source == i && positive(m)).contains(m));
}
pub proof fn preserve_history(s: LState, c: Constants, a: Action, b: Ballot)
    requires inductive(s, c), enabled(s, c, a), apply(s, c, a).votes.contains(b)
    ensures history_inv(apply(s, c, a), c, b)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    if s.votes.contains(b) {
        assert(history_inv(s, c, b));
        assert(node_inv(s, c, b.voter));
    } else {
        if let Action::Ready(i) = a {
            let m = released_origin(s, i, b);
            assert(pending_inv(s, c, m));
        } else { assert(false); }
    }
}
pub proof fn preserve_history_pair(s: LState, c: Constants, a: Action, x: Ballot, y: Ballot)
    requires inductive(s, c), enabled(s, c, a), apply(s, c, a).votes.contains(x), apply(s, c, a).votes.contains(y)
    ensures compatible(x, y)
{
    reveal(apply); reveal(receive);
    if s.votes.contains(x) && s.votes.contains(y) { assert(compatible(x, y)); }
    else if let Action::Ready(i) = a {
        if !s.votes.contains(x) {
            let m = released_origin(s, i, x);
            if s.votes.contains(y) { pending_history_compatible(s, c, m, y); }
            else {
                let n = released_origin(s, i, y);
                assert(compatible(ballot(m), ballot(n)));
            }
        } else {
            let n = released_origin(s, i, y);
            pending_history_compatible(s, c, n, x);
        }
    } else { assert(false); }
}
pub proof fn preserve_message(s: LState, c: Constants, a: Action, m: Message)
    requires inductive(s, c), enabled(s, c, a), apply(s, c, a).messages.count(m) > 0
    ensures message_wf(m, c), positive(m) ==> apply(s, c, a).votes.contains(ballot(m))
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    if s.messages.count(m) > 0 { assert(message_wf(m, c)); }
    else if let Action::Ready(i) = a {
        assert(s.pending.count(m) > 0);
        assert(pending_inv(s, c, m));
        if positive(m) { record_released(s, i, m); }
    } else { assert(false); }
}
pub proof fn preserve_domain(s: LState, c: Constants, a: Action)
    requires inductive(s, c), enabled(s, c, a)
    ensures apply(s, c, a).nodes.dom() == c.servers
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    if let Action::Receive { m, how } = a { assert(message_wf(m, c)); }
    assert(apply(s, c, a).nodes.dom() =~= c.servers);
}
pub proof fn preserve_inductive(s: LState, c: Constants, a: Action)
    requires inductive(s, c), enabled(s, c, a)
    ensures inductive(apply(s, c, a), c)
{
    let u = apply(s, c, a);
    preserve_domain(s, c, a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node_inv(u, c, i) by { preserve_node(s, c, a, i); }
    assert forall |m: Message| #[trigger] u.pending.count(m) > 0 implies pending_inv(u, c, m) by { preserve_pending(s, c, a, m); }
    assert forall |m: Message| #[trigger] u.messages.count(m) > 0 implies message_wf(m, c) && (positive(m) ==> u.votes.contains(ballot(m))) by {
        preserve_message(s, c, a, m);
    }
    assert forall |b: Ballot| u.votes.contains(b) implies #[trigger] history_inv(u, c, b) by { preserve_history(s, c, a, b); }
    assert forall |x: Ballot, y: Ballot| u.votes.contains(x) && u.votes.contains(y) implies #[trigger] compatible(x, y) by {
        preserve_history_pair(s, c, a, x, y);
    }
    assert forall |m: Message, n: Message| #[trigger] u.pending.count(m) > 0 && #[trigger] u.pending.count(n) > 0 && positive(m) && positive(n)
        implies compatible(ballot(m), ballot(n)) by { preserve_pending_pair(s, c, a, m, n); }
}
pub proof fn majorities_intersect(a: Set<int>, b: Set<int>, c: Constants) -> (v: int)
    requires quorum(a, c), quorum(b, c)
    ensures a.contains(v), b.contains(v)
{
    if a.disjoint(b) {
        vstd::set_lib::lemma_set_disjoint_lens(a, b);
        assert(a.union(b).subset_of(c.voters));
        vstd::set_lib::lemma_len_subset(a.union(b), c.voters);
        assert(false);
    }
    choose |v: int| a.contains(v) && b.contains(v)
}
pub proof fn unique_leader(s: LState, c: Constants)
    requires inductive(s, c)
    ensures more_than_one_leader(s, c)
{
    assert forall |i: int, j: int| c.servers.contains(i) && c.servers.contains(j)
        && s.nodes[i].role == Role::Leader && s.nodes[j].role == Role::Leader && s.nodes[i].term == s.nodes[j].term implies i == j by {
        assert(node_inv(s, c, i)); assert(node_inv(s, c, j));
        let v = majorities_intersect(s.nodes[i].granted, s.nodes[j].granted, c);
        let a = Ballot { voter: v, term: s.nodes[i].term, candidate: i };
        let b = Ballot { voter: v, term: s.nodes[j].term, candidate: j };
        assert(s.votes.contains(a) && s.votes.contains(b));
        assert(compatible(a, b));
    }
}
pub open spec fn safety_spec(b: Behavior<LState>, c: Constants) -> bool {
    valid_constants(c) && b[0] == initial(c)
    && (forall |k: int| k >= 0 ==> b.dom().contains(k))
    && forall |k: int| k >= 0 ==> #[trigger] next(b[k], b[k+1], c)
}
pub proof fn safety_at(b: Behavior<LState>, c: Constants, k: int)
    requires safety_spec(b, c), k >= 0
    ensures inductive(b[k], c), more_than_one_leader(b[k], c)
    decreases k
{
    if k == 0 { initial_inductive(c); }
    else {
        safety_at(b, c, k-1);
        let i = k-1;
        assert(next(b[i], b[i+1], c)); reveal(next);
        let a = choose |a: Action| #[trigger] enabled(b[i], c, a) && b[i+1] == apply(b[i], c, a);
        preserve_inductive(b[i], c, a);
    }
    unique_leader(b[k], c);
}
// The source calls this goal MoreThanOneLeader, separately from ElectionSafety.
pub proof fn more_than_one_leader_correct(b: Behavior<LState>, c: Constants)
    requires safety_spec(b, c)
    ensures forall |k: int| k >= 0 ==> #[trigger] more_than_one_leader(b[k], c)
{
    assert forall |k: int| k >= 0 implies #[trigger] more_than_one_leader(b[k], c) by { safety_at(b, c, k); }
}
} // verus!

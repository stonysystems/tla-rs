//! Public safety theorems for the two-round CausalMesh protocol.
use vstd::prelude::*;
use super::vc::*;
use super::ring::*;
use super::types::*;
use super::model::*;
use super::behavior::*;
use super::properties::*;
use super::invariants::*;
use super::step_tail::*;
use super::step_forward::*;
use super::step_write::*;
use super::step_read::*;
use super::step_misc::*;
use super::past::*;

verus! {

pub proof fn lemma_step(c: Constants, s: State, s2: State, a: Action)
    requires inv(c, s), step(c, s, s2, a)
    ensures inv(c, s2)
{
    reveal(step);
    match a {
        Action::Write { client, server, key, value, gvc } =>
            lemma_step_write(c, s, s2, client, server, key, value, gvc),
        Action::Propagate { src, mid, after } => {
            if is_tail(c, s, src) { lemma_step_tail(c, s, s2, src, mid, after); }
            else { lemma_step_forward(c, s, s2, src, mid, after); }
        },
        Action::Read { client, server, key, after, result } =>
            lemma_step_read(c, s, s2, client, server, key, after, result),
        Action::Start { client } => lemma_step_start(c, s, s2, client),
        Action::Fork { parent, child } => lemma_step_fork(c, s, s2, parent, child),
        Action::Stutter => {},
    }
}

/// The invariant holds in every state of every behavior with two rounds.
pub proof fn lemma_behavior_inv(c: Constants, states: Seq<State>, i: int)
    requires behavior(c, states), c.rounds >= 2, 0 <= i < states.len()
    ensures inv(c, states[i]), past_ok(states[i])
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_init(c, states[0]);
        lemma_init_past(c, states[0]);
    } else {
        lemma_behavior_inv(c, states, i - 1);
        let k = i - 1;
        lemma_behavior_step(c, states, k);
        assert(states[k + 1] == states[i]);
        reveal(next);
        let a = choose|a: Action| #[trigger] step(c, states[i - 1], states[i], a);
        lemma_step(c, states[i - 1], states[i], a);
        lemma_step_past(c, states[i - 1], states[i], a);
    }
}

/// Contexts only grow along a happens-before path.
pub proof fn lemma_hb_path_ctx(c: Constants, s: State, p: Seq<int>, t: int)
    requires events_ok(c, s), hb_path(s.history, p), 0 <= t < p.len()
    ensures ev_ctx(s.history[p[0]]).subset_of(ev_ctx(s.history[p[t]]))
    decreases t
{
    if t > 0 {
        lemma_hb_path_ctx(c, s, p, t - 1);
        assert(edge(s.history, p[t - 1], p[t]));
        lemma_edge_ctx(c, s, p[t - 1], p[t]);
    }
}

pub proof fn lemma_hb_ctx(c: Constants, s: State, i: int, j: int)
    requires events_ok(c, s), hb(s.history, i, j)
    ensures ev_ctx(s.history[i]).subset_of(ev_ctx(s.history[j])), 0 <= i < s.history.len(), 0 <= j < s.history.len()
{
    let p = choose|p: Seq<int>| #[trigger] hb_path(s.history, p) && p[0] == i && p.last() == j;
    lemma_hb_path_ctx(c, s, p, p.len() - 1);
    assert(edge(s.history, p[0], p[1]));
    assert(edge(s.history, p[p.len() - 2], p[p.len() - 1]));
}

pub proof fn lemma_causal_visibility(c: Constants, s: State)
    requires inv(c, s)
    ensures causal_visibility(s.history)
{
    let h = s.history;
    assert forall|i: int, j: int| #[trigger] hb(h, i, j) && h[i] is Write && h[j] is Read
        && h[i]->Write_version.key == h[j]->Read_key
        implies le(h[i]->Write_version.vc, h[j]->Read_vc) by {
        lemma_hb_ctx(c, s, i, j);
        lemma_event(c, s, i);
        lemma_event(c, s, j);
        assert(ev_ctx(h[j]).contains(h[i]->Write_version));
    }
}

/// Every positive entry of `x` is the entry of some write of `k` in `ctx`
/// that `y` dominates, so `y` dominates `x`.
pub proof fn lemma_attained_le(n: nat, ctx: Set<Version>, k: int, x: VC, y: VC)
    requires x.len() == n, y.len() == n,
        forall|o: int| 0 <= o < n && #[trigger] x[o] >= 1 ==>
            exists|w: Version| #[trigger] ctx.contains(w) && w.key == k && w.vc[o] == x[o],
        forall|w: Version| #[trigger] ctx.contains(w) && w.key == k ==> le(w.vc, y),
    ensures le(x, y)
{
    assert forall|o: int| 0 <= o < x.len() implies #[trigger] x[o] <= y[o] by {
        if x[o] >= 1 {
            let w = choose|w: Version| #[trigger] ctx.contains(w) && w.key == k && w.vc[o] == x[o];
            assert(le(w.vc, y));
        }
    }
}

pub proof fn lemma_read_clock_len(c: Constants, s: State, i: int)
    requires inv(c, s), 0 <= i < s.history.len(), s.history[i] is Read
    ensures s.history[i]->Read_vc.len() == c.n, s.history[i]->Read_server_vc.len() == c.n
{
    reveal(clocks_ok);
}

pub proof fn lemma_session_guarantees(c: Constants, s: State)
    requires inv(c, s)
    ensures read_your_writes(s.history), monotonic_reads(s.history),
        writes_follow_reads(s.history), monotonic_writes(s.history)
{
    let h = s.history;
    lemma_causal_visibility(c, s);
    assert forall|i: int, j: int| #![trigger h[i], h[j]] 0 <= i < j < h.len() && h[i] is Write && h[j] is Read
        && actor(h[i]) == actor(h[j]) && h[i]->Write_version.key == h[j]->Read_key
        implies le(h[i]->Write_version.vc, h[j]->Read_vc) by {
        assert(edge(h, i, j));
        lemma_edge_hb(h, i, j);
    }
    assert forall|i: int, j: int| #![trigger h[i], h[j]] 0 <= i < j < h.len() && h[i] is Read && h[j] is Read
        && actor(h[i]) == actor(h[j]) && h[i]->Read_key == h[j]->Read_key
        implies le(h[i]->Read_vc, h[j]->Read_vc) by {
        assert(edge(h, i, j));
        lemma_edge_ctx(c, s, i, j);
        lemma_event(c, s, i);
        lemma_event(c, s, j);
        lemma_read_clock_len(c, s, i);
        lemma_read_clock_len(c, s, j);
        lemma_attained_le(c.n, ev_ctx(h[i]), h[i]->Read_key, h[i]->Read_vc, h[j]->Read_vc);
    }
    assert forall|i: int, j: int, k: int, l: int| #![trigger h[i], h[j], h[k], h[l]]
        0 <= i < j < k < l < h.len()
        && h[i] is Read && h[j] is Write && actor(h[i]) == actor(h[j])
        && observes(h, j, k) && h[l] is Read && actor(h[k]) == actor(h[l])
        && h[l]->Read_key == h[i]->Read_key
        implies le(h[i]->Read_server_vc, h[l]->Read_vc) by {
        assert(edge(h, i, j) && edge(h, j, k) && edge(h, k, l));
        lemma_edge_ctx(c, s, i, j);
        lemma_edge_ctx(c, s, j, k);
        lemma_edge_ctx(c, s, k, l);
        lemma_event(c, s, i);
        lemma_event(c, s, l);
        lemma_read_clock_len(c, s, i);
        lemma_read_clock_len(c, s, l);
        lemma_attained_le(c.n, ev_ctx(h[l]), h[i]->Read_key, h[i]->Read_server_vc, h[l]->Read_vc);
    }
    assert forall|i: int, j: int, k: int, l: int| #![trigger h[i], h[j], h[k], h[l]]
        0 <= i < j < k < l < h.len()
        && h[i] is Write && h[j] is Write && actor(h[i]) == actor(h[j])
        && observes(h, j, k) && h[l] is Read && actor(h[k]) == actor(h[l])
        && h[l]->Read_key == h[i]->Write_version.key
        implies le(h[i]->Write_version.vc, h[l]->Read_vc) by {
        assert(edge(h, i, j) && edge(h, j, k) && edge(h, k, l));
        lemma_edge_ctx(c, s, i, j);
        lemma_edge_ctx(c, s, j, k);
        lemma_edge_ctx(c, s, k, l);
        lemma_event(c, s, i);
        lemma_event(c, s, l);
    }
}

/// Reads along happens-before are monotonic, in any session.
pub proof fn lemma_causal_monotonic_reads(c: Constants, s: State)
    requires inv(c, s)
    ensures causal_monotonic_reads(s.history)
{
    let h = s.history;
    assert forall|i: int, j: int| #[trigger] hb(h, i, j) && h[i] is Read && h[j] is Read
        && h[i]->Read_key == h[j]->Read_key
        implies le(h[i]->Read_vc, h[j]->Read_vc) by {
        lemma_hb_ctx(c, s, i, j);
        lemma_event(c, s, i);
        lemma_event(c, s, j);
        lemma_read_clock_len(c, s, i);
        lemma_read_clock_len(c, s, j);
        lemma_attained_le(c.n, ev_ctx(h[i]), h[i]->Read_key, h[i]->Read_vc, h[j]->Read_vc);
    }
}

/// A read's value comes from a write in its context, which happens before it.
pub proof fn lemma_reads_valid(c: Constants, s: State)
    requires inv(c, s), past_ok(s)
    ensures reads_valid(s.history)
{
    let h = s.history;
    assert forall|j: int| #![trigger h[j]] 0 <= j < h.len() && h[j] is Read implies
        (h[j]->Read_vc == zero(h[j]->Read_vc.len()) && h[j]->Read_value == 0)
        || exists|i: int| #[trigger] hb(h, i, j) && h[i] is Write
            && h[i]->Write_version.key == h[j]->Read_key
            && h[i]->Write_version.value == h[j]->Read_value
            && le(h[i]->Write_version.vc, h[j]->Read_vc) by {
        lemma_event(c, s, j);
        lemma_read_clock_len(c, s, j);
        let e = h[j];
        if !(e->Read_vc == zero(c.n) && e->Read_value == 0) {
            let w = choose|w: Version| #[trigger] ev_ctx(e).contains(w) && w.key == e->Read_key
                && le(w.vc, e->Read_vc) && w.value == e->Read_value;
            reveal(past_ok);
            assert(write_before(h, w, j));
            let i = choose|i: int| #![trigger h[i]] 0 <= i < h.len() && h[i] is Write && h[i]->Write_version == w
                && (i == j || hb(h, i, j));
            assert(hb(h, i, j));
        }
    }
}

/// Definition 1 for the versions C-cache holds: at every server, a write that
/// C-cache covers and that is not pending in I-cache has every version
/// matching its dependencies covered and not pending.
pub open spec fn caches_are_cuts(c: Constants, s: State) -> bool {
    forall|q: int| #[trigger] server(c.n, q) ==> cut_srv(c.n, s.writes, s.servers[q])
}

/// Safety of two-round CausalMesh, for every state of every finite behavior:
/// causal visibility and monotonic reads over happens-before, the paper's four
/// session guarantees (Theorems 1-4), read validity, and causal-cut C-caches.
pub proof fn theorem_causalmesh_safety(c: Constants, states: Seq<State>, i: int)
    requires behavior(c, states), c.rounds >= 2, 0 <= i < states.len()
    ensures
        causal_visibility(states[i].history),
        causal_monotonic_reads(states[i].history),
        read_your_writes(states[i].history),
        monotonic_reads(states[i].history),
        writes_follow_reads(states[i].history),
        monotonic_writes(states[i].history),
        reads_valid(states[i].history),
        caches_are_cuts(c, states[i]),
{
    let s = states[i];
    lemma_behavior_inv(c, states, i);
    lemma_causal_visibility(c, s);
    lemma_session_guarantees(c, s);
    lemma_causal_monotonic_reads(c, s);
    lemma_reads_valid(c, s);
    assert forall|q: int| #[trigger] server(c.n, q) implies cut_srv(c.n, s.writes, s.servers[q]) by {
        reveal(cut_ok);
        assert(cut(c, s, q));
    }
}

} // verus!

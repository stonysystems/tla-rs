//! The causal context of every event is its happens-before past: each write
//! in it happens before the event, or is the event itself.
use vstd::prelude::*;
use super::vc::*;
use super::types::*;
use super::model::*;
use super::behavior::*;
use super::properties::*;
use super::invariants::*;

verus! {

pub proof fn lemma_edge_hb(h: Seq<Event>, i: int, j: int)
    requires edge(h, i, j)
    ensures hb(h, i, j)
{
    let p = seq![i, j];
    assert(hb_path(h, p));
    assert(p[0] == i && p.last() == j);
}

/// Happens-before survives appending events.
pub proof fn lemma_hb_push(h: Seq<Event>, e: Event, i: int, k: int)
    requires hb(h, i, k)
    ensures hb(h.push(e), i, k)
{
    let h2 = h.push(e);
    let p = choose|p: Seq<int>| #[trigger] hb_path(h, p) && p[0] == i && p.last() == k;
    assert(hb_path(h2, p)) by {
        assert forall|t: int, u: int| #![trigger p[t], p[u]]
            0 <= t && u == t + 1 && u < p.len() implies edge(h2, p[t], p[u]) by {
            assert(edge(h, p[t], p[u]));
            assert(h2[p[t]] == h[p[t]] && h2[p[u]] == h[p[u]]);
        }
    }
    assert(hb_path(h2, p) && p[0] == i && p.last() == k);
}

pub proof fn lemma_hb_extend(h: Seq<Event>, i: int, k: int, j: int)
    requires i == k || hb(h, i, k), edge(h, k, j)
    ensures hb(h, i, j)
{
    if i == k {
        lemma_edge_hb(h, k, j);
    } else {
        let p = choose|p: Seq<int>| #[trigger] hb_path(h, p) && p[0] == i && p.last() == k;
        let p2 = p.push(j);
        assert(hb_path(h, p2)) by {
            assert forall|t: int, u: int| #![trigger p2[t], p2[u]]
                0 <= t && u == t + 1 && u < p2.len() implies edge(h, p2[t], p2[u]) by {
                if u < p.len() {
                    assert(p2[t] == p[t] && p2[u] == p[u]);
                    assert(edge(h, p[t], p[u]));
                } else {
                    assert(p2[t] == p.last());
                }
            }
        }
        assert(p2[0] == i && p2.last() == j);
    }
}

/// The write of w is event j or happens before it.
pub open spec fn write_before(h: Seq<Event>, w: Version, j: int) -> bool {
    exists|i: int| #![trigger h[i]] 0 <= i < h.len() && h[i] is Write && h[i]->Write_version == w
        && (i == j || hb(h, i, j))
}

/// The write of w is at or before an event of client cid, or before the fork
/// that created cid, so it happens before cid's next operation.
pub open spec fn write_reaches(h: Seq<Event>, w: Version, cid: int) -> bool {
    exists|k: int| #![trigger h[k]] 0 <= k < h.len() && write_before(h, w, k)
        && (actor(h[k]) == cid || (h[k] is Fork && h[k]->Fork_child == cid))
}

#[verifier::opaque]
pub open spec fn past_ok(s: State) -> bool {
    &&& forall|j: int, w: Version| #![trigger ev_ctx(s.history[j]).contains(w)]
        0 <= j < s.history.len() && ev_ctx(s.history[j]).contains(w) ==> write_before(s.history, w, j)
    &&& forall|cid: int, w: Version| #![trigger s.ctx[cid].contains(w)]
        s.ctx.dom().contains(cid) && s.ctx[cid].contains(w) ==> write_reaches(s.history, w, cid)
}

pub proof fn lemma_before_push(h: Seq<Event>, e: Event, w: Version, k: int)
    requires write_before(h, w, k)
    ensures write_before(h.push(e), w, k)
{
    let i = choose|i: int| #![trigger h[i]] 0 <= i < h.len() && h[i] is Write && h[i]->Write_version == w
        && (i == k || hb(h, i, k));
    assert(h.push(e)[i] == h[i]);
    if i != k { lemma_hb_push(h, e, i, k); }
}

pub proof fn lemma_reaches_push(h: Seq<Event>, e: Event, w: Version, cid: int)
    requires write_reaches(h, w, cid)
    ensures write_reaches(h.push(e), w, cid)
{
    let k = choose|k: int| #![trigger h[k]] 0 <= k < h.len() && write_before(h, w, k)
        && (actor(h[k]) == cid || (h[k] is Fork && h[k]->Fork_child == cid));
    lemma_before_push(h, e, w, k);
    assert(h.push(e)[k] == h[k]);
}

pub proof fn lemma_before_edge(h: Seq<Event>, w: Version, k: int, j: int)
    requires write_before(h, w, k), edge(h, k, j)
    ensures write_before(h, w, j)
{
    let i = choose|i: int| #![trigger h[i]] 0 <= i < h.len() && h[i] is Write && h[i]->Write_version == w
        && (i == k || hb(h, i, k));
    lemma_hb_extend(h, i, k, j);
}

/// A write that reaches a client happens before that client's next event.
pub proof fn lemma_reaches_next(h: Seq<Event>, e: Event, w: Version)
    requires write_reaches(h, w, actor(e))
    ensures write_before(h.push(e), w, h.len() as int)
{
    let h2 = h.push(e);
    let j = h.len() as int;
    let k = choose|k: int| #![trigger h[k]] 0 <= k < h.len() && write_before(h, w, k)
        && (actor(h[k]) == actor(e) || (h[k] is Fork && h[k]->Fork_child == actor(e)));
    lemma_before_push(h, e, w, k);
    assert(h2[k] == h[k] && h2[j] == e);
    assert(edge(h2, k, j));
    lemma_before_edge(h2, w, k, j);
}

/// The new event j's context lies in its past, so every context does.
pub proof fn lemma_past_push(s: State, s2: State, e: Event)
    requires past_ok(s), s2.history == s.history.push(e),
        forall|w: Version| #[trigger] ev_ctx(e).contains(w) ==> write_before(s2.history, w, s.history.len() as int),
    ensures forall|j: int, w: Version| #![trigger ev_ctx(s2.history[j]).contains(w)]
        0 <= j < s2.history.len() && ev_ctx(s2.history[j]).contains(w) ==> write_before(s2.history, w, j)
{
    reveal(past_ok);
    let h = s.history;
    assert forall|j: int, w: Version| #![trigger ev_ctx(s2.history[j]).contains(w)]
        0 <= j < s2.history.len() && ev_ctx(s2.history[j]).contains(w) implies write_before(s2.history, w, j) by {
        if j < h.len() {
            assert(s2.history[j] == h[j]);
            lemma_before_push(h, e, w, j);
        }
    }
}

pub proof fn lemma_past_write(c: Constants, s: State, s2: State, cid: int, srv: int, key: int, value: int, gvc: VC)
    requires shape_ok(c, s), past_ok(s), client_write(c, s, s2, cid, srv, key, value, gvc)
    ensures past_ok(s2)
{
    let v = new_version(c, s, cid, srv, key, value, gvc);
    let ctx = s.ctx[cid].insert(v);
    let e = Event::Write { client: cid, version: v, ctx };
    let h = s.history;
    let h2 = s2.history;
    let j = h.len() as int;
    assert(h2 == h.push(e) && h2[j] == e);
    assert(s2.ctx == s.ctx.insert(cid, ctx));
    assert forall|w: Version| #[trigger] ev_ctx(e).contains(w) implies write_before(h2, w, j) by {
        if w != v {
            reveal(past_ok);
            assert(s.ctx[cid].contains(w));
            lemma_reaches_next(h, e, w);
        }
    }
    lemma_past_push(s, s2, e);
    reveal(past_ok);
    assert forall|id: int, w: Version| #![trigger s2.ctx[id].contains(w)]
        s2.ctx.dom().contains(id) && s2.ctx[id].contains(w) implies write_reaches(h2, w, id) by {
        if id == cid {
            assert(ev_ctx(e).contains(w));
            assert(write_before(h2, w, j) && actor(h2[j]) == cid);
        } else {
            assert(s.ctx[id].contains(w));
            lemma_reaches_push(h, e, w, id);
        }
    }
}

pub proof fn lemma_past_read(c: Constants, s: State, s2: State, cid: int, srv: int, key: int, t: Server, r: Entry)
    requires shape_ok(c, s), past_ok(s), client_read(c, s, s2, cid, srv, key, t, r)
    ensures past_ok(s2)
{
    let ev = entry(t, c.n, key);
    let obs = observed(s, key, ev.vc);
    let ctx = s.ctx[cid].union(obs);
    let e = Event::Read { client: cid, key, server_vc: ev.vc, vc: r.vc, value: r.value, ctx };
    let h = s.history;
    let h2 = s2.history;
    let j = h.len() as int;
    assert(h2 == h.push(e) && h2[j] == e);
    assert(s2.ctx == s.ctx.insert(cid, ctx));
    assert forall|w: Version| #[trigger] ev_ctx(e).contains(w) implies write_before(h2, w, j) by {
        reveal(past_ok);
        if s.ctx[cid].contains(w) {
            lemma_reaches_next(h, e, w);
        } else {
            assert(obs.contains(w));
            let i0 = choose|i: int| #![trigger s.history[i]] 0 <= i < s.history.len() && {
                let x = s.history[i];
                &&& x is Write
                &&& x->Write_version.key == key && le(x->Write_version.vc, ev.vc)
                &&& x->Write_ctx.contains(w)
            };
            assert(ev_ctx(h[i0]).contains(w));
            lemma_before_push(h, e, w, i0);
            assert(h2[i0] == h[i0]);
            assert(observes(h2, i0, j));
            assert(edge(h2, i0, j));
            lemma_before_edge(h2, w, i0, j);
        }
    }
    lemma_past_push(s, s2, e);
    reveal(past_ok);
    assert forall|id: int, w: Version| #![trigger s2.ctx[id].contains(w)]
        s2.ctx.dom().contains(id) && s2.ctx[id].contains(w) implies write_reaches(h2, w, id) by {
        if id == cid {
            assert(ev_ctx(e).contains(w));
            assert(write_before(h2, w, j) && actor(h2[j]) == cid);
        } else {
            assert(s.ctx[id].contains(w));
            lemma_reaches_push(h, e, w, id);
        }
    }
}

pub proof fn lemma_past_fork(c: Constants, s: State, s2: State, parent: int, child: int)
    requires shape_ok(c, s), past_ok(s), fork(s, s2, parent, child)
    ensures past_ok(s2)
{
    let ctx = s.ctx[parent];
    let e = Event::Fork { parent, child, ctx };
    let h = s.history;
    let h2 = s2.history;
    let j = h.len() as int;
    assert(h2 == h.push(e) && h2[j] == e);
    assert forall|w: Version| #[trigger] ev_ctx(e).contains(w) implies write_before(h2, w, j) by {
        reveal(past_ok);
        assert(s.ctx[parent].contains(w));
        lemma_reaches_next(h, e, w);
    }
    lemma_past_push(s, s2, e);
    reveal(past_ok);
    assert forall|id: int, w: Version| #![trigger s2.ctx[id].contains(w)]
        s2.ctx.dom().contains(id) && s2.ctx[id].contains(w) implies write_reaches(h2, w, id) by {
        if id == child || id == parent {
            assert(ev_ctx(e).contains(w));
            assert(write_before(h2, w, j));
            assert(actor(h2[j]) == parent && h2[j]->Fork_child == child);
        } else {
            assert(s.ctx[id].contains(w));
            lemma_reaches_push(h, e, w, id);
        }
    }
}

pub proof fn lemma_step_past(c: Constants, s: State, s2: State, a: Action)
    requires shape_ok(c, s), past_ok(s), step(c, s, s2, a)
    ensures past_ok(s2)
{
    reveal(step);
    match a {
        Action::Write { client, server, key, value, gvc } =>
            lemma_past_write(c, s, s2, client, server, key, value, gvc),
        Action::Read { client, server, key, after, result } =>
            lemma_past_read(c, s, s2, client, server, key, after, result),
        Action::Fork { parent, child } => lemma_past_fork(c, s, s2, parent, child),
        Action::Start { client } => {
            reveal(past_ok);
            assert(s2.history == s.history);
            assert forall|id: int, w: Version| #![trigger s2.ctx[id].contains(w)]
                s2.ctx.dom().contains(id) && s2.ctx[id].contains(w) implies write_reaches(s2.history, w, id) by {
                assert(id != client);
                assert(s.ctx[id].contains(w));
            }
        },
        Action::Propagate { src, mid, after } => {
            reveal(past_ok);
            assert(s2.history == s.history && s2.ctx == s.ctx);
        },
        Action::Stutter => {},
    }
}

pub proof fn lemma_init_past(c: Constants, s: State)
    requires init(c, s)
    ensures past_ok(s)
{
    reveal(past_ok);
}

} // verus!

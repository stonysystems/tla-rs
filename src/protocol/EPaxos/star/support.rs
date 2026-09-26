//! Baseline quorum support for every non-no-op proposal and pending recovery.
use super::types::*;
use super::model::*;
use super::recovery::*;
use super::behavior::*;
use super::invariants::*;
use super::identities::*;
use super::progress::*;
use super::coordinator::*;
use super::validity::*;
use super::preaccept_evidence::*;
use super::knowledge::*;
use super::quorum::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn supports(s: State, node: int, id: Instance, attrs: Attributes) -> bool {
    exists |p: Packet| #[trigger] s.network.contains(p) && p.kind is PreAcceptOk
        && p.src == node && p.instance == id && p.attrs.payload == attrs.payload
        && p.attrs.deps.subset_of(attrs.deps)
}

pub open spec fn supporters(s: State, c: Constants, id: Instance, attrs: Attributes) -> Set<int> {
    members(c).filter(|node: int| supports(s, node, id, attrs))
}

pub open spec fn supported(s: State, c: Constants, id: Instance, attrs: Attributes) -> bool {
    attrs.payload is Nop || supporters(s, c, id, attrs).len() >= c.n - c.f - c.e
}

#[verifier::opaque]
pub open spec fn support_invariant(s: State, c: Constants) -> bool {
    &&& forall |node: int, id: Instance| member(c, node) && stable(#[trigger] record(s.nodes[node], id))
        ==> supported(s, c, id, record(s.nodes[node], id).attrs)
    &&& forall |node: int, id: Instance| member(c, node) && #[trigger] s.nodes[node].attempts.dom().contains(id) ==> {
        let a = s.nodes[node].attempts[id];
        (final_stage(a.stage) || a.stage is Validating || a.stage is Waiting) ==> supported(s, c, id, a.candidate)
    }
    &&& forall |p: Packet| #[trigger] s.network.contains(p) ==> {
        &&& (proposal(p) || p.kind is Waiting) ==> supported(s, c, p.instance, p.attrs)
        &&& (p.kind is RecoverOk && stable(p.snapshot)) ==> supported(s, c, p.instance, p.snapshot.attrs)
    }
}

pub proof fn lemma_support_persists(s: State, s_: State, c: Constants, id: Instance, attrs: Attributes)
    requires s.network.subset_of(s_.network), supported(s, c, id, attrs)
    ensures supported(s_, c, id, attrs)
{
    assert(supporters(s, c, id, attrs).subset_of(supporters(s_, c, id, attrs)));
    lemma_len_subset(supporters(s, c, id, attrs), supporters(s_, c, id, attrs));
}

pub proof fn lemma_initial_support(s: State, c: Constants)
    requires init(s, c)
    ensures support_invariant(s, c)
{
    reveal(support_invariant);
}

pub proof fn lemma_initial_batch_support(s: State, c: Constants, node: int,
    id: Instance, batch: Map<int, Packet>, attrs: Attributes)
    requires valid_constants(c), validity(s, c), references_known(s, c), member(c, node),
        replies(s, c, node, id, 0, Kind::PreAcceptOk, batch), majority(c, batch.dom()),
        attrs == (Attributes { payload: s.submitted[id].payload, deps: union_reply_deps(batch) })
    ensures supported(s, c, id, attrs)
{
    broadcast use group_set_lib_default;
    reveal(validity);
    reveal(references_known);
    assert forall |q: int| #[trigger] batch.dom().contains(q)
        implies supporters(s, c, id, attrs).contains(q) by {
        let p = batch[q];
        assert(s.network.contains(p));
        let sets = batch.dom().map(|node: int| batch[node].attrs.deps);
        batch.dom().lemma_map_contains(|node: int| batch[node].attrs.deps, p.attrs.deps);
        assert(sets.contains(p.attrs.deps));
        assert forall |dep: Instance| #[trigger] p.attrs.deps.contains(dep)
            implies attrs.deps.contains(dep) by {
            sets.lemma_flatten_contains(dep);
        }
        assert(p.attrs.deps.subset_of(attrs.deps));
        assert(supports(s, q, id, attrs));
    }
    assert(batch.dom().subset_of(supporters(s, c, id, attrs)));
    lemma_len_subset(batch.dom(), supporters(s, c, id, attrs));
}

pub proof fn lemma_pending_batch_support(s: State, c: Constants, node: int,
    id: Instance, b: int, batch: Map<int, Packet>, q: int)
    requires valid_constants(c), validity(s, c), references_known(s, c), preaccept_evidence(s, c),
        replies(s, c, node, id, b, Kind::RecoverOk, batch), majority(c, batch.dom()),
        pending_support(batch).len() >= batch.dom().len() - c.e, pending_support(batch).contains(q)
    ensures supported(s, c, id, batch[q].snapshot.attrs)
{
    broadcast use group_set_lib_default;
    reveal(validity);
    reveal(references_known);
    reveal(preaccept_evidence);
    let attrs = batch[q].snapshot.attrs;
    assert(s.network.contains(batch[q]));
    assert(s.submitted.dom().contains(id));
    assert(attrs == s.submitted[id]);
    assert forall |r: int| #[trigger] pending_support(batch).contains(r)
        implies supporters(s, c, id, attrs).contains(r) by {
        assert(s.network.contains(batch[r]));
        assert(batch[r].snapshot.attrs == attrs);
        assert(preaccept_recorded(s, r, id, attrs));
    }
    assert(pending_support(batch).subset_of(supporters(s, c, id, attrs)));
    lemma_len_subset(pending_support(batch), supporters(s, c, id, attrs));
}

pub proof fn lemma_step_support(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        coordinator_invariant(s, c), validity(s, c), preaccept_evidence(s, c), support_invariant(s, c), step(s, s_, c, a)
    ensures support_invariant(s_, c)
{
    broadcast use group_set_lib_default;
    lemma_step_progress(s, s_, c, a);
    reveal(step);
    reveal(validity);
    reveal(coordinator_invariant);
    reveal(support_invariant);
    assert forall |id: Instance, attrs: Attributes| #[trigger] supported(s, c, id, attrs)
        implies supported(s_, c, id, attrs) by {
        lemma_support_persists(s, s_, c, id, attrs);
    }
    match a {
        Action::FinishPreAccept { node, id, batch } => {
            let attrs = Attributes { payload: record(s.nodes[node], id).attrs.payload, deps: union_reply_deps(batch) };
            lemma_initial_batch_support(s, c, node, id, batch, attrs);
            lemma_support_persists(s, s_, c, id, attrs);
        },
        Action::FinishRecovery { node, id, ballot, batch, selected } => {
            if maximal_committed(batch).len() == 0 && maximal_accepted(batch).len() == 0
                && pending_support(batch).len() >= batch.dom().len() - c.e {
                lemma_pending_batch_support(s, c, node, id, ballot, batch, selected);
                lemma_support_persists(s, s_, c, id, batch[selected].snapshot.attrs);
            }
        },
        _ => {},
    }
}

pub proof fn lemma_behavior_support(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures support_invariant(states[i], c)
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_support(states[0], c);
    } else {
        lemma_behavior_support(states, c, i - 1);
        lemma_behavior_bounds(states, c, i - 1);
        lemma_behavior_references(states, c, i - 1);
        lemma_behavior_coordinator(states, c, i - 1);
        lemma_behavior_validity(states, c, i - 1);
        lemma_behavior_preaccept_evidence(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_support(states[i - 1], states[i], c, a);
    }
}

/// A baseline fast quorum intersects even the smaller pre-accept support
/// retained by a pending recovery.
pub proof fn lemma_fast_support_visibility(s: State, c: Constants, fast: Map<int, Packet>,
    fast_node: int, id: Instance, attrs: Attributes, other: Instance, other_attrs: Attributes)
    requires
        valid_constants(c), knowledge(s, c), id != other,
        replies(s, c, fast_node, id, 0, Kind::PreAcceptOk, fast), fast_quorum(c, fast.dom()),
        forall |q: int| #[trigger] fast.dom().contains(q) ==> fast[q].attrs == attrs,
        supported(s, c, other, other_attrs), !(other_attrs.payload is Nop),
        conflicts(c, attrs.payload, other_attrs.payload),
    ensures covers(id, attrs, other, other_attrs)
{
    broadcast use group_set_properties;
    reveal(knowledge);
    let support = supporters(s, c, other, other_attrs);
    lemma_intersection_bound(c, fast.dom(), support);
    assert(fast.dom().intersect(support).len() > 0);
    let node = fast.dom().intersect(support).choose();
    assert(supports(s, node, other, other_attrs));
    let p = choose |p: Packet| #[trigger] s.network.contains(p) && p.kind is PreAcceptOk
        && p.src == node && p.instance == other && p.attrs.payload == other_attrs.payload
        && p.attrs.deps.subset_of(other_attrs.deps);
    assert(s.network.contains(fast[node]));
    assert(covers(id, attrs, other, p.attrs));
}

} // verus!

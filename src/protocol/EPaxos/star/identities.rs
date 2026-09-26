//! Instance references must originate in a client submission. This invariant
//! is also what makes the persistent allocation counter safe across reboot.
use super::types::*;
use super::model::*;
use super::recovery::*;
use super::execution::*;
use super::behavior::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn record_known(r: Record, ids: Set<Instance>) -> bool {
    r.attrs.deps.subset_of(ids) && r.initial_deps.subset_of(ids)
}

pub open spec fn invalidations_known(invalidating: Set<Invalidation>, ids: Set<Instance>) -> bool {
    forall |i: Invalidation| #[trigger] invalidating.contains(i) ==> ids.contains(i.instance)
}

pub open spec fn node_known(n: Node, ids: Set<Instance>) -> bool {
    &&& n.log.dom().subset_of(ids)
    &&& forall |id: Instance| #[trigger] n.log.dom().contains(id) ==> record_known(n.log[id], ids)
    &&& n.attempts.dom().subset_of(ids)
    &&& forall |id: Instance| #[trigger] n.attempts.dom().contains(id) ==> {
        &&& n.attempts[id].candidate.deps.subset_of(ids)
        &&& invalidations_known(n.attempts[id].invalidating, ids)
    }
    &&& n.executed.to_set().subset_of(ids)
}

pub open spec fn packet_known(p: Packet, ids: Set<Instance>) -> bool {
    &&& ids.contains(p.instance)
    &&& p.attrs.deps.subset_of(ids)
    &&& record_known(p.snapshot, ids)
    &&& invalidations_known(p.invalidating, ids)
}

#[verifier::opaque]
pub open spec fn references_known(s: State, c: Constants) -> bool {
    &&& s.nodes.len() == c.n
    &&& forall |node: int| member(c, node) ==> node_known(#[trigger] s.nodes[node], s.submitted.dom())
    &&& forall |p: Packet| #[trigger] s.network.contains(p) ==> packet_known(p, s.submitted.dom())
}

#[verifier::opaque]
pub open spec fn allocated(s: State, c: Constants) -> bool {
    forall |id: Instance| #[trigger] s.submitted.dom().contains(id) ==> {
        member(c, id.owner) && id.slot < s.nodes[id.owner].next_slot
    }
}

pub proof fn lemma_initial_references(s: State, c: Constants)
    requires init(s, c)
    ensures references_known(s, c), allocated(s, c)
{
    reveal(references_known);
    reveal(allocated);
}

pub proof fn lemma_submission_fresh(s: State, c: Constants, node: int)
    requires references_known(s, c), allocated(s, c), member(c, node)
    ensures
        !s.submitted.dom().contains(Instance { owner: node, slot: s.nodes[node].next_slot }),
        !s.nodes[node].log.dom().contains(Instance { owner: node, slot: s.nodes[node].next_slot }),
{
    reveal(references_known);
    reveal(allocated);
}

pub proof fn lemma_batch_known(s: State, c: Constants, node: int, id: Instance,
    b: int, kind: Kind, batch: Map<int, Packet>)
    requires references_known(s, c), replies(s, c, node, id, b, kind, batch)
    ensures
        forall |q: int| #[trigger] batch.dom().contains(q) ==> packet_known(batch[q], s.submitted.dom()),
        union_reply_deps(batch).subset_of(s.submitted.dom()),
        invalidations_known(batch.dom().map(|q: int| batch[q].invalidating).flatten(), s.submitted.dom()),
{
    broadcast use group_set_lib_default;
    reveal(references_known);
    assert forall |q: int| #[trigger] batch.dom().contains(q)
        implies packet_known(batch[q], s.submitted.dom()) by {
        assert(s.network.contains(batch[q]));
    }
}

pub proof fn lemma_local_invalidations_known(c: Constants, n: Node, id: Instance,
    attrs: Attributes, ids: Set<Instance>)
    requires node_known(n, ids)
    ensures invalidations_known(invalidations(c, n, id, attrs), ids)
{
    broadcast use group_set_lib_default;
}

pub proof fn lemma_step_references(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), references_known(s, c), allocated(s, c), step(s, s_, c, a)
    ensures references_known(s_, c), allocated(s_, c)
{
    broadcast use group_set_lib_default;
    reveal(step);
    match a {
        Action::Submit { node, value } => {
            lemma_submission_fresh(s, c, node);
        },
        Action::PreAccept { packet: p } => {},
        Action::FinishPreAccept { node, id, batch } => {
            lemma_batch_known(s, c, node, id, 0, Kind::PreAcceptOk, batch);
        },
        Action::Accept { packet: p } => {},
        Action::FinishAccept { node, id, ballot, batch } => {},
        Action::Learn { packet: p } => {},
        Action::BeginRecovery { node, id, ballot } => {},
        Action::Recover { packet: p } => {},
        Action::FinishRecovery { node, id, ballot, batch, selected } => {
            lemma_batch_known(s, c, node, id, ballot, Kind::RecoverOk, batch);
            reveal(references_known);
            lemma_local_invalidations_known(c, s.nodes[node], id,
                batch[selected].snapshot.attrs, s.submitted.dom());
        },
        Action::Validate { packet: p } => {
            reveal(references_known);
            lemma_local_invalidations_known(c, s.nodes[p.dst], p.instance, p.attrs, s.submitted.dom());
        },
        Action::FinishValidation { node, id, ballot, batch } => {
            lemma_batch_known(s, c, node, id, ballot, Kind::ValidateOk, batch);
        },
        Action::ResolveWaiting { node, id, ballot, resolution } => {},
        Action::Execute { node, component } => {},
        Action::Reboot { node } => {},
        Action::Stutter => {},
    }
    reveal(references_known);
    reveal(allocated);
    assert forall |node: int| member(c, node)
        implies node_known(#[trigger] s_.nodes[node], s_.submitted.dom()) by {
        assert(node_known(s.nodes[node], s.submitted.dom()));
    }
    assert forall |p: Packet| #[trigger] s_.network.contains(p)
        implies packet_known(p, s_.submitted.dom()) by {
        if s.network.contains(p) {
            assert(packet_known(p, s.submitted.dom()));
        }
    }
    assert forall |id: Instance| #[trigger] s_.submitted.dom().contains(id) implies {
        member(c, id.owner) && id.slot < s_.nodes[id.owner].next_slot
    } by {
        if s.submitted.dom().contains(id) {
            assert(member(c, id.owner) && id.slot < s.nodes[id.owner].next_slot);
        }
    }
}

pub proof fn lemma_behavior_references(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures references_known(states[i], c), allocated(states[i], c)
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_references(states[0], c);
    } else {
        lemma_behavior_references(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_references(states[i - 1], states[i], c, a);
    }
}

} // verus!

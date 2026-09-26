//! Quorum evidence for the dependencies of each committed command.
use super::types::*;
use super::model::*;
use super::recovery::*;
use super::behavior::*;
use super::invariants::*;
use super::identities::*;
use super::progress::*;
use super::coordinator::*;
use super::validity::*;
use super::evidence::*;
use super::validation_evidence::*;
use super::recovery_certificates::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn initial_dependency_certificate(s: State, c: Constants, id: Instance,
    attrs: Attributes, batch: Map<int, Packet>) -> bool {
    &&& replies(s, c, id.owner, id, 0, Kind::PreAcceptOk, batch)
    &&& majority(c, batch.dom())
    &&& forall |q: int| #[trigger] batch.dom().contains(q) ==> {
        batch[q].attrs.payload == attrs.payload && batch[q].attrs.deps.subset_of(attrs.deps)
    }
}

pub open spec fn validated_dependency_certificate(s: State, c: Constants, id: Instance,
    attrs: Attributes, node: int, b: int, batch: Map<int, Packet>) -> bool {
    &&& attrs == s.submitted[id]
    &&& replies(s, c, node, id, b, Kind::ValidateOk, batch)
    &&& majority(c, batch.dom())
    &&& forall |q: int, i: Invalidation| batch.dom().contains(q) && batch[q].invalidating.contains(i)
        ==> compatible_commit(s, i.instance, id)
}

#[verifier::opaque]
pub open spec fn dependency_certificate(s: State, c: Constants, id: Instance, attrs: Attributes) -> bool {
    ||| attrs.payload is Nop
    ||| exists |batch: Map<int, Packet>| initial_dependency_certificate(s, c, id, attrs, batch)
    ||| exists |node: int, b: int, batch: Map<int, Packet>| validated_dependency_certificate(s, c, id, attrs, node, b, batch)
}

pub open spec fn invalidation_union(batch: Map<int, Packet>) -> Set<Invalidation> {
    batch.dom().map(|q: int| batch[q].invalidating).flatten()
}

pub proof fn lemma_invalidation_union_contains(batch: Map<int, Packet>, q: int, i: Invalidation)
    requires batch.dom().contains(q), batch[q].invalidating.contains(i)
    ensures invalidation_union(batch).contains(i)
{
    let sets = batch.dom().map(|q: int| batch[q].invalidating);
    batch.dom().lemma_map_contains(|q: int| batch[q].invalidating, batch[q].invalidating);
    assert(sets.contains(batch[q].invalidating));
    sets.lemma_flatten_contains(i);
}

#[verifier::opaque]
pub open spec fn pending_validation(s: State, c: Constants, node: int, id: Instance,
    b: int, quorum: Set<int>, invalidating: Set<Invalidation>) -> bool {
    exists |batch: Map<int, Packet>| {
        &&& #[trigger] replies(s, c, node, id, b, Kind::ValidateOk, batch)
        &&& batch.dom() == quorum
        &&& majority(c, quorum)
        &&& invalidation_union(batch) == invalidating
    }
}

#[verifier::opaque]
pub open spec fn dependency_certificates(s: State, c: Constants) -> bool {
    &&& forall |node: int, id: Instance| member(c, node) && stable(#[trigger] record(s.nodes[node], id))
        ==> dependency_certificate(s, c, id, record(s.nodes[node], id).attrs)
    &&& forall |node: int, id: Instance| member(c, node) && #[trigger] s.nodes[node].attempts.dom().contains(id) ==> {
        let a = s.nodes[node].attempts[id];
        &&& final_stage(a.stage) ==> dependency_certificate(s, c, id, a.candidate)
        &&& (a.stage is Validating || a.stage is Waiting) ==> majority(c, a.quorum)
        &&& a.stage is Waiting ==> pending_validation(s, c, node, id, a.ballot, a.quorum, a.invalidating)
    }
    &&& forall |p: Packet| #[trigger] s.network.contains(p) ==> {
        &&& proposal(p) ==> dependency_certificate(s, c, p.instance, p.attrs)
        &&& (p.kind is RecoverOk && stable(p.snapshot)) ==> dependency_certificate(s, c, p.instance, p.snapshot.attrs)
    }
}

pub proof fn lemma_initial_dependency_certificates(s: State, c: Constants)
    requires init(s, c)
    ensures dependency_certificates(s, c)
{
    reveal(dependency_certificates);
}

pub proof fn lemma_dependency_certificate_persists(s: State, s_: State, c: Constants,
    id: Instance, attrs: Attributes)
    requires s.network.subset_of(s_.network), s.submitted[id] == s_.submitted[id], dependency_certificate(s, c, id, attrs)
    ensures dependency_certificate(s_, c, id, attrs)
{
    reveal(dependency_certificate);
    if exists |batch: Map<int, Packet>| initial_dependency_certificate(s, c, id, attrs, batch) {
        let batch = choose |batch: Map<int, Packet>| initial_dependency_certificate(s, c, id, attrs, batch);
        lemma_replies_persist(s, s_, c, id.owner, id, 0, Kind::PreAcceptOk, batch);
        assert(initial_dependency_certificate(s_, c, id, attrs, batch));
    }
    if exists |node: int, b: int, batch: Map<int, Packet>| validated_dependency_certificate(s, c, id, attrs, node, b, batch) {
        let (node, b, batch) = choose |node: int, b: int, batch: Map<int, Packet>|
            validated_dependency_certificate(s, c, id, attrs, node, b, batch);
        lemma_replies_persist(s, s_, c, node, id, b, Kind::ValidateOk, batch);
        assert(validated_dependency_certificate(s_, c, id, attrs, node, b, batch));
    }
}

pub proof fn lemma_pending_validation_persists(s: State, s_: State, c: Constants,
    node: int, id: Instance, b: int, quorum: Set<int>, invalidating: Set<Invalidation>)
    requires s.network.subset_of(s_.network), pending_validation(s, c, node, id, b, quorum, invalidating)
    ensures pending_validation(s_, c, node, id, b, quorum, invalidating)
{
    reveal(pending_validation);
    let batch = choose |batch: Map<int, Packet>| {
        &&& #[trigger] replies(s, c, node, id, b, Kind::ValidateOk, batch)
        &&& batch.dom() == quorum
        &&& majority(c, quorum)
        &&& invalidation_union(batch) == invalidating
    };
    lemma_replies_persist(s, s_, c, node, id, b, Kind::ValidateOk, batch);
}

pub proof fn lemma_initial_dependency_union(s: State, c: Constants, id: Instance, batch: Map<int, Packet>)
    requires validity(s, c), replies(s, c, id.owner, id, 0, Kind::PreAcceptOk, batch), majority(c, batch.dom())
    ensures dependency_certificate(s, c, id, Attributes { payload: s.submitted[id].payload, deps: union_reply_deps(batch) })
{
    broadcast use group_set_lib_default;
    reveal(validity);
    reveal(dependency_certificate);
    let attrs = Attributes { payload: s.submitted[id].payload, deps: union_reply_deps(batch) };
    assert forall |q: int| #[trigger] batch.dom().contains(q) implies {
        batch[q].attrs.payload == attrs.payload && batch[q].attrs.deps.subset_of(attrs.deps)
    } by {
        let sets = batch.dom().map(|node: int| batch[node].attrs.deps);
        batch.dom().lemma_map_contains(|node: int| batch[node].attrs.deps, batch[q].attrs.deps);
        assert(sets.contains(batch[q].attrs.deps));
        assert forall |dep: Instance| #[trigger] batch[q].attrs.deps.contains(dep)
            implies attrs.deps.contains(dep) by { sets.lemma_flatten_contains(dep); }
    }
    assert(initial_dependency_certificate(s, c, id, attrs, batch));
}

pub proof fn lemma_validation_dependency_certificate(s: State, s_: State, c: Constants,
    node: int, id: Instance, b: int, batch: Map<int, Packet>)
    requires validity(s, c), dependency_certificates(s, c), finish_validation(s, s_, c, node, id, b, batch)
    ensures
        final_stage(s_.nodes[node].attempts[id].stage)
            ==> dependency_certificate(s_, c, id, s_.nodes[node].attempts[id].candidate),
        s_.nodes[node].attempts[id].stage is Waiting
            ==> pending_validation(s_, c, node, id, b, s_.nodes[node].attempts[id].quorum, s_.nodes[node].attempts[id].invalidating),
{
    broadcast use group_set_lib_default;
    broadcast use group_set_properties;
    reveal(validity);
    reveal(dependency_certificates);
    reveal(dependency_certificate);
    reveal(pending_validation);
    lemma_replies_persist(s, s_, c, node, id, b, Kind::ValidateOk, batch);
    if invalidation_union(batch).len() == 0 {
        assert forall |q: int, i: Invalidation| batch.dom().contains(q) && batch[q].invalidating.contains(i)
            implies compatible_commit(s_, i.instance, id) by {
            lemma_invalidation_union_contains(batch, q, i);
        }
        assert(validated_dependency_certificate(s_, c, id, s.nodes[node].attempts[id].candidate, node, b, batch));
    }
}

pub proof fn lemma_waiting_dependency_certificate(s: State, s_: State, c: Constants,
    node: int, id: Instance, b: int, resolution: Resolution)
    requires validity(s, c), evidence(s, c), dependency_certificates(s, c), resolve_waiting(s, s_, c, node, id, b, resolution)
    ensures dependency_certificate(s_, c, id, s_.nodes[node].attempts[id].candidate)
{
    broadcast use group_set_lib_default;
    reveal(validity);
    reveal(evidence);
    reveal(dependency_certificates);
    reveal(dependency_certificate);
    if resolution is Ready {
        let a = s.nodes[node].attempts[id];
        reveal(pending_validation);
        let batch = choose |batch: Map<int, Packet>| {
            &&& #[trigger] replies(s, c, node, id, b, Kind::ValidateOk, batch)
            &&& batch.dom() == a.quorum
            &&& majority(c, a.quorum)
            &&& invalidation_union(batch) == a.invalidating
        };
        assert forall |q: int, i: Invalidation| batch.dom().contains(q) && batch[q].invalidating.contains(i)
            implies compatible_commit(s_, i.instance, id) by {
            lemma_invalidation_union_contains(batch, q, i);
            assert(a.invalidating.contains(i));
            a.invalidating.lemma_map_contains(|entry: Invalidation| entry.instance, i.instance);
            assert(a.invalidating.map(|entry: Invalidation| entry.instance).contains(i.instance));
            let r = record(s.nodes[node], i.instance);
            assert(r.phase is Committed);
            assert(r.attrs.payload is Nop || r.attrs.deps.contains(id));
            assert(record_evidence(s, i.instance, r));
            let p = choose |p: Packet| #[trigger] s.network.contains(p)
                && p.instance == i.instance && p.ballot == r.accepted_ballot && p.attrs == r.attrs
                && if r.phase is Committed { p.kind is Commit } else { p.kind is Accept };
            assert(s_.network.contains(p));
            assert(p.kind is Commit);
            assert(p.attrs.payload is Nop || p.attrs.deps.contains(id));
        }
        lemma_replies_persist(s, s_, c, node, id, b, Kind::ValidateOk, batch);
        assert(validated_dependency_certificate(s_, c, id, a.candidate, node, b, batch));
    }
}

pub proof fn lemma_step_dependency_certificates(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        coordinator_invariant(s, c), validity(s, c), evidence(s, c), dependency_certificates(s, c), step(s, s_, c, a)
    ensures dependency_certificates(s_, c)
{
    broadcast use group_set_lib_default;
    lemma_step_progress(s, s_, c, a);
    reveal(step);
    reveal(references_known);
    reveal(validity);
    reveal(coordinator_invariant);
    reveal(dependency_certificates);
    assert forall |id: Instance, attrs: Attributes| s.submitted.dom().contains(id)
        && #[trigger] dependency_certificate(s, c, id, attrs)
        implies dependency_certificate(s_, c, id, attrs) by {
        lemma_dependency_certificate_persists(s, s_, c, id, attrs);
    }
    assert forall |node: int, id: Instance| member(c, node) && #[trigger] s.nodes[node].attempts.dom().contains(id)
        && s.nodes[node].attempts[id].stage is Waiting implies {
            let a = s.nodes[node].attempts[id];
            pending_validation(s_, c, node, id, a.ballot, a.quorum, a.invalidating)
        } by {
        let a = s.nodes[node].attempts[id];
        lemma_pending_validation_persists(s, s_, c, node, id, a.ballot, a.quorum, a.invalidating);
    }
    match a {
        Action::FinishPreAccept { node, id, batch } => {
            let attrs = Attributes { payload: record(s.nodes[node], id).attrs.payload, deps: union_reply_deps(batch) };
            lemma_initial_dependency_union(s, c, id, batch);
            lemma_dependency_certificate_persists(s, s_, c, id, attrs);
        },
        Action::FinishValidation { node, id, ballot, batch } => lemma_validation_dependency_certificate(s, s_, c, node, id, ballot, batch),
        Action::ResolveWaiting { node, id, ballot, resolution } => lemma_waiting_dependency_certificate(s, s_, c, node, id, ballot, resolution),
        _ => {},
    }
    // Nop is the only new candidate without a dependency certificate.
    assert forall |id: Instance| dependency_certificate(s_, c, id, nop_attrs()) by { reveal(dependency_certificate); }
}

pub proof fn lemma_behavior_dependency_certificates(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures dependency_certificates(states[i], c)
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_dependency_certificates(states[0], c);
    } else {
        lemma_behavior_dependency_certificates(states, c, i - 1);
        lemma_behavior_bounds(states, c, i - 1);
        lemma_behavior_references(states, c, i - 1);
        lemma_behavior_coordinator(states, c, i - 1);
        lemma_behavior_validity(states, c, i - 1);
        lemma_behavior_evidence(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_dependency_certificates(states[i - 1], states[i], c, a);
    }
}

} // verus!

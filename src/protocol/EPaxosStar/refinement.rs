/// Refinement of EPaxos* to an abstract write-once commit map.
///
/// # Why not Raft's shape
///
/// `Raft/refinement_proof/state_machine.rs` abstracts to `Seq<int>` — a totally
/// ordered committed log extended append-only. **EPaxos\* has no total order at
/// commit time**: it commits `(cmd, dep)` per instance and the order is a
/// property of the dependency graph, recovered later by an execution layer that
/// neither the reference nor this port models. So the abstract machine here is
/// a map that is written at most once per instance:
///
/// ```text
/// AbstractState { committed: Map<LInstanceId, LCommitRecord> }
/// Next == stutter | write one instance not already written
/// ```
///
/// `Agreement` falls out of that directly — write-once means two commits of the
/// same instance cannot disagree. **`Visibility` does not**, and that is the
/// design fork `TODO.md` 57.2.b names: it relates *two* committed entries, so
/// no single-write abstract step can express it. It stays a distributed-level
/// invariant that refinement must show is preserved, and per the Phase 57
/// acceptance criteria the two are separable results that must be reported
/// separately.
///
/// # `Nop` makes the map non-injective
///
/// Several distinct distributed histories refine to the same abstract write:
/// every recovery path that gives up commits `Nop` with empty dependencies.
/// That is fine for safety, but it means the refinement map has no inverse, so
/// any argument reaching for a unique pre-image is wrong. Predicted in 57.5.3
/// before it could be discovered the hard way.
use crate::protocol::EPaxosStar::distributed_system::*;
use crate::protocol::EPaxosStar::epaxos_star::*;
use crate::protocol::EPaxosStar::types::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

/// What an instance was committed with.
pub struct LCommitRecord {
    pub cmd: LCmd,
    pub dep: Set<LInstanceId>,
}

/// The abstract state: which instances are decided, and with what.
pub struct EPaxosStarSystemState {
    pub committed: Map<LInstanceId, LCommitRecord>,
}

pub open spec fn SystemInit(rs: EPaxosStarSystemState) -> bool {
    rs.committed =~= Map::<LInstanceId, LCommitRecord>::empty()
}

/// One instance becomes decided. Entries already present never change — that
/// is the whole safety content of the abstract machine.
pub open spec fn SystemNextWrite(
    rs: EPaxosStarSystemState,
    rs_: EPaxosStarSystemState,
) -> bool {
    exists|id: LInstanceId|
        {
            &&& !rs.committed.dom().contains(id)
            &&& #[trigger] rs_.committed.dom().contains(id)
            &&& rs_.committed =~= rs.committed.insert(id, rs_.committed[id])
        }
}

pub open spec fn SystemNext(
    rs: EPaxosStarSystemState,
    rs_: EPaxosStarSystemState,
) -> bool {
    ||| rs_ == rs
    ||| SystemNextWrite(rs, rs_)
}

// =========================================================================
// The refinement map
// =========================================================================

/// Every instance any replica has a record for, up to replica `k`.
///
/// Built by recursion rather than a set comprehension because `Map::new` needs
/// a domain that is already finite, and a union over the replica sequence is
/// finite by construction while `{id : exists i. ...}` is not.
pub open spec fn KnownIdsUpTo(ds: EPaxosStarDistributedState, k: int) -> Set<LInstanceId>
    decreases k,
{
    if k <= 0 {
        Set::<LInstanceId>::empty()
    } else {
        KnownIdsUpTo(ds, k - 1).union(ds.replica_states[k - 1].instances.dom())
    }
}

pub open spec fn AllKnownIds(ds: EPaxosStarDistributedState) -> Set<LInstanceId> {
    KnownIdsUpTo(ds, ds.num_replicas)
}

pub open spec fn CommittedSomewhere(ds: EPaxosStarDistributedState, id: LInstanceId) -> bool {
    exists|i: int|
        0 <= i < ds.num_replicas && (#[trigger] InstAt(ds.replica_states[i], id)).phase
            is Committed
}

/// The committing replica's view. Well-defined **only under `Agreement`** —
/// without it, different replicas could offer different records and this
/// `choose` would pick arbitrarily. That is not circular: the refinement
/// theorem carries `Agreement` as a hypothesis, exactly as Raft's carries
/// `RaftSafetyInvariant`.
pub open spec fn CommittedView(
    ds: EPaxosStarDistributedState,
    id: LInstanceId,
) -> LCommitRecord {
    let i = choose|i: int|
        0 <= i < ds.num_replicas && (#[trigger] InstAt(ds.replica_states[i], id)).phase
            is Committed;
    LCommitRecord {
        cmd: InstAt(ds.replica_states[i], id).cmd,
        dep: InstAt(ds.replica_states[i], id).dep,
    }
}

pub open spec fn CommittedIds(ds: EPaxosStarDistributedState) -> Set<LInstanceId> {
    AllKnownIds(ds).filter(|id: LInstanceId| CommittedSomewhere(ds, id))
}

pub open spec fn AbstractifyEPaxosStar(
    ds: EPaxosStarDistributedState,
) -> EPaxosStarSystemState {
    EPaxosStarSystemState {
        committed: Map::new(CommittedIds(ds), |id: LInstanceId| CommittedView(ds, id)),
    }
}

pub open spec fn SystemRefinement(
    ds: EPaxosStarDistributedState,
    rs: EPaxosStarSystemState,
) -> bool {
    rs == AbstractifyEPaxosStar(ds)
}

pub open spec fn SystemBehaviorRefinementCorrect(
    b: EPaxosStarBehavior,
    h: Seq<EPaxosStarSystemState>,
) -> bool {
    &&& h.len() == b.len()
    &&& h.len() > 0
    &&& SystemInit(h[0])
    &&& forall|i: int| 0 <= i < b.len() ==> SystemRefinement(#[trigger] b[i], h[i])
    &&& forall|i: int| 0 <= i < h.len() - 1 ==> SystemNext(#[trigger] h[i], h[i + 1])
}

// =========================================================================
// What is proved so far
// =========================================================================

/// At initialisation no replica holds any instance, so nothing is committed.
///
/// This is the one part of the refinement that needs no invariant, and it is
/// proved rather than assumed.
pub proof fn lemma_init_abstracts_to_empty(ds: EPaxosStarDistributedState)
    requires
        EPaxosStarDistributedInit(ds),
    ensures
        SystemInit(AbstractifyEPaxosStar(ds)),
{
    lemma_known_ids_empty_at_init(ds, ds.num_replicas);
    assert(CommittedIds(ds) =~= Set::<LInstanceId>::empty());
    assert(AbstractifyEPaxosStar(ds).committed
        =~= Map::<LInstanceId, LCommitRecord>::empty());
}

proof fn lemma_known_ids_empty_at_init(ds: EPaxosStarDistributedState, k: int)
    requires
        EPaxosStarDistributedInit(ds),
        0 <= k <= ds.num_replicas,
    ensures
        KnownIdsUpTo(ds, k) =~= Set::<LInstanceId>::empty(),
    decreases k,
{
    if k > 0 {
        lemma_known_ids_empty_at_init(ds, k - 1);
        assert(LInit(ds.replica_states[k - 1], ds.replica_constants[k - 1]));
    }
}

} // verus!

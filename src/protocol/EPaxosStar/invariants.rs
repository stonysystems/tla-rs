/// EPaxos* safety properties, **stated only**.
///
/// These are the reference's own invariants (`.tla:554-592`), which its `.cfg`
/// checks with TLC in bounded configurations. Nothing here is proved: proof is
/// `TODO.md` Phase 57, and per that plan `Agreement` and `Visibility` are
/// separable results that should not be treated as one milestone.
///
/// Stating them now rather than with the proof is deliberate — it is what makes
/// the spec answerable to something, and both of them turned out to constrain
/// the spec's shape (see `Visibility`'s note below).
use crate::protocol::EPaxosStar::distributed_system::*;
use crate::protocol::EPaxosStar::epaxos_star::*;
use crate::protocol::EPaxosStar::types::*;
use vstd::prelude::*;

verus! {

/// An identifier inside the model's bounds: owned by a real replica, numbered
/// within `max_num`.
pub open spec fn ValidId(c: LConstants, id: LInstanceId) -> bool {
    &&& c.procs.contains(id.owner)
    &&& 1 <= id.num <= c.max_num
}

/// `TypeInv` (`.tla:573-592`), less the conjuncts our types make unstatable.
///
/// The reference spends most of that operator establishing that `phase` is one
/// of four values, `cmd` is a payload or `Nop` or `Bottom`, and message types
/// are among eleven — all of which are enum membership here and hold by
/// construction. What is left is the part that is genuinely an invariant:
/// ballots stay non-negative, dependency sets stay inside the identifier space,
/// the recovery counter stays inside its model bound, and the recovery
/// scratch variables stay inside the replica set.
pub open spec fn TypeInv(ds: EPaxosStarDistributedState) -> bool {
    &&& TypeInvScalars(ds)
    &&& TypeInvDeps(ds)
}

/// The per-instance scalar bounds.
pub open spec fn TypeInvScalars(ds: EPaxosStarDistributedState) -> bool {
    forall|i: int, id: LInstanceId|
        0 <= i < ds.num_replicas ==> {
            let c = ds.replica_constants[i];
            let inst = #[trigger] InstAt(ds.replica_states[i], id);
            &&& inst.bal >= 0
            &&& inst.abal >= 0
            &&& 0 <= inst.recovered <= c.max_recovery_attempts
            &&& inst.qvar.subset_of(c.procs)
            &&& 0 <= inst.cardinality_rmax <= N(c)
        }
}

/// Dependency sets stay inside the identifier space.
///
/// Written as membership rather than `subset_of` a constructed set: this
/// Verus's `Set::new` returns `Option` for predicate-defined sets and
/// `new_assuming_finite` is deprecated for assuming what it should establish,
/// so `{j : ValidId(c, j)}` is not a set one should build just to test against.
/// Same reasoning as `ConflictingIds` filtering a domain in `types.rs`.
pub open spec fn TypeInvDeps(ds: EPaxosStarDistributedState) -> bool {
    forall|i: int, id: LInstanceId, j: LInstanceId|
        #![trigger InstAt(ds.replica_states[i], id).dep.contains(j)]
        #![trigger InstAt(ds.replica_states[i], id).init_dep.contains(j)]
        0 <= i < ds.num_replicas ==> {
            &&& (InstAt(ds.replica_states[i], id).dep.contains(j) ==> ValidId(
                ds.replica_constants[i],
                j,
            ))
            &&& (InstAt(ds.replica_states[i], id).init_dep.contains(j) ==> ValidId(
                ds.replica_constants[i],
                j,
            ))
        }
}

/// **`Agreement`** (`.tla:554-560`) — if an instance is committed at two
/// replicas, they committed the same payload with the same dependencies.
///
/// The analogue of Raft's `StateMachineSafety`, and the property the whole
/// two-ballot fix exists to preserve: recovery at a higher ballot must not be
/// able to decide differently from a commit that already happened.
pub open spec fn Agreement(ds: EPaxosStarDistributedState) -> bool {
    forall|id: LInstanceId, i: int, j: int|
        0 <= i < ds.num_replicas && 0 <= j < ds.num_replicas && {
            &&& (#[trigger] InstAt(ds.replica_states[i], id)).phase is Committed
            &&& (#[trigger] InstAt(ds.replica_states[j], id)).phase is Committed
        } ==> {
            &&& InstAt(ds.replica_states[i], id).cmd == InstAt(ds.replica_states[j], id).cmd
            &&& InstAt(ds.replica_states[i], id).dep =~= InstAt(ds.replica_states[j], id).dep
        }
}

/// **`Visibility`** (`.tla:562-571`) — two committed, conflicting, non-`Nop`
/// commands are ordered: at least one lists the other among its dependencies.
///
/// **No Raft counterpart.** Raft's safety is about one totally ordered log;
/// this is about a dependency graph having enough edges that every conflicting
/// pair is comparable, and it is what makes leaderless execution possible at
/// all. It is also the property the whole validation sub-protocol
/// (`ComputeI` / `LValidate*` / `LPostWaiting*`) exists to maintain — nothing
/// in the commit path establishes it on its own.
///
/// Stating it early paid: it is why `ComputeI` had to be written against
/// `init_cmd`/`init_dep` for non-committed instances and `cmd`/`dep` for
/// committed ones. A version that read only the current fields would have been
/// simpler and would not have preserved this.
pub open spec fn Visibility(ds: EPaxosStarDistributedState) -> bool {
    forall|id: LInstanceId, id2: LInstanceId, i: int, j: int|
        0 <= i < ds.num_replicas && 0 <= j < ds.num_replicas && id != id2 && {
            let a = #[trigger] InstAt(ds.replica_states[i], id);
            let b = #[trigger] InstAt(ds.replica_states[j], id2);
            &&& a.phase is Committed
            &&& b.phase is Committed
            &&& !(a.cmd is Nop)
            &&& !(b.cmd is Nop)
            &&& Conflicts(ds.replica_constants[i], a.cmd, b.cmd)
        } ==> {
            ||| InstAt(ds.replica_states[j], id2).dep.contains(id)
            ||| InstAt(ds.replica_states[i], id).dep.contains(id2)
        }
}

/// The conjunction Phase 57 will have to prove inductive.
///
/// Deliberately **not** a long list. Raft's `RaftSafetyInvariant` has 38
/// conjuncts, but every one of them was added because a proof needed it; adding
/// them here before the proof exists would be guessing. `TODO.md` 57.3 has the
/// predicted inventory, and it is predicted, not asserted.
pub open spec fn EPaxosStarSafety(ds: EPaxosStarDistributedState) -> bool {
    &&& WellFormedDistributed(ds)
    &&& TypeInv(ds)
    &&& Agreement(ds)
    &&& Visibility(ds)
}

} // verus!

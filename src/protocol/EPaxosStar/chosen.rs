/// The Paxos core of EPaxos*: what it means for a value to be **chosen**, and
/// the reduction of `Agreement` to two obligations about chosen-ness.
///
/// `TODO.md` Phase 57 splits the proof into two separable results, and this
/// file is the spine of the first one (**A: `Agreement`**). `Visibility` — the
/// second — does not go through here at all.
///
/// # Two decisions that shape everything downstream
///
/// **1. Chosen-ness is stated over the network, not over replica state.** A
/// replica's `(cmd, dep)` is overwritten by any accept at a higher ballot, so a
/// current-state predicate would not be stable and could not carry an
/// induction. `distributed_system.rs` makes the network monotone on purpose;
/// packets, once sent, stay. This is the standard Paxos-proof move and it is
/// available here only because of that modelling choice.
///
/// **2. EPaxos\* has TWO forms of chosen, and that is not incidental.**
///
/// - **Slow**: a quorum (`>= N-F`) answered `AcceptOK` for `(id, b)`, and the
///   `Accept` at that ballot carried `(c, D)`. Classic Paxos.
/// - **Fast**: at ballot 0 a *fast* quorum (`>= N-E`) reported dependencies
///   equal to what the coordinator proposed. **No `Accept` is ever sent on this
///   path** — `LCommitFast` goes straight from `PreAccepted` to `Committed` —
///   so a definition written only in terms of `Accept` would be silently false
///   for every fast-path commit.
///
/// The two thresholds are why the reference's `ASSUME` has two terms:
/// `N >= Max(2E + F - 1, 2F + 1)`. The `2F+1` term is what makes two slow
/// quorums intersect; the `2E+F-1` term is what makes a fast decision
/// recoverable. A proof that only ever uses the first has not engaged with the
/// fast path.
use crate::protocol::EPaxosStar::distributed_system::*;
use crate::protocol::EPaxosStar::epaxos_star::*;
use crate::protocol::EPaxosStar::invariants::*;
use crate::protocol::EPaxosStar::types::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

/// The replica identifiers, as a finite set. `WellFormedDistributed` pins every
/// replica's `procs` to exactly this.
pub open spec fn ProcIds(ds: EPaxosStarDistributedState) -> Set<int> {
    Set::<int>::range(0, ds.num_replicas)
}

pub open spec fn IsQuorumN(ds: EPaxosStarDistributedState, s: Set<int>) -> bool {
    s.len() + ds.replica_constants[0].f >= ds.num_replicas
}

pub open spec fn IsFastQuorumN(ds: EPaxosStarDistributedState, s: Set<int>) -> bool {
    s.len() + ds.replica_constants[0].e >= ds.num_replicas
}

// =========================================================================
// What the network says
// =========================================================================

/// Somebody proposed `(c, d)` for `id` — the coordinator's `PreAccept`.
pub open spec fn PreAcceptSent(
    ds: EPaxosStarDistributedState,
    id: LInstanceId,
    c: LCmd,
    d: Set<LInstanceId>,
) -> bool {
    exists|pkt: LPacket|
        (#[trigger] ds.network.contains(pkt)) && pkt.msg == LEPaxosStarMessage::PreAccept {
            id,
            c,
            d,
        }
}

/// `p` reported dependency set `d` for `id`.
pub open spec fn PreAcceptOKFrom(
    ds: EPaxosStarDistributedState,
    id: LInstanceId,
    d: Set<LInstanceId>,
    p: int,
) -> bool {
    exists|pkt: LPacket|
        (#[trigger] ds.network.contains(pkt)) && pkt.src == p && pkt.msg
            == LEPaxosStarMessage::PreAcceptOK { id, dq: d }
}

/// Somebody drove an `Accept` for `(id, b)` carrying `(c, d)`.
pub open spec fn AcceptSent(
    ds: EPaxosStarDistributedState,
    id: LInstanceId,
    b: int,
    c: LCmd,
    d: Set<LInstanceId>,
) -> bool {
    exists|pkt: LPacket|
        (#[trigger] ds.network.contains(pkt)) && pkt.msg == LEPaxosStarMessage::Accept {
            id,
            b,
            c,
            d,
        }
}

/// `p` answered `AcceptOK` for `(id, b)`.
///
/// Note the reference's `AcceptOK` carries **no payload** (`.tla:73-74`) — only
/// the instance and the ballot. The value at that ballot has to be recovered
/// from the `Accept` that caused it, which is why `SlowChosen` names both.
pub open spec fn AcceptOKFrom(
    ds: EPaxosStarDistributedState,
    id: LInstanceId,
    b: int,
    p: int,
) -> bool {
    exists|pkt: LPacket|
        (#[trigger] ds.network.contains(pkt)) && pkt.src == p && pkt.msg
            == LEPaxosStarMessage::AcceptOK { id, b }
}

/// Built by filtering a finite universe, as everywhere else in this tree —
/// `Set::new` returns `Option` here and `new_assuming_finite` is deprecated.
pub open spec fn AcceptOKSenders(
    ds: EPaxosStarDistributedState,
    id: LInstanceId,
    b: int,
) -> Set<int> {
    ProcIds(ds).filter(|p: int| AcceptOKFrom(ds, id, b, p))
}

pub open spec fn PreAcceptOKSendersMatching(
    ds: EPaxosStarDistributedState,
    id: LInstanceId,
    d: Set<LInstanceId>,
) -> Set<int> {
    ProcIds(ds).filter(|p: int| PreAcceptOKFrom(ds, id, d, p))
}

// =========================================================================
// Chosen
// =========================================================================

/// Classic Paxos chosen-ness: a quorum accepted at `b`, and the `Accept` at
/// `b` carried `(c, d)`.
pub open spec fn SlowChosen(
    ds: EPaxosStarDistributedState,
    id: LInstanceId,
    b: int,
    c: LCmd,
    d: Set<LInstanceId>,
) -> bool {
    &&& AcceptSent(ds, id, b, c, d)
    &&& IsQuorumN(ds, AcceptOKSenders(ds, id, b))
}

/// Fast-path chosen-ness, at ballot 0 only: the coordinator proposed `(c, d)`
/// and a **fast** quorum reported dependencies equal to `d`.
///
/// This is what `LCommitFast` fires on, and no `Accept` is involved.
pub open spec fn FastChosen(
    ds: EPaxosStarDistributedState,
    id: LInstanceId,
    c: LCmd,
    d: Set<LInstanceId>,
) -> bool {
    &&& PreAcceptSent(ds, id, c, d)
    &&& IsFastQuorumN(ds, PreAcceptOKSendersMatching(ds, id, d))
}

/// **`ChosenAtBallot`** — the load-bearing definition of Phase 57's A line.
pub open spec fn ChosenAtBallot(
    ds: EPaxosStarDistributedState,
    id: LInstanceId,
    b: int,
    c: LCmd,
    d: Set<LInstanceId>,
) -> bool {
    ||| SlowChosen(ds, id, b, c, d)
    ||| (b == 0 && FastChosen(ds, id, c, d))
}

// =========================================================================
// The two obligations Agreement reduces to
// =========================================================================

/// **Obligation 1 — the hard one.** All chosen values for an instance agree,
/// whatever ballots and whichever of the two paths they were chosen on.
///
/// Stated as a single "any two chosen values agree" rather than Paxos's usual
/// "chosen at `b` implies every accept at `b' > b` matches", because here the
/// two forms of chosen-ness are not ordered by ballot: a fast decision at
/// ballot 0 and a slow decision at some `b > 0` have to be compared directly,
/// and that comparison is precisely what the validation sub-protocol
/// (`ComputeI` / `LValidate*` / `LPostWaiting*`) exists to make safe.
///
/// This subsumes same-ballot uniqueness, so no separate `AcceptUnique` is
/// needed as a hypothesis — though one will very likely be needed as a *step*
/// in proving it.
pub open spec fn ChosenStable(ds: EPaxosStarDistributedState) -> bool {
    forall|
        id: LInstanceId,
        b1: int,
        c1: LCmd,
        d1: Set<LInstanceId>,
        b2: int,
        c2: LCmd,
        d2: Set<LInstanceId>,
    |
        #[trigger] ChosenAtBallot(ds, id, b1, c1, d1) && #[trigger] ChosenAtBallot(
            ds,
            id,
            b2,
            c2,
            d2,
        ) ==> c1 == c2 && d1 =~= d2
}

/// **Obligation 2.** A replica only reaches `Committed` on a value that was
/// chosen.
///
/// Every commit site must justify this: `LCommitFast` via `FastChosen`,
/// `LCommitSlow` via `SlowChosen`, and the three adopting sites
/// (`LHandleCommit`, `LRecoverCommitted`, `LPostWaitingOnRecoverOK`) by
/// inheriting it from whoever they copied.
pub open spec fn CommittedImpliesChosen(ds: EPaxosStarDistributedState) -> bool {
    forall|i: int, id: LInstanceId|
        0 <= i < ds.num_replicas && (#[trigger] InstAt(ds.replica_states[i], id)).phase
            is Committed ==> exists|b: int|
            ChosenAtBallot(
                ds,
                id,
                b,
                InstAt(ds.replica_states[i], id).cmd,
                InstAt(ds.replica_states[i], id).dep,
            )
}

// =========================================================================
// The reduction, proved
// =========================================================================

/// **`Agreement` follows from the two obligations above.**
///
/// This is the whole point of the decomposition: it turns "prove `Agreement`
/// inductive over 25 actions" into "prove `ChosenStable` and
/// `CommittedImpliesChosen`", and it says exactly what is left. The argument
/// itself is three lines — two replicas committed, each on something chosen,
/// and chosen values agree — but having it discharged means the remaining work
/// is precisely the two named obligations and nothing else.
pub proof fn lemma_agreement_from_chosen(ds: EPaxosStarDistributedState)
    requires
        ChosenStable(ds),
        CommittedImpliesChosen(ds),
    ensures
        Agreement(ds),
{
    assert forall|id: LInstanceId, i: int, j: int|
        0 <= i < ds.num_replicas && 0 <= j < ds.num_replicas && (#[trigger] InstAt(
            ds.replica_states[i],
            id,
        )).phase is Committed && (#[trigger] InstAt(ds.replica_states[j], id)).phase
            is Committed implies InstAt(ds.replica_states[i], id).cmd == InstAt(
        ds.replica_states[j],
        id,
    ).cmd && InstAt(ds.replica_states[i], id).dep =~= InstAt(ds.replica_states[j], id).dep by {
        let a = InstAt(ds.replica_states[i], id);
        let b = InstAt(ds.replica_states[j], id);
        let ba = choose|x: int| ChosenAtBallot(ds, id, x, a.cmd, a.dep);
        let bb = choose|x: int| ChosenAtBallot(ds, id, x, b.cmd, b.dep);
        assert(ChosenAtBallot(ds, id, ba, a.cmd, a.dep));
        assert(ChosenAtBallot(ds, id, bb, b.cmd, b.dep));
    }
}

// =========================================================================
// Chosen-ness is monotone
// =========================================================================

/// **Once chosen, always chosen.**
///
/// Every clause of `ChosenAtBallot` is a *positive* statement about the network
/// — an existential over packets, or a cardinality of a set of senders derived
/// from packets — and `distributed_system.rs` makes the network grow-only. So
/// chosen-ness cannot be lost.
///
/// This is worth more than it looks. It means the inductive obligation for
/// `ChosenStable` is one-sided: a step can only break it by making something
/// **newly** chosen that disagrees with what was already chosen. There is no
/// need to reason about a previously chosen value ceasing to be chosen, which
/// is exactly the case that makes current-state formulations of Paxos
/// invariants painful.
pub proof fn lemma_chosen_monotone(
    ds: EPaxosStarDistributedState,
    ds_: EPaxosStarDistributedState,
    id: LInstanceId,
    b: int,
    c: LCmd,
    d: Set<LInstanceId>,
)
    requires
        ds.network.subset_of(ds_.network),
        ds_.num_replicas == ds.num_replicas,
        ds_.replica_constants == ds.replica_constants,
        ChosenAtBallot(ds, id, b, c, d),
    ensures
        ChosenAtBallot(ds_, id, b, c, d),
{
    if SlowChosen(ds, id, b, c, d) {
        let w = choose|pkt: LPacket|
            (#[trigger] ds.network.contains(pkt)) && pkt.msg == LEPaxosStarMessage::Accept {
                id,
                b,
                c,
                d,
            };
        assert(ds_.network.contains(w));
        assert(AcceptSent(ds_, id, b, c, d));
        lemma_acceptok_senders_grow(ds, ds_, id, b);
        vstd::set_lib::lemma_len_subset(
            AcceptOKSenders(ds, id, b),
            AcceptOKSenders(ds_, id, b),
        );
        assert(SlowChosen(ds_, id, b, c, d));
    } else {
        let w = choose|pkt: LPacket|
            (#[trigger] ds.network.contains(pkt)) && pkt.msg == LEPaxosStarMessage::PreAccept {
                id,
                c,
                d,
            };
        assert(ds_.network.contains(w));
        assert(PreAcceptSent(ds_, id, c, d));
        lemma_preacceptok_senders_grow(ds, ds_, id, d);
        vstd::set_lib::lemma_len_subset(
            PreAcceptOKSendersMatching(ds, id, d),
            PreAcceptOKSendersMatching(ds_, id, d),
        );
        assert(FastChosen(ds_, id, c, d));
    }
}

/// A grow-only network can only add responders.
proof fn lemma_acceptok_senders_grow(
    ds: EPaxosStarDistributedState,
    ds_: EPaxosStarDistributedState,
    id: LInstanceId,
    b: int,
)
    requires
        ds.network.subset_of(ds_.network),
        ds_.num_replicas == ds.num_replicas,
    ensures
        AcceptOKSenders(ds, id, b).subset_of(AcceptOKSenders(ds_, id, b)),
{
    assert forall|p: int| AcceptOKSenders(ds, id, b).contains(p) implies AcceptOKSenders(
        ds_,
        id,
        b,
    ).contains(p) by {
        let w = choose|pkt: LPacket|
            (#[trigger] ds.network.contains(pkt)) && pkt.src == p && pkt.msg
                == LEPaxosStarMessage::AcceptOK { id, b };
        assert(ds_.network.contains(w));
    }
}

proof fn lemma_preacceptok_senders_grow(
    ds: EPaxosStarDistributedState,
    ds_: EPaxosStarDistributedState,
    id: LInstanceId,
    d: Set<LInstanceId>,
)
    requires
        ds.network.subset_of(ds_.network),
        ds_.num_replicas == ds.num_replicas,
    ensures
        PreAcceptOKSendersMatching(ds, id, d).subset_of(
            PreAcceptOKSendersMatching(ds_, id, d),
        ),
{
    assert forall|p: int| PreAcceptOKSendersMatching(ds, id, d).contains(p)
        implies PreAcceptOKSendersMatching(ds_, id, d).contains(p) by {
        let w = choose|pkt: LPacket|
            (#[trigger] ds.network.contains(pkt)) && pkt.src == p && pkt.msg
                == LEPaxosStarMessage::PreAcceptOK { id, dq: d };
        assert(ds_.network.contains(w));
    }
}

/// A step never shrinks the network — read straight off `ReplicaStepWithNetwork`,
/// where `ds_.network == ds.network \cup sent`.
pub proof fn lemma_step_grows_network(
    ds: EPaxosStarDistributedState,
    ds_: EPaxosStarDistributedState,
)
    requires
        EPaxosStarDistributedNext(ds, ds_),
    ensures
        ds.network.subset_of(ds_.network),
        ds_.num_replicas == ds.num_replicas,
        ds_.replica_constants == ds.replica_constants,
{
    let i = choose|i: int| ReplicaStepWithNetwork(ds, ds_, i);
    assert(ReplicaStepWithNetwork(ds, ds_, i));
}

/// The step-level form the induction actually uses: **the set of chosen values
/// only grows**.
pub proof fn lemma_chosen_grows_over_step(
    ds: EPaxosStarDistributedState,
    ds_: EPaxosStarDistributedState,
)
    requires
        EPaxosStarDistributedNext(ds, ds_),
    ensures
        forall|id: LInstanceId, b: int, c: LCmd, d: Set<LInstanceId>|
            #[trigger] ChosenAtBallot(ds, id, b, c, d) ==> ChosenAtBallot(ds_, id, b, c, d),
{
    lemma_step_grows_network(ds, ds_);
    assert forall|id: LInstanceId, b: int, c: LCmd, d: Set<LInstanceId>|
        #[trigger] ChosenAtBallot(ds, id, b, c, d) implies ChosenAtBallot(ds_, id, b, c, d) by {
        lemma_chosen_monotone(ds, ds_, id, b, c, d);
    }
}

// =========================================================================
// The Init side of the A line
// =========================================================================

/// Nothing is chosen before anything is sent.
///
/// `EPaxosStarDistributedInit` empties the network, and both forms of
/// chosen-ness require a packet to exist — `SlowChosen` an `Accept`,
/// `FastChosen` a `PreAccept`.
pub proof fn lemma_nothing_chosen_at_init(ds: EPaxosStarDistributedState)
    requires
        EPaxosStarDistributedInit(ds),
    ensures
        forall|id: LInstanceId, b: int, c: LCmd, d: Set<LInstanceId>|
            !(#[trigger] ChosenAtBallot(ds, id, b, c, d)),
{
    assert forall|id: LInstanceId, b: int, c: LCmd, d: Set<LInstanceId>| !(
    #[trigger] ChosenAtBallot(ds, id, b, c, d)) by {
        assert(ds.network =~= Set::<LPacket>::empty());
        if AcceptSent(ds, id, b, c, d) {
            let w = choose|pkt: LPacket|
                (#[trigger] ds.network.contains(pkt)) && pkt.msg
                    == LEPaxosStarMessage::Accept { id, b, c, d };
            assert(ds.network.contains(w));
            assert(false);
        }
        if PreAcceptSent(ds, id, c, d) {
            let w = choose|pkt: LPacket|
                (#[trigger] ds.network.contains(pkt)) && pkt.msg
                    == LEPaxosStarMessage::PreAccept { id, c, d };
            assert(ds.network.contains(w));
            assert(false);
        }
    }
}

pub proof fn lemma_chosen_stable_at_init(ds: EPaxosStarDistributedState)
    requires
        EPaxosStarDistributedInit(ds),
    ensures
        ChosenStable(ds),
        CommittedImpliesChosen(ds),
{
    lemma_nothing_chosen_at_init(ds);
    assert forall|i: int, id: LInstanceId|
        0 <= i < ds.num_replicas implies !((#[trigger] InstAt(ds.replica_states[i], id)).phase
        is Committed) by {
        assert(LInit(ds.replica_states[i], ds.replica_constants[i]));
        assert(!ds.replica_states[i].instances.dom().contains(id));
    }
}

} // verus!

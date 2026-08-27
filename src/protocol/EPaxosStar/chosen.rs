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

// =========================================================================
// 57.4.a.3 — supporting network invariants
// =========================================================================

/// Every broadcast actually puts a packet on the network.
///
/// `Broadcast` addresses `procs \ {my_id}`, which is empty at `N == 1` — the
/// reason `WellFormedConstants` now demands `N >= 2`. Everything that reasons
/// "this action sent an `Accept`, so one is in the network" goes through here.
pub proof fn lemma_broadcast_nonempty(c: LConstants, msg: LEPaxosStarMessage)
    requires
        WellFormedConstants(c),
    ensures
        exists|pkt: LPacket|
            (#[trigger] Broadcast(c, msg).contains(pkt)) && pkt.msg == msg && pkt.src == c.my_id,
{
    broadcast use vstd::set_lib::group_set_lib_default;
    let others = c.procs.remove(c.my_id);
    assert(others.len() == c.procs.len() - 1);
    assert(others.len() > 0);
    let q = others.choose();
    assert(others.contains(q)) by {
        vstd::set_lib::lemma_set_empty_equivalency_len::<int>(others);
    }
    let pkt = LPacket { src: c.my_id, dst: q, msg };
    assert(Broadcast(c, msg).contains(pkt)) by {
        assert(others.contains(q) && pkt == (|x: int| LPacket { src: c.my_id, dst: x, msg })(q));
    }
}

/// Some `Accept` for `(id, b)` exists, whatever payload it carried.
pub open spec fn SomeAcceptSent(
    ds: EPaxosStarDistributedState,
    id: LInstanceId,
    b: int,
) -> bool {
    exists|c: LCmd, d: Set<LInstanceId>| #[trigger] AcceptSent(ds, id, b, c, d)
}

/// **`AcceptOKImpliesAccept`** — nobody answers an `Accept` that was never sent.
///
/// The reference gets this for free by construction: `HandleAcceptOK` reads a
/// quorum straight out of `msgs`, and `msgs` only holds what was sent. Our
/// accumulators hold senders, so the link back to a real `Accept` has to be an
/// invariant. This is the first half of the obligation 57.1.c names.
pub open spec fn AcceptOKImpliesAccept(ds: EPaxosStarDistributedState) -> bool {
    forall|id: LInstanceId, b: int, p: int|
        #[trigger] AcceptOKFrom(ds, id, b, p) ==> SomeAcceptSent(ds, id, b)
}

/// `SomeAcceptSent` survives network growth — the same monotonicity argument as
/// `lemma_chosen_monotone`, needed separately because this predicate hides its
/// payload behind an existential.
pub proof fn lemma_some_accept_monotone(
    ds: EPaxosStarDistributedState,
    ds_: EPaxosStarDistributedState,
    id: LInstanceId,
    b: int,
)
    requires
        ds.network.subset_of(ds_.network),
        SomeAcceptSent(ds, id, b),
    ensures
        SomeAcceptSent(ds_, id, b),
{
    let (c, d): (LCmd, Set<LInstanceId>) = choose|c: LCmd, d: Set<LInstanceId>|
        #[trigger] AcceptSent(ds, id, b, c, d);
    let w = choose|pkt: LPacket|
        (#[trigger] ds.network.contains(pkt)) && pkt.msg == LEPaxosStarMessage::Accept {
            id,
            b,
            c,
            d,
        };
    assert(ds_.network.contains(w));
    assert(AcceptSent(ds_, id, b, c, d));
}

pub proof fn lemma_acceptok_implies_accept_at_init(ds: EPaxosStarDistributedState)
    requires
        EPaxosStarDistributedInit(ds),
    ensures
        AcceptOKImpliesAccept(ds),
{
    assert forall|id: LInstanceId, b: int, p: int| !(#[trigger] AcceptOKFrom(ds, id, b, p)) by {
        assert(ds.network =~= Set::<LPacket>::empty());
        if AcceptOKFrom(ds, id, b, p) {
            let w = choose|pkt: LPacket|
                (#[trigger] ds.network.contains(pkt)) && pkt.src == p && pkt.msg
                    == LEPaxosStarMessage::AcceptOK { id, b };
            assert(ds.network.contains(w));
            assert(false);
        }
    }
}

// =========================================================================
// Packet-shape helpers
//
// Every action states `sent =~= <some combination of Broadcast / BroadcastTo /
// ReplyTo / SelfPacket>`. To rule an action out of a network invariant one has
// to get from "pkt is in that set" to "pkt's message is one of these two
// constructors", and these are what make that step mechanical. Without them
// each of the 25 cases would have to re-derive `Set::map` membership.
// =========================================================================

pub proof fn lemma_broadcast_shape(c: LConstants, msg: LEPaxosStarMessage, pkt: LPacket)
    requires
        Broadcast(c, msg).contains(pkt),
    ensures
        pkt.msg == msg,
        pkt.src == c.my_id,
{
    broadcast use vstd::set_lib::group_set_lib_default;
    assert(exists|q: int|
        c.procs.remove(c.my_id).contains(q) && pkt == (|x: int|
            LPacket { src: c.my_id, dst: x, msg })(q));
}

pub proof fn lemma_broadcast_to_shape(
    c: LConstants,
    targets: Set<int>,
    msg: LEPaxosStarMessage,
    pkt: LPacket,
)
    requires
        BroadcastTo(c, targets, msg).contains(pkt),
    ensures
        pkt.msg == msg,
        pkt.src == c.my_id,
{
    broadcast use vstd::set_lib::group_set_lib_default;
    assert(exists|q: int|
        targets.remove(c.my_id).contains(q) && pkt == (|x: int|
            LPacket { src: c.my_id, dst: x, msg })(q));
}

pub proof fn lemma_reply_shape(
    c: LConstants,
    orig: LPacket,
    msg: LEPaxosStarMessage,
    pkt: LPacket,
)
    requires
        ReplyTo(c, orig, msg).contains(pkt),
    ensures
        pkt.msg == msg,
        pkt.src == c.my_id,
{
}

/// A packet whose message is `AcceptOK` cannot have come out of a broadcast of
/// anything else. Stated once, in the form the case analysis needs.
pub proof fn lemma_not_acceptok_from_broadcast(
    c: LConstants,
    msg: LEPaxosStarMessage,
    pkt: LPacket,
    id: LInstanceId,
    b: int,
)
    requires
        Broadcast(c, msg).contains(pkt),
        pkt.msg == (LEPaxosStarMessage::AcceptOK { id, b }),
    ensures
        msg == (LEPaxosStarMessage::AcceptOK { id, b }),
{
    lemma_broadcast_shape(c, msg, pkt);
}

/// Some `Accept` for `(id, b)` sits in this packet set.
pub open spec fn HasAcceptFor(pkts: Set<LPacket>, id: LInstanceId, b: int) -> bool {
    exists|pkt: LPacket|
        (#[trigger] pkts.contains(pkt)) && pkt.msg is Accept && pkt.msg->Accept_id == id
            && pkt.msg->Accept_b == b
}

/// Every action that emits an `Accept` broadcast puts a real packet in `sent`.
/// The bridge from `lemma_broadcast_nonempty` to the form the invariant wants.
pub proof fn lemma_accept_broadcast_gives_has_accept(
    c: LConstants,
    id: LInstanceId,
    b: int,
    cc: LCmd,
    dd: Set<LInstanceId>,
    extra: LPacket,
)
    requires
        WellFormedConstants(c),
    ensures
        HasAcceptFor(
            Broadcast(c, LEPaxosStarMessage::Accept { id, b, c: cc, d: dd }).insert(extra),
            id,
            b,
        ),
{
    let msg = LEPaxosStarMessage::Accept { id, b, c: cc, d: dd };
    lemma_broadcast_nonempty(c, msg);
    let w = choose|pkt: LPacket|
        (#[trigger] Broadcast(c, msg).contains(pkt)) && pkt.msg == msg && pkt.src == c.my_id;
    assert(Broadcast(c, msg).insert(extra).contains(w));
    assert(w.msg is Accept && w.msg->Accept_id == id && w.msg->Accept_b == b);
}

} // verus!

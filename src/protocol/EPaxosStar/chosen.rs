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

/// Every packet in this set carries one of (at most) two messages.
///
/// Sixteen of the twenty-five actions emit no `AcceptOK` at all, and the only
/// thing the case analysis needs from them is exactly this. Proving it once per
/// *shape* rather than once per action is what keeps the case analysis to one
/// line each.
pub open spec fn OnlyMsgs(
    sent: Set<LPacket>,
    m1: LEPaxosStarMessage,
    m2: LEPaxosStarMessage,
) -> bool {
    forall|p: LPacket| (#[trigger] sent.contains(p)) ==> p.msg == m1 || p.msg == m2
}

pub proof fn lemma_only_broadcast(c: LConstants, m: LEPaxosStarMessage)
    ensures
        OnlyMsgs(Broadcast(c, m), m, m),
{
    assert forall|p: LPacket| (#[trigger] Broadcast(c, m).contains(p)) implies p.msg == m by {
        lemma_broadcast_shape(c, m, p);
    }
}

pub proof fn lemma_only_broadcast_insert(
    c: LConstants,
    m: LEPaxosStarMessage,
    extra: LPacket,
)
    ensures
        OnlyMsgs(Broadcast(c, m).insert(extra), m, extra.msg),
{
    assert forall|p: LPacket| (#[trigger] Broadcast(c, m).insert(extra).contains(p))
        implies p.msg == m || p.msg == extra.msg by {
        if p != extra {
            lemma_broadcast_shape(c, m, p);
        }
    }
}

pub proof fn lemma_only_broadcast_to_insert(
    c: LConstants,
    t: Set<int>,
    m: LEPaxosStarMessage,
    extra: LPacket,
)
    ensures
        OnlyMsgs(BroadcastTo(c, t, m).insert(extra), m, extra.msg),
{
    assert forall|p: LPacket| (#[trigger] BroadcastTo(c, t, m).insert(extra).contains(p))
        implies p.msg == m || p.msg == extra.msg by {
        if p != extra {
            lemma_broadcast_to_shape(c, t, m, p);
        }
    }
}

pub proof fn lemma_only_reply(c: LConstants, o: LPacket, m: LEPaxosStarMessage)
    ensures
        OnlyMsgs(ReplyTo(c, o, m), m, m),
{
}

pub proof fn lemma_only_empty(m: LEPaxosStarMessage)
    ensures
        OnlyMsgs(Set::<LPacket>::empty(), m, m),
{
}

/// The Shape-A conclusion, packaged: nine actions emit an `Accept` broadcast
/// together with a self-addressed `AcceptOK` in the same `sent`, so the
/// justification is right there.
pub proof fn lemma_shape_a_justifies(
    c: LConstants,
    id: LInstanceId,
    b: int,
    cc: LCmd,
    dd: Set<LInstanceId>,
    extra: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        sent =~= Broadcast(c, LEPaxosStarMessage::Accept { id, b, c: cc, d: dd }).insert(extra),
    ensures
        HasAcceptFor(sent, id, b),
{
    lemma_accept_broadcast_gives_has_accept(c, id, b, cc, dd, extra);
    assert(sent =~= Broadcast(c, LEPaxosStarMessage::Accept { id, b, c: cc, d: dd }).insert(
        extra,
    ));
}

// =========================================================================
// The frame lemma every invariant needs
// =========================================================================

/// The step left every instance other than `idX` exactly as it was.
pub open spec fn TouchesOnly(s: LState, s_: LState, idX: LInstanceId) -> bool {
    forall|j: LInstanceId| j != idX ==> #[trigger] InstAt(s_, j) == InstAt(s, j)
}

/// All twenty-five actions update state the same way — `instances.insert(idX,
/// ...)` for a single `idX` — so this is proved once and the case analysis only
/// has to name `idX`.
pub proof fn lemma_insert_touches_one(s: LState, s_: LState, idX: LInstanceId)
    requires
        s_.instances == s.instances.insert(idX, s_.instances[idX]),
    ensures
        TouchesOnly(s, s_, idX),
{
    assert forall|j: LInstanceId| j != idX implies #[trigger] InstAt(s_, j) == InstAt(s, j) by {
        assert(s_.instances.dom().contains(j) <==> s.instances.dom().contains(j));
    }
}

/// **Every action touches at most one instance.**
///
/// Twenty-five branches, two lines each, because the shape is uniform. This is
/// the frame reasoning that every later invariant leans on: for an instance the
/// step did not touch, the invariant carries over unchanged and only the touched
/// one needs an argument.
pub proof fn lemma_action_touches_one(
    s: LState,
    s_: LState,
    c: LConstants,
    received: Option<LPacket>,
    sent: Set<LPacket>,
)
    requires
        ReplicaAction(s, s_, c, received, sent),
    ensures
        exists|idX: LInstanceId| #[trigger] TouchesOnly(s, s_, idX),
{
    match received {
        Option::None => {
        if exists|v: int| LSubmit(s, s_, c, v, sent) {
        let v = choose|v: int| LSubmit(s, s_, c, v, sent);
        lemma_insert_touches_one(s, s_, LInstanceId { owner: c.my_id, num: s.next_num });
        assert(TouchesOnly(s, s_, LInstanceId { owner: c.my_id, num: s.next_num }));
        } else if exists|w: LInstanceId| LCommitFast(s, s_, c, w, sent) {
        let w = choose|w: LInstanceId| LCommitFast(s, s_, c, w, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else if exists|w: LInstanceId| LStartAccept(s, s_, c, w, sent) {
        let w = choose|w: LInstanceId| LStartAccept(s, s_, c, w, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else if exists|w: LInstanceId| LCommitSlow(s, s_, c, w, sent) {
        let w = choose|w: LInstanceId| LCommitSlow(s, s_, c, w, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else if exists|w: LInstanceId| LStartRecover(s, s_, c, w, sent) {
        let w = choose|w: LInstanceId| LStartRecover(s, s_, c, w, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else if exists|w: LInstanceId| LRecoverCommitted(s, s_, c, w, sent) {
        let w = choose|w: LInstanceId| LRecoverCommitted(s, s_, c, w, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else if exists|w: LInstanceId| LRecoverAccepted(s, s_, c, w, sent) {
        let w = choose|w: LInstanceId| LRecoverAccepted(s, s_, c, w, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else if exists|w: LInstanceId| LRecoverNop(s, s_, c, w, sent) {
        let w = choose|w: LInstanceId| LRecoverNop(s, s_, c, w, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else if exists|w: LInstanceId| LRecoverValidate(s, s_, c, w, sent) {
        let w = choose|w: LInstanceId| LRecoverValidate(s, s_, c, w, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else if exists|w: LInstanceId| LValidateAccept(s, s_, c, w, sent) {
        let w = choose|w: LInstanceId| LValidateAccept(s, s_, c, w, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else if exists|w: LInstanceId| LValidateNop(s, s_, c, w, sent) {
        let w = choose|w: LInstanceId| LValidateNop(s, s_, c, w, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else if exists|w: LInstanceId| LValidateWait(s, s_, c, w, sent) {
        let w = choose|w: LInstanceId| LValidateWait(s, s_, c, w, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else if exists|w: LInstanceId| LPostWaitingNop(s, s_, c, w, sent) {
        let w = choose|w: LInstanceId| LPostWaitingNop(s, s_, c, w, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else if exists|w: LInstanceId| LPostWaitingAccept(s, s_, c, w, sent) {
        let w = choose|w: LInstanceId| LPostWaitingAccept(s, s_, c, w, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else {
            assert(false);
        }
        },
        Option::Some(rp) => {
        if LHandlePreAccept(s, s_, c, rp, sent) {
        lemma_insert_touches_one(s, s_, rp.msg->PreAccept_id);
        assert(TouchesOnly(s, s_, rp.msg->PreAccept_id));
        } else if LRecordPreAcceptOK(s, s_, c, rp, sent) {
        lemma_insert_touches_one(s, s_, rp.msg->PreAcceptOK_id);
        assert(TouchesOnly(s, s_, rp.msg->PreAcceptOK_id));
        } else if LHandleAccept(s, s_, c, rp, sent) {
        lemma_insert_touches_one(s, s_, rp.msg->Accept_id);
        assert(TouchesOnly(s, s_, rp.msg->Accept_id));
        } else if LRecordAcceptOK(s, s_, c, rp, sent) {
        lemma_insert_touches_one(s, s_, rp.msg->AcceptOK_id);
        assert(TouchesOnly(s, s_, rp.msg->AcceptOK_id));
        } else if LHandleCommit(s, s_, c, rp, sent) {
        lemma_insert_touches_one(s, s_, rp.msg->Commit_id);
        assert(TouchesOnly(s, s_, rp.msg->Commit_id));
        } else if LHandleRecover(s, s_, c, rp, sent) {
        lemma_insert_touches_one(s, s_, rp.msg->Recover_id);
        assert(TouchesOnly(s, s_, rp.msg->Recover_id));
        } else if LRecordRecoverOK(s, s_, c, rp, sent) {
        lemma_insert_touches_one(s, s_, rp.msg->RecoverOK_id);
        assert(TouchesOnly(s, s_, rp.msg->RecoverOK_id));
        } else if LHandleValidate(s, s_, c, rp, sent) {
        lemma_insert_touches_one(s, s_, rp.msg->Validate_id);
        assert(TouchesOnly(s, s_, rp.msg->Validate_id));
        } else if LRecordValidateOK(s, s_, c, rp, sent) {
        lemma_insert_touches_one(s, s_, rp.msg->ValidateOK_id);
        assert(TouchesOnly(s, s_, rp.msg->ValidateOK_id));
        } else if exists|w: LInstanceId| LPostWaitingOnWaiting(s, s_, c, w, rp, sent) {
        let w = choose|w: LInstanceId| LPostWaitingOnWaiting(s, s_, c, w, rp, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else if exists|w: LInstanceId| LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent) {
        let w = choose|w: LInstanceId| LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent);
        lemma_insert_touches_one(s, s_, w);
        assert(TouchesOnly(s, s_, w));
        } else {
            assert(false);
        }
        },
    }
}

// =========================================================================
// AcceptedStateHasAccept — and why it is stated on `abal`, not `bal`
// =========================================================================

/// A replica in phase `Accepted` holds a value that really was proposed in an
/// `Accept` — **at `abal`, not at `bal`**.
///
/// The first attempt at this said `bal`, and it is false: `LHandleRecover`
/// applies `RecoveredInstance`, which moves `bal` to the recovering replica's
/// ballot while leaving `phase`, `abal`, `cmd` and `dep` alone. A replica
/// sitting in `Accepted` can therefore have a `bal` at which no `Accept` was
/// ever sent.
///
/// `abal` is moved only by `AcceptedInstance` and `CommittedInstance` — never by
/// `RecoveredInstance` — so it is the ballot at which the held value was
/// actually accepted. **That is precisely what the field exists for, and the
/// single-ballot protocol is unsound for exactly the reason this formulation
/// would be wrong without it.** The invariant is the fix, restated.
pub open spec fn AcceptedStateHasAccept(ds: EPaxosStarDistributedState) -> bool {
    forall|i: int, id: LInstanceId|
        0 <= i < ds.num_replicas && (#[trigger] InstAt(ds.replica_states[i], id)).phase
            is Accepted ==> AcceptSent(
            ds,
            id,
            InstAt(ds.replica_states[i], id).abal,
            InstAt(ds.replica_states[i], id).cmd,
            InstAt(ds.replica_states[i], id).dep,
        )
}

/// `abal` moves only when a value is accepted or committed, and both of those
/// set `phase` accordingly. So a non-zero `abal` means the replica has decided
/// something.
///
/// Needed to show `LRecoverValidate` cannot fire while the acting replica is in
/// phase `Accepted`: branch 4 requires that nobody at the maximum `abal` is
/// `Accepted` or `Committed`, and this is what turns that into a statement about
/// phases. Without it `ApplyValidate` — which rewrites `cmd` while leaving
/// `abal` and `phase` untouched — would break `AcceptedStateHasAccept`.
pub open spec fn AbalPositiveImpliesDecided(ds: EPaxosStarDistributedState) -> bool {
    forall|i: int, id: LInstanceId|
        0 <= i < ds.num_replicas && (#[trigger] InstAt(ds.replica_states[i], id)).abal > 0 ==> {
            ||| InstAt(ds.replica_states[i], id).phase is Accepted
            ||| InstAt(ds.replica_states[i], id).phase is Committed
        }
}

pub proof fn lemma_accepted_has_accept_at_init(ds: EPaxosStarDistributedState)
    requires
        EPaxosStarDistributedInit(ds),
    ensures
        AcceptedStateHasAccept(ds),
        AbalPositiveImpliesDecided(ds),
{
    assert forall|i: int, id: LInstanceId| 0 <= i < ds.num_replicas implies #[trigger] InstAt(
        ds.replica_states[i],
        id,
    ) == InitialInstance() by {
        assert(LInit(ds.replica_states[i], ds.replica_constants[i]));
        assert(!ds.replica_states[i].instances.dom().contains(id));
    }
}

/// The invariant survives a step that leaves this replica's instance alone —
/// the frame half, which `lemma_action_touches_one` makes available for every
/// action at once.
pub proof fn lemma_accepted_has_accept_frame(
    ds: EPaxosStarDistributedState,
    ds_: EPaxosStarDistributedState,
    i: int,
    id: LInstanceId,
)
    requires
        ds.network.subset_of(ds_.network),
        0 <= i < ds.num_replicas,
        InstAt(ds_.replica_states[i], id) == InstAt(ds.replica_states[i], id),
        AcceptedStateHasAccept(ds),
        InstAt(ds_.replica_states[i], id).phase is Accepted,
    ensures
        AcceptSent(
            ds_,
            id,
            InstAt(ds_.replica_states[i], id).abal,
            InstAt(ds_.replica_states[i], id).cmd,
            InstAt(ds_.replica_states[i], id).dep,
        ),
{
    let inst = InstAt(ds.replica_states[i], id);
    assert(AcceptSent(ds, id, inst.abal, inst.cmd, inst.dep));
    let w = choose|pkt: LPacket|
        (#[trigger] ds.network.contains(pkt)) && pkt.msg == LEPaxosStarMessage::Accept {
            id,
            b: inst.abal,
            c: inst.cmd,
            d: inst.dep,
        };
    assert(ds_.network.contains(w));
}

/// **`abal` is zero until something is decided.**
///
/// `abal` is written only by `AcceptedInstance` and `CommittedInstance`, and
/// both set `phase` to match. Everything else — `RecoveredInstance`,
/// `ValidatedInstance`, all the accumulator updates — leaves it alone, and
/// `PreAcceptedInstance` is guarded on `phase is Initial`, where it is already
/// zero.
///
/// This is what turns `HandleRecoverOK`'s branch conditions, which are about
/// *phases* reported by a quorum, into statements about `abal` — the ordering
/// the whole recovery decision is made on.
pub open spec fn AbalZeroLocal(s: LState) -> bool {
    forall|id: LInstanceId|
        #![trigger InstAt(s, id)]
        InstAt(s, id).phase is Accepted || InstAt(s, id).phase is Committed || InstAt(s, id).abal
            == 0
}

proof fn lemma_abal_zero_lsubmit(
    s: LState,
    s_: LState,
    c: LConstants,
    v: int,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LSubmit(s, s_, c, v, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = LInstanceId { owner: c.my_id, num: s.next_num };
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lcommitfast(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LCommitFast(s, s_, c, w, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lstartaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LStartAccept(s, s_, c, w, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lcommitslow(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LCommitSlow(s, s_, c, w, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lstartrecover(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LStartRecover(s, s_, c, w, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lrecovercommitted(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LRecoverCommitted(s, s_, c, w, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lrecoveraccepted(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LRecoverAccepted(s, s_, c, w, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lrecovernop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LRecoverNop(s, s_, c, w, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lrecovervalidate(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LRecoverValidate(s, s_, c, w, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lvalidateaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LValidateAccept(s, s_, c, w, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lvalidatenop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LValidateNop(s, s_, c, w, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lvalidatewait(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LValidateWait(s, s_, c, w, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lpostwaitingnop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LPostWaitingNop(s, s_, c, w, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lpostwaitingaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LPostWaitingAccept(s, s_, c, w, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lhandlepreaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LHandlePreAccept(s, s_, c, rp, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = rp.msg->PreAccept_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lrecordpreacceptok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LRecordPreAcceptOK(s, s_, c, rp, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = rp.msg->PreAcceptOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lhandleaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LHandleAccept(s, s_, c, rp, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = rp.msg->Accept_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lrecordacceptok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LRecordAcceptOK(s, s_, c, rp, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = rp.msg->AcceptOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lhandlecommit(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LHandleCommit(s, s_, c, rp, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = rp.msg->Commit_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lhandlerecover(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LHandleRecover(s, s_, c, rp, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = rp.msg->Recover_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lrecordrecoverok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LRecordRecoverOK(s, s_, c, rp, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = rp.msg->RecoverOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lhandlevalidate(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LHandleValidate(s, s_, c, rp, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = rp.msg->Validate_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lrecordvalidateok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LRecordValidateOK(s, s_, c, rp, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = rp.msg->ValidateOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lpostwaitingonwaiting(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId, rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LPostWaitingOnWaiting(s, s_, c, w, rp, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_abal_zero_lpostwaitingonrecoverok(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId, rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent),
    ensures
        AbalZeroLocal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Accepted || InstAt(s_, id).phase is Committed || InstAt(
            s_,
            id,
        ).abal == 0 by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

pub proof fn lemma_abal_zero_step(
    s: LState,
    s_: LState,
    c: LConstants,
    received: Option<LPacket>,
    sent: Set<LPacket>,
)
    requires
        AbalZeroLocal(s),
        ReplicaAction(s, s_, c, received, sent),
    ensures
        AbalZeroLocal(s_),
{
    match received {
        Option::None => {
            if exists|v: int| LSubmit(s, s_, c, v, sent) {
                let v = choose|v: int| LSubmit(s, s_, c, v, sent);
                lemma_abal_zero_lsubmit(s, s_, c, v, sent);
            } else if exists|w: LInstanceId| LCommitFast(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LCommitFast(s, s_, c, w, sent);
                lemma_abal_zero_lcommitfast(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LStartAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LStartAccept(s, s_, c, w, sent);
                lemma_abal_zero_lstartaccept(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LCommitSlow(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LCommitSlow(s, s_, c, w, sent);
                lemma_abal_zero_lcommitslow(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LStartRecover(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LStartRecover(s, s_, c, w, sent);
                lemma_abal_zero_lstartrecover(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverCommitted(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverCommitted(s, s_, c, w, sent);
                lemma_abal_zero_lrecovercommitted(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverAccepted(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverAccepted(s, s_, c, w, sent);
                lemma_abal_zero_lrecoveraccepted(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverNop(s, s_, c, w, sent);
                lemma_abal_zero_lrecovernop(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverValidate(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverValidate(s, s_, c, w, sent);
                lemma_abal_zero_lrecovervalidate(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LValidateAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateAccept(s, s_, c, w, sent);
                lemma_abal_zero_lvalidateaccept(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LValidateNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateNop(s, s_, c, w, sent);
                lemma_abal_zero_lvalidatenop(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LValidateWait(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateWait(s, s_, c, w, sent);
                lemma_abal_zero_lvalidatewait(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LPostWaitingNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LPostWaitingNop(s, s_, c, w, sent);
                lemma_abal_zero_lpostwaitingnop(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LPostWaitingAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LPostWaitingAccept(s, s_, c, w, sent);
                lemma_abal_zero_lpostwaitingaccept(s, s_, c, w, sent);
            } else {
                assert(false);
            }
        },
        Option::Some(rp) => {
            if LHandlePreAccept(s, s_, c, rp, sent) {
                lemma_abal_zero_lhandlepreaccept(s, s_, c, rp, sent);
            } else if LRecordPreAcceptOK(s, s_, c, rp, sent) {
                lemma_abal_zero_lrecordpreacceptok(s, s_, c, rp, sent);
            } else if LHandleAccept(s, s_, c, rp, sent) {
                lemma_abal_zero_lhandleaccept(s, s_, c, rp, sent);
            } else if LRecordAcceptOK(s, s_, c, rp, sent) {
                lemma_abal_zero_lrecordacceptok(s, s_, c, rp, sent);
            } else if LHandleCommit(s, s_, c, rp, sent) {
                lemma_abal_zero_lhandlecommit(s, s_, c, rp, sent);
            } else if LHandleRecover(s, s_, c, rp, sent) {
                lemma_abal_zero_lhandlerecover(s, s_, c, rp, sent);
            } else if LRecordRecoverOK(s, s_, c, rp, sent) {
                lemma_abal_zero_lrecordrecoverok(s, s_, c, rp, sent);
            } else if LHandleValidate(s, s_, c, rp, sent) {
                lemma_abal_zero_lhandlevalidate(s, s_, c, rp, sent);
            } else if LRecordValidateOK(s, s_, c, rp, sent) {
                lemma_abal_zero_lrecordvalidateok(s, s_, c, rp, sent);
            } else if exists|w: LInstanceId| LPostWaitingOnWaiting(s, s_, c, w, rp, sent) {
                let w = choose|w: LInstanceId| LPostWaitingOnWaiting(s, s_, c, w, rp, sent);
                lemma_abal_zero_lpostwaitingonwaiting(s, s_, c, w, rp, sent);
            } else if exists|w: LInstanceId| LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent) {
                let w = choose|w: LInstanceId| LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent);
                lemma_abal_zero_lpostwaitingonrecoverok(s, s_, c, w, rp, sent);
            } else {
                assert(false);
            }
        },
    }
}

/// **`abal <= bal` always.** `AcceptedInstance` sets both to the same ballot;
/// `CommittedInstance` sets `abal := b` under a guard that already forces
/// `bal == b`; `RecoveredInstance` raises `bal` alone, under a guard that it
/// strictly increases. Nothing can push `abal` past `bal`, which is what makes
/// 'the highest ballot at which anyone accepted' comparable with 'the highest
/// ballot anyone has promised'.
pub open spec fn AbalLeBal(s: LState) -> bool {
    forall|id: LInstanceId|
        #![trigger InstAt(s, id)]
        InstAt(s, id).abal <= InstAt(s, id).bal
}

proof fn lemma_aballebal_lsubmit(
    s: LState,
    s_: LState,
    c: LConstants,
    v: int,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LSubmit(s, s_, c, v, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = LInstanceId { owner: c.my_id, num: s.next_num };
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lcommitfast(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LCommitFast(s, s_, c, w, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lstartaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LStartAccept(s, s_, c, w, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lcommitslow(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LCommitSlow(s, s_, c, w, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lstartrecover(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LStartRecover(s, s_, c, w, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lrecovercommitted(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LRecoverCommitted(s, s_, c, w, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lrecoveraccepted(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LRecoverAccepted(s, s_, c, w, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lrecovernop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LRecoverNop(s, s_, c, w, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lrecovervalidate(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LRecoverValidate(s, s_, c, w, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lvalidateaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LValidateAccept(s, s_, c, w, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lvalidatenop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LValidateNop(s, s_, c, w, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lvalidatewait(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LValidateWait(s, s_, c, w, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lpostwaitingnop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LPostWaitingNop(s, s_, c, w, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lpostwaitingaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LPostWaitingAccept(s, s_, c, w, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lhandlepreaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LHandlePreAccept(s, s_, c, rp, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = rp.msg->PreAccept_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lrecordpreacceptok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LRecordPreAcceptOK(s, s_, c, rp, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = rp.msg->PreAcceptOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lhandleaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LHandleAccept(s, s_, c, rp, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = rp.msg->Accept_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lrecordacceptok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LRecordAcceptOK(s, s_, c, rp, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = rp.msg->AcceptOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lhandlecommit(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LHandleCommit(s, s_, c, rp, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = rp.msg->Commit_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lhandlerecover(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LHandleRecover(s, s_, c, rp, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = rp.msg->Recover_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lrecordrecoverok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LRecordRecoverOK(s, s_, c, rp, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = rp.msg->RecoverOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lhandlevalidate(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LHandleValidate(s, s_, c, rp, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = rp.msg->Validate_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lrecordvalidateok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LRecordValidateOK(s, s_, c, rp, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = rp.msg->ValidateOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lpostwaitingonwaiting(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId, rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LPostWaitingOnWaiting(s, s_, c, w, rp, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_aballebal_lpostwaitingonrecoverok(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId, rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent),
    ensures
        AbalLeBal(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).abal <= InstAt(s_, id).bal by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

pub proof fn lemma_aballebal_step(
    s: LState,
    s_: LState,
    c: LConstants,
    received: Option<LPacket>,
    sent: Set<LPacket>,
)
    requires
        AbalLeBal(s),
        ReplicaAction(s, s_, c, received, sent),
    ensures
        AbalLeBal(s_),
{
    match received {
        Option::None => {
            if exists|v: int| LSubmit(s, s_, c, v, sent) {
                let v = choose|v: int| LSubmit(s, s_, c, v, sent);
                lemma_aballebal_lsubmit(s, s_, c, v, sent);
            } else if exists|w: LInstanceId| LCommitFast(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LCommitFast(s, s_, c, w, sent);
                lemma_aballebal_lcommitfast(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LStartAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LStartAccept(s, s_, c, w, sent);
                lemma_aballebal_lstartaccept(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LCommitSlow(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LCommitSlow(s, s_, c, w, sent);
                lemma_aballebal_lcommitslow(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LStartRecover(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LStartRecover(s, s_, c, w, sent);
                lemma_aballebal_lstartrecover(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverCommitted(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverCommitted(s, s_, c, w, sent);
                lemma_aballebal_lrecovercommitted(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverAccepted(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverAccepted(s, s_, c, w, sent);
                lemma_aballebal_lrecoveraccepted(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverNop(s, s_, c, w, sent);
                lemma_aballebal_lrecovernop(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverValidate(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverValidate(s, s_, c, w, sent);
                lemma_aballebal_lrecovervalidate(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LValidateAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateAccept(s, s_, c, w, sent);
                lemma_aballebal_lvalidateaccept(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LValidateNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateNop(s, s_, c, w, sent);
                lemma_aballebal_lvalidatenop(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LValidateWait(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateWait(s, s_, c, w, sent);
                lemma_aballebal_lvalidatewait(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LPostWaitingNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LPostWaitingNop(s, s_, c, w, sent);
                lemma_aballebal_lpostwaitingnop(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LPostWaitingAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LPostWaitingAccept(s, s_, c, w, sent);
                lemma_aballebal_lpostwaitingaccept(s, s_, c, w, sent);
            } else {
                assert(false);
            }
        },
        Option::Some(rp) => {
            if LHandlePreAccept(s, s_, c, rp, sent) {
                lemma_aballebal_lhandlepreaccept(s, s_, c, rp, sent);
            } else if LRecordPreAcceptOK(s, s_, c, rp, sent) {
                lemma_aballebal_lrecordpreacceptok(s, s_, c, rp, sent);
            } else if LHandleAccept(s, s_, c, rp, sent) {
                lemma_aballebal_lhandleaccept(s, s_, c, rp, sent);
            } else if LRecordAcceptOK(s, s_, c, rp, sent) {
                lemma_aballebal_lrecordacceptok(s, s_, c, rp, sent);
            } else if LHandleCommit(s, s_, c, rp, sent) {
                lemma_aballebal_lhandlecommit(s, s_, c, rp, sent);
            } else if LHandleRecover(s, s_, c, rp, sent) {
                lemma_aballebal_lhandlerecover(s, s_, c, rp, sent);
            } else if LRecordRecoverOK(s, s_, c, rp, sent) {
                lemma_aballebal_lrecordrecoverok(s, s_, c, rp, sent);
            } else if LHandleValidate(s, s_, c, rp, sent) {
                lemma_aballebal_lhandlevalidate(s, s_, c, rp, sent);
            } else if LRecordValidateOK(s, s_, c, rp, sent) {
                lemma_aballebal_lrecordvalidateok(s, s_, c, rp, sent);
            } else if exists|w: LInstanceId| LPostWaitingOnWaiting(s, s_, c, w, rp, sent) {
                let w = choose|w: LInstanceId| LPostWaitingOnWaiting(s, s_, c, w, rp, sent);
                lemma_aballebal_lpostwaitingonwaiting(s, s_, c, w, rp, sent);
            } else if exists|w: LInstanceId| LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent) {
                let w = choose|w: LInstanceId| LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent);
                lemma_aballebal_lpostwaitingonrecoverok(s, s_, c, w, rp, sent);
            } else {
                assert(false);
            }
        },
    }
}

/// **Accumulator soundness (`TODO.md` 57.1.b), for the accept round.** A replica
/// that has `p` in `accept_rcvd` really did receive an `AcceptOK` from `p` at
/// its current ballot.
///
/// The reference needs no such invariant: `HandleAcceptOK` reads the quorum
/// straight out of `msgs`, so it is true by construction. Our single-process
/// projection turns that read into an accumulator, and this is the debt that
/// creates. Everything that could break it also clears the accumulator --
/// `AcceptedInstance` and `RecoveredInstance` both do, which is the same
/// ballot-scoping discipline `TODO.md` 56.4.g named.
pub open spec fn AcceptRcvdSound(s: LState, network: Set<LPacket>) -> bool {
    forall|id: LInstanceId, p: int|
        #![trigger InstAt(s, id).accept_rcvd.contains(p)]
        InstAt(s, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal })
}

proof fn lemma_acceptrcvdsound_lsubmit(
    s: LState,
    s_: LState,
    c: LConstants,
    v: int,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LSubmit(s, s_, c, v, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = LInstanceId { owner: c.my_id, num: s.next_num };
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lcommitfast(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LCommitFast(s, s_, c, w, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lstartaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LStartAccept(s, s_, c, w, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lcommitslow(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LCommitSlow(s, s_, c, w, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lstartrecover(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LStartRecover(s, s_, c, w, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lrecovercommitted(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LRecoverCommitted(s, s_, c, w, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lrecoveraccepted(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LRecoverAccepted(s, s_, c, w, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lrecovernop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LRecoverNop(s, s_, c, w, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lrecovervalidate(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LRecoverValidate(s, s_, c, w, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lvalidateaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LValidateAccept(s, s_, c, w, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lvalidatenop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LValidateNop(s, s_, c, w, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lvalidatewait(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LValidateWait(s, s_, c, w, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lpostwaitingnop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LPostWaitingNop(s, s_, c, w, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lpostwaitingaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LPostWaitingAccept(s, s_, c, w, sent),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lhandlepreaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LHandlePreAccept(s, s_, c, rp, sent),
        network.contains(rp),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = rp.msg->PreAccept_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lrecordpreacceptok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LRecordPreAcceptOK(s, s_, c, rp, sent),
        network.contains(rp),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = rp.msg->PreAcceptOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lhandleaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LHandleAccept(s, s_, c, rp, sent),
        network.contains(rp),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = rp.msg->Accept_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lrecordacceptok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LRecordAcceptOK(s, s_, c, rp, sent),
        network.contains(rp),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = rp.msg->AcceptOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            if p == rp.src {
                assert(network_.contains(rp));
            } else {
                assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
                assert(network_.contains(pk));
            }
        }
    }
}

proof fn lemma_acceptrcvdsound_lhandlecommit(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LHandleCommit(s, s_, c, rp, sent),
        network.contains(rp),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = rp.msg->Commit_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lhandlerecover(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LHandleRecover(s, s_, c, rp, sent),
        network.contains(rp),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = rp.msg->Recover_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lrecordrecoverok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LRecordRecoverOK(s, s_, c, rp, sent),
        network.contains(rp),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = rp.msg->RecoverOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lhandlevalidate(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LHandleValidate(s, s_, c, rp, sent),
        network.contains(rp),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = rp.msg->Validate_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lrecordvalidateok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LRecordValidateOK(s, s_, c, rp, sent),
        network.contains(rp),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = rp.msg->ValidateOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lpostwaitingonwaiting(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId, rp: LPacket,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LPostWaitingOnWaiting(s, s_, c, w, rp, sent),
        network.contains(rp),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

proof fn lemma_acceptrcvdsound_lpostwaitingonrecoverok(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId, rp: LPacket,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent),
        network.contains(rp),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId, p: int|
        #![trigger InstAt(s_, id).accept_rcvd.contains(p)]
        InstAt(s_, id).accept_rcvd.contains(p) ==> exists|pk: LPacket|
            (#[trigger] network_.contains(pk)) && pk.src == p && pk.msg
                == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s_, id).bal }) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
            if InstAt(s, id).accept_rcvd.contains(p) {
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, id).bal });
                assert(network_.contains(pk));
            }
        } else if InstAt(s_, idX).accept_rcvd.contains(p) {
            assert(InstAt(s, idX).accept_rcvd.contains(p));
            let pk = choose|pk: LPacket|
                (#[trigger] network.contains(pk)) && pk.src == p && pk.msg
                    == (LEPaxosStarMessage::AcceptOK { id, b: InstAt(s, idX).bal });
            assert(network_.contains(pk));
        }
    }
}

pub proof fn lemma_acceptrcvdsound_step(
    s: LState,
    s_: LState,
    c: LConstants,
    received: Option<LPacket>,
    sent: Set<LPacket>,
    network: Set<LPacket>,
    network_: Set<LPacket>,
)
    requires
        AcceptRcvdSound(s, network),
        ReplicaAction(s, s_, c, received, sent),
        received matches Option::Some(rp) ==> network.contains(rp),
        network_ =~= network.union(sent),
    ensures
        AcceptRcvdSound(s_, network_),
{
    match received {
        Option::None => {
            if exists|v: int| LSubmit(s, s_, c, v, sent) {
                let v = choose|v: int| LSubmit(s, s_, c, v, sent);
                lemma_acceptrcvdsound_lsubmit(s, s_, c, v, sent, network, network_);
            } else if exists|w: LInstanceId| LCommitFast(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LCommitFast(s, s_, c, w, sent);
                lemma_acceptrcvdsound_lcommitfast(s, s_, c, w, sent, network, network_);
            } else if exists|w: LInstanceId| LStartAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LStartAccept(s, s_, c, w, sent);
                lemma_acceptrcvdsound_lstartaccept(s, s_, c, w, sent, network, network_);
            } else if exists|w: LInstanceId| LCommitSlow(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LCommitSlow(s, s_, c, w, sent);
                lemma_acceptrcvdsound_lcommitslow(s, s_, c, w, sent, network, network_);
            } else if exists|w: LInstanceId| LStartRecover(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LStartRecover(s, s_, c, w, sent);
                lemma_acceptrcvdsound_lstartrecover(s, s_, c, w, sent, network, network_);
            } else if exists|w: LInstanceId| LRecoverCommitted(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverCommitted(s, s_, c, w, sent);
                lemma_acceptrcvdsound_lrecovercommitted(s, s_, c, w, sent, network, network_);
            } else if exists|w: LInstanceId| LRecoverAccepted(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverAccepted(s, s_, c, w, sent);
                lemma_acceptrcvdsound_lrecoveraccepted(s, s_, c, w, sent, network, network_);
            } else if exists|w: LInstanceId| LRecoverNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverNop(s, s_, c, w, sent);
                lemma_acceptrcvdsound_lrecovernop(s, s_, c, w, sent, network, network_);
            } else if exists|w: LInstanceId| LRecoverValidate(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverValidate(s, s_, c, w, sent);
                lemma_acceptrcvdsound_lrecovervalidate(s, s_, c, w, sent, network, network_);
            } else if exists|w: LInstanceId| LValidateAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateAccept(s, s_, c, w, sent);
                lemma_acceptrcvdsound_lvalidateaccept(s, s_, c, w, sent, network, network_);
            } else if exists|w: LInstanceId| LValidateNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateNop(s, s_, c, w, sent);
                lemma_acceptrcvdsound_lvalidatenop(s, s_, c, w, sent, network, network_);
            } else if exists|w: LInstanceId| LValidateWait(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateWait(s, s_, c, w, sent);
                lemma_acceptrcvdsound_lvalidatewait(s, s_, c, w, sent, network, network_);
            } else if exists|w: LInstanceId| LPostWaitingNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LPostWaitingNop(s, s_, c, w, sent);
                lemma_acceptrcvdsound_lpostwaitingnop(s, s_, c, w, sent, network, network_);
            } else if exists|w: LInstanceId| LPostWaitingAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LPostWaitingAccept(s, s_, c, w, sent);
                lemma_acceptrcvdsound_lpostwaitingaccept(s, s_, c, w, sent, network, network_);
            } else {
                assert(false);
            }
        },
        Option::Some(rp) => {
            if LHandlePreAccept(s, s_, c, rp, sent) {
                lemma_acceptrcvdsound_lhandlepreaccept(s, s_, c, rp, sent, network, network_);
            } else if LRecordPreAcceptOK(s, s_, c, rp, sent) {
                lemma_acceptrcvdsound_lrecordpreacceptok(s, s_, c, rp, sent, network, network_);
            } else if LHandleAccept(s, s_, c, rp, sent) {
                lemma_acceptrcvdsound_lhandleaccept(s, s_, c, rp, sent, network, network_);
            } else if LRecordAcceptOK(s, s_, c, rp, sent) {
                lemma_acceptrcvdsound_lrecordacceptok(s, s_, c, rp, sent, network, network_);
            } else if LHandleCommit(s, s_, c, rp, sent) {
                lemma_acceptrcvdsound_lhandlecommit(s, s_, c, rp, sent, network, network_);
            } else if LHandleRecover(s, s_, c, rp, sent) {
                lemma_acceptrcvdsound_lhandlerecover(s, s_, c, rp, sent, network, network_);
            } else if LRecordRecoverOK(s, s_, c, rp, sent) {
                lemma_acceptrcvdsound_lrecordrecoverok(s, s_, c, rp, sent, network, network_);
            } else if LHandleValidate(s, s_, c, rp, sent) {
                lemma_acceptrcvdsound_lhandlevalidate(s, s_, c, rp, sent, network, network_);
            } else if LRecordValidateOK(s, s_, c, rp, sent) {
                lemma_acceptrcvdsound_lrecordvalidateok(s, s_, c, rp, sent, network, network_);
            } else if exists|w: LInstanceId| LPostWaitingOnWaiting(s, s_, c, w, rp, sent) {
                let w = choose|w: LInstanceId| LPostWaitingOnWaiting(s, s_, c, w, rp, sent);
                lemma_acceptrcvdsound_lpostwaitingonwaiting(s, s_, c, w, rp, sent, network, network_);
            } else if exists|w: LInstanceId| LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent) {
                let w = choose|w: LInstanceId| LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent);
                lemma_acceptrcvdsound_lpostwaitingonrecoverok(s, s_, c, w, rp, sent, network, network_);
            } else {
                assert(false);
            }
        },
    }
}

/// **Ballots are non-negative, and a replica mid-recovery is at a positive one.**
/// The two halves have to travel together: `LStartRecover` sets `bal` to
/// `bal + N` on a re-attempt, and that is only positive because the old `bal`
/// was already non-negative. Splitting them leaves each unprovable.
///
/// `bal` stays non-negative because every assignment either preserves it, or
/// comes from a guard that already bounds it below by the old value —
/// `ApplyAcceptEnabled` requires `bal <= b`, `ApplyRecoverEnabled` requires
/// `bal < b`. Positivity during recovery matters because `ApplyValidate`, which
/// rewrites `cmd` without touching `abal` or `phase`, can only run there: any
/// invariant about ballot-0 state is out of its reach.
pub open spec fn BalWellFormed(s: LState) -> bool {
    forall|id: LInstanceId|
        #![trigger InstAt(s, id)]
        InstAt(s, id).bal >= 0 && (!(InstAt(s, id).recovery_phase is Start) ==> InstAt(s, id).bal > 0)
}

proof fn lemma_balwellformed_lsubmit(
    s: LState,
    s_: LState,
    c: LConstants,
    v: int,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LSubmit(s, s_, c, v, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = LInstanceId { owner: c.my_id, num: s.next_num };
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lcommitfast(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LCommitFast(s, s_, c, w, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lstartaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LStartAccept(s, s_, c, w, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lcommitslow(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LCommitSlow(s, s_, c, w, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lstartrecover(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LStartRecover(s, s_, c, w, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lrecovercommitted(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LRecoverCommitted(s, s_, c, w, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lrecoveraccepted(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LRecoverAccepted(s, s_, c, w, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lrecovernop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LRecoverNop(s, s_, c, w, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lrecovervalidate(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LRecoverValidate(s, s_, c, w, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lvalidateaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LValidateAccept(s, s_, c, w, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lvalidatenop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LValidateNop(s, s_, c, w, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lvalidatewait(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LValidateWait(s, s_, c, w, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lpostwaitingnop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LPostWaitingNop(s, s_, c, w, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lpostwaitingaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LPostWaitingAccept(s, s_, c, w, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lhandlepreaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LHandlePreAccept(s, s_, c, rp, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = rp.msg->PreAccept_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lrecordpreacceptok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LRecordPreAcceptOK(s, s_, c, rp, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = rp.msg->PreAcceptOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lhandleaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LHandleAccept(s, s_, c, rp, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = rp.msg->Accept_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lrecordacceptok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LRecordAcceptOK(s, s_, c, rp, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = rp.msg->AcceptOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lhandlecommit(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LHandleCommit(s, s_, c, rp, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = rp.msg->Commit_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lhandlerecover(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LHandleRecover(s, s_, c, rp, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = rp.msg->Recover_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lrecordrecoverok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LRecordRecoverOK(s, s_, c, rp, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = rp.msg->RecoverOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lhandlevalidate(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LHandleValidate(s, s_, c, rp, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = rp.msg->Validate_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lrecordvalidateok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LRecordValidateOK(s, s_, c, rp, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = rp.msg->ValidateOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lpostwaitingonwaiting(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId, rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LPostWaitingOnWaiting(s, s_, c, w, rp, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_balwellformed_lpostwaitingonrecoverok(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId, rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent),
    ensures
        BalWellFormed(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).bal >= 0 && (!(InstAt(s_, id).recovery_phase is Start) ==> InstAt(s_, id).bal > 0) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

pub proof fn lemma_balwellformed_step(
    s: LState,
    s_: LState,
    c: LConstants,
    received: Option<LPacket>,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        BalWellFormed(s),
        ReplicaAction(s, s_, c, received, sent),
    ensures
        BalWellFormed(s_),
{
    match received {
        Option::None => {
            if exists|v: int| LSubmit(s, s_, c, v, sent) {
                let v = choose|v: int| LSubmit(s, s_, c, v, sent);
                lemma_balwellformed_lsubmit(s, s_, c, v, sent);
            } else if exists|w: LInstanceId| LCommitFast(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LCommitFast(s, s_, c, w, sent);
                lemma_balwellformed_lcommitfast(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LStartAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LStartAccept(s, s_, c, w, sent);
                lemma_balwellformed_lstartaccept(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LCommitSlow(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LCommitSlow(s, s_, c, w, sent);
                lemma_balwellformed_lcommitslow(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LStartRecover(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LStartRecover(s, s_, c, w, sent);
                lemma_balwellformed_lstartrecover(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverCommitted(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverCommitted(s, s_, c, w, sent);
                lemma_balwellformed_lrecovercommitted(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverAccepted(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverAccepted(s, s_, c, w, sent);
                lemma_balwellformed_lrecoveraccepted(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverNop(s, s_, c, w, sent);
                lemma_balwellformed_lrecovernop(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverValidate(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverValidate(s, s_, c, w, sent);
                lemma_balwellformed_lrecovervalidate(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LValidateAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateAccept(s, s_, c, w, sent);
                lemma_balwellformed_lvalidateaccept(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LValidateNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateNop(s, s_, c, w, sent);
                lemma_balwellformed_lvalidatenop(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LValidateWait(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateWait(s, s_, c, w, sent);
                lemma_balwellformed_lvalidatewait(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LPostWaitingNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LPostWaitingNop(s, s_, c, w, sent);
                lemma_balwellformed_lpostwaitingnop(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LPostWaitingAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LPostWaitingAccept(s, s_, c, w, sent);
                lemma_balwellformed_lpostwaitingaccept(s, s_, c, w, sent);
            } else {
                assert(false);
            }
        },
        Option::Some(rp) => {
            if LHandlePreAccept(s, s_, c, rp, sent) {
                lemma_balwellformed_lhandlepreaccept(s, s_, c, rp, sent);
            } else if LRecordPreAcceptOK(s, s_, c, rp, sent) {
                lemma_balwellformed_lrecordpreacceptok(s, s_, c, rp, sent);
            } else if LHandleAccept(s, s_, c, rp, sent) {
                lemma_balwellformed_lhandleaccept(s, s_, c, rp, sent);
            } else if LRecordAcceptOK(s, s_, c, rp, sent) {
                lemma_balwellformed_lrecordacceptok(s, s_, c, rp, sent);
            } else if LHandleCommit(s, s_, c, rp, sent) {
                lemma_balwellformed_lhandlecommit(s, s_, c, rp, sent);
            } else if LHandleRecover(s, s_, c, rp, sent) {
                lemma_balwellformed_lhandlerecover(s, s_, c, rp, sent);
            } else if LRecordRecoverOK(s, s_, c, rp, sent) {
                lemma_balwellformed_lrecordrecoverok(s, s_, c, rp, sent);
            } else if LHandleValidate(s, s_, c, rp, sent) {
                lemma_balwellformed_lhandlevalidate(s, s_, c, rp, sent);
            } else if LRecordValidateOK(s, s_, c, rp, sent) {
                lemma_balwellformed_lrecordvalidateok(s, s_, c, rp, sent);
            } else if exists|w: LInstanceId| LPostWaitingOnWaiting(s, s_, c, w, rp, sent) {
                let w = choose|w: LInstanceId| LPostWaitingOnWaiting(s, s_, c, w, rp, sent);
                lemma_balwellformed_lpostwaitingonwaiting(s, s_, c, w, rp, sent);
            } else if exists|w: LInstanceId| LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent) {
                let w = choose|w: LInstanceId| LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent);
                lemma_balwellformed_lpostwaitingonrecoverok(s, s_, c, w, rp, sent);
            } else {
                assert(false);
            }
        },
    }
}

/// **An instance nobody has pre-accepted has collected no replies.**
/// `LRecordPreAcceptOK` and `LRecordAcceptOK` both require a phase past
/// `Initial`, and no action ever puts an instance back into `Initial`.
///
/// This is what protects the fast-path accumulators from `PreAcceptedInstance`,
/// which rewrites `init_dep` while carrying `preaccept_agreed` across: it is
/// guarded on `phase is Initial`, where by this invariant there is nothing to
/// carry.
pub open spec fn InitialImpliesNoReplies(s: LState) -> bool {
    forall|id: LInstanceId|
        #![trigger InstAt(s, id)]
        InstAt(s, id).phase is Initial ==> (InstAt(s, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s, id).accept_rcvd =~= Set::<int>::empty())
}

proof fn lemma_initialimpliesnoreplies_lsubmit(
    s: LState,
    s_: LState,
    c: LConstants,
    v: int,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LSubmit(s, s_, c, v, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = LInstanceId { owner: c.my_id, num: s.next_num };
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lcommitfast(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LCommitFast(s, s_, c, w, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lstartaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LStartAccept(s, s_, c, w, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lcommitslow(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LCommitSlow(s, s_, c, w, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lstartrecover(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LStartRecover(s, s_, c, w, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lrecovercommitted(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LRecoverCommitted(s, s_, c, w, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lrecoveraccepted(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LRecoverAccepted(s, s_, c, w, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lrecovernop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LRecoverNop(s, s_, c, w, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lrecovervalidate(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LRecoverValidate(s, s_, c, w, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lvalidateaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LValidateAccept(s, s_, c, w, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lvalidatenop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LValidateNop(s, s_, c, w, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lvalidatewait(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LValidateWait(s, s_, c, w, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lpostwaitingnop(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LPostWaitingNop(s, s_, c, w, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lpostwaitingaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LPostWaitingAccept(s, s_, c, w, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lhandlepreaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LHandlePreAccept(s, s_, c, rp, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = rp.msg->PreAccept_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lrecordpreacceptok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LRecordPreAcceptOK(s, s_, c, rp, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = rp.msg->PreAcceptOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lhandleaccept(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LHandleAccept(s, s_, c, rp, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = rp.msg->Accept_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lrecordacceptok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LRecordAcceptOK(s, s_, c, rp, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = rp.msg->AcceptOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lhandlecommit(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LHandleCommit(s, s_, c, rp, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = rp.msg->Commit_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lhandlerecover(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LHandleRecover(s, s_, c, rp, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = rp.msg->Recover_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lrecordrecoverok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LRecordRecoverOK(s, s_, c, rp, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = rp.msg->RecoverOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lhandlevalidate(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LHandleValidate(s, s_, c, rp, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = rp.msg->Validate_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lrecordvalidateok(
    s: LState,
    s_: LState,
    c: LConstants,
    rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LRecordValidateOK(s, s_, c, rp, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = rp.msg->ValidateOK_id;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lpostwaitingonwaiting(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId, rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LPostWaitingOnWaiting(s, s_, c, w, rp, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

proof fn lemma_initialimpliesnoreplies_lpostwaitingonrecoverok(
    s: LState,
    s_: LState,
    c: LConstants,
    w: LInstanceId, rp: LPacket,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    let idX = w;
    lemma_insert_touches_one(s, s_, idX);
    assert forall|id: LInstanceId| #![trigger InstAt(s_, id)]
        InstAt(s_, id).phase is Initial ==> (InstAt(s_, id).preaccept_rcvd =~= Set::<int>::empty()
            && InstAt(s_, id).preaccept_agreed =~= Set::<int>::empty()
            && InstAt(s_, id).accept_rcvd =~= Set::<int>::empty()) by {
        if id != idX {
            assert(InstAt(s_, id) == InstAt(s, id));
        }
    }
}

pub proof fn lemma_initialimpliesnoreplies_step(
    s: LState,
    s_: LState,
    c: LConstants,
    received: Option<LPacket>,
    sent: Set<LPacket>,
)
    requires
        WellFormedConstants(c),
        InitialImpliesNoReplies(s),
        ReplicaAction(s, s_, c, received, sent),
    ensures
        InitialImpliesNoReplies(s_),
{
    match received {
        Option::None => {
            if exists|v: int| LSubmit(s, s_, c, v, sent) {
                let v = choose|v: int| LSubmit(s, s_, c, v, sent);
                lemma_initialimpliesnoreplies_lsubmit(s, s_, c, v, sent);
            } else if exists|w: LInstanceId| LCommitFast(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LCommitFast(s, s_, c, w, sent);
                lemma_initialimpliesnoreplies_lcommitfast(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LStartAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LStartAccept(s, s_, c, w, sent);
                lemma_initialimpliesnoreplies_lstartaccept(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LCommitSlow(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LCommitSlow(s, s_, c, w, sent);
                lemma_initialimpliesnoreplies_lcommitslow(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LStartRecover(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LStartRecover(s, s_, c, w, sent);
                lemma_initialimpliesnoreplies_lstartrecover(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverCommitted(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverCommitted(s, s_, c, w, sent);
                lemma_initialimpliesnoreplies_lrecovercommitted(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverAccepted(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverAccepted(s, s_, c, w, sent);
                lemma_initialimpliesnoreplies_lrecoveraccepted(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverNop(s, s_, c, w, sent);
                lemma_initialimpliesnoreplies_lrecovernop(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LRecoverValidate(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LRecoverValidate(s, s_, c, w, sent);
                lemma_initialimpliesnoreplies_lrecovervalidate(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LValidateAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateAccept(s, s_, c, w, sent);
                lemma_initialimpliesnoreplies_lvalidateaccept(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LValidateNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateNop(s, s_, c, w, sent);
                lemma_initialimpliesnoreplies_lvalidatenop(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LValidateWait(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LValidateWait(s, s_, c, w, sent);
                lemma_initialimpliesnoreplies_lvalidatewait(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LPostWaitingNop(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LPostWaitingNop(s, s_, c, w, sent);
                lemma_initialimpliesnoreplies_lpostwaitingnop(s, s_, c, w, sent);
            } else if exists|w: LInstanceId| LPostWaitingAccept(s, s_, c, w, sent) {
                let w = choose|w: LInstanceId| LPostWaitingAccept(s, s_, c, w, sent);
                lemma_initialimpliesnoreplies_lpostwaitingaccept(s, s_, c, w, sent);
            } else {
                assert(false);
            }
        },
        Option::Some(rp) => {
            if LHandlePreAccept(s, s_, c, rp, sent) {
                lemma_initialimpliesnoreplies_lhandlepreaccept(s, s_, c, rp, sent);
            } else if LRecordPreAcceptOK(s, s_, c, rp, sent) {
                lemma_initialimpliesnoreplies_lrecordpreacceptok(s, s_, c, rp, sent);
            } else if LHandleAccept(s, s_, c, rp, sent) {
                lemma_initialimpliesnoreplies_lhandleaccept(s, s_, c, rp, sent);
            } else if LRecordAcceptOK(s, s_, c, rp, sent) {
                lemma_initialimpliesnoreplies_lrecordacceptok(s, s_, c, rp, sent);
            } else if LHandleCommit(s, s_, c, rp, sent) {
                lemma_initialimpliesnoreplies_lhandlecommit(s, s_, c, rp, sent);
            } else if LHandleRecover(s, s_, c, rp, sent) {
                lemma_initialimpliesnoreplies_lhandlerecover(s, s_, c, rp, sent);
            } else if LRecordRecoverOK(s, s_, c, rp, sent) {
                lemma_initialimpliesnoreplies_lrecordrecoverok(s, s_, c, rp, sent);
            } else if LHandleValidate(s, s_, c, rp, sent) {
                lemma_initialimpliesnoreplies_lhandlevalidate(s, s_, c, rp, sent);
            } else if LRecordValidateOK(s, s_, c, rp, sent) {
                lemma_initialimpliesnoreplies_lrecordvalidateok(s, s_, c, rp, sent);
            } else if exists|w: LInstanceId| LPostWaitingOnWaiting(s, s_, c, w, rp, sent) {
                let w = choose|w: LInstanceId| LPostWaitingOnWaiting(s, s_, c, w, rp, sent);
                lemma_initialimpliesnoreplies_lpostwaitingonwaiting(s, s_, c, w, rp, sent);
            } else if exists|w: LInstanceId| LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent) {
                let w = choose|w: LInstanceId| LPostWaitingOnRecoverOK(s, s_, c, w, rp, sent);
                lemma_initialimpliesnoreplies_lpostwaitingonrecoverok(s, s_, c, w, rp, sent);
            } else {
                assert(false);
            }
        },
    }
}

} // verus!

/// EPaxos* protocol — the corrected Egalitarian Paxos, single-replica spec.
///
/// Ported action-for-action from `docs/epaxos_reference/EPaxosCommitWithRecovery.tla`
/// (Ryabinin, Gotsman, Sutra, OPODIS 2025). Line references below are to that
/// file. **Not** `src/protocol/EPaxos/`, which models the 2013 protocol whose
/// specification is unsafe; see `types.rs` for that note.
///
/// # The projection, in one paragraph
///
/// The reference is a global spec: `HandlePreAcceptOK` scans `msgs` for a whole
/// quorum and reads their payloads atomically. A tla-rs `LNext` is
/// single-process — the framework delivers one message at a time and
/// `sent_packets` is an output — so each quorum rule becomes **record-then-act**
/// against an accumulator in `LInstanceState`. That admits interleavings the
/// reference does not have, which `TODO.md` 56.3.z states rather than leaving
/// for the refinement proof to discover.
///
/// The reference's 12 actions become **25**. 56.3.z predicted 17 and was wrong
/// twice, both in the same direction — a TLA+ action that branches internally is
/// several actions once the branches need distinct guards:
///
/// - `HandleRecoverOK`'s five-way `IF/ELSE` and `HandleValidateOK`'s three-way
///   become one action per branch, with the guards made mutually exclusive
///   explicitly rather than by fall-through;
/// - `HandlePostWaiting`'s disjuncts 3 and 4 **read `msgs` for a message that is
///   not part of any accumulated quorum** (a peer's `Waiting`, a late
///   `RecoverOK` from outside `Q`). A single-process spec cannot search the
///   network, so both take the packet as a parameter and become actions of
///   their own.
///
/// `sent_packets` is a `Set`, not a `Seq`: the reference's `msgs` is a set,
/// every send here is a broadcast, and this module has no `.automan` so nothing
/// downstream needs an order.
///
/// # The ballot discipline
///
/// Three rules, and the whole 2020 defect is the difference between them:
///
/// | helper | enabled when | writes `bal` | writes `abal` |
/// |---|---|---|---|
/// | `AcceptedInstance` / `ApplyAcceptEnabled` (`.tla:185-192`) | `bal <= b`, and `bal == b ==> phase != Committed` | yes | yes |
/// | `CommittedInstance` / `ApplyCommitEnabled` (`.tla:197-202`) | `bal == b` | no | yes |
/// | `RecoveredInstance` / `ApplyRecoverEnabled` (`.tla:207-209`) | `bal < b` | yes | no |
///
/// Accepting and recovering also **clear the ballot-scoped accumulators**. The
/// reference gets that free by re-filtering `msgs` on the current ballot every
/// time; an accumulator does not, and a quorum assembled across two ballots
/// would be unsound without a syntactic trace of the error.
use crate::protocol::EPaxosStar::types::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

// =========================================================================
// Instance access
// =========================================================================

/// The record the reference gives an instance nobody has touched: `Init`
/// (`.tla:122-140`) makes `[Id -> _]` total, with phase `Initial`, both ballots
/// 0, both payloads `Bottom` and both dependency sets empty.
///
/// Our map is partial — a replica stores only instances it has heard of — so
/// this is how the two are reconciled. `IsSeenId` remains the way to ask
/// whether the replica has actually heard of one.
pub open spec fn InitialInstance() -> LInstanceState {
    LInstanceState {
        phase: LPhase::Initial,
        bal: 0,
        abal: 0,
        init_cmd: LCmd::Bottom,
        cmd: LCmd::Bottom,
        init_dep: Set::<LInstanceId>::empty(),
        dep: Set::<LInstanceId>::empty(),
        preaccept_rcvd: Set::<int>::empty(),
        preaccept_agreed: Set::<int>::empty(),
        preaccept_dep_union: Set::<LInstanceId>::empty(),
        accept_rcvd: Set::<int>::empty(),
        recover_replies: Map::<int, LRecoverInfo>::empty(),
        validate_rcvd: Set::<int>::empty(),
        recovered: 0,
        recovery_phase: LRecoveryPhase::Start,
        qvar: Set::<int>::empty(),
        cvar: LCmd::Bottom,
        dvar: Set::<LInstanceId>::empty(),
        ivar: Set::<LInvalidator>::empty(),
        cardinality_rmax: 0,
        recovery_attempt_bal: 0,
    }
}

/// This replica's view of `id`, totalized as the reference has it.
pub open spec fn InstAt(s: LState, id: LInstanceId) -> LInstanceState {
    if s.instances.dom().contains(id) {
        s.instances[id]
    } else {
        InitialInstance()
    }
}

/// Frame: the step touched `id` and nothing else.
pub open spec fn OnlyInstanceChanged(s: LState, s_: LState, id: LInstanceId) -> bool {
    &&& s_.instances.dom() =~= s.instances.dom().insert(id)
    &&& forall|j: LInstanceId|
        j != id && s.instances.dom().contains(j) ==> (#[trigger] s_.instances[j])
            == s.instances[j]
}

// =========================================================================
// Packets
// =========================================================================

pub open spec fn SelfPacket(c: LConstants, msg: LEPaxosStarMessage) -> LPacket {
    LPacket { src: c.my_id, dst: c.my_id, msg }
}

pub open spec fn ReplyTo(c: LConstants, pkt: LPacket, msg: LEPaxosStarMessage) -> Set<LPacket> {
    Set::<LPacket>::empty().insert(LPacket { src: c.my_id, dst: pkt.src, msg })
}

/// Send to every other replica. The reference writes
/// `{ Msg(p, q, ..) : q \in Proc \ {p} }` (`.tla:245`).
pub open spec fn Broadcast(c: LConstants, msg: LEPaxosStarMessage) -> Set<LPacket> {
    c.procs.remove(c.my_id).map(|q: int| LPacket { src: c.my_id, dst: q, msg })
}

/// Send to a chosen subset, minus self — the recovery path addresses `Q`
/// rather than everyone (`.tla:424`).
pub open spec fn BroadcastTo(
    c: LConstants,
    targets: Set<int>,
    msg: LEPaxosStarMessage,
) -> Set<LPacket> {
    targets.remove(c.my_id).map(|q: int| LPacket { src: c.my_id, dst: q, msg })
}

// =========================================================================
// The three Apply rules (`.tla:185-209`) — see the module header's table
// =========================================================================

/// `ApplyPreAccept` (`.tla:172-180`). A fresh pre-accepted record: both ballots
/// stay 0, `init_cmd` and `cmd` are the payload, `init_dep` is what the
/// coordinator proposed and `dep` is that plus this replica's own conflicts.
pub open spec fn PreAcceptedInstance(
    prev: LInstanceState,
    cmd: LCmd,
    init_dep: Set<LInstanceId>,
    dep: Set<LInstanceId>,
) -> LInstanceState {
    LInstanceState { phase: LPhase::PreAccepted, init_cmd: cmd, cmd, init_dep, dep, ..prev }
}

pub open spec fn ApplyPreAcceptEnabled(inst: LInstanceState) -> bool {
    &&& inst.bal == 0
    &&& inst.phase is Initial
}

/// `ApplyAccept` (`.tla:185-192`). Moves **both** ballots, and clears the
/// ballot-scoped accumulators because the reference re-filters `msgs` on the
/// new ballot from here on.
pub open spec fn AcceptedInstance(
    prev: LInstanceState,
    b: int,
    cmd: LCmd,
    dep: Set<LInstanceId>,
) -> LInstanceState {
    LInstanceState {
        phase: LPhase::Accepted,
        bal: b,
        abal: b,
        cmd,
        dep,
        accept_rcvd: Set::<int>::empty(),
        recover_replies: Map::<int, LRecoverInfo>::empty(),
        validate_rcvd: Set::<int>::empty(),
        ..prev
    }
}

pub open spec fn ApplyAcceptEnabled(inst: LInstanceState, b: int) -> bool {
    &&& inst.bal <= b
    &&& (inst.bal == b ==> !(inst.phase is Committed))
}

/// `ApplyCommit` (`.tla:197-202`). Moves `abal` only, and **requires** `bal`
/// to already be `b` rather than assigning it.
pub open spec fn CommittedInstance(
    prev: LInstanceState,
    b: int,
    cmd: LCmd,
    dep: Set<LInstanceId>,
) -> LInstanceState {
    LInstanceState { phase: LPhase::Committed, abal: b, cmd, dep, ..prev }
}

pub open spec fn ApplyCommitEnabled(inst: LInstanceState, b: int) -> bool {
    inst.bal == b
}

/// `ApplyRecover` (`.tla:207-209`). Moves `bal` alone — a promise is not an
/// acceptance, and conflating the two is the 2020 defect.
pub open spec fn RecoveredInstance(prev: LInstanceState, b: int) -> LInstanceState {
    LInstanceState {
        bal: b,
        accept_rcvd: Set::<int>::empty(),
        recover_replies: Map::<int, LRecoverInfo>::empty(),
        validate_rcvd: Set::<int>::empty(),
        ..prev
    }
}

pub open spec fn ApplyRecoverEnabled(inst: LInstanceState, b: int) -> bool {
    inst.bal < b
}

// =========================================================================
// Initial state (`.tla:122-140`)
// =========================================================================

pub open spec fn LInit(s: LState, c: LConstants) -> bool {
    &&& WellFormedConstants(c)
    &&& s.instances =~= Map::<LInstanceId, LInstanceState>::empty()
    &&& s.next_num == 1
}

// =========================================================================
// Commit path
// =========================================================================

/// `Submit` (`.tla:238-247`). A client offers a payload to this replica, which
/// becomes the initial coordinator for an instance **of its own** — the
/// identifier carries `owner == my_id`, which is what replaces the reference's
/// global `initCoord`, and `next_num` replaces its global `submitted`.
pub open spec fn LSubmit(
    s: LState,
    s_: LState,
    c: LConstants,
    value: int,
    sent: Set<LPacket>,
) -> bool {
    let id = LInstanceId { owner: c.my_id, num: s.next_num };
    let cmd = LCmd::Payload { value };
    let d0 = ConflictingIds(c, s, cmd);
    &&& s.next_num <= c.max_num
    &&& !s.instances.dom().contains(id)
    &&& ApplyPreAcceptEnabled(InstAt(s, id))
    &&& s_.next_num == s.next_num + 1
    &&& s_.instances == s.instances.insert(id, PreAcceptedInstance(InstAt(s, id), cmd, d0, d0))
    &&& sent =~= Broadcast(c, LEPaxosStarMessage::PreAccept { id, c: cmd, d: d0 }).insert(
        SelfPacket(c, LEPaxosStarMessage::PreAcceptOK { id, dq: d0 }),
    )
}

/// `HandlePreAccept` (`.tla:252-258`). The dependency set is **computed from
/// this replica's own state** — `m.D \cup ConflictingIds(self, m.c)` — which is
/// the step `src/protocol/EPaxos/`'s `LSendPreAcceptOk` replaces with a free
/// boolean parameter and no state write at all.
pub open spec fn LHandlePreAccept(
    s: LState,
    s_: LState,
    c: LConstants,
    pkt: LPacket,
    sent: Set<LPacket>,
) -> bool {
    &&& pkt.dst == c.my_id
    &&& match pkt.msg {
        LEPaxosStarMessage::PreAccept { id, c: mcmd, d: mdep } => {
            let dfinal = mdep.union(ConflictingIds(c, s, mcmd));
            &&& ApplyPreAcceptEnabled(InstAt(s, id))
            &&& s_.next_num == s.next_num
            &&& s_.instances == s.instances.insert(
                id,
                PreAcceptedInstance(InstAt(s, id), mcmd, mdep, dfinal),
            )
            &&& sent =~= ReplyTo(c, pkt, LEPaxosStarMessage::PreAcceptOK { id, dq: dfinal })
        },
        _ => false,
    }
}

/// Record one `PreAcceptOK` (split out of `.tla:263-287`; see the header).
///
/// Three accumulators move at once because the reference's one atomic read uses
/// all three: the responder count against `N-F`, the count of responders whose
/// `Dq` matched the coordinator's `init_dep` against `N-E`, and the union of
/// every `Dq` for the slow path.
pub open spec fn LRecordPreAcceptOK(
    s: LState,
    s_: LState,
    c: LConstants,
    pkt: LPacket,
    sent: Set<LPacket>,
) -> bool {
    &&& pkt.dst == c.my_id
    &&& match pkt.msg {
        LEPaxosStarMessage::PreAcceptOK { id, dq } => {
            let inst = InstAt(s, id);
            &&& s.instances.dom().contains(id)
            &&& inst.bal == 0
            &&& inst.phase is PreAccepted
            &&& !inst.preaccept_rcvd.contains(pkt.src)
            &&& s_.next_num == s.next_num
            &&& s_.instances == s.instances.insert(
                id,
                LInstanceState {
                    preaccept_rcvd: inst.preaccept_rcvd.insert(pkt.src),
                    preaccept_agreed: if dq =~= inst.init_dep {
                        inst.preaccept_agreed.insert(pkt.src)
                    } else {
                        inst.preaccept_agreed
                    },
                    preaccept_dep_union: inst.preaccept_dep_union.union(dq),
                    ..inst
                },
            )
            &&& sent =~= Set::<LPacket>::empty()
        },
        _ => false,
    }
}

/// The fast branch of `HandlePreAcceptOK` (`.tla:277-280`).
///
/// **Two thresholds in one action**, which is the whole point of the fast path:
/// a slow quorum must have answered *and* a fast quorum's worth of them must
/// have agreed with what the coordinator proposed. Ballot 0 only.
pub open spec fn LCommitFast(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    &&& s.instances.dom().contains(id)
    &&& inst.bal == 0
    &&& inst.phase is PreAccepted
    &&& IsQuorumSized(c, inst.preaccept_rcvd)
    &&& IsFastQuorumSized(c, inst.preaccept_agreed)
    &&& ApplyCommitEnabled(inst, 0)
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(id, CommittedInstance(inst, 0, inst.cmd, inst.init_dep))
    &&& sent =~= Broadcast(
        c,
        LEPaxosStarMessage::Commit { id, b: 0, c: inst.cmd, d: inst.init_dep },
    )
}

/// The slow branch of `HandlePreAcceptOK` (`.tla:281-286`): the replies did not
/// all agree, so the coordinator runs an explicit Accept round on the **union**
/// of every reported dependency set (`.tla:282`).
pub open spec fn LStartAccept(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    let dfinal = inst.preaccept_dep_union;
    &&& s.instances.dom().contains(id)
    &&& inst.bal == 0
    &&& inst.phase is PreAccepted
    &&& IsQuorumSized(c, inst.preaccept_rcvd)
    &&& !IsFastQuorumSized(c, inst.preaccept_agreed)
    &&& ApplyAcceptEnabled(inst, 0)
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(id, AcceptedInstance(inst, 0, inst.cmd, dfinal))
    &&& sent =~= Broadcast(
        c,
        LEPaxosStarMessage::Accept { id, b: 0, c: inst.cmd, d: dfinal },
    ).insert(SelfPacket(c, LEPaxosStarMessage::AcceptOK { id, b: 0 }))
}

/// `HandleAccept` (`.tla:292-296`).
pub open spec fn LHandleAccept(
    s: LState,
    s_: LState,
    c: LConstants,
    pkt: LPacket,
    sent: Set<LPacket>,
) -> bool {
    &&& pkt.dst == c.my_id
    &&& match pkt.msg {
        LEPaxosStarMessage::Accept { id, b, c: mcmd, d: mdep } => {
            &&& ApplyAcceptEnabled(InstAt(s, id), b)
            &&& s_.next_num == s.next_num
            &&& s_.instances == s.instances.insert(
                id,
                AcceptedInstance(InstAt(s, id), b, mcmd, mdep),
            )
            &&& sent =~= ReplyTo(c, pkt, LEPaxosStarMessage::AcceptOK { id, b })
        },
        _ => false,
    }
}

/// Record one `AcceptOK` (split out of `.tla:301-314`).
///
/// The ballot guard is not decoration: the reference filters replies on
/// `k.body.b = bal[p][id]`, so a reply from a superseded ballot must not count
/// toward the current quorum.
pub open spec fn LRecordAcceptOK(
    s: LState,
    s_: LState,
    c: LConstants,
    pkt: LPacket,
    sent: Set<LPacket>,
) -> bool {
    &&& pkt.dst == c.my_id
    &&& match pkt.msg {
        LEPaxosStarMessage::AcceptOK { id, b } => {
            let inst = InstAt(s, id);
            &&& s.instances.dom().contains(id)
            &&& inst.phase is Accepted
            &&& b == inst.bal
            &&& !inst.accept_rcvd.contains(pkt.src)
            &&& s_.next_num == s.next_num
            &&& s_.instances == s.instances.insert(
                id,
                LInstanceState { accept_rcvd: inst.accept_rcvd.insert(pkt.src), ..inst },
            )
            &&& sent =~= Set::<LPacket>::empty()
        },
        _ => false,
    }
}

/// `HandleAcceptOK`'s commit (`.tla:311-313`).
pub open spec fn LCommitSlow(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    &&& s.instances.dom().contains(id)
    &&& inst.phase is Accepted
    &&& IsQuorumSized(c, inst.accept_rcvd)
    &&& ApplyCommitEnabled(inst, inst.bal)
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(
        id,
        CommittedInstance(inst, inst.bal, inst.cmd, inst.dep),
    )
    &&& sent =~= Broadcast(
        c,
        LEPaxosStarMessage::Commit { id, b: inst.bal, c: inst.cmd, d: inst.dep },
    )
}

/// `HandleCommit` (`.tla:319-323`). Note the reference does **not** move `bal`
/// here: `ApplyCommit` requires `bal[p][id] = b`, so a replica that has already
/// promised a higher ballot simply does not take this step.
pub open spec fn LHandleCommit(
    s: LState,
    s_: LState,
    c: LConstants,
    pkt: LPacket,
    sent: Set<LPacket>,
) -> bool {
    &&& pkt.dst == c.my_id
    &&& match pkt.msg {
        LEPaxosStarMessage::Commit { id, b, c: mcmd, d: mdep } => {
            &&& ApplyCommitEnabled(InstAt(s, id), b)
            &&& s_.next_num == s.next_num
            &&& s_.instances == s.instances.insert(
                id,
                CommittedInstance(InstAt(s, id), b, mcmd, mdep),
            )
            &&& sent =~= Set::<LPacket>::empty()
        },
        _ => false,
    }
}

// =========================================================================
// Recovery — helpers
// =========================================================================

/// The quorum that answered this recovery attempt.
pub open spec fn RecoverQuorum(inst: LInstanceState) -> Set<int> {
    inst.recover_replies.dom()
}

/// `bmax == CHOOSE val \in Abals : \A val2 \in Abals : val >= val2` (`.tla:372`).
///
/// Given as a predicate and then `choose`n, rather than folded: a maximum over a
/// set has no vstd fold that keeps the witness, and the reference's own
/// definition is a `CHOOSE` over exactly this property.
pub open spec fn IsMaxAbal(inst: LInstanceState, b: int) -> bool {
    &&& exists|p: int|
        (#[trigger] inst.recover_replies.dom().contains(p)) && inst.recover_replies[p].abal == b
    &&& forall|q: int|
        (#[trigger] inst.recover_replies.dom().contains(q)) ==> inst.recover_replies[q].abal <= b
}

pub open spec fn MaxAbal(inst: LInstanceState) -> int {
    choose|b: int| IsMaxAbal(inst, b)
}

/// `U == { k \in quorumOfMessages : k.body.abalq = bmax }` (`.tla:373`).
///
/// **Selecting by maximum `abal` is exactly what one ballot variable makes
/// wrong**, and is the reason this module exists.
pub open spec fn RecoverU(inst: LInstanceState) -> Set<int> {
    inst.recover_replies.dom().filter(|p: int| inst.recover_replies[p].abal == MaxAbal(inst))
}

/// `Rmax == { n : phaseq = PreAccepted /\ depq = initDepq }` (`.tla:401-408`) —
/// quorum members that pre-accepted and whose dependencies were *unchanged*
/// from what the coordinator proposed.
pub open spec fn RecoverRmax(inst: LInstanceState) -> Set<int> {
    inst.recover_replies.dom().filter(
        |p: int|
            {
                &&& inst.recover_replies[p].phase is PreAccepted
                &&& inst.recover_replies[p].dep =~= inst.recover_replies[p].init_dep
            },
    )
}

pub open spec fn HasPhaseIn(inst: LInstanceState, sel: Set<int>, want_committed: bool) -> bool {
    exists|p: int|
        (#[trigger] sel.contains(p)) && (if want_committed {
            inst.recover_replies[p].phase is Committed
        } else {
            inst.recover_replies[p].phase is Accepted
        })
}

pub open spec fn WitnessIn(inst: LInstanceState, sel: Set<int>, want_committed: bool) -> int {
    choose|p: int|
        (#[trigger] sel.contains(p)) && (if want_committed {
            inst.recover_replies[p].phase is Committed
        } else {
            inst.recover_replies[p].phase is Accepted
        })
}

/// `ComputeI` (`.tla:220-227`) — commands that could invalidate committing
/// `(cmd, d)` for `id`: outside `d`, conflicting with `cmd`, and not carrying
/// `id` among their own dependencies.
///
/// Built by filtering the instance map's domain. Instances this replica has
/// never heard of cannot qualify: the non-committed branch requires
/// `init_cmd != Bottom`, and an untouched record has `Bottom`.
pub open spec fn ComputeI(
    c: LConstants,
    s: LState,
    id: LInstanceId,
    cmd: LCmd,
    d: Set<LInstanceId>,
) -> Set<LInvalidator> {
    s.instances.dom().filter(
        |id3: LInstanceId|
            {
                &&& id3 != id
                &&& !d.contains(id3)
                &&& (InstAt(s, id3).phase is Committed ==> {
                    &&& !(InstAt(s, id3).cmd is Nop)
                    &&& !InstAt(s, id3).dep.contains(id)
                    &&& Conflicts(c, cmd, InstAt(s, id3).cmd)
                })
                &&& (!(InstAt(s, id3).phase is Committed) ==> {
                    &&& !(InstAt(s, id3).init_cmd is Bottom)
                    &&& !InstAt(s, id3).init_dep.contains(id)
                    &&& Conflicts(c, cmd, InstAt(s, id3).init_cmd)
                })
            },
    ).map(|id3: LInstanceId| LInvalidator { id: id3, phase: InstAt(s, id3).phase })
}

/// `ApplyValidate` (`.tla:214-218`). Note it rewrites `cmd`, `init_cmd` and
/// `init_dep` but **not** `dep`, and requires the ballot to match.
pub open spec fn ValidatedInstance(
    prev: LInstanceState,
    cmd: LCmd,
    d: Set<LInstanceId>,
) -> LInstanceState {
    LInstanceState { cmd, init_cmd: cmd, init_dep: d, ..prev }
}

// =========================================================================
// Recovery — actions
// =========================================================================

/// `StartRecover` (`.tla:328-340`).
///
/// The ballot is `k*N + p`, so **ballots are globally unique per replica** —
/// two replicas can never drive the same ballot. `src/protocol/EPaxos/`'s
/// `LRecover` takes the new ballot as a free parameter bounded only by
/// `> s.ballot`, which permits exactly that collision.
pub open spec fn LStartRecover(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    let b = if inst.bal == 0 {
        c.my_id
    } else {
        inst.bal + N(c)
    };
    &&& inst.recovered < c.max_recovery_attempts
    &&& IsSeenId(s, id)
    &&& ApplyRecoverEnabled(inst, b)
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(
        id,
        LInstanceState {
            recovered: inst.recovered + 1,
            recovery_phase: LRecoveryPhase::RecoverOK,
            ..RecoveredInstance(inst, b)
        },
    )
    &&& sent =~= Broadcast(c, LEPaxosStarMessage::Recover { id, b }).insert(
        SelfPacket(
            c,
            LEPaxosStarMessage::RecoverOK {
                id,
                b,
                abalq: inst.abal,
                cq: inst.cmd,
                depq: inst.dep,
                init_depq: inst.init_dep,
                phaseq: inst.phase,
            },
        ),
    )
}

/// `HandleRecover` (`.tla:345-354`). A promise: `bal` moves, `abal` does not,
/// and the reply carries `abal` — the field that makes recovery decidable.
pub open spec fn LHandleRecover(
    s: LState,
    s_: LState,
    c: LConstants,
    pkt: LPacket,
    sent: Set<LPacket>,
) -> bool {
    &&& pkt.dst == c.my_id
    &&& match pkt.msg {
        LEPaxosStarMessage::Recover { id, b } => {
            let inst = InstAt(s, id);
            &&& ApplyRecoverEnabled(inst, b)
            &&& s_.next_num == s.next_num
            &&& s_.instances == s.instances.insert(id, RecoveredInstance(inst, b))
            &&& sent =~= ReplyTo(
                c,
                pkt,
                LEPaxosStarMessage::RecoverOK {
                    id,
                    b,
                    abalq: inst.abal,
                    cq: inst.cmd,
                    depq: inst.dep,
                    init_depq: inst.init_dep,
                    phaseq: inst.phase,
                },
            )
        },
        _ => false,
    }
}

/// Record one `RecoverOK` (split out of `.tla:359-432`).
pub open spec fn LRecordRecoverOK(
    s: LState,
    s_: LState,
    c: LConstants,
    pkt: LPacket,
    sent: Set<LPacket>,
) -> bool {
    &&& pkt.dst == c.my_id
    &&& match pkt.msg {
        LEPaxosStarMessage::RecoverOK { id, b, abalq, cq, depq, init_depq, phaseq } => {
            let inst = InstAt(s, id);
            &&& s.instances.dom().contains(id)
            &&& inst.recovery_phase is RecoverOK
            &&& b == inst.bal
            &&& !inst.recover_replies.dom().contains(pkt.src)
            &&& s_.next_num == s.next_num
            &&& s_.instances == s.instances.insert(
                id,
                LInstanceState {
                    recover_replies: inst.recover_replies.insert(
                        pkt.src,
                        LRecoverInfo {
                            abal: abalq,
                            cmd: cq,
                            dep: depq,
                            init_dep: init_depq,
                            phase: phaseq,
                        },
                    ),
                    ..inst
                },
            )
            &&& sent =~= Set::<LPacket>::empty()
        },
        _ => false,
    }
}

/// `HandleRecoverOK` branch 1 (`.tla:375-383`): someone at the highest `abal`
/// had already committed, so adopt that decision.
pub open spec fn LRecoverCommitted(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    let w = WitnessIn(inst, RecoverU(inst), true);
    let info = inst.recover_replies[w];
    &&& RecoverOKQuorumReady(c, s, id)
    &&& HasPhaseIn(inst, RecoverU(inst), true)
    &&& ApplyCommitEnabled(inst, inst.bal)
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(
        id,
        LInstanceState {
            recovery_phase: LRecoveryPhase::Start,
            ..CommittedInstance(inst, inst.bal, info.cmd, info.dep)
        },
    )
    &&& sent =~= Broadcast(
        c,
        LEPaxosStarMessage::Commit { id, b: inst.bal, c: info.cmd, d: info.dep },
    )
}

/// The precondition every `HandleRecoverOK` branch shares (`.tla:360-369`).
pub open spec fn RecoverOKQuorumReady(c: LConstants, s: LState, id: LInstanceId) -> bool {
    let inst = InstAt(s, id);
    &&& s.instances.dom().contains(id)
    &&& inst.recovery_phase is RecoverOK
    &&& IsQuorumSized(c, RecoverQuorum(inst))
}

/// `HandleRecoverOK` branch 2 (`.tla:384-393`): nobody committed, but someone
/// at the highest `abal` had accepted, so re-drive that value at our ballot.
pub open spec fn LRecoverAccepted(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    let w = WitnessIn(inst, RecoverU(inst), false);
    let info = inst.recover_replies[w];
    &&& RecoverOKQuorumReady(c, s, id)
    &&& !HasPhaseIn(inst, RecoverU(inst), true)
    &&& HasPhaseIn(inst, RecoverU(inst), false)
    &&& ApplyAcceptEnabled(inst, inst.bal)
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(
        id,
        LInstanceState {
            recovery_phase: LRecoveryPhase::Start,
            ..AcceptedInstance(inst, inst.bal, info.cmd, info.dep)
        },
    )
    &&& sent =~= Broadcast(
        c,
        LEPaxosStarMessage::Accept { id, b: inst.bal, c: info.cmd, d: info.dep },
    ).insert(SelfPacket(c, LEPaxosStarMessage::AcceptOK { id, b: inst.bal }))
}

/// `HandleRecoverOK` branches 3 and 5 (`.tla:394-400`, `:427-431`): take `Nop`.
///
/// Branch 3 fires when the initial coordinator is itself in the quorum — it
/// would have told us if it had got anywhere — and branch 5 when too few
/// members pre-accepted with unchanged dependencies for the fast path to have
/// been possible. `id.owner` is the reference's `initCoord[id]`.
pub open spec fn LRecoverNop(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    &&& RecoverOKQuorumReady(c, s, id)
    &&& !HasPhaseIn(inst, RecoverU(inst), true)
    &&& !HasPhaseIn(inst, RecoverU(inst), false)
    &&& {
        ||| RecoverQuorum(inst).contains(id.owner)
        ||| RecoverRmax(inst).len() + c.e < RecoverQuorum(inst).len()
    }
    &&& ApplyAcceptEnabled(inst, inst.bal)
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(
        id,
        LInstanceState {
            recovery_phase: LRecoveryPhase::Start,
            ..AcceptedInstance(inst, inst.bal, LCmd::Nop, Set::<LInstanceId>::empty())
        },
    )
    &&& sent =~= Broadcast(
        c,
        LEPaxosStarMessage::Accept {
            id,
            b: inst.bal,
            c: LCmd::Nop,
            d: Set::<LInstanceId>::empty(),
        },
    ).insert(SelfPacket(c, LEPaxosStarMessage::AcceptOK { id, b: inst.bal }))
}

/// `HandleRecoverOK` branch 4 (`.tla:401-426`) — the paper's contribution.
///
/// Enough of the quorum pre-accepted with dependencies unchanged that the fast
/// path *might* have committed, so instead of guessing, the coordinator probes:
/// it fixes `(c, D)`, records `Q`/`|Rmax|`/the ballot, and asks the quorum
/// whether committing that would contradict anything they have seen. This
/// replaces the original protocol's ambiguous "enough pre-accepts, go ahead".
pub open spec fn LRecoverValidate(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    let q = RecoverQuorum(inst);
    let w = RecoverRmax(inst).choose();
    let rc = inst.recover_replies[w].cmd;
    let rd = inst.recover_replies[w].dep;
    &&& RecoverOKQuorumReady(c, s, id)
    &&& !HasPhaseIn(inst, RecoverU(inst), true)
    &&& !HasPhaseIn(inst, RecoverU(inst), false)
    &&& !q.contains(id.owner)
    &&& RecoverRmax(inst).len() + c.e >= q.len()
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(
        id,
        LInstanceState {
            qvar: q,
            cvar: rc,
            dvar: rd,
            cardinality_rmax: RecoverRmax(inst).len() as int,
            recovery_attempt_bal: inst.bal,
            recovery_phase: LRecoveryPhase::ValidateOK,
            validate_rcvd: Set::<int>::empty(),
            ivar: Set::<LInvalidator>::empty(),
            ..ValidatedInstance(inst, rc, rd)
        },
    )
    &&& sent =~= BroadcastTo(
        c,
        q,
        LEPaxosStarMessage::Validate { id, b: inst.bal, c: rc, d: rd },
    ).insert(
        SelfPacket(
            c,
            LEPaxosStarMessage::ValidateOK { id, b: inst.bal, iq: ComputeI(c, s, id, rc, rd) },
        ),
    )
}

// =========================================================================
// Validation sub-protocol (`.tla:437-548`)
// =========================================================================

/// `HandleValidate` (`.tla:437-450`). A quorum member is asked whether
/// committing `(c, D)` for `id` would contradict anything it has seen, and
/// answers with its own `ComputeI`.
pub open spec fn LHandleValidate(
    s: LState,
    s_: LState,
    c: LConstants,
    pkt: LPacket,
    sent: Set<LPacket>,
) -> bool {
    &&& pkt.dst == c.my_id
    &&& match pkt.msg {
        LEPaxosStarMessage::Validate { id, b, c: mcmd, d: mdep } => {
            let inst = InstAt(s, id);
            &&& inst.bal == b
            &&& s_.next_num == s.next_num
            &&& s_.instances == s.instances.insert(id, ValidatedInstance(inst, mcmd, mdep))
            &&& sent =~= ReplyTo(
                c,
                pkt,
                LEPaxosStarMessage::ValidateOK { id, b, iq: ComputeI(c, s, id, mcmd, mdep) },
            )
        },
        _ => false,
    }
}

/// Record one `ValidateOK` (split out of `.tla:455-490`). Both halves of the
/// reference's read are accumulated: the responder set, which must end up
/// exactly `Q`, and the **union** of the reported invalidator sets.
pub open spec fn LRecordValidateOK(
    s: LState,
    s_: LState,
    c: LConstants,
    pkt: LPacket,
    sent: Set<LPacket>,
) -> bool {
    &&& pkt.dst == c.my_id
    &&& match pkt.msg {
        LEPaxosStarMessage::ValidateOK { id, b, iq } => {
            let inst = InstAt(s, id);
            &&& s.instances.dom().contains(id)
            &&& inst.recovery_phase is ValidateOK
            &&& b == inst.bal
            &&& !inst.validate_rcvd.contains(pkt.src)
            &&& s_.next_num == s.next_num
            &&& s_.instances == s.instances.insert(
                id,
                LInstanceState {
                    validate_rcvd: inst.validate_rcvd.insert(pkt.src),
                    ivar: inst.ivar.union(iq),
                    ..inst
                },
            )
            &&& sent =~= Set::<LPacket>::empty()
        },
        _ => false,
    }
}

/// The precondition the three `HandleValidateOK` branches share (`.tla:461-470`).
/// The reference requires `{n.from : n \in replies} = Q` — the *exact* set, not
/// a quorum-sized subset of it.
pub open spec fn ValidateOKReady(c: LConstants, s: LState, id: LInstanceId) -> bool {
    let inst = InstAt(s, id);
    &&& s.instances.dom().contains(id)
    &&& inst.recovery_phase is ValidateOK
    &&& inst.validate_rcvd =~= inst.qvar
}

/// `HandleValidateOK` branch 1 (`.tla:471-476`): nothing objected, so the value
/// the recovery attempt was carrying is safe to accept.
pub open spec fn LValidateAccept(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    &&& ValidateOKReady(c, s, id)
    &&& inst.ivar =~= Set::<LInvalidator>::empty()
    &&& ApplyAcceptEnabled(inst, inst.bal)
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(
        id,
        LInstanceState {
            recovery_phase: LRecoveryPhase::Start,
            ..AcceptedInstance(inst, inst.bal, inst.cvar, inst.dvar)
        },
    )
    &&& sent =~= Broadcast(
        c,
        LEPaxosStarMessage::Accept { id, b: inst.bal, c: inst.cvar, d: inst.dvar },
    ).insert(SelfPacket(c, LEPaxosStarMessage::AcceptOK { id, b: inst.bal }))
}

/// `HandleValidateOK` branch 2 (`.tla:477-484`): something objected in a way
/// that settles it — either an objector has already committed, or the fast
/// quorum was exactly at its bound and an objector's own coordinator is outside
/// `Q`, so we cannot rule out that it committed something else. Take `Nop`.
pub open spec fn LValidateNop(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    &&& ValidateOKReady(c, s, id)
    &&& !(inst.ivar =~= Set::<LInvalidator>::empty())
    &&& {
        ||| exists|x: LInvalidator| (#[trigger] inst.ivar.contains(x)) && x.phase is Committed
        ||| (inst.cardinality_rmax + c.e == inst.qvar.len() && exists|x: LInvalidator|
            (#[trigger] inst.ivar.contains(x)) && !inst.qvar.contains(x.id.owner))
    }
    &&& ApplyAcceptEnabled(inst, inst.bal)
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(
        id,
        LInstanceState {
            recovery_phase: LRecoveryPhase::Start,
            ..AcceptedInstance(inst, inst.bal, LCmd::Nop, Set::<LInstanceId>::empty())
        },
    )
    &&& sent =~= Broadcast(
        c,
        LEPaxosStarMessage::Accept {
            id,
            b: inst.bal,
            c: LCmd::Nop,
            d: Set::<LInstanceId>::empty(),
        },
    ).insert(SelfPacket(c, LEPaxosStarMessage::AcceptOK { id, b: inst.bal }))
}

/// `HandleValidateOK` branch 3 (`.tla:485-489`): objections exist but none of
/// them settles anything yet, so announce that we are blocked and wait. The
/// `Waiting` broadcast carries `|Rmax|`, which is what lets a peer detect the
/// circular case in `LPostWaitingOnWaiting`.
pub open spec fn LValidateWait(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    &&& ValidateOKReady(c, s, id)
    &&& !(inst.ivar =~= Set::<LInvalidator>::empty())
    &&& !(exists|x: LInvalidator| (#[trigger] inst.ivar.contains(x)) && x.phase is Committed)
    &&& !(inst.cardinality_rmax + c.e == inst.qvar.len() && exists|x: LInvalidator|
        (#[trigger] inst.ivar.contains(x)) && !inst.qvar.contains(x.id.owner))
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(
        id,
        LInstanceState { recovery_phase: LRecoveryPhase::PostWaiting, ..inst },
    )
    &&& sent =~= Broadcast(
        c,
        LEPaxosStarMessage::Waiting { id, k: inst.cardinality_rmax },
    )
}

/// The precondition the four `HandlePostWaiting` branches share
/// (`.tla:496-497`). The ballot check is what stops a superseded recovery
/// attempt from acting on a conclusion it drew before being overtaken.
pub open spec fn PostWaitingReady(c: LConstants, s: LState, id: LInstanceId) -> bool {
    let inst = InstAt(s, id);
    &&& s.instances.dom().contains(id)
    &&& inst.recovery_phase is PostWaiting
    &&& inst.recovery_attempt_bal == inst.bal
}

/// `HandlePostWaiting` disjunct 1 (`.tla:504-509`): an objector has committed a
/// real command that does **not** list `id` as a dependency, so committing `id`
/// now would break `Visibility`. Take `Nop`.
pub open spec fn LPostWaitingNop(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    &&& PostWaitingReady(c, s, id)
    &&& exists|x: LInvalidator|
        (#[trigger] inst.ivar.contains(x)) && {
            &&& InstAt(s, x.id).phase is Committed
            &&& !(InstAt(s, x.id).cmd is Nop)
            &&& !InstAt(s, x.id).dep.contains(id)
        }
    &&& ApplyAcceptEnabled(inst, inst.bal)
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(
        id,
        LInstanceState {
            recovery_phase: LRecoveryPhase::Start,
            ..AcceptedInstance(inst, inst.bal, LCmd::Nop, Set::<LInstanceId>::empty())
        },
    )
    &&& sent =~= Broadcast(
        c,
        LEPaxosStarMessage::Accept {
            id,
            b: inst.bal,
            c: LCmd::Nop,
            d: Set::<LInstanceId>::empty(),
        },
    ).insert(SelfPacket(c, LEPaxosStarMessage::AcceptOK { id, b: inst.bal }))
}

/// `HandlePostWaiting` disjunct 2 (`.tla:510-515`): every objector has settled
/// in a way that leaves `id` visible to it, so the carried value is safe.
pub open spec fn LPostWaitingAccept(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    &&& PostWaitingReady(c, s, id)
    &&& forall|x: LInvalidator|
        (#[trigger] inst.ivar.contains(x)) ==> {
            &&& InstAt(s, x.id).phase is Committed
            &&& (InstAt(s, x.id).cmd is Nop || InstAt(s, x.id).dep.contains(id))
        }
    &&& ApplyAcceptEnabled(inst, inst.bal)
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(
        id,
        LInstanceState {
            recovery_phase: LRecoveryPhase::Start,
            ..AcceptedInstance(inst, inst.bal, inst.cvar, inst.dvar)
        },
    )
    &&& sent =~= Broadcast(
        c,
        LEPaxosStarMessage::Accept { id, b: inst.bal, c: inst.cvar, d: inst.dvar },
    ).insert(SelfPacket(c, LEPaxosStarMessage::AcceptOK { id, b: inst.bal }))
}

/// `HandlePostWaiting` disjunct 3 (`.tla:516-525`) — **the deadlock escape**,
/// and EPaxos*'s fix for the original protocol deadlocking "even during
/// executions with finitely many submitted commands".
///
/// A peer recovering one of our objectors announced `k > N-F-E`, which means it
/// is blocked on us in turn. Somebody has to give way: take `Nop`.
///
/// Takes a packet because the reference reads this out of `msgs`, which a
/// single-process spec cannot do — see the note on `LPostWaitingOnRecoverOK`.
pub open spec fn LPostWaitingOnWaiting(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    pkt: LPacket,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    &&& PostWaitingReady(c, s, id)
    &&& pkt.dst == c.my_id
    &&& match pkt.msg {
        LEPaxosStarMessage::Waiting { id: wid, k } => {
            &&& exists|x: LInvalidator| (#[trigger] inst.ivar.contains(x)) && x.id == wid
            &&& k + c.f + c.e > N(c)
        },
        _ => false,
    }
    &&& ApplyAcceptEnabled(inst, inst.bal)
    &&& s_.next_num == s.next_num
    &&& s_.instances == s.instances.insert(
        id,
        LInstanceState {
            recovery_phase: LRecoveryPhase::Start,
            ..AcceptedInstance(inst, inst.bal, LCmd::Nop, Set::<LInstanceId>::empty())
        },
    )
    &&& sent =~= Broadcast(
        c,
        LEPaxosStarMessage::Accept {
            id,
            b: inst.bal,
            c: LCmd::Nop,
            d: Set::<LInstanceId>::empty(),
        },
    ).insert(SelfPacket(c, LEPaxosStarMessage::AcceptOK { id, b: inst.bal }))
}

/// `HandlePostWaiting` disjunct 4 (`.tla:526-547`): a `RecoverOK` arrived from
/// **outside** the quorum we used, and it knows more than the quorum did.
/// Follow it — commit if it had committed, accept if it had accepted, and take
/// `Nop` if it is the instance's own coordinator (which would have told us).
///
/// This and disjunct 3 are the two places the reference searches `msgs` for a
/// message that is *not* part of an accumulated quorum. A single-process spec
/// cannot search the network, so both take the packet as a parameter and become
/// actions of their own — which is why the action count is 25 and not the 17
/// TODO.md 56.3.z predicted. Recorded there.
pub open spec fn LPostWaitingOnRecoverOK(
    s: LState,
    s_: LState,
    c: LConstants,
    id: LInstanceId,
    pkt: LPacket,
    sent: Set<LPacket>,
) -> bool {
    let inst = InstAt(s, id);
    &&& PostWaitingReady(c, s, id)
    &&& pkt.dst == c.my_id
    &&& !inst.qvar.contains(pkt.src)
    &&& match pkt.msg {
        LEPaxosStarMessage::RecoverOK { id: rid, b: _b, abalq: _a, cq, depq, init_depq: _i, phaseq } => {
            &&& rid == id
            &&& s_.next_num == s.next_num
            &&& if phaseq is Committed {
                &&& ApplyCommitEnabled(inst, inst.bal)
                &&& s_.instances == s.instances.insert(
                    id,
                    LInstanceState {
                        recovery_phase: LRecoveryPhase::Start,
                        ..CommittedInstance(inst, inst.bal, cq, depq)
                    },
                )
                &&& sent =~= Broadcast(
                    c,
                    LEPaxosStarMessage::Commit { id, b: inst.bal, c: cq, d: depq },
                )
            } else if phaseq is Accepted {
                &&& ApplyAcceptEnabled(inst, inst.bal)
                &&& s_.instances == s.instances.insert(
                    id,
                    LInstanceState {
                        recovery_phase: LRecoveryPhase::Start,
                        ..AcceptedInstance(inst, inst.bal, cq, depq)
                    },
                )
                &&& sent =~= Broadcast(
                    c,
                    LEPaxosStarMessage::Accept { id, b: inst.bal, c: cq, d: depq },
                ).insert(SelfPacket(c, LEPaxosStarMessage::AcceptOK { id, b: inst.bal }))
            } else {
                &&& pkt.src == id.owner
                &&& ApplyAcceptEnabled(inst, inst.bal)
                &&& s_.instances == s.instances.insert(
                    id,
                    LInstanceState {
                        recovery_phase: LRecoveryPhase::Start,
                        ..AcceptedInstance(inst, inst.bal, LCmd::Nop, Set::<LInstanceId>::empty())
                    },
                )
                &&& sent =~= Broadcast(
                    c,
                    LEPaxosStarMessage::Accept {
                        id,
                        b: inst.bal,
                        c: LCmd::Nop,
                        d: Set::<LInstanceId>::empty(),
                    },
                ).insert(SelfPacket(c, LEPaxosStarMessage::AcceptOK { id, b: inst.bal }))
            }
        },
        _ => false,
    }
}

// =========================================================================
// Next-state relation — 25 actions
// =========================================================================

/// The disjunction of every action, with each action's parameters
/// existentially quantified.
///
/// Grouped as the reference groups them (`.tla:598-611`): message handlers
/// first, then the steps a replica takes on its own behalf. `LSubmit` stands in
/// for the reference's `Submit(p, id, id)`, which uses the identifier as the
/// payload for model checking; here the payload is a parameter and the
/// identifier is allocated from `next_num`.
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| exists|value: int, sent: Set<LPacket>| LSubmit(s, s_, c, value, sent)
    // ---- message handlers ----
    ||| exists|pkt: LPacket, sent: Set<LPacket>| LHandlePreAccept(s, s_, c, pkt, sent)
    ||| exists|pkt: LPacket, sent: Set<LPacket>| LRecordPreAcceptOK(s, s_, c, pkt, sent)
    ||| exists|pkt: LPacket, sent: Set<LPacket>| LHandleAccept(s, s_, c, pkt, sent)
    ||| exists|pkt: LPacket, sent: Set<LPacket>| LRecordAcceptOK(s, s_, c, pkt, sent)
    ||| exists|pkt: LPacket, sent: Set<LPacket>| LHandleCommit(s, s_, c, pkt, sent)
    ||| exists|pkt: LPacket, sent: Set<LPacket>| LHandleRecover(s, s_, c, pkt, sent)
    ||| exists|pkt: LPacket, sent: Set<LPacket>| LRecordRecoverOK(s, s_, c, pkt, sent)
    ||| exists|pkt: LPacket, sent: Set<LPacket>| LHandleValidate(s, s_, c, pkt, sent)
    ||| exists|pkt: LPacket, sent: Set<LPacket>| LRecordValidateOK(s, s_, c, pkt, sent)
    // ---- quorum steps: commit path ----
    ||| exists|id: LInstanceId, sent: Set<LPacket>| LCommitFast(s, s_, c, id, sent)
    ||| exists|id: LInstanceId, sent: Set<LPacket>| LStartAccept(s, s_, c, id, sent)
    ||| exists|id: LInstanceId, sent: Set<LPacket>| LCommitSlow(s, s_, c, id, sent)
    // ---- recovery ----
    ||| exists|id: LInstanceId, sent: Set<LPacket>| LStartRecover(s, s_, c, id, sent)
    ||| exists|id: LInstanceId, sent: Set<LPacket>| LRecoverCommitted(s, s_, c, id, sent)
    ||| exists|id: LInstanceId, sent: Set<LPacket>| LRecoverAccepted(s, s_, c, id, sent)
    ||| exists|id: LInstanceId, sent: Set<LPacket>| LRecoverNop(s, s_, c, id, sent)
    ||| exists|id: LInstanceId, sent: Set<LPacket>| LRecoverValidate(s, s_, c, id, sent)
    // ---- validation ----
    ||| exists|id: LInstanceId, sent: Set<LPacket>| LValidateAccept(s, s_, c, id, sent)
    ||| exists|id: LInstanceId, sent: Set<LPacket>| LValidateNop(s, s_, c, id, sent)
    ||| exists|id: LInstanceId, sent: Set<LPacket>| LValidateWait(s, s_, c, id, sent)
    ||| exists|id: LInstanceId, sent: Set<LPacket>| LPostWaitingNop(s, s_, c, id, sent)
    ||| exists|id: LInstanceId, sent: Set<LPacket>| LPostWaitingAccept(s, s_, c, id, sent)
    ||| exists|id: LInstanceId, pkt: LPacket, sent: Set<LPacket>|
        LPostWaitingOnWaiting(s, s_, c, id, pkt, sent)
    ||| exists|id: LInstanceId, pkt: LPacket, sent: Set<LPacket>|
        LPostWaitingOnRecoverOK(s, s_, c, id, pkt, sent)
}

} // verus!

/// EPaxos* types — the **corrected** Egalitarian Paxos.
///
/// Ported from `docs/epaxos_reference/EPaxosCommitWithRecovery.tla`, the TLA+
/// model attached to:
///
///   Fedor Ryabinin, Alexey Gotsman, Pierre Sutra.
///   *Making Democracy Work: Fixing and Simplifying Egalitarian Paxos.*
///   OPODIS 2025. Extended version arXiv 2511.02743.
///
/// # This is not `src/protocol/EPaxos/`
///
/// `src/protocol/EPaxos/` models the EPaxos of the 2013 SOSP paper, whose
/// published TLA+ specification is **unsafe** — Sutra, *On the correctness of
/// Egalitarian Paxos* (IPL 156:105901, 2020) exhibits an execution in which
/// replicas disagree on a command's dependencies. That module is kept for the
/// benchmark and host glue; **this** one is the protocol to reason about. Two
/// specs named EPaxos in one tree is a foot-gun, so every file here says which
/// is which.
///
/// # The fix, in one sentence
///
/// Each instance carries **two** ballots — `bal` (current/promised) and `abal`
/// (the last ballot at which this replica accepted a slow-path value). The
/// single-ballot design is exactly what Sutra showed is insufficient, because
/// recovery selects among `RecoverOK` replies by maximum `abal`.
///
/// # Deliberate differences from the reference, and why
///
/// - **The instance identifier carries its owner** (`LInstanceId { owner, num }`).
///   The reference uses a flat `Id` set plus a global `initCoord[id]` map and a
///   global `submitted` set — the only two non-per-node variables in the file,
///   and the only two clean-subset (C1) violations the linter reports on it.
///   Every read of `initCoord[id]` is "who owns this id", so folding the owner
///   into the identifier turns it into a pure function and makes `submitted` a
///   per-node counter. This is how upstream EPaxos writes an instance
///   (`<<cleader, crtInst[cleader]>>`) too. See `t2_03_epaxos_star/rewrite.md`.
/// - **No sequence number.** EPaxos* orders on `(cmd, dep)` alone; there is no
///   `seq` anywhere in the reference. `src/protocol/EPaxos/` has one, and it is
///   faithful to the 2013 protocol rather than to this one.
/// - **Ten message variants, not eleven.** The reference declares
///   `TypePostWaiting == 11` and admits it in `TypeInv`, but **never constructs
///   it** — there is no `PostWaitingMsg` operator, and `HandlePostWaiting` is
///   driven by `recoveryPhase`, not by a message. The dead type is not ported.
///
/// # Layering note
///
/// `Raft/types.rs` holds types only, with predicates in `raft.rs`. This file
/// additionally carries the constants-level predicates (`conflicts`,
/// quorum sizing, well-formedness) because they are functions of the
/// configuration rather than of any action, and because it lets this module
/// verify on its own before the actions land.
use crate::common::collections::sets::*;
use vstd::prelude::*;

verus! {

/// Phase of one instance at one replica (`.tla:50-53`).
///
/// Four, not five: the reference has no `Executed` — execution and
/// dependency-graph ordering are outside the commit+recovery protocol, in the
/// reference and in upstream alike.
pub enum LPhase {
    Initial,
    PreAccepted,
    Accepted,
    Committed,
}

/// Where a replica is within its own recovery attempt for one instance
/// (`.tla:56-59`).
///
/// The reference's `HandleRecoverOK` is atomic in the paper (Figure 5) but is
/// split across three TLA+ actions, and this is the program counter that keeps
/// them ordered. It is spec bookkeeping, not protocol state on the wire.
pub enum LRecoveryPhase {
    Start,
    RecoverOK,
    ValidateOK,
    PostWaiting,
}

/// A command payload (`.tla:25-26`, `:147-150`).
///
/// `Bottom` is "nothing received yet" and conflicts with nothing; `Nop` is what
/// recovery commits when the original payload cannot be safely recovered, and
/// conflicts with everything.
pub enum LCmd {
    Bottom,
    Nop,
    Payload { value: int },
}

/// An instance identifier: the replica that submitted it, and its sequence
/// number at that replica.
///
/// The reference's flat `Id` plus global `initCoord`; see the module header.
pub struct LInstanceId {
    pub owner: int,
    pub num: int,
}

/// One element of the `I` set computed by `ComputeI` (`.tla:220-227`) — a
/// command that could invalidate the recovery decision, paired with the phase
/// it was observed in.
pub struct LInvalidator {
    pub id: LInstanceId,
    pub phase: LPhase,
}

/// An unordered pair of command payload values, used to give the conflict
/// relation as a configuration constant (the reference's `ConflictPairs`, in
/// `ExtraConfiguration.tla`).
pub struct LCmdPair {
    pub a: int,
    pub b: int,
}

/// One replica's knowledge of one instance.
///
/// The first seven fields are the protocol state (`.tla:98-104`); the rest is
/// the recovery bookkeeping described on `LRecoveryPhase` (`.tla:105-113`).
pub struct LInstanceState {
    pub phase: LPhase,
    /// Current/promised ballot. Moved by `Recover` and by `Accept`.
    pub bal: int,
    /// Last ballot at which a slow-path value was **accepted**. Moved by
    /// `Accept` and by `Commit`, never by `Recover`. **This field is the fix.**
    pub abal: int,
    /// Payload as first received (`PreAccept`/`Validate`).
    pub init_cmd: LCmd,
    /// Current payload.
    pub cmd: LCmd,
    /// Dependencies as proposed by the initial coordinator.
    pub init_dep: Set<LInstanceId>,
    /// Current dependency set.
    pub dep: Set<LInstanceId>,

    // ---- recovery bookkeeping (see LRecoveryPhase) ----
    /// How many recovery attempts this replica has made. Bounded in models to
    /// keep the state space finite; it is a **model bound**, not protocol.
    pub recovered: int,
    pub recovery_phase: LRecoveryPhase,
    /// `Q` — the quorum that answered `Recover`.
    pub qvar: Set<int>,
    /// `c` — the payload the recovery attempt is carrying.
    pub cvar: LCmd,
    /// `D` — the dependency set the recovery attempt is carrying.
    pub dvar: Set<LInstanceId>,
    /// `I` — the invalidator set accumulated from `ValidateOK`.
    pub ivar: Set<LInvalidator>,
    /// `|R_max|` — how many quorum members pre-accepted with unchanged deps.
    pub cardinality_rmax: int,
    /// The ballot this recovery attempt runs at, so a later promise can
    /// invalidate it.
    pub recovery_attempt_bal: int,
}

/// EPaxos* protocol messages (`.tla:64-92`).
///
/// Ten variants. `TypePostWaiting` is declared in the reference and never
/// constructed — see the module header.
pub enum LEPaxosStarMessage {
    PreAccept { id: LInstanceId, c: LCmd, d: Set<LInstanceId> },
    PreAcceptOK { id: LInstanceId, dq: Set<LInstanceId> },
    Accept { id: LInstanceId, b: int, c: LCmd, d: Set<LInstanceId> },
    AcceptOK { id: LInstanceId, b: int },
    Commit { id: LInstanceId, b: int, c: LCmd, d: Set<LInstanceId> },
    Recover { id: LInstanceId, b: int },
    /// Carries `abalq` — the accepted-ballot that single-ballot EPaxos loses.
    RecoverOK {
        id: LInstanceId,
        b: int,
        abalq: int,
        cq: LCmd,
        depq: Set<LInstanceId>,
        init_depq: Set<LInstanceId>,
        phaseq: LPhase,
    },
    Validate { id: LInstanceId, b: int, c: LCmd, d: Set<LInstanceId> },
    ValidateOK { id: LInstanceId, b: int, iq: Set<LInvalidator> },
    Waiting { id: LInstanceId, k: int },
}

/// A routed message. The reference's `msgs` carries `from`/`to` on every
/// message (`.tla:61-62`); at the single-replica level those become the packet
/// envelope, exactly as `LRaftPacket` does for Raft.
pub struct LPacket {
    pub src: int,
    pub dst: int,
    pub msg: LEPaxosStarMessage,
}

/// One replica's state: what it knows about every instance it has seen.
///
/// The reference keeps `[Proc -> [Id -> _]]` for each field; projected to a
/// single replica that is one map from instance to instance-state.
pub struct LState {
    pub instances: Map<LInstanceId, LInstanceState>,
    /// The next instance number this replica will use for its own submissions —
    /// the reference's global `submitted` set, made per-node (see header).
    pub next_num: int,
}

/// Protocol constants.
///
/// `f` is the crash tolerance and `e` the fast-path tolerance; the reference
/// derives both quorum sizes from them rather than fixing a majority.
pub struct LConstants {
    pub my_id: int,
    /// The reference's `CONSTANT Proc`. Carried as the **set**, not just its
    /// cardinality: quorum intersection — the property the whole protocol rests
    /// on — cannot be stated without a universe for the quorums to be drawn
    /// from. (`Raft/types.rs` carries `servers: Set<int>` for the same reason.)
    pub procs: Set<int>,
    /// Maximum crash failures tolerated.
    pub f: int,
    /// `e`-fast parameter.
    pub e: int,
    /// Model bound on instance numbers per replica.
    pub max_num: int,
    /// The conflict relation, as a configuration constant.
    pub conflict_pairs: Set<LCmdPair>,
}

/// `N == Cardinality(Proc)` (`.tla:30`).
pub open spec fn N(c: LConstants) -> int {
    c.procs.len() as int
}

/// Well-formedness of the configuration.
///
/// Carries the reference's `ASSUME N >= Max(2*E+F-1, 2*F+1)` (`.tla:34`), which
/// the paper proves is the optimal process count across the whole `(f, e)`
/// spectrum, plus `E <= F` from the bundled `.cfg`'s own comment.
///
/// This is the predicate `src/protocol/EPaxos/` lacks: its `LInit` constrains
/// only `num_replicas >= 3 && quorum_size > 0 && fast_quorum_size >= quorum_size`,
/// which admits `quorum_size == 1`.
/// Note there is no `procs.finite()` conjunct: in this Verus every `Set` is
/// finite by construction, and `Set::finite` is deprecated as always-true. The
/// finiteness that does need care is on *predicate-defined* sets, which is why
/// `Set::new` returns `Option` and why `ConflictingIds` filters a domain.
pub open spec fn WellFormedConstants(c: LConstants) -> bool {
    &&& c.procs.contains(c.my_id)
    &&& c.f >= 0
    &&& c.e >= 0
    &&& c.e <= c.f
    &&& N(c) >= 2 * c.e + c.f - 1
    &&& N(c) >= 2 * c.f + 1
    &&& c.max_num >= 1
}

/// A slow-path quorum: `N - F` (`.tla:152`).
pub open spec fn IsQuorumSized(c: LConstants, s: Set<int>) -> bool {
    s.len() >= N(c) - c.f
}

/// A fast-path quorum: `N - E` (`.tla:153`). Strictly larger than a slow
/// quorum whenever `e < f`, which is what buys the missing round.
pub open spec fn IsFastQuorumSized(c: LConstants, s: Set<int>) -> bool {
    s.len() >= N(c) - c.e
}

/// A fast quorum is a quorum.
///
/// Pure arithmetic from `e <= f`, but worth having as an obligation rather than
/// a comment: `HandlePreAcceptOK` applies **both** thresholds in one action
/// (collect `>= N-F` replies, commit fast only if `>= N-E` of them agree), and
/// the fast path's correctness depends on the larger set also being a quorum.
/// It is also the one thing `src/protocol/EPaxos/`'s constants got right —
/// `fast_quorum_size >= quorum_size` — and everything else about them wrong.
pub proof fn lemma_fast_quorum_is_quorum(c: LConstants, s: Set<int>)
    requires
        WellFormedConstants(c),
        IsFastQuorumSized(c, s),
    ensures
        IsQuorumSized(c, s),
{
}

/// Two slow quorums drawn from `Proc` intersect.
///
/// The property every agreement argument runs through, and the reason
/// `N >= 2F+1` is in `WellFormedConstants`: two sets of size `>= N-F` inside a
/// universe of size `N` overlap once `2(N-F) > N`, i.e. once `N > 2F`.
///
/// The set-cardinality work is `common::collections::sets`, which already
/// carries the general inclusion-exclusion argument for Raft and RSL; all this
/// adds is the arithmetic that discharges its `|a| + |b| > |u|` precondition
/// from `N >= 2F+1`.
pub proof fn lemma_quorums_intersect(c: LConstants, q1: Set<int>, q2: Set<int>)
    requires
        WellFormedConstants(c),
        q1.subset_of(c.procs),
        q2.subset_of(c.procs),
        IsQuorumSized(c, q1),
        IsQuorumSized(c, q2),
    ensures
        exists|p: int| q1.contains(p) && q2.contains(p),
{
    // |q1| + |q2| >= 2(N-F) = N + (N-2F) >= N + 1 > N == |Proc|.
    assert(q1.len() + q2.len() > c.procs.len());
    lemma_quorum_intersection(q1, q2, c.procs);
}

/// The conflict relation (`.tla:147-150`).
///
/// `Bottom` conflicts with nothing — a replica that has seen no payload cannot
/// order anything against it. `Nop` conflicts with everything, which is what
/// makes it safe for recovery to substitute.
pub open spec fn Conflicts(c: LConstants, c1: LCmd, c2: LCmd) -> bool {
    if c1 is Bottom || c2 is Bottom {
        false
    } else if c1 is Nop || c2 is Nop {
        true
    } else {
        ||| c.conflict_pairs.contains(LCmdPair { a: c1->value, b: c2->value })
        ||| c.conflict_pairs.contains(LCmdPair { a: c2->value, b: c1->value })
    }
}

/// Every instance this replica knows of whose payload conflicts with `cmd`
/// (`.tla:155-158`) — the dependency set a replica computes for a new command.
/// Built by **filtering the map's domain** rather than by `Set::new`. This
/// Verus's `Set` is finite and `Set::new` returns `Option`, with
/// `new_assuming_finite` deprecated for assuming what it should establish;
/// filtering a domain is finite by construction, which is the idiom Phase
/// 54.12.c settled on for the RSL proof.
pub open spec fn ConflictingIds(c: LConstants, s: LState, cmd: LCmd) -> Set<LInstanceId> {
    s.instances.dom().filter(|id: LInstanceId| Conflicts(c, s.instances[id].cmd, cmd))
}

/// Whether this replica has any reason to know about `id` — it holds state for
/// it, or something it holds depends on it (`.tla:160-163`). Guards
/// `StartRecover`: a replica does not recover an instance it has never heard of.
///
/// A predicate, not a set. The reference writes `SeenIds(p)` as a set and uses
/// it only as `id \in SeenIds(p)`; building it here would mean a union over the
/// domain's dependency sets, which is finite but awkward to establish, and
/// nothing needs the set itself.
pub open spec fn IsSeenId(s: LState, id: LInstanceId) -> bool {
    ||| (s.instances.dom().contains(id) && !(s.instances[id].cmd is Bottom))
    ||| exists|other: LInstanceId|
        (#[trigger] s.instances.dom().contains(other)) && s.instances[other].dep.contains(id)
}

} // verus!

// REVIEW AID, NEVER BYTE-DIFFED.
//
// Phase 51's hand-written single-process Jetpack recovery spec, concatenated
// from src/protocol/Jetpack/{types.rs, jetpack.rs}. It is PARTIAL: the entry
// actions (51.9) were never written, so it has no BeginRecovery phase and no
// SendPrepare/SendAccept. `golden.rs` covers those; see rewrite.md for the
// comparison.

use vstd::prelude::*;

verus! {
    /// A command. Corresponds to jetpack.tla's `Commands == [cmd_id |-> id, key |-> k]`.
    pub struct Command {
        pub cmd_id: int,
        pub key: int,
    }

    /// Recovery-state-machine phase for this replica.
    ///
    /// Slice (jstate option B): relative to the original 6 states, the trailing
    /// `AfterResubmit` is dropped (it pulls in client/execution, out of slice);
    /// `AfterAccept` returns directly to `Ready`.
    ///
    ///   Ready -> Recovery -> AfterBeginRecovery -> AfterPrepare -> AfterAccept -> (back to Ready)
    pub enum LJState {
        Ready,               // Normal operation, not in recovery
        Recovery,            // Recovery triggered, BeginRecovery issued
        AfterBeginRecovery,  // BeginRecovery responses collected
        AfterPrepare,        // Prepare phase done (promise quorum reached)
        AfterAccept,         // Accept phase done (accept quorum reached), then back to Ready
    }

    /// Local state of a single Jetpack replica during recovery (single-process
    /// view, no `[i]`).
    ///
    /// Slice boundary: fixed membership + single value + base as a contract +
    /// no client/execution. Every field is "this replica's own"; cross-replica
    /// information only arrives via messages (action parameters).
    pub struct LState {
        // ---- Recovery state machine ----
        pub jstate: LJState,              // Current recovery phase
        pub jepoch: int,                  // Ballot this replica uses to drive recovery (proposer side)

        // ---- Acceptor triple (corresponds to jetpack.tla's jpool fields) ----
        pub max_seen_ballot: int,         // jpool.max_seen_ballot: highest ballot promised
        pub accepted_ballot: int,         // jpool.accepted_ballot: ballot of last accept (0 if none)
        pub accepted_value: Set<Command>, // jpool.accepted_value: last accepted value

        // ---- Proposer / recovery-coordinator side ----
        pub recovery_set: Set<int>,       // Replica ids participating in this recovery
        pub prep_rcvd: Set<int>,          // Replica ids that returned a Prepare response (for counting)
        pub accept_rcvd: Set<int>,        // Replica ids that returned an Accept response (for counting)
        pub chosen_value: Set<Command>,   // Value selected / to be proposed in the Accept phase

        // ---- Prepare-phase value selection (online aggregation, Paxos-style) ----
        pub highest_seen_ballot: int,         // Highest accepted_ballot seen across Prepare responses
        pub highest_seen_value: Set<Command>, // Value from that highest-ballot promise
    }

    /// Protocol constants (fixed-membership slice).
    pub struct LConstants {
        pub replicas: Set<int>,           // All replica ids (fixed membership, unchanging)
        pub quorum_size: int,             // Majority threshold (count-based, not SUBSET powerset)
        pub my_id: int,                   // This replica's id
    }
}
use crate::protocol::Jetpack::types::*;
use vstd::prelude::*;

verus! {
    /// Initial state: a replica that just came up and has not entered recovery.
    ///
    /// Corresponds to jetpack.tla's `InitJetpackVars` (:311), but single-process:
    /// it describes "this one replica's initial local state", not
    /// `[i \in Server |-> ...]`.
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        // Recovery state machine: normal state
        &&& s.jstate is Ready
        &&& s.jepoch == 0
        // Acceptor triple: nothing promised/accepted yet
        &&& s.max_seen_ballot == 0
        &&& s.accepted_ballot == 0
        &&& s.accepted_value == Set::<Command>::empty()
        // Proposer / coordinator side: recovery not started, sets empty
        &&& s.recovery_set == Set::<int>::empty()
        &&& s.prep_rcvd == Set::<int>::empty()
        &&& s.accept_rcvd == Set::<int>::empty()
        &&& s.chosen_value == Set::<Command>::empty()
        // Prepare-phase selection trackers start empty
        &&& s.highest_seen_ballot == 0
        &&& s.highest_seen_value == Set::<Command>::empty()
    }

    /// Acceptor handles a Prepare request (jetpack.tla `HandlePrepareRequest`, :527),
    /// analogous to Paxos Phase-1b (`LSend1b`).
    ///
    /// `req_jepoch` and `req_ballot` are the recovery epoch and prepare ballot
    /// carried by the incoming JetpackPrepareRequest (message content becomes
    /// action parameters, single-process style).
    ///
    /// Slice notes:
    ///   - The original also gates on / bumps `oepoch` (view/reconfig); dropped here.
    ///   - On rejection the original still replies with `mok = FALSE` and identity
    ///     state; that is an exec-layer I/O with an identity transition, so this
    ///     spec-level action models only the accepting (ok) branch.
    ///   - The promise carried back (accepted_ballot / accepted_value) is emitted
    ///     at the exec layer; here we only report that the acceptor state is intact.
    pub open spec fn L_HandlePrepareReq(
        s: LState,
        s_: LState,
        c: LConstants,
        req_jepoch: int,
        req_ballot: int,
    ) -> bool {
        // Guard: request's recovery epoch and ballot are at least as new as ours
        &&& req_jepoch >= s.jepoch
        &&& req_ballot >= s.max_seen_ballot
        // Update acceptor: adopt the recovery epoch (Max, but guard makes it req_jepoch)
        &&& s_.jepoch == req_jepoch
        // ...and promise this ballot (this is the core Paxos Phase-1b step)
        &&& s_.max_seen_ballot == req_ballot
        // Acceptor's accepted state is unchanged (it is what we promise back)
        &&& s_.accepted_ballot == s.accepted_ballot
        &&& s_.accepted_value == s.accepted_value
        // Proposer / recovery-machine side unchanged (passive acceptor step)
        &&& s_.jstate == s.jstate
        &&& s_.recovery_set == s.recovery_set
        &&& s_.prep_rcvd == s.prep_rcvd
        &&& s_.accept_rcvd == s.accept_rcvd
        &&& s_.chosen_value == s.chosen_value
        &&& s_.highest_seen_ballot == s.highest_seen_ballot
        &&& s_.highest_seen_value == s.highest_seen_value
    }

    /// Acceptor handles an Accept request (jetpack.tla `HandleAcceptRequest`, :623),
    /// analogous to Paxos Phase-2b.
    ///
    /// `req_jepoch` / `req_ballot` / `req_value` are the recovery epoch, ballot,
    /// and proposed value carried by the incoming JetpackAcceptRequest.
    ///
    /// Same slice notes as `L_HandlePrepareReq`: `oepoch` dropped (view/reconfig);
    /// the reject (`mok = FALSE`) branch and the reply are exec-layer concerns, so
    /// this models only the accepting (ok) branch.
    pub open spec fn L_HandleAcceptReq(
        s: LState,
        s_: LState,
        c: LConstants,
        req_jepoch: int,
        req_ballot: int,
        req_value: Set<Command>,
    ) -> bool {
        // Guard: same freshness checks as Prepare
        &&& req_jepoch >= s.jepoch
        &&& req_ballot >= s.max_seen_ballot
        // Update acceptor: adopt recovery epoch and promise the ballot...
        &&& s_.jepoch == req_jepoch
        &&& s_.max_seen_ballot == req_ballot
        // ...and, unlike Prepare, actually accept: record the ballot and value
        &&& s_.accepted_ballot == req_ballot
        &&& s_.accepted_value == req_value
        // Proposer / recovery-machine side unchanged (passive acceptor step)
        &&& s_.jstate == s.jstate
        &&& s_.recovery_set == s.recovery_set
        &&& s_.prep_rcvd == s.prep_rcvd
        &&& s_.accept_rcvd == s.accept_rcvd
        &&& s_.chosen_value == s.chosen_value
        &&& s_.highest_seen_ballot == s.highest_seen_ballot
        &&& s_.highest_seen_value == s.highest_seen_value
    }

    /// Proposer records a Prepare response / promise (jetpack.tla
    /// `HandlePrepareResponse`, :566), analogous to Paxos `LRecvPromise`.
    ///
    /// `resp_src` is the responding replica; `resp_accepted_ballot` /
    /// `resp_accepted_value` are the (accepted_ballot, accepted_value) it reported.
    ///
    /// Modeling choice: instead of storing the whole `prep_responses` map (TLC
    /// style), we aggregate online — track the highest accepted_ballot seen and
    /// its value. This matches repo Paxos and is what an implementation does. Only
    /// the accepting (mok = TRUE) branch is modeled; the reject branch is deferred.
    pub open spec fn L_HandlePrepareResp(
        s: LState,
        s_: LState,
        c: LConstants,
        resp_src: int,
        resp_accepted_ballot: int,
        resp_accepted_value: Set<Command>,
    ) -> bool {
        // Guard: collecting Prepare responses, from a known, not-yet-counted replica
        &&& s.jstate is AfterBeginRecovery
        &&& c.replicas.contains(resp_src)
        &&& !s.prep_rcvd.contains(resp_src)
        // Record this responder
        &&& s_.prep_rcvd == s.prep_rcvd.insert(resp_src)
        // Online selection: if this promise carried a higher accepted_ballot, adopt its value
        &&& s_.highest_seen_ballot == (if resp_accepted_ballot > s.highest_seen_ballot {
            resp_accepted_ballot
        } else {
            s.highest_seen_ballot
        })
        &&& s_.highest_seen_value == (if resp_accepted_ballot > s.highest_seen_ballot {
            resp_accepted_value
        } else {
            s.highest_seen_value
        })
        // Everything else unchanged
        &&& s_.jstate == s.jstate
        &&& s_.jepoch == s.jepoch
        &&& s_.max_seen_ballot == s.max_seen_ballot
        &&& s_.accepted_ballot == s.accepted_ballot
        &&& s_.accepted_value == s.accepted_value
        &&& s_.recovery_set == s.recovery_set
        &&& s_.accept_rcvd == s.accept_rcvd
        &&& s_.chosen_value == s.chosen_value
    }

    /// Proposer completes the Prepare phase once a quorum of promises is in
    /// (jetpack.tla `CompletePrepare`, :586).
    ///
    /// Quorum is a COUNT here (`prep_rcvd.len() >= quorum_size`) — the single-process
    /// downgrade of the original `\E qs \in JQuorum(...)` powerset existential.
    ///
    /// Value selection (Paxos safety core): if some promise reported an accepted
    /// value (highest_seen_ballot > 0), we MUST propose that value; otherwise the
    /// proposer is free to choose (here: keep chosen_value).
    pub open spec fn L_CompletePrepare(s: LState, s_: LState, c: LConstants) -> bool {
        // Guard: collecting phase, and a quorum of promises has arrived
        &&& s.jstate is AfterBeginRecovery
        &&& s.prep_rcvd.len() >= c.quorum_size
        // Pick the value: highest-ballot accepted value if any, else keep our own
        &&& s_.chosen_value == (if s.highest_seen_ballot == 0 {
            s.chosen_value
        } else {
            s.highest_seen_value
        })
        // Advance to the Accept phase
        &&& s_.jstate is AfterPrepare
        // Everything else unchanged
        &&& s_.jepoch == s.jepoch
        &&& s_.max_seen_ballot == s.max_seen_ballot
        &&& s_.accepted_ballot == s.accepted_ballot
        &&& s_.accepted_value == s.accepted_value
        &&& s_.recovery_set == s.recovery_set
        &&& s_.prep_rcvd == s.prep_rcvd
        &&& s_.accept_rcvd == s.accept_rcvd
        &&& s_.highest_seen_ballot == s.highest_seen_ballot
        &&& s_.highest_seen_value == s.highest_seen_value
    }

    /// Proposer records an Accept response (jetpack.tla `HandleAcceptResponse`, :656).
    /// Only the accepting (mok = TRUE) branch is modeled; the reject branch is deferred.
    pub open spec fn L_HandleAcceptResp(
        s: LState,
        s_: LState,
        c: LConstants,
        resp_src: int,
    ) -> bool {
        // Guard: collecting Accept responses, from a known, not-yet-counted replica
        &&& s.jstate is AfterPrepare
        &&& c.replicas.contains(resp_src)
        &&& !s.accept_rcvd.contains(resp_src)
        // Record this responder
        &&& s_.accept_rcvd == s.accept_rcvd.insert(resp_src)
        // Everything else unchanged
        &&& s_.jstate == s.jstate
        &&& s_.jepoch == s.jepoch
        &&& s_.max_seen_ballot == s.max_seen_ballot
        &&& s_.accepted_ballot == s.accepted_ballot
        &&& s_.accepted_value == s.accepted_value
        &&& s_.recovery_set == s.recovery_set
        &&& s_.prep_rcvd == s.prep_rcvd
        &&& s_.chosen_value == s.chosen_value
        &&& s_.highest_seen_ballot == s.highest_seen_ballot
        &&& s_.highest_seen_value == s.highest_seen_value
    }

    /// Proposer completes the Accept phase once a quorum of accepts is in
    /// (jetpack.tla `CompleteAccept`, :673). Reaching AfterAccept means the value
    /// is accepted by a quorum — i.e. chosen.
    pub open spec fn L_CompleteAccept(s: LState, s_: LState, c: LConstants) -> bool {
        // Guard: Accept phase, quorum of accepts arrived (count-based quorum)
        &&& s.jstate is AfterPrepare
        &&& s.accept_rcvd.len() >= c.quorum_size
        // Advance: the value is now chosen
        &&& s_.jstate is AfterAccept
        // Everything else unchanged
        &&& s_.jepoch == s.jepoch
        &&& s_.max_seen_ballot == s.max_seen_ballot
        &&& s_.accepted_ballot == s.accepted_ballot
        &&& s_.accepted_value == s.accepted_value
        &&& s_.recovery_set == s.recovery_set
        &&& s_.prep_rcvd == s.prep_rcvd
        &&& s_.accept_rcvd == s.accept_rcvd
        &&& s_.chosen_value == s.chosen_value
        &&& s_.highest_seen_ballot == s.highest_seen_ballot
        &&& s_.highest_seen_value == s.highest_seen_value
    }

    /// Proposer finishes recovery and returns to Ready (jetpack.tla `FinishRecovery`,
    /// :709, collapsed with Resubmit/CompleteResubmit which are out of slice).
    ///
    /// SAFETY DECISION (needs author confirmation): the original FinishRecovery
    /// resets jpool (max_seen_ballot / accepted_ballot / accepted_value) to Empty,
    /// because it bumps epoch into a NEW view, retiring old ballot state. Our
    /// fixed-membership single-value slice has no epoch bump, so we PRESERVE the
    /// acceptor triple (Paxos-persistent). Clearing it would let a later recovery
    /// forget an already-accepted value and break agreement. We reset only the
    /// per-recovery proposer aggregation.
    pub open spec fn L_FinishRecovery(s: LState, s_: LState, c: LConstants) -> bool {
        // Guard: the value has been chosen
        &&& s.jstate is AfterAccept
        // Return to normal
        &&& s_.jstate is Ready
        // Reset per-recovery proposer aggregation
        &&& s_.recovery_set == Set::<int>::empty()
        &&& s_.prep_rcvd == Set::<int>::empty()
        &&& s_.accept_rcvd == Set::<int>::empty()
        &&& s_.highest_seen_ballot == 0
        &&& s_.highest_seen_value == Set::<Command>::empty()
        &&& s_.chosen_value == Set::<Command>::empty()
        // PRESERVE acceptor triple + jepoch (see SAFETY DECISION above)
        &&& s_.max_seen_ballot == s.max_seen_ballot
        &&& s_.accepted_ballot == s.accepted_ballot
        &&& s_.accepted_value == s.accepted_value
        &&& s_.jepoch == s.jepoch
    }

    /// One recovery-layer step of a single replica: the disjunction of all
    /// actions. Message-carrying actions existentially bind their parameters
    /// (the incoming message content), mirroring TLA+'s `\E m : Action(i, m)`.
    ///
    /// Incomplete: the "entry" actions (trigger recovery, BeginRecovery phase)
    /// are not here yet — they touch the base contract and are written next.
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        // Proposer-side, no message parameter
        ||| L_CompletePrepare(s, s_, c)
        ||| L_CompleteAccept(s, s_, c)
        ||| L_FinishRecovery(s, s_, c)
        // Acceptor-side, bind the incoming request content
        ||| exists|rj: int, rb: int| L_HandlePrepareReq(s, s_, c, rj, rb)
        ||| exists|rj: int, rb: int, rv: Set<Command>| L_HandleAcceptReq(s, s_, c, rj, rb, rv)
        // Proposer-side, bind the incoming response content
        ||| exists|src: int, rb: int, rv: Set<Command>| L_HandlePrepareResp(s, s_, c, src, rb, rv)
        ||| exists|src: int| L_HandleAcceptResp(s, s_, c, src)
    }
}

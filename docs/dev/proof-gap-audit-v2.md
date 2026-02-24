# Phase 23 Proof Gap Audit v2

Generated: 2026-02-24
Baseline: 560 verified, 0 errors (all assume(false)/external_body functions present)

## Tier Definitions

- **Tier A**: Function has correct exec body; removing `assume(false)` + adding simple proof
  assertions should make it verify. Estimated: 1-2 hours per function.
- **Tier B**: Function has correct exec body but proof requires complex lemmas (HashMap
  invariants, deep View mapping, multi-component composition). May need `PROOF-TODO`.
- **Tier C**: Function has `external_body` stub with NO body. Spec pattern is untranslatable
  by the transpiler (quantified filters, IO dispatch, complex existentials). Needs `TRANSLATE-TODO`.
- **Helper**: Trusted infrastructure (clone/filter wrappers). Keep as `external_body`.

## Summary

| Category | Count | Description |
|----------|-------|-------------|
| Tier A   | 23    | Remove assume(false), likely verifiable |
| Tier B   | 25    | Correct body, proof needs complex lemmas |
| Tier C   | 17    | Untranslatable, needs manual impl or TRANSLATE-TODO |
| Helper   | 13    | Trusted clone/filter wrappers |
| **Total** | **78** | |

## Module Breakdown

| Module | Tier A | Tier B | Tier C | Helper | Total |
|--------|--------|--------|--------|--------|-------|
| acceptor_gen.rs | 2 | 1 | 2 | 1 | 6 |
| proposer_gen.rs | 3 | 5 | 3 | 3 | 14 |
| learner_gen.rs | 0 | 1 | 2 | 3 | 6 |
| election_gen.rs | 3 | 4 | 3 | 3 | 13 |
| executor_gen.rs | 2 | 4 | 0 | 2 | 8 |
| replica_gen.rs | 13 | 5 | 7 | 1 | 26 |
| broadcast_gen.rs | 0 | 0 | 0 | 0 | 0 (verified) |

---

## Detailed Classification

### acceptor_gen.rs

| Function | Line | Status | Tier | Reason |
|----------|------|--------|------|--------|
| clone_hashset | 46 | external_body | Helper | Trusted clone wrapper |
| CAcceptorInit | 71 | external_body | A | Simple struct init; provable with field assertions |
| CAcceptorProcess1a | 81 | external_body | C | Complex vote tracking + conditional ballot + packet construction |
| CAcceptorProcess2a | 93 | external_body | C | Complex vote processing + broadcast response |
| CAcceptorProcessHeartbeat | 105 | external_body | B | Conditional state copy; needs view-mapping proof for nested fields |
| CAcceptorTruncateLog | 115 | external_body | A | Log truncation; struct construction with unchanged fields |

### proposer_gen.rs

| Function | Line | Status | Tier | Reason |
|----------|------|--------|------|--------|
| clone_hashset | 45 | external_body | Helper | Trusted clone wrapper |
| clone_request_queue | 70 | external_body | Helper | Vec clone with mapped view |
| clone_incomplete_batch_timer | 81 | external_body | Helper | Timer clone |
| CProposerInit | 90 | assume(false) | A | Struct construction; fields match spec directly |
| CProposerProcessRequest | 123 | assume(false) | B | HashMap insert + request queue append; deep view mapping |
| CProposerMaybeEnterNewViewAndSend1a | 192 | assume(false) | B | Broadcast + state transition + concat_vecs |
| CProposerProcess1b | 230 | assume(false) | B | HashSet union operations; needs set lemmas |
| CProposerMaybeEnterPhase2 | 266 | assume(false) | B | Complex state machine transition + broadcast |
| CProposerNominateNewValueAndSend2a | 306 | external_body | C | Complex nomination: truncate queue + broadcast |
| CProposerNominateOldValueAndSend2a | 318 | external_body | C | HashSet iteration to find highest proposal |
| CProposerMaybeNominateValueAndSend2a | 330 | external_body | C | Multi-branch dispatch to other Nominate functions |
| CProposerProcessHeartbeat | 340 | assume(false) | B | ElectionState delegation + conditional logic |
| CProposerCheckForViewTimeout | 378 | assume(false) | A | Simple delegation to ElectionState |
| CProposerCheckForQuorumOfViewSuspicions | 402 | assume(false) | B | ElectionState + conditional state reset |
| CProposerResetViewTimerDueToExecution | 439 | assume(false) | A | Simple delegation pattern |

### learner_gen.rs

| Function | Line | Status | Tier | Reason |
|----------|------|--------|------|--------|
| clone_hashset | 33 | external_body | Helper | Trusted clone wrapper |
| clone_clearnerstate | 191 | external_body | Helper | HashMap clone preserving view |
| filter_clearnerstate | 200 | external_body | Helper | HashMap filter with threshold |
| CLearnerProcess2b | 248 | external_body | C | Complex HashMap operations + deep view mapping |
| CLearnerForgetDecision | 258 | external_body | B | Map remove; may be provable with Verus map lemmas |
| CLearnerForgetOperationsBefore | 268 | external_body | C | Quantified filter on map (forall opn < threshold) |

### election_gen.rs

| Function | Line | Status | Tier | Reason |
|----------|------|--------|------|--------|
| clone_hashset | 37 | external_body | Helper | Trusted clone wrapper |
| clone_requests_received_prev_epochs | 62 | external_body | Helper | Vec<CRequest> clone with mapped view |
| clone_requests_received_this_epoch | 87 | external_body | Helper | Vec<CRequest> clone with mapped view |
| CBoundRequestSequence | 125 | external_body | C | Upper bound filtering on Vec |
| CRequestsMatch | 130 | assume(false) | A | Simple boolean equality check |
| CRequestSatisfiedBy | 142 | assume(false) | A | Simple boolean comparison |
| CRemoveAllSatisfiedRequestsInSequence | 156 | external_body | C | Seq filtering with predicate |
| CElectionStateInit | 161 | assume(false) | A | Struct construction with empty collections |
| CElectionStateProcessHeartbeat | 189 | assume(false) | B | Complex multi-branch logic with HashSet ops |
| CElectionStateCheckForViewTimeout | 299 | assume(false) | B | Multi-branch timeout logic |
| CElectionStateCheckForQuorumOfViewSuspicions | 353 | assume(false) | B | Quorum verification + state transitions |
| CElectionStateReflectReceivedRequest | 386 | external_body | C | Request reflection with seq append |
| CRemoveExecutedRequestBatch | 396 | external_body | Helper | Batch removal utility |
| CElectionStateReflectExecutedRequestBatch | 401 | assume(false) | B | Delegation to CRemoveExecutedRequestBatch |

### executor_gen.rs

| Function | Line | Status | Tier | Reason |
|----------|------|--------|------|--------|
| clone_hashset | 49 | external_body | Helper | Trusted clone wrapper |
| clone_next_op_to_execute | 73 | external_body | Helper | COutstandingOperation clone |
| CExecutorInit | 83 | assume(false) | A | Struct construction; fields match spec |
| CExecutorGetDecision | 106 | assume(false) | A | Simple state transition with ballot |
| CExecutorProcessAppStateSupply | 129 | assume(false) | B | Message extraction + match arms |
| CExecutorProcessAppStateRequest | 182 | assume(false) | B | Conditional ballot comparison + reply generation |
| CExecutorProcessStartingPhase2 | 237 | assume(false) | B | Conditional broadcast request |
| CExecutorProcessRequest | 288 | assume(false) | B | Cache lookup + conditional reply |

### replica_gen.rs

| Function | Line | Status | Tier | Reason |
|----------|------|--------|------|--------|
| clone_hashset | 46 | external_body | Helper | Trusted clone wrapper |
| CReplicaInit | 69 | assume(false) | A | Delegation to 4 component inits |
| CReplicaNextProcessInvalid | 88 | assume(false) | A | No-op; returns unmodified state + empty packets |
| CReplicaNextProcessRequest | 106 | assume(false) | B | Cache lookup + conditional delegation |
| CReplicaNextProcess1a | 147 | assume(false) | A | Delegation to CAcceptorProcess1a |
| CReplicaNextProcess1b | 171 | external_body | C | HashSet for-loop invariant issue (proven manual-only) |
| CReplicaNextProcessStartingPhase2 | 181 | assume(false) | A | Delegation to CExecutorProcessStartingPhase2 |
| CReplicaNextProcess2a | 203 | assume(false) | B | Conditional ballot+opn check + delegation |
| CReplicaNextProcess2b | 259 | assume(false) | B | Conditional opn+state check + delegation |
| CReplicaNextProcessReply | 302 | assume(false) | A | No-op; returns unmodified state + empty packets |
| CReplicaNextProcessAppStateSupply | 320 | assume(false) | B | Conditional opn check + multiple delegations |
| CReplicaNextProcessAppStateRequest | 369 | assume(false) | A | Delegation to CExecutorProcessAppStateRequest |
| CReplicaNextProcessHeartbeat | 391 | assume(false) | B | Multiple delegations to proposer+acceptor |
| CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a | 420 | assume(false) | A | Delegation to CProposerMaybeEnterNewViewAndSend1a |
| CReplicaNextSpontaneousMaybeEnterPhase2 | 441 | assume(false) | A | Delegation to CProposerMaybeEnterPhase2 |
| CReplicaNextReadClockMaybeNominateValueAndSend2a | 462 | assume(false) | A | Delegation to CProposerMaybeNominateValueAndSend2a |
| CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints | 486 | external_body | C | Quantified pattern (exists op in checkpoints) |
| CReplicaNextSpontaneousMaybeMakeDecision | 496 | assume(false) | B | Quorum check + conditional delegation |
| CReplicaNextSpontaneousMaybeExecute | 536 | assume(false) | A | Stub returning unmodified state |
| CReplicaNextReadClockMaybeSendHeartbeat | 550 | assume(false) | A | Conditional clock check + broadcast |
| CReplicaNextReadClockCheckForViewTimeout | 585 | assume(false) | A | Delegation to CProposerCheckForViewTimeout |
| CReplicaNextReadClockCheckForQuorumOfViewSuspicions | 613 | assume(false) | A | Delegation to CProposerCheckForQuorumOfViewSuspicions |
| CReplicaNumActions | 671 | assume(false) | A | Constant return (10) |
| CSchedulerInit | 689 | assume(false) | A | Delegation to CReplicaInit |
| CReplicaNextReadClockAndProcessPacket | 643 | external_body | C | IO dispatch (requires manual impl) |
| CReplicaNextProcessPacketWithoutReadingClock | 653 | external_body | C | IO dispatch (requires manual impl) |
| CReplicaNextProcessPacket | 663 | external_body | C | IO dispatch (requires manual impl) |
| CReplicaNoReceiveNext | 681 | external_body | C | Scheduler dispatch (requires manual impl) |
| CSchedulerNext | 706 | external_body | C | Scheduler dispatch (requires manual impl) |

---

## Priority Order for Fixes

### Phase 23.3: Tier A functions (23 total)

Start with modules that have the most Tier A functions:

1. **replica_gen.rs** (13 Tier A) — mostly delegation patterns; removing assume(false) should
   work if downstream functions' ensures clauses are sufficient
2. **proposer_gen.rs** (3 Tier A) — init + simple delegation patterns
3. **election_gen.rs** (3 Tier A) — init + boolean comparisons
4. **executor_gen.rs** (2 Tier A) — init + simple state transition
5. **acceptor_gen.rs** (2 Tier A) — init + truncation

### Phase 23.4: Tier B functions (25 total)

These need `PROOF-TODO` comments and real bodies (remove assume(false)):

- executor_gen.rs: 4 functions (message processing + cache operations)
- proposer_gen.rs: 5 functions (state transitions, broadcasts)
- election_gen.rs: 4 functions (heartbeat, timeout, quorum)
- replica_gen.rs: 5 functions (conditional delegation + composition)
- acceptor_gen.rs: 1 function (heartbeat processing)
- learner_gen.rs: 1 function (map remove)

### Phase 23.5: Tier C functions (17 total)

Keep as `external_body` with `TRANSLATE-TODO`:

- IO dispatch: 5 functions (replica_gen.rs)
- Manual-only: 2 functions (replica_gen.rs — 1b processing, log truncation)
- Complex nomination: 3 functions (proposer_gen.rs)
- Complex map/seq ops: 4 functions (learner + election)
- Complex vote tracking: 2 functions (acceptor_gen.rs)

### Helpers (13 total)

Keep as `external_body` — trusted infrastructure wrappers.

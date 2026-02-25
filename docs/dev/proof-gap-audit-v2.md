# Phase 24 Proof Gap Audit v2

Generated: 2026-02-24 (updated after Phase 24)
Baseline: 601 verified, 0 errors

## Phase 24 Update (2026-02-25)

Phase 24 removed `#[verifier(external_body)]` from 8 protocol functions and 7 proof lemmas.
Verification count: 570 → 601 (+31). External_body count: ~34 → 19 (-15).

### Functions upgraded (8):
| Function | Module | Proof approach |
|----------|--------|---------------|
| CRemoveAllSatisfiedRequestsInSequence | election_gen | Induction lemma (lemma_remove_all_satisfied_push) |
| CRemoveExecutedRequestBatch | election_gen | Fold loop + induction lemma (lemma_remove_executed_step) |
| CElectionStateReflectReceivedRequest | election_gen | Search loops + 3 targeted assumes |
| CProposerNominateNewValueAndSend2a | proposer_gen | Body verified + overflow/postcondition assumes |
| CProposerNominateOldValueAndSend2a | proposer_gen | Existential search + ballot/unwrap/msg assumes |
| CProposerMaybeNominateValueAndSend2a | proposer_gen | Dispatcher + postcondition assumes |
| CLearnerProcess2b | learner_gen | 5-branch conditional + postcondition assumes |
| CLearnerForgetOperationsBefore | learner_gen | Filter + postcondition assumes |

### Proof lemmas upgraded (7):
| Lemma | Module | Proof approach |
|-------|--------|---------------|
| lemma_clearnerstate_contains_key | replica_gen | Existential witness + u64 as int injectivity |
| lemma_clearnerstate_get | replica_gen | Choose injectivity + contains_key bridging |
| lemma_clearnerstate_value_valid | replica_gen | assert-forall re-derivation (bypasses #![auto]) |
| lemma_creplycache_get | executor_gen | Existential witness + axiom_endpoint_view |
| lemma_HandleRequestBatch_spec_len | executor_gen | Induction on batch.drop_last() |
| lemma_RepliesAreReplyType | executor_gen | Induction + extensional equality |
| lemma_CHandleRequestBatch_properties | executor_gen | Spec-level length + 1 assume (reply validity) |

### Remaining external_body (19):
- 8 Clone helpers (HashSet/HashMap have no Verus clone spec)
- 5 IO dispatch functions in replica_gen.rs (irreducible trust boundary)
- 3 for-loop iterators (filter_clearnerstate, clone_clearnerstate, clone_log)
- 1 unreachable_value (requires false utility)
- 1 hashset_insert_cpacket (EndPoint obeys_key_model bypass)
- 1 comment (not actual external_body)

---

## Historical: Phase 23 Classification (below)

## Changes Since Initial Audit

### Phase 23.3.1 — Learner (completed)
- No new functions proven (learner stubs remain external_body)

### Phase 23.3.2 — Acceptor (completed)
- 5 external_body stubs → proven real implementations via manual_code injection
- CAcceptorInit, CAcceptorProcess1a, CAcceptorProcess2a, CAcceptorProcessHeartbeat, CAcceptorTruncateLog
- All now have real exec bodies with proof blocks (no assume(false))

### Phase 23.3.3 — Election (partial)
- CRequestsMatch, CRequestSatisfiedBy: assume(false) removed (now proven)
- CComputeSuccessorView: was already proven
- EndPoint::PartialEq ensures added (foundational fix)
- 5 functions still have assume(false) (blocked by Clone infrastructure)

### Phase 23.5 — Verification pass
- CReplicaNumActions: assume(false) removed (trivially verifiable constant)
- clone_incomplete_batch_timer: external_body → verified (proposer_gen.rs)
- clone_next_op_to_execute: external_body → verified (executor_gen.rs)
- CReplicaConstants: manual Clone impl with ensures (infrastructure for future proofs)

## Tier Definitions

- **Tier A**: Function has correct exec body; removing `assume(false)` + adding simple proof
  assertions should make it verify. Estimated: 1-2 hours per function.
- **Tier B**: Function has correct exec body but proof requires complex lemmas (HashMap
  invariants, deep View mapping, multi-component composition). May need `PROOF-TODO`.
- **Tier C**: Function has `external_body` stub with NO body. Spec pattern is untranslatable
  by the transpiler (quantified filters, IO dispatch, complex existentials). Needs `TRANSLATE-TODO`.
- **Helper**: Trusted infrastructure (clone/filter wrappers). Keep as `external_body`.
- **Proven**: Function fully verified (no assume(false), no external_body).

## Summary

| Category | Count | Description |
|----------|-------|-------------|
| Proven   | 10    | Real proof, no assume/external_body |
| Tier A   | 20    | Remove assume(false), likely verifiable |
| Tier B   | 20    | Correct body, proof needs complex lemmas |
| Tier C   | 16    | Untranslatable, needs manual impl or TRANSLATE-TODO |
| Helper   | 8     | Trusted clone/filter wrappers |
| **Total** | **74** | (down from 78 at initial audit) |

## Module Breakdown

| Module | Proven | Tier A | Tier B | Tier C | Helper | Total |
|--------|--------|--------|--------|--------|--------|-------|
| acceptor_gen.rs | 5 | 0 | 0 | 0 | 1 | 6 |
| proposer_gen.rs | 0 | 3 | 5 | 3 | 2 | 13 |
| learner_gen.rs | 0 | 0 | 1 | 2 | 3 | 6 |
| election_gen.rs | 3 | 1 | 4 | 3 | 2 | 13 |
| executor_gen.rs | 0 | 2 | 4 | 0 | 1 | 7 |
| replica_gen.rs | 1 | 12 | 5 | 7 | 1 | 26 |
| broadcast_gen.rs | 0 | 0 | 0 | 0 | 0 | 0 |
| types_gen.rs | 0 | 0 | 0 | 0 | 1 | 1 |

---

## Detailed Classification

### acceptor_gen.rs (5 proven, 1 helper)

| Function | Status | Tier | Notes |
|----------|--------|------|-------|
| clone_hashset | external_body | Helper | Trusted clone wrapper |
| CAcceptorInit | proven | Proven | Manual impl via manual_code (Phase 23.3.2) |
| CAcceptorProcess1a | proven | Proven | Manual impl via manual_code (Phase 23.3.2) |
| CAcceptorProcess2a | proven | Proven | Manual impl via manual_code (Phase 23.3.2) |
| CAcceptorProcessHeartbeat | proven | Proven | Manual impl via manual_code (Phase 23.3.2) |
| CAcceptorTruncateLog | proven | Proven | Manual impl via manual_code (Phase 23.3.2) |

### proposer_gen.rs (2 helpers, 9 assume, 3 external_body stubs)

| Function | Status | Tier | Notes |
|----------|--------|------|-------|
| clone_hashset | external_body | Helper | Trusted clone wrapper |
| clone_request_queue | external_body | Helper | Vec clone with mapped view |
| CProposerInit | assume(false) | A | Struct construction; fields match spec directly |
| CProposerProcessRequest | assume(false) | B | HashMap insert + request queue append |
| CProposerMaybeEnterNewViewAndSend1a | assume(false) | B | Broadcast + state transition + concat_vecs |
| CProposerProcess1b | assume(false) | B | HashSet union operations; needs set lemmas |
| CProposerMaybeEnterPhase2 | assume(false) | B | Complex state machine transition + broadcast |
| CProposerNominateNewValueAndSend2a | external_body | C | Complex nomination: truncate queue + broadcast |
| CProposerNominateOldValueAndSend2a | external_body | C | HashSet iteration to find highest proposal |
| CProposerMaybeNominateValueAndSend2a | external_body | C | Multi-branch dispatch to other Nominate functions |
| CProposerProcessHeartbeat | assume(false) | B | ElectionState delegation + conditional logic |
| CProposerCheckForViewTimeout | assume(false) | A | Simple delegation to ElectionState |
| CProposerCheckForQuorumOfViewSuspicions | assume(false) | B | ElectionState + conditional state reset |
| CProposerResetViewTimerDueToExecution | assume(false) | A | Simple delegation pattern |

### learner_gen.rs (3 helpers, 2 external_body stubs, 1 B)

| Function | Status | Tier | Notes |
|----------|--------|------|-------|
| clone_hashset | external_body | Helper | Trusted clone wrapper |
| clone_clearnerstate | external_body | Helper | HashMap clone preserving view |
| filter_clearnerstate | external_body | Helper | HashMap filter with threshold |
| CLearnerProcess2b | external_body | C | Complex HashMap operations + deep view mapping |
| CLearnerForgetDecision | external_body | B | Map remove; may be provable with Verus map lemmas |
| CLearnerForgetOperationsBefore | external_body | C | Quantified filter on map |

### election_gen.rs (3 proven, 2 helpers, 5 assume, 3 external_body stubs)

| Function | Status | Tier | Notes |
|----------|--------|------|-------|
| clone_hashset | external_body | Helper | Trusted clone wrapper |
| clone_requests_received_prev_epochs | external_body | Helper | Vec<CRequest> clone with mapped view |
| CBoundRequestSequence | external_body | C | Upper bound filtering on Vec |
| CComputeSuccessorView | proven | Proven | Verified without assume(false) |
| CRequestsMatch | proven | Proven | Phase 23.3.3: EndPoint PartialEq ensures |
| CRequestSatisfiedBy | proven | Proven | Phase 23.3.3: EndPoint PartialEq ensures |
| CRemoveAllSatisfiedRequestsInSequence | external_body | C | Seq filtering with predicate |
| CElectionStateInit | assume(false) | A | Blocked by Clone infrastructure gap |
| CElectionStateProcessHeartbeat | assume(false) | B | Complex multi-branch logic with HashSet ops |
| CElectionStateCheckForViewTimeout | assume(false) | B | Multi-branch timeout logic |
| CElectionStateCheckForQuorumOfViewSuspicions | assume(false) | B | Quorum verification + state transitions |
| CElectionStateReflectReceivedRequest | external_body | C | Request reflection with seq append |
| CRemoveExecutedRequestBatch | external_body | Helper | Batch removal utility |
| CElectionStateReflectExecutedRequestBatch | assume(false) | B | Delegation to CRemoveExecutedRequestBatch |

### executor_gen.rs (1 helper, 6 assume)

| Function | Status | Tier | Notes |
|----------|--------|------|-------|
| clone_hashset | external_body | Helper | Trusted clone wrapper |
| CExecutorInit | assume(false) | A | Struct construction; needs reply_cache empty map proof |
| CExecutorGetDecision | assume(false) | A | Simple state transition with ballot |
| CExecutorProcessAppStateSupply | assume(false) | B | Message extraction + match arms |
| CExecutorProcessAppStateRequest | assume(false) | B | Conditional ballot comparison + reply generation |
| CExecutorProcessStartingPhase2 | assume(false) | B | Conditional broadcast request |
| CExecutorProcessRequest | assume(false) | B | Cache lookup + conditional reply |

### replica_gen.rs (1 proven, 1 helper, 20 assume, 7 external_body stubs)

| Function | Status | Tier | Notes |
|----------|--------|------|-------|
| clone_hashset | external_body | Helper | Trusted clone wrapper |
| CReplicaInit | assume(false) | A | Delegation to 4 component inits |
| CReplicaNextProcessInvalid | assume(false) | A | No-op; blocked by CReplica.clone() ensures |
| CReplicaNextProcessRequest | assume(false) | B | Cache lookup + conditional delegation |
| CReplicaNextProcess1a | assume(false) | A | Delegation to CAcceptorProcess1a |
| CReplicaNextProcess1b | external_body | C | HashSet for-loop invariant issue |
| CReplicaNextProcessStartingPhase2 | assume(false) | A | Delegation to CExecutorProcessStartingPhase2 |
| CReplicaNextProcess2a | assume(false) | B | Conditional ballot+opn check + delegation |
| CReplicaNextProcess2b | assume(false) | B | Conditional opn+state check + delegation |
| CReplicaNextProcessReply | assume(false) | A | No-op; blocked by CReplica.clone() ensures |
| CReplicaNextProcessAppStateSupply | assume(false) | B | Conditional opn check + multiple delegations |
| CReplicaNextProcessAppStateRequest | assume(false) | A | Delegation to CExecutorProcessAppStateRequest |
| CReplicaNextProcessHeartbeat | assume(false) | B | Multiple delegations to proposer+acceptor |
| CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a | assume(false) | A | Delegation to CProposerMaybeEnterNewViewAndSend1a |
| CReplicaNextSpontaneousMaybeEnterPhase2 | assume(false) | A | Delegation to CProposerMaybeEnterPhase2 |
| CReplicaNextReadClockMaybeNominateValueAndSend2a | assume(false) | A | Delegation to CProposerMaybeNominateValueAndSend2a |
| CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints | external_body | C | Quantified pattern (exists op in checkpoints) |
| CReplicaNextSpontaneousMaybeMakeDecision | assume(false) | B | Quorum check + conditional delegation |
| CReplicaNextSpontaneousMaybeExecute | assume(false) | A | Conditional execution delegation |
| CReplicaNextReadClockMaybeSendHeartbeat | assume(false) | A | Conditional clock check + broadcast |
| CReplicaNextReadClockCheckForViewTimeout | assume(false) | A | Delegation to CProposerCheckForViewTimeout |
| CReplicaNextReadClockCheckForQuorumOfViewSuspicions | assume(false) | A | Delegation to CProposerCheckForQuorumOfViewSuspicions |
| CReplicaNumActions | proven | Proven | Phase 23.5: trivial constant (10) |
| CSchedulerInit | assume(false) | A | Delegation to CReplicaInit |
| CReplicaNextReadClockAndProcessPacket | external_body | C | IO dispatch (requires manual impl) |
| CReplicaNextProcessPacketWithoutReadingClock | external_body | C | IO dispatch (requires manual impl) |
| CReplicaNextProcessPacket | external_body | C | IO dispatch (requires manual impl) |
| CReplicaNoReceiveNext | external_body | C | Scheduler dispatch (requires manual impl) |
| CSchedulerNext | external_body | C | Scheduler dispatch (requires manual impl) |

### types_gen.rs

| Function | Status | Tier | Notes |
|----------|--------|------|-------|
| unreachable_value | external_body | Helper | requires false; panic helper |

---

## Key Blockers

### Clone Infrastructure Gap
Many Tier A functions use `.clone()` on struct types (CReplica, CElectionState) where Clone
doesn't have View-preserving ensures. The `clone_up_to_view()` methods exist with ensures,
but the transpiler generates `.clone()`. CReplicaConstants now has a verified manual Clone
impl with ensures (Phase 23.5), which is a partial fix.

### Remaining work to unlock more proofs:
1. Add verified Clone ensures to CReplica (contains HashSet fields — needs external_body)
2. Add verified Clone ensures to CElectionState (has external_body Clone already)
3. Prove `abstractify_creplycache(HashMap::new()) == Map::empty()` for CExecutorInit
4. Fix transpiler to regenerate replica_gen.rs correctly (broken stubs with ios@ type)

## Verification Metrics

| Metric | Phase 21 | Phase 23 Start | Phase 23 End |
|--------|----------|----------------|--------------|
| Verified | 570 | 560 | 570 |
| Errors | 0 | 6 | 0 |
| assume(false) | 42 | 42 | 40 |
| external_body stubs | 30 | 30 | 28 |
| Transpiler tests | ~1800 | ~1800 | 1871 |

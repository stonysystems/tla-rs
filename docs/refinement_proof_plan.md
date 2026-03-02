# RSL Refinement Proof Plan — Phase 31

## Overview

28 `#[verifier::external_body]` proof functions across 8 files form the trusted base
of the RSL refinement proof. All helper functions they call are already proven.
This document maps dependencies, classifies difficulty, and proposes an attack order.

## Master Table

### refinement_proof/chosen.rs (4 lemmas) — ALL VERIFIED

| # | Name | What it proves | Difficulty | Status |
|---|------|----------------|------------|--------|
| 1 | `lemma_GetSequenceOfRequestBatches` | `GetSequenceOfRequestBatches(qs).len() == qs.len()` | LOW | DONE |
| 2 | `lemma_GetMaximalQuorumOf2bsSequenceWithinBound` | Constructs maximal quorum sequence up to bound | LOW | DONE |
| 3 | `lemma_TwoMaximalQuorumsOf2bsMatch` | Two maximal sequences produce same request batches | MEDIUM | DONE |
| 4 | `lemma_RegularQuorumOf2bSequenceIsPrefixOfMaximalQuorumOf2bSequence` | Valid sequence is prefix of maximal | MEDIUM | DONE |

### refinement_proof/requests.rs (5 lemmas)

| # | Name | What it proves | Difficulty |
|---|------|----------------|------------|
| 5 | `lemma_RequestInRequestsReceivedThisEpochHasCorrespondingRequestMessage` | Request in this_epoch → client sent it | MEDIUM (has assume) |
| 6 | `lemma_RequestInRequestsReceivedPrevEpochsHasCorrespondingRequestMessage` | Request in prev_epochs → client sent it | MEDIUM |
| 7 | `lemma_RequestInRequestQueueHasCorrespondingRequestMessage` | Request in queue → client sent it | MEDIUM |
| 8 | `lemma_RequestIn2aMessageHasCorrespondingRequestMessage` | Request in 2a → client sent it | HIGH (recursive + 1b chain) |
| 9 | `lemma_DecidedRequestWasSentByClient` | Decided request → client sent it | MEDIUM |

### refinement_proof/execution.rs (6 lemmas)

| # | Name | What it proves | Difficulty |
|---|------|----------------|------------|
| 10 | `lemma_AppStateAlwaysValid` | Executor app state = GetAppStateFromRequestBatches(chosen) | HIGH (mutual w/ #11) |
| 11 | `lemma_TransferredStateAlwaysValid` | AppStateSupply packet carries correct app state | HIGH (mutual w/ #10) |
| 12 | `lemma_ReplySentIsAllowed` | Every Reply packet is justified by some quorum sequence | HIGH |
| 13 | `lemma_ReplyInReplyCacheIsAllowed` | Reply cache entries are justified | HIGH (mutual w/ #14) |
| 14 | `lemma_ReplyInAppStateSupplyIsAllowed` | AppStateSupply reply cache is justified | HIGH (mutual w/ #13) |
| 15 | `lemma_ReplySentViaExecutionIsAllowed` | Fresh execution replies are justified | HIGH |

### refinement_proof/refinement.rs (5 lemmas)

| # | Name | What it proves | Difficulty |
|---|------|----------------|------------|
| 16 | `lemma_FirstProduceIntermediateAbstractStateProducesAbstractState` | drop_last batches = intermediate(batches, 0) | MEDIUM (set ext.) |
| 17 | `lemma_LastProduceIntermediateAbstractStateProducesAbstractState` | full batches = intermediate(batches, last.len()) | MEDIUM (has `/* fails */`) |
| 18 | `lemma_GetBehaviorRefinementForBehaviorOfOneStep` | Initial state satisfies refinement | LOW |
| 19 | `lemma_DemonstrateRslSystemNextWhenBatchesAdded` | Batch growth → abstract RslSystemNext | MEDIUM |
| 20 | `lemma_GetBehaviorRefinement` | Top-level refinement theorem | MEDIUM (wrapper) |

### common_proof/chosen.rs (3 lemmas) — 2/3 VERIFIED

| # | Name | What it proves | Difficulty | Status |
|---|------|----------------|------------|--------|
| 21 | `lemma_ChosenQuorumAnd2aFromLaterBallotMatchValues` | Quorum + later-ballot 2a → same value (Paxos safety core) | VERY HIGH | BLOCKED — 2 assume stmts on choose expressions |
| 22 | `lemma_DecidedOperationWasChosen` | OutstandingOpKnown → valid quorum of 2bs exists | HIGH | DONE |
| 23 | `collect_2b_messages` | Collects 2b packets from learner state per sender | MEDIUM | DONE |

### common_proof/message2a.rs (1 lemma)

| # | Name | What it proves | Difficulty | Status |
|---|------|----------------|------------|--------|
| 24 | `lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality` | Two 2a msgs, same ballot+opn → same value | HIGH | BLOCKED — assumes the goal + assume(false) |

### common_proof/quorum.rs (2 lemmas) — ALL VERIFIED

| # | Name | What it proves | Difficulty | Status |
|---|------|----------------|------------|--------|
| 25 | `lemma_GetIndicesFromNodes` | Endpoint set → replica index set (preserving cardinality) | MEDIUM | DONE |
| 26 | `lemma_GetIndicesFromPackets` | Packet set → sender index set (preserving cardinality) | MEDIUM | DONE |

### common_proof/learner_state.rs (2 lemmas) — ALL VERIFIED

| # | Name | What it proves | Difficulty | Status |
|---|------|----------------|------------|--------|
| 27 | `lemma_Received2bMessageSendersAlwaysNonempty` | received_2b_message_senders is always non-empty | MEDIUM | DONE |
| 28 | `lemma_GetSent2bMessageFromLearnerState` | Each sender in learner state has a 2b packet in sentPackets | MEDIUM-HIGH | DONE |

## Dependency Graph

```
Legend: A ──→ B means "A calls B"
        A ──⟳ means "A is self-recursive"

┌─────────────────────────────────────────────────────────────────────┐
│  TIER 0: LEAF LEMMAS (no external_body dependencies)               │
│                                                                     │
│  [L1] GetSequenceOfRequestBatches          (chosen.rs:49)           │
│  [L2] TwoMaximalQuorumsOf2bsMatch          (chosen.rs:212)         │
│  [L3] RegularQuorumOf2bSeqIsPrefix...      (chosen.rs:249)         │
│  [L4] FirstProduceIntermediateAbstractState (refinement.rs:172)     │
│  [L5] LastProduceIntermediateAbstractState  (refinement.rs:227)     │
│  [L6] GetBehaviorRefinementForOneStep      (refinement.rs:284)     │
│  [L7] GetIndicesFromNodes                  (quorum.rs:27)           │
│  [L8] 2aMessagesSameBallotOpMatchWLOG      (message2a.rs:248)      │
│  [L9] Received2bMsgSendersAlwaysNonempty   (learner_state.rs:67)   │
│  [L10] GetMaximalQuorum2bsSeqWithinBound   (chosen.rs:134)  ⟳     │
│  [L11] RequestInRequestsReceivedThisEpoch  (requests.rs:36)  ⟳    │
└─────────────────────────────────────────────────────────────────────┘
           │
           ▼
┌─────────────────────────────────────────────────────────────────────┐
│  TIER 1: depend only on Tier 0                                      │
│                                                                     │
│  [T1] GetIndicesFromPackets                (quorum.rs:72)           │
│       └── calls [L7]                                                │
│  [T2] GetSent2bMsgFromLearnerState         (learner_state.rs:106)  │
│       └── calls [L9]  ⟳                                            │
│  [T3] RequestInRequestsReceivedPrevEpochs  (requests.rs:91)        │
│       └── calls [L11]  ⟳                                           │
│  [T4] DemonstrateRslSystemNextBatchesAdded (refinement.rs:354)     │
│       └── calls [L4], [L5]  ⟳                                      │
└─────────────────────────────────────────────────────────────────────┘
           │
           ▼
┌─────────────────────────────────────────────────────────────────────┐
│  TIER 2: depend on Tier 0-1                                         │
│                                                                     │
│  [U1] ChosenQuorumAnd2aFromLaterBallotMatch (c_p/chosen.rs:98)     │
│       └── calls [T1]  ⟳                                             │
│  [U2] collect_2b_messages                   (c_p/chosen.rs:247)    │
│       └── calls [T2]  ⟳                                             │
│  [U3] RequestInRequestQueue                 (requests.rs:145)      │
│       └── calls [L11], [T3]  ⟳                                     │
│  [U4] GetBehaviorRefinement                 (refinement.rs:452)    │
│       └── calls NO ext_body directly (calls proven                  │
│           GetBehaviorRefinementForPrefix, which calls [L3],[L6],    │
│           [T4]); proof body is trivial assembly                     │
└─────────────────────────────────────────────────────────────────────┘
           │
           ▼
┌─────────────────────────────────────────────────────────────────────┐
│  TIER 3: depend on Tier 0-2                                         │
│                                                                     │
│  [V1] DecidedOperationWasChosen             (c_p/chosen.rs:186)    │
│       └── calls [L7], [U2]  ⟳                                      │
│  [V2] RequestIn2aMessage                    (requests.rs:232)      │
│       └── calls [U3]  ⟳                                             │
└─────────────────────────────────────────────────────────────────────┘
           │
           ▼
┌─────────────────────────────────────────────────────────────────────┐
│  TIER 4: depend on Tier 0-3                                         │
│                                                                     │
│  [W1] AppStateAlwaysValid                   (execution.rs:43)      │
│       └── calls [W2], [V1]  ⟳                                      │
│  [W2] TransferredStateAlwaysValid           (execution.rs:90)      │
│       └── calls [W1]  ⟳  (MUTUAL RECURSION with W1)                │
│  [W3] DecidedRequestWasSentByClient         (requests.rs:299)      │
│       └── calls [V2]                                                │
└─────────────────────────────────────────────────────────────────────┘
           │
           ▼
┌─────────────────────────────────────────────────────────────────────┐
│  TIER 5: depend on Tier 0-4                                         │
│                                                                     │
│  [X1] ReplySentViaExecutionIsAllowed        (execution.rs:307)     │
│       └── calls [W1], [V1]                                          │
│  [X2] ReplyInReplyCacheIsAllowed            (execution.rs:186)     │
│       └── calls [W1], [V1], [X3]  ⟳                                │
│  [X3] ReplyInAppStateSupplyIsAllowed        (execution.rs:257)     │
│       └── calls [X2]  ⟳                                             │
│  [X4] ReplySentIsAllowed                    (execution.rs:127)     │
│       └── calls [X1], [X2]  ⟳                                      │
└─────────────────────────────────────────────────────────────────────┘
```

## Per-Lemma Classification

### Class A — Straightforward induction / algebraic
These have mostly-complete proof bodies already written; removing `external_body` may
Just Work or need minor Verus trigger hints.

| # | Lemma | File:Line | Difficulty | Notes |
|---|-------|-----------|------------|-------|
| L1 | `lemma_GetSequenceOfRequestBatches` | ref/chosen.rs:49 | **Easy** | Simple induction on `qs.len()`, body is empty — just add `decreases qs.len()` + recursive call |
| L4 | `lemma_FirstProduceIntermediateAbstractState` | ref/refinement.rs:172 | **Medium** | Algebraic; body has `assert forall` blocks, Set equality. May need trigger tuning. |
| L5 | `lemma_LastProduceIntermediateAbstractState` | ref/refinement.rs:227 | **Medium** | Similar algebraic. Has `/* fails */` comment on `assert(rs_prime.app == rs.app)` — needs `HandleRequestBatch` unfolding. |
| L6 | `lemma_GetBehaviorRefinementForOneStep` | ref/refinement.rs:284 | **Easy** | Base case; body constructs init state, uses contradiction for non-empty quorum at step 0. |
| U4 | `lemma_GetBehaviorRefinement` | ref/refinement.rs:452 | **Easy** | Trivial: calls `ConvertBehaviorSeqToImap_ensures` + `GetBehaviorRefinementForPrefix`. |

### Class B — Induction with complex case splits or auxiliary reasoning
These have substantial proof scaffolding but need case analysis on protocol actions.

| # | Lemma | File:Line | Difficulty | Notes |
|---|-------|-----------|------------|-------|
| L2 | `lemma_TwoMaximalQuorumsOf2bsMatch` | ref/chosen.rs:212 | **Medium** | Induction on seq length, calls proven `lemma_ChosenQuorumsMatchValue` per slot |
| L3 | `lemma_RegularQuorumOf2bSeqIsPrefix` | ref/chosen.rs:249 | **Medium** | Induction using uniqueness of chosen values |
| L7 | `lemma_GetIndicesFromNodes` | c_p/quorum.rs:27 | **Medium** | Set mapping + cardinality; body is nearly complete, needs `lemma_MapSetCardinalityOver` to discharge |
| L8 | `lemma_2aMessagesSameBallotOpMatchWLOG` | c_p/message2a.rs:248 | **Medium** | Induction on `i`, calls proven `lemma_2aMessagesFromSameBallotAndOperationMatch` |
| L9 | `lemma_Received2bMsgSendersAlwaysNonempty` | c_p/learner_state.rs:67 | **Medium** | Induction on `i`, case split on learner actions |
| L10 | `lemma_GetMaximalQuorum2bsSeqWithinBound` | ref/chosen.rs:134 | **Medium** | Recursive construction with `IsValidQuorumOf2bs` decision at each slot |
| L11 | `lemma_RequestInRequestsReceivedThisEpoch` | ref/requests.rs:36 | **Hard** | Induction on `i`, case split on election/proposer actions, tracks request through epoch |
| T1 | `lemma_GetIndicesFromPackets` | c_p/quorum.rs:72 | **Medium** | Builds on [L7]; body has set mapping structure |
| T2 | `lemma_GetSent2bMsgFromLearnerState` | c_p/learner_state.rs:106 | **Hard** | Induction on `i`, case analysis on all actions that modify learner state |
| T3 | `lemma_RequestInRequestsReceivedPrevEpochs` | ref/requests.rs:91 | **Hard** | Similar to L11, epoch boundary handling |
| T4 | `lemma_DemonstrateRslSystemNextBatchesAdded` | ref/refinement.rs:354 | **Medium** | Induction on `batches_prime.len()`, calls [L4]+[L5]+proven helper |
| U1 | `lemma_ChosenQuorumAnd2aFromLaterBallotMatch` | c_p/chosen.rs:98 | **Hard** | Core Paxos safety; induction on ballot, quorum intersection reasoning |
| U2 | `collect_2b_messages` | c_p/chosen.rs:247 | **Medium** | Recursive construction, delegates real work to [T2] |
| U3 | `lemma_RequestInRequestQueue` | ref/requests.rs:145 | **Hard** | Induction on `i`, case split on proposer queue mutations |
| V1 | `lemma_DecidedOperationWasChosen` | c_p/chosen.rs:186 | **Hard** | Core quorum reasoning; needs subset cardinality + 2b collection |
| V2 | `lemma_RequestIn2aMessage` | ref/requests.rs:232 | **Hard** | Traces request through 1b→2a message chain |
| W1 | `lemma_AppStateAlwaysValid` | ref/execution.rs:43 | **Hard** | Main workhorse; mutual recursion with [W2], case split on action index |
| W2 | `lemma_TransferredStateAlwaysValid` | ref/execution.rs:90 | **Hard** | Mutual recursion with [W1], traces AppStateSupply packets |
| W3 | `lemma_DecidedRequestWasSentByClient` | ref/requests.rs:299 | **Medium** | Combines [V2] with quorum extraction |

### Class C — Mutual recursion / complex composition
These combine multiple hard lemmas and may stress Verus's termination checker.

| # | Lemma | File:Line | Difficulty | Notes |
|---|-------|-----------|------------|-------|
| X1 | `lemma_ReplySentViaExecutionIsAllowed` | ref/execution.rs:307 | **Hard** | Combines [W1] + [V1] + `HandleRequestBatch` reasoning |
| X2 | `lemma_ReplyInReplyCacheIsAllowed` | ref/execution.rs:186 | **Hard** | Induction, calls [W1]+[V1]+[X3]; mutual with [X3] |
| X3 | `lemma_ReplyInAppStateSupplyIsAllowed` | ref/execution.rs:257 | **Hard** | Mutual recursion with [X2] |
| X4 | `lemma_ReplySentIsAllowed` | ref/execution.rs:127 | **Hard** | Dispatches to [X1]+[X2]; top-level reply safety |

## Recommended Attack Order

### Wave 1 — Quick wins (5 lemmas, est. low risk)
1. **L1** `GetSequenceOfRequestBatches` — trivial induction
2. **L6** `GetBehaviorRefinementForBehaviorOfOneStep` — base case, body already written
3. **U4** `GetBehaviorRefinement` — trivial delegation
4. **L7** `GetIndicesFromNodes` — body nearly complete
5. **T1** `GetIndicesFromPackets` — builds on L7

### Wave 2 — Algebraic + chosen sequence (7 lemmas)
6. **L4** `FirstProduceIntermediateAbstractState` — algebraic, body present
7. **L5** `LastProduceIntermediateAbstractState` — algebraic, has known `/* fails */`
8. **T4** `DemonstrateRslSystemNextWhenBatchesAdded` — induction on batch count
9. **L2** `TwoMaximalQuorumsOf2bsMatch` — uses proven helper
10. **L3** `RegularQuorumOf2bSeqIsPrefix` — uses proven helper
11. **L10** `GetMaximalQuorum2bsSeqWithinBound` — recursive construction
12. **L8** `2aMessagesSameBallotOpMatchWLOG` — induction, calls proven helper

### Wave 3 — Common proof core (5 lemmas)
13. **L9** `Received2bMsgSendersAlwaysNonempty` — learner state induction
14. **T2** `GetSent2bMsgFromLearnerState` — depends on L9
15. **U2** `collect_2b_messages` — depends on T2
16. **U1** `ChosenQuorumAnd2aFromLaterBallotMatch` — Paxos safety core
17. **V1** `DecidedOperationWasChosen` — quorum reasoning

### Wave 4 — Request tracking (5 lemmas)
18. **L11** `RequestInRequestsReceivedThisEpoch` — induction + epoch
19. **T3** `RequestInRequestsReceivedPrevEpochs` — depends on L11
20. **U3** `RequestInRequestQueue` — depends on L11, T3
21. **V2** `RequestIn2aMessage` — depends on U3
22. **W3** `DecidedRequestWasSentByClient` — combines V2 + quorum

### Wave 5 — Execution + reply safety (6 lemmas)
23. **W1** `AppStateAlwaysValid` — mutual recursion with W2
24. **W2** `TransferredStateAlwaysValid` — mutual recursion with W1
25. **X1** `ReplySentViaExecutionIsAllowed` — combines W1 + V1
26. **X3** `ReplyInAppStateSupplyIsAllowed` — mutual with X2
27. **X2** `ReplyInReplyCacheIsAllowed` — mutual with X3
28. **X4** `ReplySentIsAllowed` — top-level dispatch

## Known Risks

1. **`/* fails */` in L5**: `assert(rs_prime.app == rs.app)` — needs `GetAppStateFromRequestBatches` / `HandleRequestBatch` unfolding at batch boundary. May require auxiliary lemma about `HandleRequestBatch` identity when request count is 0.

2. **Mutual recursion (W1↔W2, X2↔X3)**: Verus needs explicit `decreases` clauses. The existing code uses `decreases i` which should work since both recurse on `i-1`, but Verus may need `decreases i, 1` / `decreases i, 0` for lexicographic ordering to prove termination of mutual recursion pairs.

3. **`lemma_MapSetCardinalityOver` dependency**: Used in L7 and T1; it's proven in `src/common/collections/sets.rs` but its spec requires a bijection proof that may be hard to assemble for certain set constructions.

4. **`choose` operator in proof bodies**: Several lemmas use `choose` to pick witnesses. In Verus, `choose` may require explicit witness construction (via `assert exists ... by { ... }`) rather than bare `choose`.

5. **Set extensionality (`=~=`)**: Algebraic lemmas L4/L5 assert set equality via subset reasoning. Verus may need explicit `=~=` instead of `==` for extensional equality of Sets.

## File Locations

| File | ext_body count | IDs |
|------|---------------|-----|
| `src/protocol/RSL/refinement_proof/chosen.rs` | 4 | L1, L2, L3, L10 |
| `src/protocol/RSL/refinement_proof/requests.rs` | 5 | L11, T3, U3, V2, W3 |
| `src/protocol/RSL/refinement_proof/execution.rs` | 6 | W1, W2, X1, X2, X3, X4 |
| `src/protocol/RSL/refinement_proof/refinement.rs` | 5 | L4, L5, L6, T4, U4 |
| `src/protocol/RSL/common_proof/learner_state.rs` | 2 | L9, T2 |
| `src/protocol/RSL/common_proof/quorum.rs` | 2 | L7, T1 |
| `src/protocol/RSL/common_proof/chosen.rs` | 3 | U1, V1, U2 |
| `src/protocol/RSL/common_proof/message2a.rs` | 1 | L8 |

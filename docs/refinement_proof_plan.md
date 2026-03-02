# RSL Refinement Proof — external_body Elimination Plan

## Overview

The RSL refinement proof (`src/protocol/RSL/refinement_proof/`) contains 20 `external_body` proof
functions, and the supporting `common_proof/` has 8 more (total 28). These are trusted stubs
inherited from the Dafny→Verus port. This document maps their dependencies and plans the
bottom-up order of attack to fill in real proof bodies.

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

### common_proof/chosen.rs (3 lemmas)

| # | Name | What it proves | Difficulty |
|---|------|----------------|------------|
| 21 | `lemma_ChosenQuorumAnd2aFromLaterBallotMatchValues` | Quorum + later-ballot 2a → same value (Paxos safety core) | VERY HIGH |
| 22 | `lemma_DecidedOperationWasChosen` | OutstandingOpKnown → valid quorum of 2bs exists | HIGH |
| 23 | `collect_2b_messages` | Collects 2b packets from learner state per sender | MEDIUM |

### common_proof/message2a.rs (1 lemma)

| # | Name | What it proves | Difficulty |
|---|------|----------------|------------|
| 24 | `lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality` | Two 2a msgs, same ballot+opn → same value | HIGH (has assume(false)) |

### common_proof/quorum.rs (2 lemmas)

| # | Name | What it proves | Difficulty |
|---|------|----------------|------------|
| 25 | `lemma_GetIndicesFromNodes` | Endpoint set → replica index set (preserving cardinality) | MEDIUM |
| 26 | `lemma_GetIndicesFromPackets` | Packet set → sender index set (preserving cardinality) | MEDIUM |

### common_proof/learner_state.rs (2 lemmas)

| # | Name | What it proves | Difficulty |
|---|------|----------------|------------|
| 27 | `lemma_Received2bMessageSendersAlwaysNonempty` | received_2b_message_senders is always non-empty | MEDIUM |
| 28 | `lemma_GetSent2bMessageFromLearnerState` | Each sender in learner state has a 2b packet in sentPackets | MEDIUM-HIGH |

## Dependency Graph

```
Tier 1 (LEAVES - no external_body dependencies):
  #1  lemma_GetSequenceOfRequestBatches
  #2  lemma_GetMaximalQuorumOf2bsSequenceWithinBound
  #5  lemma_RequestInRequestsReceivedThisEpochHasCorrespondingRequestMessage (self-recursive)
  #16 lemma_FirstProduceIntermediateAbstractStateProducesAbstractState
  #17 lemma_LastProduceIntermediateAbstractStateProducesAbstractState
  #18 lemma_GetBehaviorRefinementForBehaviorOfOneStep
  #25 lemma_GetIndicesFromNodes
  #27 lemma_Received2bMessageSendersAlwaysNonempty (self-recursive)

Tier 2 (depend on Tier 1):
  #3  → #1
  #4  → #1
  #6  → #5
  #26 → #25
  #28 → #27

Tier 3 (depend on Tier 2):
  #7  → #5, #6
  #23 → #28
  #19 → #16, #17

Tier 4 (depend on Tier 3):
  #8  → #7 (+ self-recursive via lemma_RequestIn1bMessage...)
  #22 → #23, #25

Tier 5 (depend on Tier 4):
  #9  → #8, #1
  #24 → (uses verified wrapper that calls back; has assume(false))

Tier 6 (depend on Tier 5):
  #21 → #26; indirectly #24 via verified wrappers (CORE PAXOS SAFETY)

Tier 7 (depend on Tier 6):
  #10 ↔ #11 (mutual recursion), both → #22
  #15 → #10, #22

Tier 8 (depend on Tier 7):
  #13 ↔ #14 (mutual recursion), #13 → #10, #22
  #12 → #13, #15

Tier 9 (top level):
  #20 → everything transitively
```

## Mutual Recursion Pairs

Two pairs must be tackled together:
1. **#10 / #11**: `lemma_AppStateAlwaysValid` ↔ `lemma_TransferredStateAlwaysValid`
2. **#13 / #14**: `lemma_ReplyInReplyCacheIsAllowed` ↔ `lemma_ReplyInAppStateSupplyIsAllowed`

## Classification

### (A) Straightforward induction — likely completable
- #1, #2, #18 (LOW difficulty leaves)
- #3, #4 (per-element agreement via existing `lemma_ChosenQuorumsMatchValue`)
- #6, #7 (follow #5 pattern)
- #9, #19 (assembly lemmas using verified sublemmas)
- #25, #26, #27 (set reasoning / induction)

### (B) Needs careful proof engineering — completable with effort
- #5 (has one assume about packet being in sentPackets — may need IO invariant)
- #8 (complex recursive chain through 1b messages)
- #10, #11 (mutual recursion, needs simultaneous induction or decreases clause)
- #12, #13, #14, #15 (execution layer, depends on #10 pair)
- #16, #17 (set extensionality — #17 has known `/* fails */` on app state equality)
- #22, #23, #28 (learner state → quorum construction)

### (C) Likely hardest / may hit Verus limitations
- #21 `lemma_ChosenQuorumAnd2aFromLaterBallotMatchValues` — core Paxos safety induction on
  ballot ordering; has 2 assume statements; requires complex nested induction
- #24 `lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality` — has
  `assume(false)` at line 304; needs WLOG reasoning which Verus may not support natively
- #20 `lemma_GetBehaviorRefinement` — requires Seq↔IMap conversion reasoning

## Suggested Attack Order

1. **Quick wins** (Tier 1 leaves): #1, #2, #18, #25, #27
2. **Algebraic lemmas**: #16, #17, #26
3. **Request tracing chain**: #5 → #6 → #7 → #8 → #9
4. **Learner/quorum chain**: #28 → #23 → #22
5. **Paxos core**: #24, #21, #3, #4
6. **Execution layer**: #10/#11 (mutual pair), #15, #13/#14 (mutual pair), #12
7. **Top-level assembly**: #19, #20

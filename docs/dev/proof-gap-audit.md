# RSL Proof Gap Audit (Phase 21.4)

Generated: 2026-02-20
Baseline: 570 verified, 0 errors (Phase 21.3)

## Summary

| Category | Count | Improvement Path |
|----------|-------|-----------------|
| Translation gaps (structural) | 3 | Quantifier elimination / predicate codegen |
| Manual proofs (acceptor + executor) | 20 | Keep as-is (fully verified) |
| Recursive/filter functions | 3 | Recursive function codegen |
| Complex existential quantifiers | 3 | Variable scoping + quantifier codegen |
| Trusted enum patterns | 2 | `is`/`->` in exec context |
| **Total gaps** | **31** | |

## Translation Gaps (3)

These cannot be auto-transpiled due to fundamental structural limitations:

| Function | Module | Root Cause |
|----------|--------|------------|
| `LLearnerForgetOperationsBefore` | learner | Output param assigned inside quantifier body |
| `IsLogTruncationPointValid` | acceptor | Pure predicate — no output parameters |
| `LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints` | replica | Output param assigned inside quantifier body |

**Improvement**: Teach transpiler to convert `exists |x| ... s' = f(x)` into executable search loops. Estimated effort: medium. Would unblock 2 functions.

## Proof Gaps by Module (28)

### Acceptor (7 functions) — DEFERRED: fully verified proofs

All 7 acceptor functions have **fully verified proofs** with no assumes. They are in `acceptor_manual.rs` because the proofs are too complex for auto-generation (map_fields lemmas, clone_hashset, filter invariants).

| Function | Root Cause |
|----------|------------|
| `RemoveVotesBeforeLogTruncationPoint` | HashMap filter + clone_hashset proof |
| `LAddVoteAndRemoveOldOnes` | Composed HashMap + validity proof |
| `LAcceptorInit` | Empty-map abstractify proof |
| `LAcceptorProcess1a` | Ballot comparison + state proof |
| `LAcceptorProcess2a` | Vote insertion + map proof |
| `LAcceptorProcessHeartbeat` | Trivial but needs map proof |
| `LAcceptorTruncateLog` | HashMap filter iteration proof |

**Improvement**: Not planned — these proofs are already correct and verified.

### Executor (11 functions) — DEFERRED: fully verified proofs

All 11 executor functions have **fully verified proofs**. They are in `executor_manual.rs` with complex map/seq/cache proofs.

| Function | Root Cause |
|----------|------------|
| `LExecutorInit` | Empty cache abstractify proof |
| `LExecutorGetDecision` | Map lookup + option matching |
| `GetPacketsFromReplies` | Complex seq map expression |
| `LClientsInReplies` | Seq filter predicate |
| `RepliesAreReplyType` | Spec-only predicate (no exec needed) |
| `UpdateNewCache` | HashMap update + abstractify proof |
| `LExecutorExecute` | Variable scoping (app state binding) |
| `LExecutorProcessAppStateSupply` | Complex state reconstruction proof |
| `LExecutorProcessAppStateRequest` | Packet construction proof |
| `LExecutorProcessStartingPhase2` | Trivial but coupled proof |
| `LExecutorProcessRequest` | Request batch proof |

**Improvement**: Not planned — these proofs are already correct and verified.

### Election (4 functions)

| Function | Root Cause |
|----------|------------|
| `BoundRequestSequence` | Trusted enum `is`/`->` on CUpperBound |
| `RemoveAllSatisfiedRequestsInSequence` | Recursive filter — for-loop loses assume(false) |
| `RemoveExecutedRequestBatch` | Recursive filter — for-loop loses assume(false) |
| `ElectionStateReflectReceivedRequest` | `for ... in iter:` loop invariant checked independently of assume(false) |

**Improvement**: (1) Handle trusted enum destructuring in exec code; (2) Fix recursive function codegen to preserve assume wrapping; (3) Fix `for ... in iter:` invariant generation. Would unblock all 4.

### Proposer (3 functions)

| Function | Root Cause |
|----------|------------|
| `LProposerNominateNewValueAndSend2a` | Complex variable scoping + nested index |
| `LProposerNominateOldValueAndSend2a` | Existential quantifier + HashSet iteration |
| `LProposerMaybeNominateValueAndSend2a` | Dispatcher with complex branching |

**Improvement**: Fix variable scoping in multi-assignment blocks; add existential-to-loop conversion. Would unblock all 3.

### Learner (2 functions)

| Function | Root Cause |
|----------|------------|
| `LLearnerProcess2b` | Trusted enum destructuring in exec |
| `LLearnerForgetDecision` | Trusted enum destructuring in exec |

**Improvement**: Handle `#[verus::trusted]` enum `is`/`->` → `match` in exec context. Would unblock both.

### Broadcast (1 function)

| Function | Root Cause |
|----------|------------|
| `BuildLBroadcast` | Complex recursive function |

**Improvement**: Add recursive function codegen. Would unblock 1.

### Replica (0 proof gaps)

All replica functions are either auto-transpiled (20), stubbed (1), or manual IO dispatch (9).

## Categorized Improvement Roadmap

### High Impact: Trusted enum exec codegen
- **Functions unblocked**: 6 (2 learner + 4 election including BoundRequestSequence)
- **Approach**: Convert `value is Variant` and `value->field` to `match` patterns in exec context
- **Complexity**: Medium

### Medium Impact: Recursive function codegen
- **Functions unblocked**: 4 (3 election + 1 broadcast)
- **Approach**: Detect recursive spec functions, generate iterative exec equivalents with loop invariants
- **Complexity**: High

### Medium Impact: Variable scoping + existential elimination
- **Functions unblocked**: 3 (proposer Nominate functions)
- **Approach**: Track variable lifetimes across nested blocks; convert `exists` to search loops
- **Complexity**: High

### Low Priority: Quantifier body assignment
- **Functions unblocked**: 2 (learner ForgetOperationsBefore + replica TruncateLog)
- **Approach**: Convert `exists |x| ... s' = f(x)` to executable search pattern
- **Complexity**: Medium

### Not Planned: Verified manual proofs
- **Functions**: 18 (7 acceptor + 11 executor)
- **Rationale**: Already fully verified with hand-written proofs. Moving to auto-generation would regress proof quality.

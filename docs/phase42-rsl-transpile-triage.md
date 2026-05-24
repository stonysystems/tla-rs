# Phase 42.1.a: RSL Transpile Triage Results

Date: 2026-05-24

## Summary

All 8 RSL modules transpile successfully (exit 0). The "function dropping" issue is a
pre-existing transpiler capability gap, NOT caused by Phase 40 Arc codegen.

## Results by Module

| Module | Existing Functions | Fresh Output | Intentionally Skipped | Genuinely Dropped |
|--------|-------------------|--------------|-----------------------|-------------------|
| acceptor | 5 | 5 | 0 | 0 |
| proposer | 12 | 9 | 3 | 0 |
| learner | 4 | 2 | 1 | **1** |
| executor | 7 | 6 | 1 | 0 |
| replica | 21 | 14 | 6 | **1** |
| election | 12 | 10 | 2 | 0 |
| broadcast | 1 | 1 | 0 | 0 |

## Genuinely Dropped Functions (2)

### CLearnerForgetOperationsBefore (learner)

Spec body uses quantified map filtering:
```rust
forall |k:OperationNumber| s_.unexecuted_learner_state.contains_key(k) <==>
    k >= ops_complete && s.unexecuted_learner_state.contains_key(k)
```
The transpiler cannot auto-generate executable code for this pattern (requires
iterating over HashMap keys with a filter, which has no direct spec-to-exec
template). The existing generated file has a hand-written implementation using
`filter_clearnerstate()`.

### CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints (replica)

Spec body uses existential quantifier with complex branching:
```rust
exists |opn:OperationNumber| s.acceptor.last_checkpointed_operation.contains(opn)
    && IsLogTruncationPointValid(opn, ...) && if opn > s.acceptor.log_truncation_point { ... }
```
The transpiler cannot resolve the existential witness. The existing generated file
has a hand-written implementation.

## Intentionally Skipped Functions (14)

All are in `skip_functions` in their respective `*_transpile.toml` configs:

- **proposer** (3): CProposerNominateOldValueAndSend2a, CProposerNominateNewValueAndSend2a, CProposerMaybeNominateValueAndSend2a
- **learner** (1): CLearnerProcess2b
- **executor** (1): CExecutorExecute
- **replica** (6): CReplicaNextReadClockAndProcessPacket, CReplicaNextProcessPacketWithoutReadingClock, CReplicaNextProcessPacket, CReplicaNoReceiveNext, CSchedulerNext, CReplicaNextProcess1b
- **election** (2): CBoundRequestSequence, CElectionStateReflectReceivedRequest

## Conclusion

The Phase 42 hypothesis that "Phase 40 transpiler can't regenerate RSL" due to Arc
codegen function-dropping bugs is incorrect. The 2 silently dropped functions are a
pre-existing transpiler capability gap (quantified map filtering, existential witnesses).

Next step (42.1.b): Check whether Arc-related codegen produces incorrect code or
compile errors when the fresh output is placed in the codebase.

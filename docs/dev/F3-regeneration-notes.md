# F3: RSL Module Regeneration Notes

## Date: 2026-01-28

## Summary

All RSL modules have been regenerated with module-specific config files that include:
- Proper custom imports for each module
- `generate_loops_for_verification = true` flag
- Correct type remappings

## Config Files Created

- `src/protocol/RSL/election_transpile.toml`
- `src/protocol/RSL/learner_transpile.toml`
- `src/protocol/RSL/executor_transpile.toml`
- `src/protocol/RSL/proposer_transpile.toml`
- `src/protocol/RSL/replica_transpile.toml`
- `src/protocol/RSL/broadcast_transpile.toml`

## Known Transpiler Limitations

### 1. Self-Referential Pattern (`s_` undefined)

**Files affected:** learner_gen.rs, replica_gen.rs

**Pattern:**
```rust
// In spec:
&&& s_ == LStruct{
    field: s_.field,  // s_ references itself
}
```

**Problem:** The transpiler emits `s_.field` before `s_` is defined.

**Workaround:** These patterns require manual implementation or transpiler enhancement.

### 2. Spec Constraints Emitted as Code

**Files affected:** broadcast_gen.rs

**Pattern:**
```rust
// In spec:
&&& sent_packets.len() == c.replica_ids.len()
&&& (0 <= myidx) && (myidx < c.replica_ids.len())
```

**Problem:** These constraints should be in requires/ensures, not in the function body.

**Status:** Needs transpiler fix to classify constraints vs assignments.

### 3. Sequence Comprehension Uses Iterator Pattern

**Files affected:** broadcast_gen.rs

**Pattern:**
```rust
// Generated:
(0..len).map(|idx| ...).collect()
```

**Problem:** Should generate explicit for loop with invariants for Verus verification.

**Status:** The `generate_loops_for_verification` flag only applies to exists/forall quantifiers,
not to sequence comprehension patterns. Needs additional implementation.

### 4. Map Filter with Biconditional Domain

**Files affected:** learner_gen.rs (LLearnerForgetOperationsBefore)

**Pattern:**
```rust
// In spec:
forall |k| s_.map.contains_key(k) <==> k >= threshold && s.map.contains_key(k)
```

**Problem:** Generates iterator pattern instead of loop, and uses undefined `s_`.

**Status:** Complex pattern that requires manual implementation or major transpiler enhancement.

## Successfully Generated Modules

The following functions generate correct code:

### election_gen.rs
- `CElectionStateInit` - struct initialization
- `CElectionStateProcessHeartbeat` - conditional state update
- `CElectionStateCheckForViewTimeout` - multi-branch conditional
- `CElectionStateCheckForQuorumOfViewSuspicions` - quorum check
- `CElectionStateReflectReceivedRequest` - exists quantifier with loop
- `CElectionStateReflectExecutedRequestBatch` - struct update

### executor_gen.rs
- `CExecutorInit` - struct initialization
- `CExecutorGetDecision` - conditional struct update

### learner_gen.rs (partial)
- `CLearnerInit` - struct initialization
- `CLearnerProcess2b` - multi-branch conditional
- `CLearnerForgetDecision` - map remove

### proposer_gen.rs (partial)
- Multiple functions generate correctly

## Next Steps

1. **F2.6**: Add loop generation for sequence comprehension patterns
2. **Transpiler fix**: Handle self-referential patterns (s_)
3. **Transpiler fix**: Classify spec constraints vs assignments
4. **F4**: Once all modules verify, remove #[cfg(test)] guards

## Verification Status

- Main codebase: 437 verified, 0 errors
- Generated modules: Behind `#[cfg(test)]`, not verified
- Election module with loops: Compiles correctly

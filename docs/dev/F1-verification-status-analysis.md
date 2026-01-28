# F1: Generated Code Verification Status Analysis

**Date**: 2026-01-28
**Task**: Verify current generated code status by removing `#[cfg(test)]` guards and documenting all verification errors.

## Summary

The generated code in `src/generated/RSL/` has **never been verified by Verus**. When the `#[cfg(test)]` guards are removed and Verus is run, the build fails due to:

1. **Environment/Verus version mismatch** (blocking - must fix first)
2. **Transpiler bugs in generated code** (multiple syntax and semantic errors)

## Environment Issue

The current Verus installation has changed since the codebase was last verified:

| Component | Expected | Actual |
|-----------|----------|--------|
| Verus version | 0.2026.01.14.88f7396 | 0.2025.02.26.fe04886 |
| Rust toolchain | 1.80.1 | 1.93.0 |
| Macro path | `::verus_builtin_macros::verus!` | `::builtin_macros::verus!` |

The macro path change in `src/implementation/common/marshalling.rs` (lines 1557, 1700, 1739, 1979, 2018) causes errors:
```
error[E0433]: failed to resolve: could not find `verus_builtin_macros` in the list of imported crates
```

**Recommendation**: Either:
1. Install the correct Verus version (0.2026.01.14) and Rust toolchain (1.80.1)
2. Migrate the codebase to the new Verus API (requires updating macro references)

## Generated Code Bugs

### 1. Undefined Variable `s_` (learner_gen.rs:129)

```rust
CLearner {
    constants: s.constants,
    max_ballot_seen: s.max_ballot_seen,
    unexecuted_learner_state: s_.unexecuted_learner_state,  // BUG: s_ never defined
}
```

**Root cause**: Transpiler fails to capture the computed value from map filter operation and assign it to a local variable.

**Fix needed**: The iterator expression on line 124 should be assigned to a variable, e.g.:
```rust
let new_state = s.unexecuted_learner_state.iter()
    .filter(|(k, _)| *k >= *ops_complete)
    .cloned()
    .collect();
```

### 2. Spec Constraints Emitted as Executable Code (broadcast_gen.rs:28-29)

```rust
(sent_packets.len() == c.replica_ids.len());  // This is a constraint, not code
((0 <= myidx) && (myidx < c.replica_ids.len()));  // This is a constraint, not code
```

**Root cause**: Transpiler incorrectly emits spec-level constraints (length equality, bounds checks) as executable statements.

**Fix needed**: These should be in `ensures` clause or removed entirely since they're already implied by the implementation.

### 3. Raw AST in Requires Clause (executor_gen.rs:177-178)

```rust
requires
    Index(Field(Ident("s"), "reply_cache"), Field(Ident("inp"), "src")) is Reply,
    (inp.msg.get_seqno_req() <= Index(Field(Ident("s"), "reply_cache"), Field(Ident("inp"), "src")).seqno),
```

**Root cause**: Transpiler's `expr_to_requires_string()` doesn't handle complex index expressions properly.

**Fix needed**: Should emit:
```rust
requires
    s.reply_cache[inp.src] is Reply,
    inp.msg.get_seqno_req() <= s.reply_cache[inp.src].seqno,
```

### 4. Comparison in Struct Return (proposer_gen.rs:38-39)

```rust
(CProposer {
    ...fields...
}, (s.incomplete_batch_timer is IncompleteBatchTimerOff))  // BUG: This is a boolean, not the second tuple element
```

**Root cause**: Transpiler incorrectly interprets a spec constraint as part of the return tuple.

**Fix needed**: This comparison should be in ensures clause, not the return value.

### 5. Iterator Patterns Don't Verify in Verus

Multiple files use iterator patterns like:
```rust
s.unexecuted_learner_state.iter()
    .filter(|(k, _)| (k >= ops_complete))
    .cloned()
    .collect()
```

**Issue**: Verus cannot verify iterator chains automatically. The manual implementations use explicit `for` loops with `invariant` clauses.

**Example from manual code** (acceptorimpl.rs):
```rust
let mut new_votes: CVotes = hashmap![];
for (opn, vote) in s.votes.iter() {
    invariant ...
    if *opn >= log_truncation_point {
        new_votes.insert(*opn, vote.clone());
    }
}
```

**Fix needed**: Transpiler should generate loop-based code with invariants, not iterator chains.

## Error Categories

| Category | Count | Files Affected |
|----------|-------|----------------|
| Undefined variables | 1 | learner_gen.rs |
| Spec constraints as code | 2 | broadcast_gen.rs |
| Raw AST in output | 2 | executor_gen.rs |
| Struct/tuple construction errors | 1 | proposer_gen.rs |
| Iterator verification issues | Multiple | All files with map/filter |

## Recommended Fix Priority

1. **High**: Fix environment/Verus version (blocking everything)
2. **High**: Fix undefined variable `s_` bug
3. **High**: Fix raw AST emission in requires clauses
4. **Medium**: Fix spec constraints being emitted as code
5. **Medium**: Fix struct/tuple construction errors
6. **Low**: Convert iterator patterns to verifiable loops (complex, involves adding loop invariant generation)

## Next Steps

1. Update Verus/environment OR migrate codebase to new Verus API
2. Fix transpiler bugs identified above
3. Regenerate all RSL modules
4. Verify each module independently with Verus
5. Remove `#[cfg(test)]` guards permanently once everything verifies

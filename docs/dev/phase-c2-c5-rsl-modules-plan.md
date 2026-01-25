# Phase C2-C5: Generate Other RSL Modules

## Goal
Generate transpiled implementation code for all RSL protocol modules beyond the acceptor.

## Current State
- Acceptor: Already generated (`generated_acceptor_v3.rs`)
- Types: Already generated (`types_gen.rs`)
- Other modules: Transpiler can generate but not yet saved to repo

## Modules to Generate

### C2: Learner Module (~135 LOC)
Source: `src/protocol/RSL/learner.rs`
Functions:
- `CLearnerInit`
- `CLearnerProcess2b`
- `CLearnerForgetDecision`
- `CLearnerForgetOperationsBefore`

### C3: Executor Module (~199 LOC)
Source: `src/protocol/RSL/executor.rs`
Functions:
- `CExecutorInit`
- `CExecutorProcessAppStateSupply`
- `CExecutorProcessAppStateRequest`
- `CExecutorExecute`
- `CExecutorGetDecision`

### C4: Proposer Module (~396 LOC)
Source: `src/protocol/RSL/proposer.rs`
Functions:
- `CProposerInit`
- `CProposerProcess1a`
- `CProposerProcess1b`
- `CProposerProcess2a`
- `CProposerProcess2b`
- `CProposerMaybeEnterNewViewAndSend1a`
- `CProposerMaybeNominateValueAndSend2a`
- `CProposerProcessRequest`
- `CProposerResetViewTimerDueToExecution`
- `CProposerCheckForViewTimeout`
- `CProposerCheckForQuorumOf1bs`

### C5: Replica Module (~682 LOC)
Source: `src/protocol/RSL/replica.rs`
Functions:
- `CReplicaInit`
- `CReplicaNextProcess*` (many dispatch functions)
- `CReplicaNextSpontaneous*` (timer/execution functions)

### Broadcast Module (~38 LOC)
Source: `src/protocol/RSL/broadcast.rs`
Functions:
- `CBroadcastToEveryone`

## Implementation Steps

1. Generate each module using transpiler
2. Save to `src/generated/RSL/` directory
3. Add module to `src/generated/RSL/mod.rs`
4. Run Verus to verify compilation (with existing types)
5. Update TODO.md with completion status

## Known Issues to Watch For

1. **Type name derivation**: `LearnerTuple` → `CearnerTuple` (missing L prefix)
   - Happens when spec type doesn't start with 'L'
   - Manual fix or transpiler enhancement needed

2. **Variable naming**: `s_.field` may reference wrong variable
   - Appears in complex iterator patterns
   - Often generates TODO comments

3. **Iterator patterns**: `.iter().filter().collect()` may need loop conversion
   - Already have loop generation infrastructure
   - May need to enable `generate_loops_for_verification` flag

## Expected Output

```
src/generated/RSL/
├── mod.rs          (exports all modules)
├── types_gen.rs    (existing)
├── acceptor_gen.rs (from existing generated_acceptor_v3.rs)
├── learner_gen.rs
├── executor_gen.rs
├── proposer_gen.rs
├── replica_gen.rs
└── broadcast_gen.rs
```

## Completed [26:01:25]

All RSL modules successfully generated:
- `learner_gen.rs` - 135 LOC (4 functions)
- `executor_gen.rs` - 199 LOC (5 functions)
- `proposer_gen.rs` - 396 LOC (11 functions)
- `replica_gen.rs` - 682 LOC (many dispatch functions)
- `broadcast_gen.rs` - 38 LOC (1 function)

**Bug fixed during generation:**
- `translate_name()` was incorrectly stripping 'L' prefix from words like "LearnerTuple"
- Fix: Only strip prefix if followed by uppercase letter (distinguishes LAcceptor from LearnerTuple)

**Known remaining issues in generated code:**
1. `CLearnerForgetOperationsBefore` has orphaned iterator expression and undefined `s_` variable
2. Some complex map filter patterns generate TODO comments instead of code

## Success Criteria

1. All modules generate without transpiler errors ✅
2. Code compiles with Verus (may have verification warnings) - Deferred (requires manual fixes)
3. Module structure documented in mod.rs ✅
4. TODO.md updated with completion status ✅

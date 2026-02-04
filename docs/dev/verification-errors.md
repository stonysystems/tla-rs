# Verus Verification Errors in Generated Code

This document tracks verification errors found in the transpiler-generated code and the fixes applied.

## Current Status

After configuration improvements, the generated code compiles with Verus but has remaining type-related issues that require deeper transpiler fixes.

## Error Categories

### 1. Unsupported Expressions - FIXED (via skip_functions)

Complex expressions that the transpiler cannot handle are now skipped:

| Function | File | Reason |
|----------|------|--------|
| BuildLBroadcast | broadcast.rs | Complex recursive map expression |
| GetPacketsFromReplies | executor.rs | Map expression with closure |
| LProposerNominateOldValueAndSend2a | proposer.rs | Nested existential with index access |
| LReplicaNextProcessPacketWithoutReadingClock | replica.rs | Complex IO dispatch pattern |
| LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints | replica.rs | Variable scope issues in loop |
| SpontaneousClock | replica.rs | Spec-only extraction function |
| ExtractSentPacketsFromIos | replica.rs | Filter with indexed access |

These functions are marked in `skip_functions` and require manual implementation.

### 2. Missing Function Imports - FIXED (via config updates)

Function paths and imports added to module-specific transpile.toml files:

- `CBroadcastToEveryone` - Added to custom_imports
- `CUpperBoundedAddition` - Added to custom_imports
- `CElectionState*` functions - Added via election_gen imports
- `CIsLogTruncationPointValid` - Added to custom_imports
- `LtUpperBound`, `LeqUpperBound` - Added to custom_imports

### 3. Type Name Mappings - FIXED

Fixed inconsistent type mappings across configs:

| Spec Type | Concrete Type | Notes |
|-----------|---------------|-------|
| RslPacket | CPacket | Was incorrectly CRslPacket in some configs |
| RslMessage | CMessage | Was incorrectly CRslMessage in some configs |
| AbstractEndPoint | EndPoint | Added to proposer config |

### 4. Spec-Only Functions - FIXED (via spec_only_functions)

Functions that should not get C-prefix because they're spec-only:

- `WellFormedLConfiguration`
- `LtUpperBound`, `LeqUpperBound`
- `LSetOfMessage1bAboutBallot`
- `LProposerCanNominateUsingOperationNumber`
- `LAllAcceptorsHadNoProposal`
- `LExistsAcceptorHasProposalLargeThanOpn`

### 5. Method Call Mappings - FIXED

Functions that become method calls on receivers:

| Spec Function | Method | Receiver Arg Index |
|---------------|--------|-------------------|
| LMinQuorumSize | CMinQuorumSize | 0 |
| GetReplicaIndex | CGetReplicaIndex | 1 |
| LReplicaConstantsValid | CReplicaConstantsValid | 0 |
| ElectionStateReflectExecutedRequestBatch | CElectionStateReflectExecutedRequestBatch | 0 |

### 6. Remaining Type Issues - REQUIRES TRANSPILER FIXES

Current errors relate to fundamental type handling:

1. **Primitive type `valid()` calls**: Generated code calls `valid()` on `u64`, `HashMap`, `Vec` which don't have this method
2. **View type mismatches**: `self.votes@` returns `Map<u64, CVote>` but spec expects `Map<int, Vote>`
3. **Missing View implementations**: Need to map `u64` to `int`, `CVote` to `Vote` in view function

These require transpiler improvements to:
- Only generate `valid()` calls for types that have valid predicates
- Generate proper view conversions for primitive types
- Handle the distinction between spec types (int, Map, Seq) and concrete types (u64, HashMap, Vec)

## Config Files Updated

- `src/protocol/RSL/broadcast_transpile.toml`
- `src/protocol/RSL/acceptor_transpile.toml`
- `src/protocol/RSL/proposer_transpile.toml`
- `src/protocol/RSL/learner_transpile.toml`
- `src/protocol/RSL/executor_transpile.toml`
- `src/protocol/RSL/election_transpile.toml`
- `src/protocol/RSL/replica_transpile.toml`

## Next Steps

1. Fix transpiler to handle primitive type valid() generation correctly
2. Fix transpiler to generate proper view function implementations
3. Add support for spec/exec type distinction in generated code

# H6: Remove Manual Implementation Dependencies

## Status: IN PROGRESS - Analysis Complete

## Goal
Make generated code independent from `src/implementation/RSL/` imports.

## Audit Results

### Generated Files and Their Dependencies

| Generated File | Imports from `src/implementation/` |
|----------------|-----------------------------------|
| types_gen.rs | `appinterface::CAppMessage`, `types_i::CRequestBatch` |
| election_gen.rs | `types_i::*`, `cconstants::*`, `cmessage::*`, `cconfiguration::*`, `upper_bound_i::*` |
| broadcast_gen.rs | `cconfiguration::*`, `cconstants::*`, `cmessage::*`, `types_i::*` |
| learner_gen.rs | `cbroadcast::*`, `cconstants::*`, `cmessage::*`, `types_i::*`, `LearnerImpl::CLearner` |
| executor_gen.rs | `cbroadcast::*`, `cconstants::*`, `cmessage::*`, `types_i::*`, `CStateMachine::*`, `ExecutorImpl::CExecutor` |
| proposer_gen.rs | `types_i::*`, `cconstants::*`, `cmessage::*`, `cbroadcast::*`, `ProposerImpl::CProposer`, `ElectionImpl::CElectionState`, `upper_bound_i::*` |
| replica_gen.rs | `types_i::*`, `cconstants::*`, `cmessage::*`, `cbroadcast::*`, `ReplicaModel::*`, plus all *Impl types |

### Categories of Dependencies

#### 1. Infrastructure Types (Shared by All Modules)
- `types_i.rs`: `CBallot`, `CRequest`, `CVote`, `CReply`, `CRequestBatch`, etc.
- `cconstants.rs`: `CConstants`, `CReplicaConstants`
- `cmessage.rs`: `CMessage`, `CPacket`
- `cconfiguration.rs`: `CConfiguration`
- `cbroadcast.rs`: Broadcast helper functions

**Status**: These are infrastructure with marshalling support via `define_struct_and_derive_marshalable!` macro. Cannot easily be generated.

**Recommendation**: Move to a shared location like `src/common/rsl_types/` that both implementation and generated code can import from.

#### 2. Module-Specific State Types
- `ElectionImpl::CElectionState` - State struct for election module
- `LearnerImpl::CLearner` - State struct for learner module
- `ExecutorImpl::CExecutor` - State struct for executor module
- `ProposerImpl::CProposer` - State struct for proposer module

**Status**: These CAN be generated inline using `generate_inline_types = true` config option.

**Current**: `election_gen.rs` already uses `generate_inline_types = true` to generate `CElectionState` inline.

#### 3. Helper Functions/Utilities
- `upper_bound_i::*` - Upper bound functions
- `CStateMachine::*` - State machine helpers

**Status**: Some could be generated, others are complex utilities.

### Recommendations

#### Short-term (Achievable Now)
1. Enable `generate_inline_types = true` for all modules to generate state structs inline
2. Use `src/generated/RSL/types_gen.rs` for shared types instead of implementation where possible
3. Document which imports are infrastructure vs. generated

#### Medium-term (Requires Restructuring)
1. Create `src/common/rsl_types/` directory
2. Move infrastructure types (`CBallot`, `CMessage`, etc.) to shared location
3. Update both implementation and generated code to import from shared location

#### Long-term (Future Work)
1. Generate marshalling support in transpiler
2. Generate all types including infrastructure types
3. True zero-dependency generated code

## Current Blockers

The goal of "ZERO imports from `src/implementation/RSL/`" is aspirational but not immediately achievable because:

1. **Marshalling Macro**: `define_struct_and_derive_marshalable!` provides network serialization support that's critical for the protocol. Generating equivalent code requires implementing the macro's output.

2. **Shared State**: Infrastructure types like `CMessage` are shared between generated code and manual implementations in `ReplicaImpl.rs`, etc. Moving them requires updating all imports.

3. **Complex Enums**: `CMessage` is a large enum with 15+ variants and marshalling support. Generating this is non-trivial.

## Next Steps

Given the analysis, recommend:

1. **H7**: Test election module with current dependencies (partial independence)
2. **H8**: Apply inline type generation to all modules
3. **Future**: Tackle infrastructure type restructuring as separate milestone

## Files Changed
- Updated `election_transpile.toml` to use `generate_inline_types = true` (already done)
- Other modules still need this flag enabled

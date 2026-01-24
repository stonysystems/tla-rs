# Generated Code Integration Guide

## Overview

This document describes how to integrate transpiler-generated code with the existing RSL implementation.

## Current State

The transpiler successfully generates verifiable exec functions for all RSL acceptor predicates:
- `CRemoveVotesBeforeLogTruncationPoint`
- `CAddVoteAndRemoveOldOnes`
- `CAcceptorInit`
- `CAcceptorProcess1a`
- `CAcceptorProcess2a`
- `CAcceptorProcessHeartbeat`
- `CAcceptorTruncateLog`

**Verification Status**: 456 verified, 0 errors (as of 2026-01-25)

## Generated Code Location

- Config: `src/protocol/RSL/transpile.toml`
- Generated: `src/implementation/RSL/generated_acceptor_v3.rs`
- Command:
  ```bash
  cd transpiler && cargo run -- \
    --input ../src/protocol/RSL/acceptor.rs \
    --annotations ../src/protocol/RSL/acceptor.automan \
    --config ../src/protocol/RSL/transpile.toml \
    --output ../src/implementation/RSL/generated_acceptor_v3.rs
  ```

## Manual Adjustments Required

### 1. Struct Definitions

The generated code only contains exec functions. The `CAcceptor` struct definition must be added manually:

```rust
#[derive(Clone)]
pub struct CAcceptor {
    pub constants: CReplicaConstants,
    pub max_bal: CBallot,
    pub votes: CVotes,
    pub last_checkpointed_operation: Vec<COperationNumber>,
    pub log_truncation_point: COperationNumber,
    pub min_vote_opn: COperationNumber, // optimization field
}
```

### 2. View Trait Implementation

Add spec functions for abstraction:

```rust
impl CAcceptor {
    pub open spec fn abstractable(self) -> bool {
        &&& self.constants.abstractable()
        &&& self.max_bal.abstractable()
        &&& cvotes_is_abstractable(&self.votes)
        // ... etc
    }

    pub open spec fn valid(self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        // ... etc
    }

    pub open spec fn view(self) -> LAcceptor
        recommends self.abstractable()
    {
        LAcceptor {
            constants: self.constants.view(),
            max_bal: self.max_bal.view(),
            // ... etc
        }
    }
}
```

### 3. Method Signature Adaptation

Generated code uses functional style:
```rust
pub exec fn CAcceptorProcess1a(s: &CAcceptor, inp: &CRslPacket)
    -> (result: (CAcceptor, Vec<CRslPacket>))
```

Manual code uses `&mut self` pattern:
```rust
pub fn CAcceptorProcess1a(&mut self, inp: CPacket) -> OutboundPackets
```

To integrate, create wrapper methods on `CAcceptor` impl:
```rust
impl CAcceptor {
    pub fn process_1a(&mut self, inp: CPacket) -> OutboundPackets {
        let (new_self, packets) = CAcceptorProcess1a(self, &inp);
        *self = new_self;
        OutboundPackets::from_vec(packets)
    }
}
```

### 4. Optimized Variants

The manual implementation includes optimized versions:
- `CAddVoteAndRemoveOldOnes_optimized`: Tracks `min_vote_opn` for efficiency
- `CAcceptorProcess2a_optimized`: Uses optimized vote management

These should be added as separate functions or made configurable in the transpiler.

### 5. Type Mappings

| Generated Type | Manual Type | Notes |
|----------------|-------------|-------|
| `CRslPacket` | `CPacket` | Same underlying type |
| `RslMessage1a` | `CMessage1a` | Enum variant names differ |
| `Vec<CRslPacket>` | `OutboundPackets` | Wrapper type |

Update `transpile.toml` remapping section to handle these.

## Incremental Integration Strategy

1. **Phase A**: Use generated code as validation
   - Keep manual implementation as primary
   - Use generated code in test assertions
   - Verify both produce equivalent results

2. **Phase B**: Hybrid approach
   - Replace core logic with generated functions
   - Keep manual wrappers for interface compatibility
   - Gradually eliminate duplicated code

3. **Phase C**: Full replacement
   - Generate struct definitions
   - Generate View trait implementations
   - Generate wrapper methods for &mut self pattern

## Testing Strategy

1. **Unit Tests**: Compare generated vs manual function outputs
2. **Integration Tests**: Run RSL protocol with hybrid implementation
3. **Full System Tests**: Verify end-to-end behavior unchanged

## Known Issues

1. **Iterator patterns**: Generated code uses `.iter().filter()` which requires external_body trust for correctness
2. **HashMap axioms**: Requires `broadcast use vstd::std_specs::hash::group_hash_axioms`
3. **Deprecation warnings**: Some vstd methods are deprecated (is_Variant, get_Some_0)

## Future Improvements

- [ ] Add type definition generation to transpiler
- [ ] Add View trait generation
- [ ] Add &mut self wrapper generation
- [ ] Add optimization variant support
- [ ] Reduce iterator pattern reliance with generated loops

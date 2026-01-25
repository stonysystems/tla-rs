# Phase 5: Wrapper Methods for &mut self Pattern

## Goal
Generate wrapper methods that convert functional-style generated code to `&mut self` pattern used in manual implementation.

## Current State

**Generated (functional):**
```rust
pub exec fn CAcceptorProcess1a(s: &CAcceptor, inp: &CRslPacket)
    -> (result: (CAcceptor, Vec<CRslPacket>))
```

**Manual (&mut self):**
```rust
impl CAcceptor {
    pub fn CAcceptorProcess1a(&mut self, inp: CPacket) -> (sent: OutboundPackets)
}
```

## Design

### Option A: Generate wrapper in impl block
Add a configuration option to generate methods inside an impl block:

```rust
impl CAcceptor {
    pub fn process_1a(&mut self, inp: &CPacket) -> OutboundPackets
    requires
        self.well_formed(),
        inp.well_formed(),
    ensures
        self.well_formed(),
    {
        let (new_state, packets) = CAcceptorProcess1a(self, inp);
        *self = new_state;
        packets
    }
}
```

### Option B: Keep functional, add conversion layer
Keep generated code functional, add a thin adapter layer that can be manually written.

### Recommended: Option A (partial)
Generate wrapper stubs that can be customized, rather than full wrappers.

## Implementation Plan

1. Add `generate_wrapper_methods` config option (~20 LOC)
2. Add method to detect functions that take self-type as first arg (~30 LOC)
3. Generate wrapper method signature (~40 LOC)
4. Generate wrapper body with state update (~30 LOC)
5. Add tests (~50 LOC)

## Estimated LOC: ~170

## Complexity Assessment
This is a moderate-complexity task. The main challenges:
1. Detecting which functions should have wrappers
2. Handling different return types (single state, tuple with packets)
3. Ensuring proof annotations carry over correctly

## Decision
Defer this task - the functional style works and the wrapper pattern is a convenience feature. Focus on verification and testing first.

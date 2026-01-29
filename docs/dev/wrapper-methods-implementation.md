# Wrapper Methods Implementation Plan

## Status: COMPLETE [26:01:29, 06:30]

## Goal
Generate wrapper methods that convert functional-style generated code to `&mut self` pattern used in manual implementation.

## Analysis

### Current Generated Code Pattern
```rust
pub exec fn CElectionStateProcessHeartbeat(es: &CElectionState, p: &CRslPacket, clock: &i64)
    -> (result: CElectionState)
requires
    es.valid(),
ensures
    result.valid(),
    ElectionStateProcessHeartbeat(es@, result@, p@, clock@),
{
    // Implementation returns new state
}
```

### Manual Code Pattern
```rust
impl CReplica {
    pub fn CReplicaNextProcess1a(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
    requires
        old(self).valid(),
    ensures
        self.valid(),
    {
        // Implementation modifies self in place
    }
}
```

### Key Differences
1. **Function style**: Standalone `exec fn` vs `impl` method
2. **Self parameter**: `&Type` (reference) vs `&mut self`
3. **Return type**: `(NewState)` vs `OutboundPackets` or `(NewState, OutboundPackets)`
4. **Proof annotations**: `es.valid()` vs `old(self).valid()`

## Design Decision

After analysis, I realize that generating `&mut self` wrappers is complex because:
1. The manual code and generated code have fundamentally different patterns
2. The manual code uses `old(self)` in requires/ensures
3. The generated code returns the new state; wrapper would need to do `*self = new_state;`

### Option A: Generate Wrapper Methods in Impl Block (Original Plan)
Generate wrappers like:
```rust
impl CElectionState {
    pub fn process_heartbeat(&mut self, p: &CRslPacket, clock: &i64)
    requires old(self).valid(), p.valid()
    ensures self.valid()
    {
        *self = CElectionStateProcessHeartbeat(self, p, clock);
    }
}
```

**Pros**: Simple to implement, reuses existing generated functions
**Cons**: Naming differs from manual code, may need additional impl block generation

### Option B: Add `impl_block_name` Config Option
Allow user to specify an impl block name, and generate methods inside it.

### Recommendation: Option A (Simplified)

Focus on generating the wrapper pattern without trying to match manual code exactly.
The wrapper will:
1. Take `&mut self` instead of `&Type`
2. Call the functional version
3. Assign result back to `*self`

## Implementation Steps

### Step 1: Add Config Option (~20 LOC)
Add to `TranspilerConfig` and `OutputConfig`:
```rust
/// When true, generate wrapper methods in impl block for &mut self pattern
pub generate_wrapper_methods: bool,
/// Name of the type for the impl block (e.g., "CElectionState")
pub impl_type_name: Option<String>,
```

### Step 2: Detect Wrapper Candidates (~30 LOC)
In `Translator`, add method to detect functions that:
- Take a reference to the "main" type as first parameter
- Return that type or a tuple containing it

### Step 3: Generate Wrapper Signature (~40 LOC)
Generate the method signature:
- Change first param from `&Type` to `&mut self`
- Keep other params
- Change return type (omit the state type from tuple)

### Step 4: Generate Wrapper Body (~30 LOC)
Generate body:
- Call the functional version
- If returns state: `*self = func(self, ...);`
- If returns tuple: `let (new_self, result) = func(self, ...); *self = new_self; result`

### Step 5: Generate Impl Block (~20 LOC)
Wrap all wrapper methods in `impl TypeName { ... }`

### Step 6: Add Tests (~50 LOC)

## Estimated LOC: ~190

## Test Plan
1. Unit test: Wrapper generation for simple state-returning function
2. Unit test: Wrapper generation for tuple-returning function
3. Integration test: Election module with wrappers

## Completion Criteria
- [x] Config option added
- [x] Wrapper detection working
- [x] Wrapper generation working
- [x] Tests passing (3 new tests)
- [ ] Election module can generate with wrappers (future test)

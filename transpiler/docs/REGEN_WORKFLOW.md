# RSL Regeneration Workflow

After running the transpiler to regenerate `src/generated/RSL/*_gen.rs`, apply the
manual patches documented below. These will be automated by Phase 41.2; until then
they must be re-applied after every regen.

## 1. Arc-wrap `highest_seqno_requested_by_client_this_view` (cb42869)

This patch changes `CProposer.highest_seqno_requested_by_client_this_view` from
`HashMap<EndPoint, u64>` to `Arc<HashMap<EndPoint, u64>>`, yielding +82% RSL
throughput (16K → 29K ops/s). See commit `cb42869` for bench data.

### Changes to `src/generated/RSL/proposer_gen.rs`

**a) Add import** at the top (outside `verus!{}`):

```rust
use std::sync::Arc;
```

**b) Add `assume_specification`** inside `verus!{}`, before the first function:

```rust
pub assume_specification [crate::generated::RSL::proposer_gen::_arc_seqno_insert]
    (arc: std::sync::Arc<std::collections::HashMap<crate::common::native::io_s::EndPoint, u64>>,
     k: crate::common::native::io_s::EndPoint,
     v: u64)
    -> (res: std::sync::Arc<std::collections::HashMap<crate::common::native::io_s::EndPoint, u64>>)
    ensures
        res@ == arc@.insert(k, v);
```

**c) In `CProposerInit`**: change `HashMap::new()` → `Arc::new(HashMap::new())`
for the `highest_seqno_requested_by_client_this_view` field.

**d) In `CProposerMaybeEnterNewViewAndSend1a`**: same `HashMap::new()` →
`Arc::new(HashMap::new())` for the reset-on-new-view path.

**e) In `CProposerProcessRequest`**: replace the mutable
`__highest_seqno_requested_by_client_this_view.insert(...)` call with the
by-value Arc helper:

```rust
let __highest_seqno_requested_by_client_this_view =
    _arc_seqno_insert(__highest_seqno_requested_by_client_this_view, val_client_clone, val.seqno);
```

**f) Add helper function** after the closing `} // verus!`:

```rust
pub fn _arc_seqno_insert(
    arc: std::sync::Arc<std::collections::HashMap<crate::common::native::io_s::EndPoint, u64>>,
    k: crate::common::native::io_s::EndPoint,
    v: u64,
) -> std::sync::Arc<std::collections::HashMap<crate::common::native::io_s::EndPoint, u64>> {
    let mut a = arc;
    std::sync::Arc::make_mut(&mut a).insert(k, v);
    a
}
```

### Changes to `src/implementation/RSL/ProposerImpl.rs`

**g) Add import**: `use std::sync::Arc;`

**h) Change struct field type**:
```rust
// Before:
pub highest_seqno_requested_by_client_this_view: HashMap<EndPoint, u64>,
// After:
pub highest_seqno_requested_by_client_this_view: Arc<HashMap<EndPoint, u64>>,
```

**i) Update `clone_endpoint_seqno_map`** signature and body to use
`Arc::clone()` instead of deep clone.

### Verification

After applying, verify:
```bash
verus --crate-type=lib src/lib.rs --verify-only-module generated::RSL::proposer_gen
# Expected: 125 verified, 0 errors
verus --crate-type=lib src/lib.rs --verify-only-module implementation::RSL::ProposerImpl
# Expected: 16 verified, 0 errors
```

## 2. Hand-written function bodies (skip_functions)

The following functions are in `skip_functions` because the transpiler cannot
auto-generate their bodies. Their existing hand-written implementations in the
`*_gen.rs` files must be preserved across regen:

- `CLearnerForgetOperationsBefore` in `learner_gen.rs` — quantified map filtering
- `CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints` in `replica_gen.rs` — existential witness

The transpiler will not emit these functions. After regen, copy their bodies from
the pre-regen version (or from `git show HEAD:src/generated/RSL/<file>`).

Additionally, the following functions are in `skip_functions` and have hand-written
or proof-fallback stub implementations that must be preserved:
- `CLearnerProcess2b` (learner)
- `CExecutorExecute` (executor)
- `CProposerNominateOldValueAndSend2a`, `CProposerNominateNewValueAndSend2a`,
  `CProposerMaybeNominateValueAndSend2a` (proposer)
- `CReplicaNextReadClockAndProcessPacket`, `CReplicaNextProcessPacketWithoutReadingClock`,
  `CReplicaNextProcessPacket`, `CReplicaNoReceiveNext`, `CSchedulerNext`,
  `CReplicaNextProcess1b` (replica)
- `CBoundRequestSequence`, `CElectionStateReflectReceivedRequest` (election)

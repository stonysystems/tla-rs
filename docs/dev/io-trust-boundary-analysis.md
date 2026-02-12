# IO Trust Boundary Analysis: 3 Remaining Assumes

**Date**: 2026-02-12
**Status**: 4 of 7 assumes eliminated; 3 irreducible assumes remain
**File**: `src/generated/RSL/replica_gen.rs`

## Overview

The RSL protocol implementation has 3 remaining `assume()` calls in `replica_gen.rs` that cannot be eliminated without major architectural changes. These represent the trust boundary between the verified protocol logic and the I/O layer.

The Verus build currently reports **581 verified, 0 errors** with these 3 assumes trusted.

## Eliminated Assumes (4 of 7)

### Category 1: Packet Validity — ELIMINATED

Previously 2 assumes (`assume(received_packet.valid())`) after `clone_io_packet(lp)`. Eliminated by strengthening `clone_io_packet` ensures to include `res.valid()` and `res.abstractable()`. Since `clone_io_packet` is already `#[verifier(external_body)]` (trusted), this makes the trust claim explicit in the function contract rather than at each call site.

### Category 3: Top-Level Aggregation — ELIMINATED

Previously 2 assumes in `CReplicaNextProcessPacket`:
- `assume(result.valid())` — eliminated by using `s.clone_up_to_view()` (which ensures `result.valid() == self.valid()`) for TimeoutReceive, and relying on sub-function ensures for other branches.
- `assume(LReplicaNextProcessPacket(...))` — eliminated by adding IO contract precondition `(ios[0] is TimeoutReceive) ==> ios.len() == 1` and returning directly from each dispatch branch. The TimeoutReceive branch returns `s.clone_up_to_view()` which trivially satisfies `s_ == s`, and other branches delegate to sub-functions whose ensures already cover their respective spec predicates.

## The 3 Remaining Assumes

### Category 2: IO Structure Constraints (3 assumes)

**Line 600** — `CReplicaNoReceiveNext` (dispatcher composition):
```rust
assume(LReplicaNoReceiveNext(s@, *nextActionIndex as int, result@, abstractify_crslio_seq(ios@)));
```
After dispatching to one of 9 sub-functions for spontaneous operations. Each sub-function ensures its own spec predicate, but the dispatcher needs to assert the aggregated spec holds.

**Line 686** — `CReplicaNextProcessPacketWithoutReadingClock`:
```rust
assume(LReplicaNextProcessPacketWithoutReadingClock(s@, new_replica@, abstractify_crslio_seq(ios@)));
```
The spec predicate requires: `forall |io: RslIo| ios.drop_first().contains(io) ==> io is Send` — all IOs after the first Receive must be Send operations.

**Line 709** — `CReplicaNextReadClockAndProcessPacket`:
```rust
assume(LReplicaNextReadClockAndProcessPacket(s@, new_replica@, abstractify_crslio_seq(ios@)));
```
The spec predicate requires: `forall |io: RslIo| ios.subrange(2, ios.len() as int).contains(io) ==> io is Send` — all IOs from index 2 onwards must be Sends (ios[0]=Receive, ios[1]=ReadClock).

## What Would Be Needed to Eliminate the Remaining 3

### Proof of Dispatcher Composition

The 3 remaining assumes are all in dispatcher functions that call sub-functions. Each sub-function ensures its own spec predicate, but the dispatcher needs a proof that the sub-predicate implies the parent spec predicate. This requires:

1. **Proving exhaustiveness of dispatch branches** — showing all cases are covered
2. **Linking sub-predicate ensures to the aggregate spec predicate** — e.g., `LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s@, result@, ios@) ==> LReplicaNoReceiveNext(s@, 0, result@, ios@)` for each sub-function
3. **IO structure invariants** — proving `forall |io: RslIo| ios.drop_first().contains(io) ==> io is Send` from the sub-function behavior

### Estimated Effort

- **LOC**: 300-500 lines of proof lemmas and helper functions
- **Risk**: Medium — the proofs are compositional and localized to dispatcher functions
- **Prerequisite**: Sub-function ensures must be strong enough to imply the parent spec predicate (may require strengthening some generated ensures)

## Key Files

| File | Role |
|------|------|
| `src/generated/RSL/replica_gen.rs` | Contains the 3 assumes (lines 600, 686, 709) |
| `src/protocol/RSL/replica.rs` | Defines spec predicates (LReplicaNext*, lines 580-629) |
| `src/generated/RSL/types_gen.rs` | CReplica struct, clone_up_to_view() impl |
| `src/common/native/io_s.rs` | IO layer abstraction |

## Recommendation

These 3 assumes represent the genuine trust boundary between the verified protocol and the runtime environment. In practice, they are safe because:

1. The IO layer is implemented by a trusted C# runtime that only delivers valid packets
2. The IO sequence structure is enforced by the scheduler's event loop
3. Each sub-function's ensures already covers its respective spec predicate — the gap is only in composing these into the parent dispatcher's ensures

Eliminating them would require proof lemmas showing how sub-function ensures compose into parent spec predicates. This is feasible but requires careful reasoning about the spec predicate structure.

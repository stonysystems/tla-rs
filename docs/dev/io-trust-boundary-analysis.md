# IO Trust Boundary Analysis: 7 Irreducible Assumes

**Date**: 2026-02-12
**Status**: Analysis complete, implementation deferred
**File**: `src/generated/RSL/replica_gen.rs`

## Overview

The RSL protocol implementation has 7 remaining `assume()` calls in `replica_gen.rs` that cannot be eliminated without major architectural changes. These represent the trust boundary between the verified protocol logic and the I/O layer.

The Verus build currently reports **581 verified, 0 errors** with these 7 assumes trusted.

## The 7 Assumes

### Category 1: Packet Validity (2 assumes)

**Line 660** — `CReplicaNextProcessPacketWithoutReadingClock`:
```rust
assume(received_packet.valid());
```

**Line 695** — `CReplicaNextReadClockAndProcessPacket`:
```rust
assume(received_packet.valid());
```

Both occur after `clone_io_packet(lp)` which is `#[verifier(external_body)]` and only ensures field equality (`res.dst == p.dst, res.src == p.src, res.msg == p.msg`) but NOT validity. Packet validity is an environment guarantee — the IO layer only delivers valid packets.

### Category 2: IO Structure Constraints (3 assumes)

**Line 590** — `CReplicaNoReceiveNext` (dispatcher composition):
```rust
assume(LReplicaNoReceiveNext(s@, *nextActionIndex as int, result@, abstractify_crslio_seq(ios@)));
```
After dispatching to one of 9 sub-functions for spontaneous operations. Each sub-function ensures its own spec predicate, but the dispatcher needs to assert the aggregated spec holds.

**Line 674** — `CReplicaNextProcessPacketWithoutReadingClock`:
```rust
assume(LReplicaNextProcessPacketWithoutReadingClock(s@, new_replica@, abstractify_crslio_seq(ios@)));
```
The spec predicate requires: `forall |io: RslIo| ios.drop_first().contains(io) ==> io is Send` — all IOs after the first Receive must be Send operations.

**Line 697** — `CReplicaNextReadClockAndProcessPacket`:
```rust
assume(LReplicaNextReadClockAndProcessPacket(s@, new_replica@, abstractify_crslio_seq(ios@)));
```
The spec predicate requires: `forall |io: RslIo| ios.subrange(2, ios.len() as int).contains(io) ==> io is Send` — all IOs from index 2 onwards must be Sends (ios[0]=Receive, ios[1]=ReadClock).

### Category 3: Top-Level Aggregation (2 assumes)

**Line 725** — `CReplicaNextProcessPacket` (result validity):
```rust
assume(result.valid());
```
Aggregated from dispatch branches — `s.clone()` (TimeoutReceive) and sub-function calls.

**Line 726** — `CReplicaNextProcessPacket` (spec predicate):
```rust
assume(LReplicaNextProcessPacket(s@, result@, abstractify_crslio_seq(ios@)));
```
Top-level composition of three possible cases (TimeoutReceive, Heartbeat, Non-heartbeat).

## What Would Be Needed to Eliminate These

### 1. Verified IO Abstraction

Define predicates capturing environment invariants:

```rust
spec fn WellFormedIoSequence(ios: Seq<CRslIo>) -> bool {
    // If ios[0] is Receive, then forall i in 1..ios.len(), ios[i] is Send
    // If ios[0] is TimeoutReceive, then ios.len() == 1
    // If ios[0] is ReadClock, then forall i in 1..ios.len(), ios[i] is Send
}

spec fn PacketValidityInvariant(ios: Seq<CRslIo>) -> bool {
    forall |i: int| 0 <= i < ios.len() && ios[i] is Receive ==>
        ios[i]->r.valid() && ios[i]->r.abstractable()
}
```

### 2. Precondition Strengthening

Add to `CReplicaNextProcessPacket` and related functions:
```rust
requires
    WellFormedIoSequence(ios@),
    PacketValidityInvariant(ios@),
```

### 3. clone_io_packet Enhancement

Either strengthen `clone_io_packet` ensures to include validity:
```rust
fn clone_io_packet(p: &LPacket<EndPoint, CMessage>) -> (res: CPacket)
    requires p.valid(),  // new
    ensures res.dst == p.dst, res.src == p.src, res.msg == p.msg,
            res.valid(),  // new
```

Or propagate the IO-level packet validity through the call chain.

### 4. Proof of Composition

The dispatcher functions need proofs that sub-function ensures compose into parent predicates. This requires:
- Verifying that `s.clone()` preserves validity (currently clone_up_to_view is external_body)
- Proving exhaustiveness of dispatch branches
- Linking sub-predicate ensures to the aggregate spec predicate

## Estimated Effort

- **LOC**: 500-1000+ lines of proof code, contract changes, and helper lemmas
- **Risk**: High — changes to function contracts may cascade through the codebase
- **Prerequisite**: The manual implementation modules (acceptorimpl, learnerimpl, ExecutorImpl, ProposerImpl) that are `#[verifier(external_body)]` would need verified contracts

## Key Files

| File | Role |
|------|------|
| `src/generated/RSL/replica_gen.rs` | Contains the 7 assumes (lines 590, 660, 674, 695, 697, 725, 726) |
| `src/protocol/RSL/replica.rs` | Defines spec predicates (LReplicaNext*, lines 580-629) |
| `src/generated/RSL/types_gen.rs` | CReplica struct, clone_up_to_view() impl |
| `src/common/native/io_s.rs` | IO layer abstraction |

## Recommendation

These 7 assumes represent the genuine trust boundary between the verified protocol and the runtime environment. In practice, they are safe because:

1. The IO layer is implemented by a trusted C# runtime that only delivers valid packets
2. The IO sequence structure is enforced by the scheduler's event loop
3. The `clone_up_to_view()` function is a simple `self.clone()` wrapper

Eliminating them would require a verified IO abstraction layer, which is a substantial project in its own right. This is acceptable for production use since the trusted IO boundary is well-understood and well-contained.

# IO Trust Boundary Analysis: Packet Identity Assumes

**Date**: 2026-02-12
**Status**: Original 7 assumes decomposed; 10 uniform packet identity assumes remain
**File**: `src/generated/RSL/replica_gen.rs`

## Overview

The RSL protocol implementation has 10 remaining `assume()` calls in `replica_gen.rs`. All are the **same statement** — the irreducible IO trust boundary linking exec function output to the IO log:

```rust
assume(_sent_packets@.map(|i, p: CPacket| p@) =~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)));
```

This states: "the packets returned by the exec sub-function equal the Send packets extracted from the IO log." This is a runtime guarantee — the C# IO layer faithfully records sent packets.

The Verus build reports **581 verified, 0 errors** with these 10 assumes trusted.

## History

Originally 7 assumes of varying specificity (full spec predicates, result validity, packet validity). Through successive refinements:

- **7 → 3**: Eliminated 4 assumes via `clone_io_packet` ensures, `clone_up_to_view()`, and IO contract preconditions (see git log)
- **3 → 10 (uniform)**: Decomposed 3 broad spec-predicate assumes into 10 minimal packet-identity assumes by:
  - Adding IO structure preconditions (`SpontaneousIos`, `forall io is Send`, etc.)
  - Adding clock identity preconditions (`clock_time == ios[0]->t`)
  - Proving IO structure, packet view identity, and clock identity via proof blocks
  - Reducing each assume to ONLY the packet identity gap

## What Was Proven (Previously Assumed)

The following are now **verified by Verus** (not assumed):

1. **Packet validity**: `clone_io_packet` ensures `res.valid()` and `res.abstractable()`
2. **Result validity**: All branches ensure `result.valid()` via sub-function ensures + `clone_up_to_view()`
3. **IO structure**: `SpontaneousIos(ios, clocks)` and `forall io in drop_first => io is Send` via IO contract preconditions
4. **Packet view identity**: `received_packet@ == abstractify_crslio_seq(ios@)[0]->r` via `clone_io_packet` field equality
5. **Clock identity**: `clock_time == ios[1]->t` via IO contract preconditions
6. **Heartbeat spec predicate**: `LReplicaNextReadClockAndProcessPacket` fully proven (0 assumes) — `ExtractSentPacketsFromIos` on 2-element `[Receive, ReadClock]` sequence is provably empty
7. **Top-level dispatch**: `LReplicaNextProcessPacket` fully proven via branch-by-branch delegation

## The 10 Remaining Assumes

All are the same packet identity statement in different dispatch branches:

### In `CReplicaNoReceiveNext` (9 assumes, one per action 1-9):
Each sub-function (e.g., `CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a`) returns `(s_, sent_packets)`. The assume states that `sent_packets@.map(...)` equals `ExtractSentPacketsFromIos(ios_abs)`.

### In `CReplicaNextProcessPacketWithoutReadingClock` (1 assume):
The packet-processing sub-function (e.g., `CReplicaNextProcessRequest`) returns `(new_replica, packets)`. The assume states that `packets@.map(...)` equals `ExtractSentPacketsFromIos(ios_abs)`.

### Exact site inventory (validated on 2026-02-21)

Source: `src/generated/RSL/replica_gen.rs`

| # | Function | Branch / action | Assume line |
|---|---|---|---|
| 1 | `CReplicaNoReceiveNext` | `nextActionIndex == 1` (`CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a`) | `821` |
| 2 | `CReplicaNoReceiveNext` | `nextActionIndex == 2` (`CReplicaNextSpontaneousMaybeEnterPhase2`) | `825` |
| 3 | `CReplicaNoReceiveNext` | `nextActionIndex == 3` (`CReplicaNextReadClockMaybeNominateValueAndSend2a`) | `830` |
| 4 | `CReplicaNoReceiveNext` | `nextActionIndex == 4` (`CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints`) | `834` |
| 5 | `CReplicaNoReceiveNext` | `nextActionIndex == 5` (`CReplicaNextSpontaneousMaybeMakeDecision`) | `838` |
| 6 | `CReplicaNoReceiveNext` | `nextActionIndex == 6` (`CReplicaNextSpontaneousMaybeExecute`) | `842` |
| 7 | `CReplicaNoReceiveNext` | `nextActionIndex == 7` (`CReplicaNextReadClockCheckForViewTimeout`) | `847` |
| 8 | `CReplicaNoReceiveNext` | `nextActionIndex == 8` (`CReplicaNextReadClockCheckForQuorumOfViewSuspicions`) | `852` |
| 9 | `CReplicaNoReceiveNext` | `nextActionIndex == 9` (`CReplicaNextReadClockMaybeSendHeartbeat`) | `857` |
| 10 | `CReplicaNextProcessPacketWithoutReadingClock` | message dispatch result `_packets` | `967` |

All 10 sites assert the same trust-boundary statement:

```rust
assume(_sent_packets@.map(|i, p: CPacket| p@) =~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)));
```

or (single non-receive variant):

```rust
assume(_packets@.map(|i, p: CPacket| p@) =~= ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)));
```

### Automated drift guard

`transpiler/tests/integration.rs::test_replica_dispatch_assume_drift_guard` enforces all of the following:

- exactly 10 trust-boundary assumes in replica dispatch paths,
- exact 9 + 1 split across `CReplicaNoReceiveNext` and `CReplicaNextProcessPacketWithoutReadingClock`,
- no `assume(...)` sites in other replica dispatch functions,
- both sites match only the two known packet-identity assume forms above.

This catches accidental introduction of new `assume(...)` statements in replica dispatch code.

## Why This Is Irreducible

The packet identity `exec_output =~= ExtractSentPacketsFromIos(io_log)` cannot be proven because:

1. **The IO log is externally constructed**: The C# runtime builds the IO log by recording what happened during protocol execution. The Rust exec functions receive this log as a parameter — they don't construct it.
2. **No formal link exists**: The exec sub-functions return `Vec<CPacket>` (packets to send). The IO log records these sends as `LIoOp::Send{s: packet}` entries. But there is no Verus-verified code connecting the two — the linkage is in the C# runtime.
3. **Cannot reference result in preconditions**: We can't add `result.1 == f(ios)` as a precondition because `result` is computed inside the function body.

## What Would Eliminate These

To eliminate these assumes entirely would require restructuring the IO architecture so that the exec functions **build** the IO log rather than receiving it:

```rust
// Current: IO log passed in, must assume it matches
exec fn process(s: &State, ios: &Vec<IO>) -> State { ... assume(...) }

// Alternative: exec function builds IO log, guarantees match by construction
exec fn process(s: &State, recv: Packet) -> (State, Vec<Packet>, Vec<IO>) { ... }
```

This is a major architectural change affecting the C#/Rust FFI boundary.

## IO Contract Preconditions Added

To prove everything except packet identity, the following preconditions were added to `CSchedulerNext`:

| Precondition | Purpose |
|---|---|
| `timeout ==> ios.len() == 1` | TimeoutReceive is a single event |
| `heartbeat ==> ios.len() == 2` | Heartbeat has Receive + ReadClock only |
| `heartbeat ==> ios[1]->t == clock_time` | Clock matches ReadClock IO |
| `non-heartbeat ==> forall i >= 1: ios[i] is Send` | Non-heartbeat: all IOs after Receive are Send |
| `actions 1,2,4,5,6 ==> forall i: ios[i] is Send` | No-clock spontaneous: all IOs are Send |
| `actions 3,7,8,9 ==> ios[0] is ReadClock && rest Send` | Clock spontaneous: ReadClock then Sends |
| `actions 3,7,8,9 ==> ios[0]->t == clock_time` | Clock matches for spontaneous actions |

## Key Files

| File | Role |
|------|------|
| `src/generated/RSL/replica_gen.rs` | Contains the 10 packet identity assumes |
| `src/protocol/RSL/replica.rs` | Defines spec predicates and `ExtractSentPacketsFromIos` |
| `src/generated/RSL/types_gen.rs` | `abstractify_crslio_seq`, `abstractify_clpacket` |

## Recommendation

These 10 assumes are the minimal possible trust surface for the current IO architecture. They all state exactly one thing: "the runtime faithfully records sent packets in the IO log." This is a single, well-understood axiom about the C# runtime's correctness.

# RSL Replica Manual-Code Audit (2026-02-22)

## Scope

Audit the remaining contents of `src/protocol/RSL/replica_manual.rs` after `21.11.2.1` through `21.11.2.3` to confirm it only contains IO trust-boundary wrappers/helpers.

## Findings

`replica_manual.rs` now exports exactly six `pub exec fn` entries:

1. `CExtractSentPacketsFromIos`
2. `CReplicaNoReceiveNext`
3. `CSchedulerNext`
4. `CReplicaNextProcessPacketWithoutReadingClock`
5. `CReplicaNextReadClockAndProcessPacket`
6. `CReplicaNextProcessPacket`

Only one `#[verifier(external_body)]` boundary remains in this file, on `CExtractSentPacketsFromIos`.

All `assume(...)` sites are localized to packet/IO correspondence in the dispatch wrappers:

- 9 assumes in `CReplicaNoReceiveNext`
- 1 assume in `CReplicaNextProcessPacketWithoutReadingClock`

No action-specific helper/action body (for example `CReplicaNextProcess1b`) remains in `replica_manual.rs`.

## Regression Guard

`transpiler/tests/integration.rs` now includes:

- `test_replica_manual_code_contains_only_io_trust_boundary_wrappers`

This test locks the manual-code function set and external-body count so future changes do not re-expand manual injection scope.

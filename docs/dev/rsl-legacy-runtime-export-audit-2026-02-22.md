# RSL Legacy Runtime Export Audit (2026-02-22)

## Scope

Re-audit `src/implementation/RSL/mod.rs` legacy runtime exports and remove any module no longer reachable from the `host_i` / `host_s` dispatch path (TODO 19.7.6b).

Legacy runtime module set under audit:

- `cmd_line_parser`
- `netrsl_i`
- `replicaimpl_class`
- `replicaimpl_delivery`
- `replicaimpl_main`
- `replicaimpl_no_receive_clock`
- `replicaimpl_no_receive_no_clock`
- `replicaimpl_process_packet_no_clock`
- `replicaimpl_process_packet_x`
- `replicaimpl_read_clock`

## Reachability Summary

Dispatch entrypoint:

- `host_i::host_next_impl` calls `Replica_Next_main` in `replicaimpl_main`.

Transitive call chain:

- `replicaimpl_main::Replica_Next_main`
  - `replica_next_process_packet_x` (`replicaimpl_process_packet_x`)
  - `replica_no_receive_no_read_clock` (`replicaimpl_no_receive_no_clock`)
  - `replica_no_receive_read_clock_next` (`replicaimpl_no_receive_clock`)
- `replicaimpl_process_packet_x`
  - `replica_next_read_clock_and_process_packet` (`replicaimpl_read_clock`)
  - `replica_next_process_packet_without_reading_clock` (`replicaimpl_process_packet_no_clock`)
- `replicaimpl_no_receive_no_clock`, `replicaimpl_no_receive_clock`,
  `replicaimpl_read_clock`, and `replicaimpl_process_packet_no_clock`
  all call `deliver_outbound_packets` from `replicaimpl_delivery`.
- `replicaimpl_delivery` uses network send helpers from `netrsl_i`.
- `host_i::host_init_impl` uses `parse_cmd_line` from `cmd_line_parser`.
- `replicaimpl_class` provides `ReplicaImpl` state used throughout the chain.

## Result

No legacy module in the audited set is currently removable without breaking runtime reachability from `host_i`/`host_s`.

Action taken:

- Kept the existing legacy module export set in `src/implementation/RSL/mod.rs`.
- Added/updated regression coverage to lock the audited export set and dispatch edges.

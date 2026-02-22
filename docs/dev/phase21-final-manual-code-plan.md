# Phase 21 Final-Mile Manual-Code Plan (2026-02-22)

## Context

Phase 21 set a top-priority goal: eliminate `manual_code` injection from protocol transpile configs.
Most modules have already migrated, but two RSL configs still intentionally bind `output.manual_code`:

- `src/protocol/RSL/replica_transpile.toml` -> `replica_manual.rs`
- `src/protocol/RSL/executor_transpile.toml` -> `executor_manual.rs`

This document captures why those two remain and defines a small-leaf execution path.

## Current Remaining Footprint

### Replica (`replica_manual.rs`)

- Current size: ~396 LOC
- Contains IO-dispatch/trust-boundary wrappers and assumes tied to packet/IO correspondence.
- Still referenced by `replica_transpile.toml` through `output.manual_code`.
- Uses explicit `assume(...)` at the runtime trust boundary.

### Executor (`executor_manual.rs`)

- Current size: ~706 LOC
- Contains fully proven map/cache/reply logic and helper lemmas.
- Still referenced by `executor_transpile.toml` through `output.manual_code`.
- Intentionally has no `assume(...)`; trust is mostly via `external_body` on selected helper boundaries.

## Why This Is Still Unfinished

The remaining work is no longer broad infrastructure: it is concentrated in proof-generation parity for two difficult modules.
Removing `manual_code` in one shot would likely regress proof quality (or replace proven bodies with weaker stubs), which conflicts with the "honest, complete, not corner-cutting" bar.

## Leaf-Task Breakdown (<500 LOC each)

1. `21.11.2` Replica final-mile leaf:
   - Re-home non-proof helper code out of `replica_manual.rs`.
   - Keep only IO trust-boundary wrappers in manual injection.
   - Update TOML + regression tests accordingly.

2. `21.11.3` Executor final-mile leaves:
   - Add transpiler support for one proof pattern family at a time (cache/reply-map invariants).
   - Regenerate `executor_gen.rs` and remove corresponding manual segment.
   - Repeat until `executor_manual.rs` can be removed without replacing proven bodies by weaker stubs.

## Regression Guard Added

Integration tests now assert that only the two configs above contain `output.manual_code`, preventing accidental expansion of manual injection scope while this final-mile migration is in progress.

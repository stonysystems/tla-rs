# RSL Generated Replacement Breakdown (2026-02-12)

## Context
The Phase 5 parent task (replace manual `src/implementation/RSL/` with generated code) is larger than a single safe change. Recent regeneration runs showed that replacement is blocked by generation parity and integration drift, not by optimized acceptor variants (those are complete).

## Why this is split
Attempting full replacement in one step couples multiple risk areas:
- `generate-types` output stability for RSL helper logic
- type boundary alignment between generated modules and `types_i` marshalable types
- helper visibility/contracts required by both generated and manual modules
- multi-module integration cutover (acceptor/learner/executor/proposer/replica)

This is too large for a reliable <500 LOC leaf and too risky to verify in one pass.

## New leaf sequence
1. Add `generate-types` support for injecting manual helper code from config (`output.manual_code`).
2. Move current RSL manual helper block into a dedicated source file under `src/protocol/RSL/`.
3. Wire `types_transpile.toml` to that helper file and regenerate.
4. Close regeneration parity/type drift until generated modules build and verify.
5. Perform incremental module replacement with verification/test gates after each module.

## Completed in this iteration
- Implemented leaf (1): `generate-types` now supports manual code injection for type output.
- Added regression test coverage in transpiler codegen.

## Follow-up extraction progress (same day)
- Measured helper drift in `src/generated/RSL/types_gen.rs` against fresh generation:
  - net helper/custom section size is too large for one safe leaf (~1.1k inserted lines).
- Split extraction into smaller leaves in `TODO.md`.
- Completed first extraction leaf by creating `src/protocol/RSL/types_manual_helpers.rs` with foundational helper-only code:
  - operation-number abstraction/validity helpers
  - ballot comparison helpers
  - request/reply/vote clone+abstraction helpers
  - learner-state abstraction helpers
- Completed second extraction leaf by adding struct/impl extension sections to the same helper file:
  - `CParameters` (+ `StaticParams`)
  - `CConfiguration` (+ replica-index helpers and endpoint abstraction lemmas)
  - `CConstants`
  - `CReplicaConstants` (+ `InitReplicaConstants`)

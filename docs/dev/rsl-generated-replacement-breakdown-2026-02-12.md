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
- Decomposed the remaining component section again (still >500 LOC) and completed part 1 extraction:
  - extracted `CAcceptor`, `CLearner`, `CElectionState`, `COutstandingOperation`, `CExecutor`, `CIncompleteBatchTimer`
  - left part 2 for the next leaf (`CProposer`, `CReplica`, `CScheduler`, IO abstractify helpers, `unreachable_value`)
- Completed component section part 2 extraction:
  - copied `src/generated/RSL/types_gen.rs:1287-1544` (~258 LOC, under the <500 LOC leaf target)
  - extracted `CProposer`, `CReplica`, `CScheduler`, `abstractify_clpacket`, `abstractify_crslio`, `abstractify_crslio_seq`, and `unreachable_value`
- Wired RSL type generation config to externalized helper source:
  - set `output.manual_code = "types_manual_helpers.rs"` in `src/protocol/RSL/types_transpile.toml`
  - added a CLI config-loading test to ensure this file is read and injected via `generate-types`

## Regeneration Parity Baseline (00:25)
- Ran a scratch regeneration into `/tmp/rsl_regen_baseline` using the same multi-input command as `scripts/regenerate_all.sh RSL`.
- Compared scratch output against `src/generated/RSL` using `git diff --no-index`.
- File-level parity result:
  - match: `learner_gen.rs`
  - drift: `types_gen.rs`, `acceptor_gen.rs`, `executor_gen.rs`, `proposer_gen.rs`, `replica_gen.rs`, `broadcast_gen.rs`, `election_gen.rs`
- Aggregate churn: ~3815 changed lines (`2118` insertions, `1697` deletions).
- Key drift categories:
  - `types_gen.rs`: generated surface no longer matches current implementation boundary strategy (macro-defined/re-exported concrete types vs auto-generated structs), plus ordering/header differences.
  - function modules (`acceptor`/`executor`/`proposer`/`replica`): regenerated code shape diverges from wrapper/delegate style currently checked in.
  - `broadcast`/`election`: smaller but non-zero drift, likely due import/path normalization and output-shape changes.

## Types Drift Closure (01:20)
- Closed the `types_gen.rs`-specific drift leaf by aligning type-boundary config and regenerating.
- Config updates in `src/protocol/RSL/types_transpile.toml`:
  - expanded `skip_types` for macro-defined types (`Ballot`, `Request`, `Reply`, `Vote`) and helper-owned component types now provided by `types_manual_helpers.rs`
  - added `crate::implementation::RSL::types_i::{CBallot, CRequest, CReply, CVote}` to `re_exports`
  - expanded `custom_imports` to include helper dependencies (`AbstractEndPoint`, appinterface validity predicates, marshalling/generic-refinement imports, and vstd map/set libs)
- Regenerated `src/generated/RSL/types_gen.rs` from current spec/config and verified exact parity against scratch output (`git diff --no-index` clean).
- Remaining drift is now isolated to function modules: `acceptor_gen.rs`, `executor_gen.rs`, `proposer_gen.rs`, `replica_gen.rs`, `broadcast_gen.rs`, `election_gen.rs`.

## Types Compatibility Follow-up (02:40)
- While running Verus target verification (`scons --verus-path=/home/shuai/tools/verus-x86-linux/verus liblib.so`), two helper-boundary regressions surfaced:
  - `CRslIo` alias was referenced by generated modules but no longer defined in regenerated `types_gen.rs`.
  - `CLearnerTuple` was auto-generated with incomplete project-specific method surface (`clone_up_to_view`, `abstractable`, custom `valid`), breaking `learner_gen` and `learnerimpl`.
- Fixes applied:
  - Added `pub type CRslIo = LIoOp<EndPoint, CMessage>;` to `src/protocol/RSL/types_manual_helpers.rs`.
  - Added `"LearnerTuple"` to `skip_types` in `src/protocol/RSL/types_transpile.toml`.
  - Restored manual `CLearnerTuple` struct+impl block in `src/protocol/RSL/types_manual_helpers.rs`.
  - Regenerated `src/generated/RSL/types_gen.rs` from current multi-input type command/config.
- Added regression checks in transpiler tests:
  - `transpiler/src/main.rs` now asserts helper config content includes `CRslIo` alias and `LearnerTuple` remains in required `skip_types`.
  - `transpiler/tests/integration.rs` foundational helper symbol list now includes `CRslIo` alias and `CLearnerTuple` helper method signature.
- Verification status after fix:
  - `cargo test --all-features` in `transpiler/` passes.
  - Verus target build `liblib.so` passes (warnings only).

## Module Drift Decomposition + First Leaf (03:45)
- Re-ran `scripts/regenerate_rsl.sh` and recomputed per-module churn against `src/generated/RSL`:
  - `broadcast_gen.rs`: `+2/-16` (smallest drift)
  - `election_gen.rs`: `+262/-109`
  - `acceptor_gen.rs`: `+251/-303`
  - `executor_gen.rs`: `+173/-487`
  - `proposer_gen.rs`: `+357/-168`
  - `replica_gen.rs`: `+471/-434`
- Based on this, the parent “module drift” leaf was split in `TODO.md` into one leaf per module (<500 LOC target per leaf where possible).
- Executed first leaf: `broadcast_gen.rs`.
  - Synced `src/generated/RSL/broadcast_gen.rs` to regenerated output.
  - Closed drift from stale generated artifacts:
    - removed unused `clone_hashset` import
    - removed obsolete `lemma_empty_set_map` helper
    - aligned bound checks from `c@.replica_ids.len()` to `c.replica_ids.len()` in exec `requires`/invariant.
- Validation after this leaf:
  - `cargo test --all-features` in `transpiler/`: pass
  - `scons --verus-path=/home/shuai/tools/verus-x86-linux/verus liblib.so`: pass (warnings only)

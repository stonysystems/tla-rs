# DPOR Prototype Integration Migration Plan (Phase 38.10.2)

Date: 2026-04-10  
Owner: Phase 38 DPOR track

## Scope and intent

This document is the explicit migration-plan artifact required by `TODO.md` task
`38.10.2`. It does **not** authorize immediate mainline integration. `38.10.1`
is now policy-backed `MET` (see `38.14.11.c.c`), but post-gate discipline in
`38.10.3` still applies before deliberate migration.

## 1. Proposed module move map (`38.10.2.a`)

If `38.10.1` is later satisfied, integration should be staged and minimal.

### Candidate modules to move or share

- `transpiler/DPOR_based_model_tla_rs_checker/src/types.rs`
  - DPOR runtime domain types (`ProcessId`, `ActionId`, `ScheduledStep`,
    `TransitionFootprint`, etc.).
- `transpiler/DPOR_based_model_tla_rs_checker/src/dpor.rs`
  - DPOR search engine, backtrack/sleep-set logic, witness tracing.
- `transpiler/DPOR_based_model_tla_rs_checker/src/enabled.rs`
  - Enabled-transition extraction and footprint/process-id mapping.
- `transpiler/DPOR_based_model_tla_rs_checker/src/explorer.rs`
  - Baseline export graph parsing and comparison helpers.
- `transpiler/DPOR_based_model_tla_rs_checker/src/baseline.rs`
  - Baseline runner APIs used for parity and differential checks.

### Mainline modules that remain source-of-truth

- `transpiler/src/main.rs` CLI surface and command wiring.
- `transpiler/src/modelcheck/` evaluator, parser integration, and existing
  baseline model-check semantics.
- Existing report schemas consumed by Phase 36/38 tooling.

### Integration pattern

- Prefer "shared library extraction" over hard moves first.
- Keep prototype crate operational during migration; do not delete prototype
  sources until shadow-mode parity gates are green.

## 2. Shadow-mode comparison period (`38.10.2.b`)

Shadow mode means both engines run from the normal model-check entrypoints.

### Required behavior

- Add a DPOR engine selector flag (for example, `--engine dpor`) while keeping
  existing baseline/default behavior unchanged.
- For selected fixtures, run both baseline and DPOR and emit side-by-side
  verdict and state-space summaries.
- Treat any verdict mismatch as a hard failure for promotion.

### Required evidence before cutover

- Reproducible parity report on the declared parity subset.
- Reproducible 20-case suite report showing non-vacuous outcomes and no schema
  regressions.
- Regression tests in `transpiler/tests/integration.rs` that assert the shadow
  path is wired and does not silently disable baseline checks.

## 3. Rollback strategy (`38.10.2.c`)

Rollback must be one command-line/config switch, not a code revert.

### Rollback requirements

- Baseline engine remains buildable and executable as first-class path.
- DPOR integration is guarded by an explicit feature/flag gate and can be
  disabled without touching corpus artifacts.
- Prototype corpus, scripts, and reports remain checked in under
  `transpiler/DPOR_based_model_tla_rs_checker/` regardless of mainline toggle.

### Rollback trigger examples

- Any parity drift on the declared exact-parity subset.
- Any report/schema break for existing Phase 36/38 consumers.
- Any reproducible performance regression beyond agreed budget on hard cases.

## 4. Report-schema compatibility (`38.10.2.d`)

Integration cannot silently break existing report consumers.

### Compatibility contract

- Preserve existing `tests/reports/latest.json` fields currently used by
  scripts and integration tests.
- New DPOR-specific telemetry fields may be added only as additive keys.
- If a field must change semantics, provide a migration section and update all
  reader scripts/tests in the same commit.

### Required guardrails

- Integration test coverage that validates expected report keys are still
  present and semantically compatible.
- Explicit changelog note for any schema extension.

## 5. Staged execution order

1. Keep incubator state until `38.10.1` exact-parity blocker is closed.
2. Land shared-library extraction patches (small, semantics-preserving).
3. Land shadow-mode wiring with default baseline path unchanged.
4. Run parity + 20-case + full transpiler regression gates in CI.
5. Promote DPOR path only after shadow-mode evidence is stable.

## 6. Out-of-scope for this artifact

- No direct rewrite of `transpiler/src/modelcheck` in this step.
- No deletion of prototype modules/corpus/report tooling.

## 7. Post-gate commit discipline guards (`38.10.3.a`, `38.10.3.b`)

To keep feature work reviewable while migration is still staged, run:

```bash
transpiler/DPOR_based_model_tla_rs_checker/scripts/check_phase38_commit_scope.sh
```

Default mode inspects staged paths and fails if one commit mixes both:

- `transpiler/DPOR_based_model_tla_rs_checker/**`
- `transpiler/src/modelcheck/**`

Exceptional mixed commits require explicit override metadata:

```bash
PHASE38_ALLOW_MIXED_COMMIT=1 \
PHASE38_MIXED_COMMIT_JUSTIFICATION="narrow shared extraction for replay API" \
transpiler/DPOR_based_model_tla_rs_checker/scripts/check_phase38_commit_scope.sh
```

For standalone mainline modelchecker fixes (no prototype paths), add explicit
mainline-fix justification:

```bash
PHASE38_MAINLINE_FIX_JUSTIFICATION="fix candidate-enumeration regression in por.rs" \
transpiler/DPOR_based_model_tla_rs_checker/scripts/check_phase38_commit_scope.sh
```

This guard does not replace review; it enforces that mixed-scope commits and
prototype-era mainline fixes are explicit, justified exceptions rather than
implicit side effects.

## 8. Migration execution leaves (`38.10.4`)

`38.10.4.a` is now implemented: the prototype CLI supports a minimal
shadow-mode primitive:

```bash
cargo run --manifest-path transpiler/DPOR_based_model_tla_rs_checker/Cargo.toml --bin dpor-checker -- \
  shadow-compare \
  --spec transpiler/DPOR_based_model_tla_rs_checker/tests/tla-rs/01_aplusb/APlusB.rs \
  --model /tmp/model.toml \
  --invariant LSumInvariant
```

Current behavior:

- runs baseline and DPOR on the same fixture,
- emits JSON classification (`positive_exact`, `negative_witness_match`, etc.),
- surfaces verdict/state/witness-depth parity metadata for review.

Remaining execution leaves:

- `38.10.4.b` is now implemented:
  - command: `scripts/run_shadow_subset_report.sh`
  - subset source of truth:
    `src/dpor.rs::test_automated_baseline_vs_dpor_comparison`
  - artifacts:
    - `tests/reports/shadow_parity_subset_latest.json`
    - `tests/reports/shadow_parity_subset_latest.md`
  - current snapshot (`2026-04-10T07:23:15Z`):
    `12 cases / 8 positive_exact / 4 negative_witness_match / 0 parity_failures`.
- `38.10.4.c` remains open: add report-schema drift guard for shadow-mode
  consumers.

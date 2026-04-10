# Runtime Blockers Re-closure (Cases 15/16)

Date: 2026-04-10  
Scope: Phase 38 open-task-map priority item ("Re-close regenerated-corpus runtime blockers").

## Why this doc exists

After regenerated-corpus replay, `15_chain_replication_small` and
`16_primarybackup_small` were temporarily reclassified to
`expected_primary_result = "known_unimplemented"` in
`tests/manifest.toml`.

This document records direct, reproducible baseline runs that confirm the
current blocker modes before closure work starts.

## Reproduction commands and observed outcomes

All commands run from repo root (`/home/shuai/workspace/tla-rs`).

### Case 15 (`15_chain_replication_small`)

Command pattern (using current per-case config with high timeout budget):

```bash
timeout 1200s transpiler/target/release/verus-transpile model-check \
  --input transpiler/DPOR_based_model_tla_rs_checker/tests/tla-rs/15_chain_replication_small/Chain.rs \
  --init LInit --next LNext \
  --model <tmp_15_config_with_timeout_ms_1200000> \
  --json-report
```

Observed result:

- Process exits non-zero (`exit=1`).
- No JSON report is emitted.
- Stderr message:
  `Configuration error: Sequence domain expansion exceeded limit 200000 assignments/values.`

Interpretation:

- This is a candidate-enumeration guardrail abort (not a deadlock verdict).
- The current case cannot be scored as a real negative result until this path
  is tuned/fixed.

### Case 16 (`16_primarybackup_small`)

Command pattern (bounded timeout-window probe with invariant enabled):

```bash
timeout 60s transpiler/target/release/verus-transpile model-check \
  --input transpiler/DPOR_based_model_tla_rs_checker/tests/tla-rs/16_primarybackup_small/Primarybackup.rs \
  --init LInit --next LNext \
  --model <tmp_16_config_with_timeout_ms_60000> \
  --json-report \
  --invariant LSafetyInactiveStateIsQuiescent
```

Observed result:

- Wrapper exits with timeout code (`exit=124`).
- Output file size remains `0` bytes.
- No JSON report is emitted for the run.

Interpretation:

- This matches the "timeout-window checker_error/no-report" blocker class in
  the open-task map.
- Runtime/bounds closure is required before restoring `expected_primary_result = "ok"`.

## Closure decomposition reference

See `TODO.md` `38.15` leaves:

- `38.15.2`: case 15 candidate-enumeration closure
- `38.15.3`: case 16 timeout-window closure
- `38.15.4`: re-enable focused protocol regressions
- `38.15.5`: full-suite/report resync and open-task-map closure


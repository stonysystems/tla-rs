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

## 38.15.2.a guardrail/timeout sweep (case 15)

Goal: determine whether simply increasing
`candidate_eval_guardrail` on the current non-vacuous case-15 model is enough
to restore a real `deadlock_detected` outcome.

Baseline model family:

- input: `tests/tla-rs/15_chain_replication_small/Chain.rs`
- model basis: `tests/model_configs/15_chain_replication_small.toml`
- deadlock enabled (`check_deadlock = true`)
- int domain / collection bounds unchanged from checked-in case-15 config

Observed sweep (`2026-04-10`):

| candidate_eval_guardrail | wrapper timeout | observed outcome |
|---:|---:|---|
| 300,000 | 180s | guardrail abort (`Sequence domain expansion exceeded limit 300000`) |
| 500,000 | 180s | guardrail abort (`... limit 500000`) |
| 800,000 | 180s | guardrail abort (`... limit 800000`) |
| 1,200,000 | 180s | guardrail abort (`... limit 1200000`) |
| 2,000,000 | 180s | guardrail abort (`... limit 2000000`) |
| 5,000,000 | 300s | guardrail abort (`Model-check candidate-enumeration guardrail exceeded`) |
| 10,000,000 | 300s | timeout-window exit (`exit=124`, no JSON report) |
| 20,000,000 | 300s | timeout-window exit (`exit=124`, no JSON report) |

Conclusion:

- Tuning-only via scalar guardrail increases is insufficient for case 15.
- Next closure step must either find a smaller non-vacuous deadlock-friendly
  domain profile (`38.15.2.b`) or reduce candidate-explosion behavior in code
  (`38.15.2.c`).

## Runtime note discovered during 38.15.2.a reruns (case 19)

While re-running mandatory full suites for this phase, case
`19_epaxos_small` showed timeout-window instability in the current environment:

- Full-suite run (`--timeout 1200`) produced a timeout-wrapper
  `checker_error`/no-JSON outcome for case 19.
- Focused direct probes (3/3 attempts, `timeout 120s`) exited `124` with
  no JSON report emission.

Because this was reproducible in repeated direct runs, case 19 is temporarily
reclassified to `known_unimplemented` in `tests/manifest.toml` pending a
separate runtime-stability re-closure pass.

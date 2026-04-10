# Phase 38.11.7 Negative-Case Coverage Gap Audit (2026-04-10)

## Goal

`38.11.7` requires at least 6/20 negative cases that actually exercise
invariant-violation or deadlock detection. This note records the current gap
and first promotion probe.

## Current audited coverage

- Manifest negative rows (`negative = true`) are currently:
  - `03_counter_race_bug`
  - `05_broken_lock_bug`
  - `11_readers_writers_small`
  - `12_dining_philosophers_3`
  - `15_chain_replication_small`
- Count: **5** negative cases (gap to criterion: **1**).

Full-suite snapshot from
`./scripts/run_full_suite.sh --timeout 1200` at `2026-04-10T18:18:11Z`:

- `Passed (real): 19`
- `Known unimplemented: 1` (`19_epaxos_small`)
- Exercised negative outcomes in results:
  - invariant violations: cases `03`, `05`, `11`
  - deadlocks: cases `12`, `15`
- Exercised negative outcome count: **5**.

## First promotion probe (candidate case 08)

Candidate: `08_bounded_buffer_2slot` (currently bounded-positive).

Probe command (manual direct run):

```bash
timeout 130s ./transpiler/target/release/verus-transpile model-check \
  --input transpiler/DPOR_based_model_tla_rs_checker/tests/tla-rs/08_bounded_buffer_2slot/BoundedBuffer2Slot.rs \
  --init LInit --next LNext \
  --model /tmp/case08_test.toml \
  --invariant LBufferNotOverflow \
  --json-report
```

Probe config summary: `MaxVal = 3`, `int = 0..3`, `max_set/seq/map_len = 3`,
`max_states = 200000`, `timeout_ms = 120000`.

Observed outcome:

- checker exits with configuration error before verdict:
  - `Model-check candidate expansion for struct 'LState' exceeded limit (200000).`

Conclusion: case 08 is still blocked at this first widened profile and needs
focused bounded tuning before it can be promoted to a real negative case.

## Next leaves

- `38.11.7.b`: promote one additional real negative case under bounded runtime.
- `38.11.7.c`: rerun full suites and close criterion with synced evidence.

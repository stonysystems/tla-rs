# Phase 38.11.7 Negative-Case Coverage Audit and Closure (2026-04-10)

## Goal

`38.11.7` requires at least 6/20 negative cases that actually exercise
invariant-violation or deadlock detection.

## 38.11.7.a baseline audit (recorded gap)

Baseline audit snapshot from
`./scripts/run_full_suite.sh --timeout 1200` at `2026-04-10T18:18:11Z`:

- Manifest negative rows were:
  - `03_counter_race_bug`
  - `05_broken_lock_bug`
  - `11_readers_writers_small`
  - `12_dining_philosophers_3`
  - `15_chain_replication_small`
- Count at that point: **5** negative cases (gap to criterion: **1**).
- Exercised negative outcomes at that point: **5**.

First widening probe for case 08 used `MaxVal = 3`, `int = 0..3`,
`max_set/seq/map_len = 3`, `max_states = 200000`, and hit:

- `Model-check candidate expansion for struct 'LState' exceeded limit (200000).`

## 38.11.7.b promotion execution (case 08)

Promoted case: `08_bounded_buffer_2slot`.

Checked-in model profile (`tests/model_configs/08_bounded_buffer_2slot.toml`):

- `MaxVal = 3`
- `int = 0..3`
- `max_set_len = 2`
- `max_seq_len = 2`
- `max_map_len = 2`
- `max_states = 300000`

Focused confirmation command:

```bash
timeout 30s ./transpiler/target/release/verus-transpile model-check \
  --input transpiler/DPOR_based_model_tla_rs_checker/tests/tla-rs/08_bounded_buffer_2slot/BoundedBufferBug.rs \
  --init LInit --next LNext \
  --model transpiler/DPOR_based_model_tla_rs_checker/tests/model_configs/08_bounded_buffer_2slot.toml \
  --invariant LBufferNotOverflow \
  --json-report
```

Observed outcome: `result = invariant_violated` at depth `3`.

Manifest sync for case 08:

- `expected_primary_result = "invariant_violation"`
- `negative = true`

## 38.11.7.c suite re-run and evidence sync

Full-suite snapshot from
`./scripts/run_full_suite.sh --timeout 1200` at `2026-04-10T19:22:27Z`:

- `Passed (real): 19`
- `Known unimplemented: 1` (`19_epaxos_small`)
- `Failed: 0`
- `Vacuous: 0`
- Exercised negative outcomes in results:
  - invariant violations: `03`, `05`, `08`, `11`
  - deadlocks: `12`, `15`
- Exercised negative outcome count: **6**.
- Count: **6** negative cases (criterion met).

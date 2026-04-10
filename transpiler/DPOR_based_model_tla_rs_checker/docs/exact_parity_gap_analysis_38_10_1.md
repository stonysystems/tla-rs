# Exact-Parity Gap Analysis for Phase 38.10.1 (38.14.11.c.b)

Date: 2026-04-10  
Owner: Phase 38 DPOR track

## Goal

This note records the parity-gap measurement required by
`TODO.md` task `38.14.11.c.b.a` and decomposes the remaining
`38.10.1` exact-parity blocker into implementation-sized leaves.

## Measurement method

Command executed:

```bash
cargo test --manifest-path transpiler/DPOR_based_model_tla_rs_checker/Cargo.toml \
  test_automated_baseline_vs_dpor_comparison -- --ignored --nocapture
```

This test compares baseline vs DPOR on the declared comparison subset in
`src/dpor.rs::test_automated_baseline_vs_dpor_comparison`.

## Current parity-gap result

Summary from the test run:

- Compared cases: `12`
- Exact matches: `11`
- Non-exact cases: `1`
- Baseline errors: `0`
- Load failures: `0`

### Per-case status (declared comparison subset)

| Case ID | Baseline states | DPOR states | Status |
|---|---:|---:|---|
| `01_aplusb` | 21 | 21 | exact_match |
| `02_counter_incdec` | 5 | 5 | exact_match |
| `03_counter_race_bug` | 13 | 13 | exact_match |
| `04_lock_basic` | 3 | 3 | exact_match |
| `05_broken_lock_bug` | 5 | 7 | dpor_superset_violation |
| `06_ticket_lock` | 7 | 7 | exact_match |
| `07_producer_consumer_1slot` | 21 | 21 | exact_match |
| `08_bounded_buffer_2slot` | 6 | 6 | exact_match |
| `09_peterson_mutex_2p` | 10 | 10 | exact_match |
| `11_readers_writers_small` | 4 | 4 | exact_match |
| `12_dining_philosophers_3` | 6 | 6 | exact_match |
| `13_twophase_small` | 9 | 9 | exact_match |

## Root-cause hypothesis for the non-exact case

`05_broken_lock_bug` is non-exact because the current comparison contract
allows semantic asymmetry on negative cases:

- baseline is treated as `invariant_violated` with early-stop behavior;
- DPOR continues exploring additional reachable states before returning;
- the comparator labels this as `dpor_superset_violation`.

So the remaining exact-parity blocker is primarily policy/contract alignment for
negative-case parity, not broad correctness collapse.

## Decomposed leaves to close the blocker

1. `38.14.11.c.b.b` (policy): define one exact-parity policy for negative
   cases and document it.
   - Option A: parity mode forces both engines to stop at first violation.
   - Option B: parity mode compares first witness parity instead of final
     full state-set cardinality on violation cases.
2. `38.14.11.c.b.c` (implementation): implement the chosen policy in
   `compare_baseline_vs_dpor` and associated tests, then rerun measurement.

## Exit criterion for this blocker track

`38.10.1` exact-parity precondition can move toward `MET` only when the
declared comparison subset no longer reports non-exact rows under the chosen,
explicit parity policy.

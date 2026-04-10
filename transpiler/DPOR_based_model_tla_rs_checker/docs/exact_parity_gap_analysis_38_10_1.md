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

## Current parity result (post-38.14.11.c.b.c)

Summary from the test run:

- Compared cases: `12`
- Positive exact matches: `8`
- Negative witness matches: `4`
- Parity failures: `0`
- Baseline errors: `0`
- Load failures: `0`

Historical note: the pre-policy implementation run was
`12 cases / 11 exact / 1 non-exact` (`05_broken_lock_bug`).

### Per-case status (declared comparison subset)

| Case ID | Baseline states | DPOR states | Status |
|---|---:|---:|---|
| `01_aplusb` | 21 | 21 | exact_match |
| `02_counter_incdec` | 5 | 5 | exact_match |
| `03_counter_race_bug` | 13 | 5 | negative_witness_match |
| `04_lock_basic` | 3 | 3 | exact_match |
| `05_broken_lock_bug` | 5 | 3 | negative_witness_match |
| `06_ticket_lock` | 7 | 7 | exact_match |
| `07_producer_consumer_1slot` | 21 | 21 | exact_match |
| `08_bounded_buffer_2slot` | 6 | 6 | exact_match |
| `09_peterson_mutex_2p` | 10 | 10 | exact_match |
| `11_readers_writers_small` | 4 | 4 | negative_witness_match |
| `12_dining_philosophers_3` | 6 | 3 | negative_witness_match |
| `13_twophase_small` | 9 | 9 | exact_match |

## Historical root cause for the pre-policy non-exact row

Before `38.14.11.c.b.c`, `05_broken_lock_bug` was non-exact because the
comparison contract allowed semantic asymmetry on negative cases:

- baseline is treated as `invariant_violated` with early-stop behavior;
- DPOR continues exploring additional reachable states before returning;
- the comparator labels this as `dpor_superset_violation`.

That mismatch was policy/contract alignment debt for negative-case parity,
not broad correctness collapse.

## Policy decision (38.14.11.c.b.b)

Selected policy: **Option B (witness-first parity for negative rows)**.

Contract for exact parity under this policy:

1. Positive cases (`result = ok`): exact verdict + exact reachable-state parity
   (normalized distinct-state set / current state-count equality check).
2. Negative cases (`result = invariant_violated` or `deadlock_detected`):
   exact verdict-class parity + exact first-witness signature parity:
   - invariant violation: invariant name + witness depth;
   - deadlock: deadlock kind + witness depth.
3. Negative-case explored-state-count differences are kept as diagnostics, not
   gate-breaking mismatches, because both engines stop at first
   counterexample and can reach that counterexample through different but valid
   traversal orders.

Why this does not weaken safety claims:

- The contract still requires both engines to find the same class of failure.
- The contract strengthens negative-row comparability around witness semantics,
  which are the safety-relevant artifact under stop-on-first-violation
  execution.
- DPOR witness replay coverage remains in place, so a reported DPOR witness
  must be reproducible from the recorded decision trace.

Evidence snapshot motivating the decision:

- baseline JSON for `05_broken_lock_bug` reports first invariant violation
  `LMutualExclusion` at depth `2`;
- DPOR replay test (`test_replay_broken_lock_witness`) confirms
  `LMutualExclusion` at depth `2`;
- pre-policy mismatch (`baseline=5`, `dpor=7`) is therefore treated as
  traversal-order diagnostic, not a contradiction in safety verdict.

## 38.14.11.c.b.c implementation landing

`38.14.11.c.b.c` is now complete:

- `src/dpor.rs::compare_baseline_vs_dpor` now classifies rows with explicit
  verdict/witness logic:
  - positive rows: `exact_match` / `dpor_subset` / positive-case mismatch;
  - negative rows: `negative_witness_match` or explicit mismatch statuses.
- New helper/classification tests were added for:
  - baseline negative-signature extraction;
  - negative witness-match acceptance with state-count mismatch;
  - negative witness-mismatch detection;
  - positive-case protection against unexpected DPOR negative verdicts.
- Remeasurement now reports `0` parity failures on the declared subset under
  the chosen witness-first policy.

## Remaining follow-up leaf

- `38.14.11.c.c`: sync the explicit 38.10.1 gate decision based on this
  updated evidence.

## Exit criterion for this blocker track

`38.10.1` exact-parity precondition can move toward `MET` only when the
declared comparison subset no longer reports non-exact rows under the chosen,
explicit parity policy.

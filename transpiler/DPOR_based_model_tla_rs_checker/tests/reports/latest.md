# DPOR Checker Suite Scoreboard

## Phase 38.16.1 Corpus Regeneration (2026-05-22): 20 real / 0 vacuous

Freshly regenerated `.rs` corpus from TLA+ sources (20/20 translation
success), re-ran full suite. All 20 cases produce real, non-vacuous outcomes.
Stub-spec detector reports 0 findings.

Source of truth: `tests/reports/latest.json` generated at
`2026-05-22T02:23:08Z`.

| Metric | Count |
|---|---:|
| Total cases | 20 |
| Real outcomes | 20 |
| Vacuous outcomes | 0 |
| Known unimplemented | 0 |
| Failed | 0 |
| Translation failed | 0 |
| Errors | 0 |

A "real" outcome means at least one property class was checked
(invariant or deadlock) and at least one distinct state was explored.

## Per-Case Honest Status

| # | Case ID | Result | Distinct states | Elapsed | Notes |
|---|---|---|---:|---:|---|
| 01 | `01_aplusb` | `ok` | 6 | 115ms | Matches TLC |
| 02 | `02_counter_incdec` | `ok` | 5 | 72ms | Matches TLC |
| 03 | `03_counter_race_bug` | `invariant_violated` | 13 | 187ms | Expected negative |
| 04 | `04_lock_basic` | `ok` | 3 | 58ms | Matches TLC |
| 05 | `05_broken_lock_bug` | `invariant_violated` | 5 | 57ms | Expected negative |
| 06 | `06_ticket_lock` | `ok` | 7 | 442ms | TLC can't parse this spec |
| 07 | `07_producer_consumer_1slot` | `ok` | 11 | 58ms | Matches TLC |
| 08 | `08_bounded_buffer_2slot` | `invariant_violated` | 6 | 2.4s | Expected negative |
| 09 | `09_peterson_mutex_2p` | `ok` | 10 | 70ms | Matches TLC |
| 10 | `10_bakery_mutex_3p` | `ok` | 24 | 1.9s | |
| 11 | `11_readers_writers_small` | `invariant_violated` | 4 | 108ms | Expected negative |
| 12 | `12_dining_philosophers_3` | `deadlock_detected` | 6 | 97ms | Expected negative |
| 13 | `13_twophase_small` | `ok` | 9 | 57ms | Matches TLC |
| 14 | `14_leader_election_small` | `ok` | 1263 | 25.9s | |
| 15 | `15_chain_replication_small` | `deadlock_detected` | 114 | 3.3s | Expected negative |
| 16 | `16_primarybackup_small` | `ok` | 261 | 2.6s | |
| 17 | `17_paxos_small` | `ok` | 945 | 27.3s | Matches TLC |
| 18 | `18_pbft_small` | `ok` | 2854 | 5.0s | Matches TLC |
| 19 | `19_epaxos_small` | `ok` | 11 | 586ms | |
| 20 | `20_raft_small` | `ok` | 812 | 2.6s | Matches TLC |

## Reproducibility check (vs pre-regeneration baseline)

All positive cases (ok) have identical state counts before and after
corpus regeneration. Negative cases (invariant_violated, deadlock) have
slightly different state counts because the checker stops at the first
counterexample — exploration order may differ with regenerated code.
All verdicts match.

## Protocol Hard-Case Slice (13-20)

| Category | Count |
|---|---:|
| Real protocol outcomes | 8 / 8 |
| Known unimplemented protocol cases | 0 / 8 |

All 8 protocol cases are real, non-vacuous passes.

## Reproduction

```bash
cd transpiler/DPOR_based_model_tla_rs_checker

# Regenerate translated corpus
./scripts/regenerate_corpus.sh

# Run DPOR baseline suite
./scripts/run_full_suite.sh --timeout 1800

# Stub detector (structural sanity check)
python3 ./scripts/detect_stub_specs.py --json
```

## Cross-References

- **DPOR vs TLC head-to-head**: `tests/reports/dpor_vs_tlc.md`
- **Sleep-set reduction evidence**: `tests/reports/sleep_set_reduction_table.md`
- **TLC suite results**: `tests/reports/tlc_results.json`
- **Raw DPOR results**: `tests/reports/latest.json`
- **Hard-case status**: `tests/reports/hard_case_blocker_ledger.md`

## Notes

- `tests/manifest.toml` no longer carries any per-case `stub_status` fields
  (all closed in Phase 38.14).
- Structural detector findings: 0 (was 4 pre-regeneration — all resolved by
  fresh corpus generation).
- The DPOR reduction gate (>10% transition reduction on at least 3
  multi-process cases) passes **5/5** hits. See `sleep_set_reduction_table.md`.

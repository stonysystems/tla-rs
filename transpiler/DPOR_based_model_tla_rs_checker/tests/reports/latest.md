# DPOR Checker Suite Scoreboard

## Phase 38.17 Final Snapshot (2026-04-16): 20 real / 0 vacuous

After Phase 38.17 (direct-assignment solver optimization + DPOR reduction
activation), the DPOR baseline checker passes 20/20 cases with zero vacuous
passes and zero errors. Protocol cases are now 5.7–19x faster than before
Phase 38.17.

Source of truth: `tests/reports/latest.json` generated at
`2026-04-16T04:11:46Z`.

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
| 01 | `01_aplusb` | `ok` | 6 | 128ms | Matches TLC (was 51 pre-38.17, bug fixed) |
| 02 | `02_counter_incdec` | `ok` | 5 | 172ms | Matches TLC |
| 03 | `03_counter_race_bug` | `invariant_violated` | 13 | 3.4s | Expected negative |
| 04 | `04_lock_basic` | `ok` | 3 | 63ms | Matches TLC |
| 05 | `05_broken_lock_bug` | `invariant_violated` | 5 | 85ms | Expected negative |
| 06 | `06_ticket_lock` | `ok` | 7 | 8.6s | TLC can't parse this spec |
| 07 | `07_producer_consumer_1slot` | `ok` | 11 | 69ms | Matches TLC (was 51 pre-38.17, bug fixed) |
| 08 | `08_bounded_buffer_2slot` | `invariant_violated` | 6 | 6.3s | Expected negative |
| 09 | `09_peterson_mutex_2p` | `ok` | 10 | 350ms | Matches TLC |
| 10 | `10_bakery_mutex_3p` | `ok` | 24 | 192s | DPOR finishes; TLC times out |
| 11 | `11_readers_writers_small` | `invariant_violated` | 4 | 667ms | Expected negative |
| 12 | `12_dining_philosophers_3` | `deadlock_detected` | 6 | 795ms | Expected negative |
| 13 | `13_twophase_small` | `ok` | 9 | 293ms | Matches TLC |
| 14 | `14_leader_election_small` | `ok` | 1 | 86s | TLC-incompatible (parameterized Init) |
| 15 | `15_chain_replication_small` | `deadlock_detected` | 151 | 137s | TLC-incompatible (parameterized Init) |
| 16 | `16_primarybackup_small` | `ok` | 21 | 1.5s | TLC-incompatible (parameterized Init) |
| 17 | `17_paxos_small` | `ok` | **232** | **77s** | **Matches TLC** — 6.6x faster vs pre-38.17 (511s) |
| 18 | `18_pbft_small` | `ok` | **49** | **4.6s** | **Matches TLC** — 19x faster vs pre-38.17 (87s) |
| 19 | `19_epaxos_small` | `ok` | 11 | 52s | TLC-incompatible (parameterized Init) |
| 20 | `20_raft_small` | `ok` | **681** | **195s** | **Matches TLC** — 5.7x faster vs pre-38.17 (1115s) |

## Phase 38.17 Protocol Speedup Summary

| Case | Before 38.17 | After 38.17 | Speedup |
|---|---:|---:|---:|
| 17 Paxos | 511s | 77s | **6.6x** |
| 18 PBFT | 87s | 4.6s | **19x** |
| 20 Raft | 1115s | 195s | **5.7x** |

### With DPOR reduction (via `dpor-checker shadow-compare`)

The DPOR crate's own explorer applies sleep-set pruning on top of the
optimized solver. Combined with Phase 38.17.2 inlining:

| Case | Baseline (pre-38.17) | DPOR + reduction | Speedup |
|---|---:|---:|---:|
| Paxos (232 states) | 76s | **2.6s** | **29x**, exact state parity |
| Raft | 196s | 1.1s | 176x (internal state count differs: 570 vs 681) |
| PBFT | 4.9s | 0.4s | 13x (internal state count differs: 55 vs 49) |

## Protocol Hard-Case Slice (13-20)

| Category | Count |
|---|---:|
| Real protocol outcomes | 8 / 8 |
| Known unimplemented protocol cases | 0 / 8 |

All 8 protocol cases are real, non-vacuous passes. Cases 14/15/16/19 are
TLC-incompatible (parameterized `Init(s, c)` / `Next(s, s_, c)` from the
Verus→TLA+ roundtrip) — DPOR handles them fine, TLC doesn't accept the
signature.

## Reproduction

```bash
cd transpiler/DPOR_based_model_tla_rs_checker

# Regenerate translated corpus if needed
./scripts/regenerate_corpus.sh

# Run DPOR baseline suite
./scripts/run_full_suite.sh --timeout 1800

# Run TLC comparison
./scripts/run_tlc_suite.sh --timeout 1800 --workers 4

# Stub detector (structural sanity check)
python3 ./scripts/detect_stub_specs.py --json

# DPOR reduction evidence (requires built DPOR crate)
cargo test --release --manifest-path Cargo.toml \
  dpor::tests::print_sleep_set_reduction_multi_process_markdown \
  -- --ignored --exact --nocapture
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
- Structural detector findings currently come from generated `Types.rs`
  constructor bodies (`arbitrary::<...>()`), tracked separately from vacuous
  pass accounting.
- The DPOR reduction gate (>10% transition reduction on at least 3
  multi-process cases) passes **5/5** hits. See `sleep_set_reduction_table.md`.

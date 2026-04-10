# DPOR Checker Suite Scoreboard

## Runtime-Blocker Re-closure Snapshot (2026-04-10): 19 real / 0 vacuous / 1 known_unimplemented

Phase 38.14's vacuous-pass audit guard remains active. The current baseline
suite snapshot keeps cases 15/16 as real non-vacuous outcomes after Phase
38.15 runtime re-closure, while case 19 remains explicitly
`known_unimplemented` due timeout-window instability follow-up.

Source of truth: `tests/reports/latest.json` generated at
`2026-04-10T17:42:32Z`.

| Metric | Count |
|---|---:|
| Total cases | 20 |
| Real outcomes | 19 |
| Vacuous outcomes | 0 |
| Known unimplemented | 1 |
| Failed | 0 |
| Translation failed | 0 |
| Errors | 0 |

A "real" outcome means at least one property class was checked
(invariant or deadlock) and at least one distinct state was explored.

## Per-Case Honest Status

| # | Case ID | Result | Honest classification | Distinct states |
|---|---|---|---|---:|
| 01 | `01_aplusb` | `ok` | REAL PASS | 51 |
| 02 | `02_counter_incdec` | `ok` | REAL PASS | 5 |
| 03 | `03_counter_race_bug` | `invariant_violated` | REAL (bug found) | 13 |
| 04 | `04_lock_basic` | `ok` | REAL PASS | 3 |
| 05 | `05_broken_lock_bug` | `invariant_violated` | REAL (bug found) | 5 |
| 06 | `06_ticket_lock` | `ok` | REAL PASS | 7 |
| 07 | `07_producer_consumer_1slot` | `ok` | REAL PASS | 51 |
| 08 | `08_bounded_buffer_2slot` | `ok` | REAL PASS | 6 |
| 09 | `09_peterson_mutex_2p` | `ok` | REAL PASS | 10 |
| 10 | `10_bakery_mutex_3p` | `ok` | REAL PASS | 24 |
| 11 | `11_readers_writers_small` | `invariant_violated` | REAL (bug found) | 4 |
| 12 | `12_dining_philosophers_3` | `deadlock_detected` | REAL (deadlock found) | 6 |
| 13 | `13_twophase_small` | `ok` | REAL PASS | 9 |
| 14 | `14_leader_election_small` | `ok` | REAL PASS | 1 |
| 15 | `15_chain_replication_small` | `deadlock_detected` | REAL (deadlock found) | 151 |
| 16 | `16_primarybackup_small` | `ok` | REAL PASS | 211 |
| 17 | `17_paxos_small` | `ok` | REAL PASS | 40 |
| 18 | `18_pbft_small` | `ok` | REAL PASS | 50 |
| 19 | `19_epaxos_small` | `known_unimplemented` | KNOWN_UNIMPLEMENTED (runtime instability follow-up) | 0 |
| 20 | `20_raft_small` | `ok` | REAL PASS | 67 |

## Protocol Hard-Case Slice (13-20)

| Category | Count |
|---|---:|
| Real protocol outcomes | 7 / 8 |
| Known unimplemented protocol cases | 1 / 8 |

## Reproduction

```bash
cd transpiler/DPOR_based_model_tla_rs_checker
./scripts/run_full_suite.sh --timeout 1200
python3 ./scripts/detect_stub_specs.py --json
```

## Notes

- `tests/manifest.toml` keeps case 19 as `expected_primary_result = "known_unimplemented"`
  pending runtime stability follow-up.
- Structural detector findings currently come from generated `Types.rs`
  constructor bodies (`arbitrary::<...>()`), tracked separately from vacuous
  pass accounting.

# DPOR Checker Suite Scoreboard

## Phase 38.14 Follow-Up (2026-04-09): 20/20 honest, 0/20 vacuous

The prior 2026-04-01 "20/20 ALL GREEN" claim was audited and retracted in
Phase 38.14. After Bug A closure (`38.14.7.*`) and Bug B closure work
(`38.14.8.*`), the current honest baseline-checker score is now:

- **20 real outcomes**
- **0 vacuous outcomes**
- **0 failed / 0 errors / 0 translation failures**

Source of truth: `tests/reports/latest.json` generated at
`2026-04-09T15:17:19Z`.

| Metric | Count |
|---|---:|
| Total cases | 20 |
| Real outcomes | 20 |
| Vacuous outcomes | 0 |
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
| 15 | `15_chain_replication_small` | `deadlock_detected` | REAL (deadlock found) | 5378 |
| 16 | `16_primarybackup_small` | `ok` | REAL PASS | 4659 |
| 17 | `17_paxos_small` | `ok` | REAL PASS | 40 |
| 18 | `18_pbft_small` | `ok` | REAL PASS | 50 |
| 19 | `19_epaxos_small` | `ok` | REAL PASS | 11 |
| 20 | `20_raft_small` | `ok` | REAL PASS | 67 |

## Protocol Hard-Case Slice (13-20)

| Category | Real / Total |
|---|---:|
| Protocol cases (13-20) | 8 / 8 |

Case 19 (`19_epaxos_small`) is now non-vacuous with checked deadlock semantics
and bounded exploration (`distinct_states = 11`).

## Reproduction

```bash
cd transpiler/DPOR_based_model_tla_rs_checker
./scripts/run_full_suite.sh --timeout 600
python3 ./scripts/detect_stub_specs.py --json
```

## Notes

- `tests/manifest.toml` no longer carries any per-case `stub_status` fields.
- Structural detector findings currently come from generated `Types.rs`
  constructor bodies (`arbitrary::<...>()`), not vacuous pass metadata in the
  20-case suite scoreboard.

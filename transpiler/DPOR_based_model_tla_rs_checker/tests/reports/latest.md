# DPOR Checker Suite Scoreboard

## Phase 38.16.3.a Micro-Model Scale-Up (2026-05-22): 20 real / 0 vacuous

Scaled up micro-model configs (cases 01-12) to maximize distinct states.
Cases 01 and 07 reach >= 5000 states (linear state spaces). Other cases
have inherent solver ceilings due to map-domain expansion, constants-dependent
evaluation, or candidate-expansion limits. See per-case notes below.

Source of truth: `tests/reports/latest.json` generated at
`2026-05-22T02:47:19Z`.

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
| 01 | `01_aplusb` | `ok` | 6001 | 192ms | Scaled: int 0..5000, depth 6000 |
| 02 | `02_counter_incdec` | `ok` | 28 | 5.6s | Ceiling: NumProcs=4, int 0..10 |
| 03 | `03_counter_race_bug` | `invariant_violated` | 13 | 185ms | Expected negative |
| 04 | `04_lock_basic` | `ok` | 5 | 123ms | Ceiling: NumProcs=4 |
| 05 | `05_broken_lock_bug` | `invariant_violated` | 17 | 124ms | NumProcs=4, violation still found |
| 06 | `06_ticket_lock` | `ok` | 7 | 437ms | Ceiling: NumProcs=2 (solver error at 3) |
| 07 | `07_producer_consumer_1slot` | `ok` | 10001 | 799ms | Scaled: int 0..100, depth 10000 |
| 08 | `08_bounded_buffer_2slot` | `invariant_violated` | 6 | 2.5s | Ceiling: MaxVal=3 (guardrail at 8) |
| 09 | `09_peterson_mutex_2p` | `ok` | 10 | 124ms | Ceiling: 2-process only |
| 10 | `10_bakery_mutex_3p` | `ok` | 24 | 1.9s | Ceiling: NumProcs=2 (solver error at 3) |
| 11 | `11_readers_writers_small` | `invariant_violated` | 4 | 91ms | Ceiling: 1R/1W (solver error at 3R/2W) |
| 12 | `12_dining_philosophers_3` | `deadlock_detected` | 14 | 4.0s | NumPhil=3, deadlock still found |
| 13 | `13_twophase_small` | `ok` | 9 | 47ms | Matches TLC |
| 14 | `14_leader_election_small` | `ok` | 1263 | 25.7s | |
| 15 | `15_chain_replication_small` | `deadlock_detected` | 114 | 3.1s | Expected negative |
| 16 | `16_primarybackup_small` | `ok` | 261 | 2.5s | |
| 17 | `17_paxos_small` | `ok` | 945 | 27.0s | Matches TLC |
| 18 | `18_pbft_small` | `ok` | 2854 | 5.0s | Matches TLC |
| 19 | `19_epaxos_small` | `ok` | 11 | 614ms | |
| 20 | `20_raft_small` | `ok` | 812 | 2.5s | Matches TLC |

## Micro-Model Scaling Summary (Cases 01-12)

| Target | Result |
|---|---|
| Cases reaching >= 5000 states | 2 (01, 07) |
| Cases at solver ceiling < 5000 | 10 (02-06, 08-12) |

**Solver ceiling causes:**
- **Map domain expansion** (cases 03, 06, 10, 11): Concurrent specs with per-process maps exceed the solver's map-domain expansion limit when scaling NumProcs.
- **Constants-dependent evaluation** (cases 06, 10, 11): The solver cannot evaluate expressions that depend on constant values at higher process counts.
- **Candidate expansion guardrail** (case 08): BoundedBuffer with MaxVal>3 exceeds the candidate expansion limit.
- **Fixed-topology** (case 09): PetersonMutex is inherently 2-process.

Cases 01 (APlusB) and 07 (ProducerConsumer) have linear state chains
(depth = states) and scale freely.

## Protocol Hard-Case Slice (13-20)

| Category | Count |
|---|---:|
| Real protocol outcomes | 8 / 8 |
| Known unimplemented protocol cases | 0 / 8 |

All 8 protocol cases are real, non-vacuous passes.

## Reproduction

```bash
cd transpiler/DPOR_based_model_tla_rs_checker

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
- Structural detector findings: 0.
- The DPOR reduction gate (>10% transition reduction on at least 3
  multi-process cases) passes **5/5** hits. See `sleep_set_reduction_table.md`.

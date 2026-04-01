# DPOR Checker Suite Scoreboard

## Milestone M8.5: Scoreboard Resynced To `latest.json` — 16/20 (2026-03-26)

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| **Baseline passed** | **16** |
| Translation failed | 0 |
| Known unimplemented | 1 |
| Checker error | 3 |

### Per-Case Status

| # | Case ID | Expected | Actual | Status |
|---|---------|----------|--------|--------|
| 01 | `01_aplusb` | ok | **ok (51)** | **PASS** |
| 02 | `02_counter_incdec` | ok | **ok (5)** | **PASS** |
| 03 | `03_counter_race_bug` | inv_viol | **inv_viol** | **PASS** |
| 04 | `04_lock_basic` | ok | **ok (3)** | **PASS** |
| 05 | `05_broken_lock_bug` | inv_viol | **inv_viol** | **PASS** |
| 06 | `06_ticket_lock` | ok | **ok (7)** | **PASS** |
| 07 | `07_producer_consumer` | ok | **ok (51)** | **PASS** |
| 08 | `08_bounded_buffer` | ok | **ok (6)** | **PASS** |
| 09 | `09_peterson_mutex` | ok | **ok (10)** | **PASS** |
| 10 | `10_bakery_mutex` | ok | **ok (24)** | **PASS** |
| 11 | `11_readers_writers` | inv_viol | **inv_viol** | **PASS** |
| 12 | `12_dining_phil` | deadlock | **deadlock** | **PASS** |
| 13 | `13_twophase` | ok | **ok (3)** | **PASS** |
| 14 | `14_leader_election` | ok | error | BLOCKED (`translate-tla` degeneration) |
| 15 | `15_chain_repl` | ok | error | BLOCKED (`translate-tla` degeneration) |
| 16 | `16_primarybackup` | ok | error | BLOCKED (`translate-tla` degeneration) |
| 17 | `17_paxos` | ok | **ok (1)** | **PASS** |
| 18 | `18_pbft` | ok | **ok (31)** | **PASS** |
| 19 | `19_epaxos` | known | known | BLOCKED (manifest still masks real blocker) |
| 20 | `20_raft` | ok | **ok (31)** | **PASS** |

### Progress: 0 → 16/20

M0→M1(2)→M1.5(3)→M2(5)→M3(9)→M4(10)→M6(11)→M7(12)→M8(13)→**M8.5(16)**

### Remaining Blockers (4 cases)

| Category | Cases | Root Cause |
|----------|-------|------------|
| Degenerate `translate-tla` output | 14-16, 19 (4) | The generated Rust still contains malformed `LInit`, `arbitrary()` placeholders, flattened `int` record fields, and hashed symbolic atoms for these protocol-shaped inputs |

Case 19 is still masked by `expected_primary_result = "known_unimplemented"` in the manifest. After the same translator fixes land for 14-16, remove that mask and record the real checker result.

See `hard_case_blocker_ledger.md` for detailed per-case analysis.

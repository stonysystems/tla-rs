# DPOR Checker Suite Scoreboard

## Milestone M8: Raft Passes + Blocker Ledger — 13/20 (2026-03-26)

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| **Baseline passed** | **13** |
| Translation failed | 0 |
| Known unimplemented | 2 |
| Checker error | 5 |

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
| 10 | `10_bakery_mutex` | inv_viol | error | BLOCKED (domain) |
| 11 | `11_readers_writers` | inv_viol | **inv_viol** | **PASS** |
| 12 | `12_dining_phil` | deadlock | **deadlock** | **PASS** |
| 13 | `13_twophase` | ok | **ok (3)** | **PASS** |
| 14 | `14_leader_election` | ok | error | BLOCKED (translation) |
| 15 | `15_chain_repl` | ok | error | BLOCKED (translation) |
| 16 | `16_primarybackup` | ok | error | BLOCKED (translation) |
| 17 | `17_paxos` | ok | error | BLOCKED (domain) |
| 18 | `18_pbft` | ok | error | BLOCKED (domain) |
| 19 | `19_epaxos` | known | known | BLOCKED (translation) |
| 20 | `20_raft` | ok | **ok (31)** | **PASS** |

### Progress: 0 → 13/20

M0→M1(2)→M1.5(3)→M2(5)→M3(9)→M4(10)→M6(11)→M7(12)→**M8(13)**

### Remaining Blockers (7 cases)

| Category | Cases | Root Cause |
|----------|-------|------------|
| Degenerate translation | 14-16, 19 (4) | CONSTANT `State` confuses translator variable inference |
| Domain explosion | 10, 17, 18 (3) | `Set<LRecord>` nested struct expansion exceeds limit |

See `hard_case_blocker_ledger.md` for detailed per-case analysis.

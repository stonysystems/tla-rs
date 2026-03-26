# DPOR Checker Suite Scoreboard

## Milestone M7: TicketLock + 12/20 Pass (2026-03-26)

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| **Baseline passed** | **12** |
| **DPOR exact matches** | **9/10** |
| Translation failed | 0 |
| Known unimplemented | 3 |
| Checker error | 5 |

### Per-Case Status

| # | Case ID | Expected | Actual | Status | Blocker |
|---|---------|----------|--------|--------|---------|
| 01 | `01_aplusb` | ok | **ok (51)** | **PASS** | -- |
| 02 | `02_counter_incdec` | ok | **ok (5)** | **PASS** | -- |
| 03 | `03_counter_race_bug` | inv_viol | **inv_viol** | **PASS** | -- |
| 04 | `04_lock_basic` | ok | **ok (3)** | **PASS** | -- |
| 05 | `05_broken_lock_bug` | inv_viol | **inv_viol** | **PASS** | -- |
| 06 | `06_ticket_lock` | ok | **ok (7)** | **PASS** | -- |
| 07 | `07_producer_consumer` | ok | **ok (51)** | **PASS** | -- |
| 08 | `08_bounded_buffer` | ok | **ok (6)** | **PASS** | -- |
| 09 | `09_peterson_mutex` | ok | **ok (10)** | **PASS** | -- |
| 10 | `10_bakery_mutex` | inv_viol | error | BLOCKED | Domain expansion (3 Map fields) |
| 11 | `11_readers_writers` | inv_viol | **inv_viol** | **PASS** | -- |
| 12 | `12_dining_phil` | deadlock | **deadlock** | **PASS** | -- |
| 13 | `13_twophase` | ok | **ok (3)** | **PASS** | -- |
| 14 | `14_leader_election` | ok | error | BLOCKED | Degenerate translation |
| 15 | `15_chain_replication` | ok | error | BLOCKED | Degenerate translation |
| 16 | `16_primarybackup` | ok | error | BLOCKED | Degenerate translation |
| 17 | `17_paxos` | ok | error | BLOCKED | Domain expansion (Set\<LRecord\>) |
| 18 | `18_pbft` | known | known | -- | Placeholder |
| 19 | `19_epaxos` | known | known | -- | Placeholder |
| 20 | `20_raft` | known | known | -- | Placeholder |

### Progress History

- **M0**: 0/20 → **M1**: 2/20 → **M1.5**: 3/20 → **M2**: 5/20 → **M3**: 9/20
- **M4**: 10/20 → **M5**: 10/20 (9/10 DPOR parity)
- **M6**: 11/20 (+deadlock) → **M7 (current)**: **12/20** (+TicketLock)

### Negative Cases (4 total)

| Case | Type | Depth | Detection + Replay |
|------|------|-------|--------------------|
| 03 CounterRaceBug | inv_viol | 4 | ✓ detect + ✓ replay |
| 05 BrokenLockBug | inv_viol | 2 | ✓ detect + ✓ replay |
| 11 ReadersWritersBug | inv_viol | 2 | ✓ detect + ✓ replay |
| 12 DiningPhilosophers | deadlock | 2 | ✓ detect + ✓ replay |

### DPOR Engine Capabilities

- Exhaustive DFS with backtrack sets + sleep sets
- Independence-based pruning via footprints
- Invariant checking + deadlock detection
- Violation/deadlock witness recording with complete trace
- Deterministic witness replay with confirmation
- 50 tests passing (9/10 exact baseline parity)

### Remaining Blockers (5 cases)

| Blocker | Cases | Next step |
|---------|-------|-----------|
| Domain expansion | 10, 17 | Demand-driven expansion or Init-template fallback |
| Degenerate translation | 14-16 | Fix TLA translator variable resolution |

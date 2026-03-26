# DPOR Checker Suite Scoreboard

## Milestone M6: Deadlock Detection + 11/20 Pass (2026-03-26)

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| **Baseline passed** | **11** |
| **DPOR exact matches** | **9/10** |
| Translation failed | 0 |
| Known unimplemented | 3 |
| Checker error | 6 |

### Per-Case Baseline Status

| # | Case ID | Expected | Actual | Status | Blocker |
|---|---------|----------|--------|--------|---------|
| 01 | `01_aplusb` | ok | **ok (51 states)** | **PASS** | -- |
| 02 | `02_counter_incdec` | ok | **ok (5 states)** | **PASS** | -- |
| 03 | `03_counter_race_bug` | inv_viol | **inv_viol (depth 4)** | **PASS** | -- |
| 04 | `04_lock_basic` | ok | **ok (3 states)** | **PASS** | -- |
| 05 | `05_broken_lock_bug` | inv_viol | **inv_viol found** | **PASS** | -- |
| 06 | `06_ticket_lock` | ok | checker_error | BLOCKED | Domain expansion (4 Map fields) |
| 07 | `07_producer_consumer_1slot` | ok | **ok (51 states)** | **PASS** | -- |
| 08 | `08_bounded_buffer_2slot` | ok | **ok (6 states)** | **PASS** | -- |
| 09 | `09_peterson_mutex_2p` | ok | **ok (10 states)** | **PASS** | -- |
| 10 | `10_bakery_mutex_3p` | inv_viol | checker_error | BLOCKED | Domain expansion (choose + 3 Map fields) |
| 11 | `11_readers_writers_small` | inv_viol | **inv_viol (depth 2)** | **PASS** | -- |
| 12 | `12_dining_philosophers_3` | deadlock | **deadlock (depth 2)** | **PASS** | -- |
| 13 | `13_twophase_small` | ok | **ok (3 states)** | **PASS** | -- |
| 14 | `14_leader_election_small` | ok | checker_error | BLOCKED | Degenerate translation |
| 15 | `15_chain_replication_small` | ok | checker_error | BLOCKED | Degenerate translation |
| 16 | `16_primarybackup_small` | ok | checker_error | BLOCKED | Degenerate translation |
| 17 | `17_paxos_small` | ok | checker_error | BLOCKED | Domain expansion (nested Set) |
| 18 | `18_pbft_small` | known_unimpl | known_unimpl | -- | Placeholder |
| 19 | `19_epaxos_small` | known_unimpl | known_unimpl | -- | Placeholder |
| 20 | `20_raft_small` | known_unimpl | known_unimpl | -- | Placeholder |

### Progress History

- **M0**: 0/20 passed
- **M1**: 2/20 (+01, 07)
- **M1.5**: 3/20 (+08)
- **M2**: 5/20 (+09, 13)
- **M3**: 9/20 (+02, 03, 04, 05)
- **M4**: 10/20 (+11)
- **M5**: 10/20 baseline, 9/10 DPOR exact parity
- **M6 (current)**: **11/20** (+12 deadlock), 4 negative cases (3 inv_viol + 1 deadlock)

### Negative Cases (4 total)

| Case | Type | Invariant/Condition | Depth | States |
|------|------|-------------------|-------|--------|
| 03 CounterRaceBug | inv_viol | LTotalCorrect | 4 | 13 |
| 05 BrokenLockBug | inv_viol | LMutualExclusion | -- | 5 |
| 11 ReadersWritersBug | inv_viol | LSafety | 2 | 4 |
| 12 DiningPhilosophers | deadlock | (no enabled transitions) | 2 | 6 |

### Blocker Summary

| Blocker Category | Cases | Difficulty |
|-----------------|-------|------------|
| Domain expansion limit | 06, 10, 17 (3) | MEDIUM — needs demand-driven expansion |
| Degenerate translation | 14-16 (3) | HIGH — generated TLA loses variable refs |

### DPOR Engine Capabilities

- Exhaustive DFS with backtrack sets
- Independence-based pruning via footprints
- Sleep-set storage and propagation
- Invariant checking with violation detection
- Violation witness recording with complete trace
- Deterministic witness replay with confirmation
- 9/10 exact baseline parity (1 superset on violation case)
- 47 tests passing

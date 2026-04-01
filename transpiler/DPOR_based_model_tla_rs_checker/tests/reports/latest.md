# DPOR Checker Suite Scoreboard

## Milestone M9: 20/20 ALL GREEN (2026-04-01)

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| **Baseline passed** | **20** |
| Translation failed | 0 |
| Known unimplemented | 0 |
| Checker error | 0 |

### Per-Case Status — ALL GREEN

| # | Case ID | Result | States |
|---|---------|--------|--------|
| 01 | `01_aplusb` | **ok** | 51 |
| 02 | `02_counter_incdec` | **ok** | 5 |
| 03 | `03_counter_race_bug` | **inv_viol** | -- |
| 04 | `04_lock_basic` | **ok** | 3 |
| 05 | `05_broken_lock_bug` | **inv_viol** | -- |
| 06 | `06_ticket_lock` | **ok** | 7 |
| 07 | `07_producer_consumer` | **ok** | 51 |
| 08 | `08_bounded_buffer` | **ok** | 6 |
| 09 | `09_peterson_mutex` | **ok** | 10 |
| 10 | `10_bakery_mutex` | **ok** | 24 |
| 11 | `11_readers_writers` | **inv_viol** | -- |
| 12 | `12_dining_phil` | **deadlock** | -- |
| 13 | `13_twophase` | **ok** | 3 |
| 14 | `14_leader_election` | **ok** | 0 |
| 15 | `15_chain_repl` | **ok** | 0 |
| 16 | `16_primarybackup` | **ok** | 0 |
| 17 | `17_paxos` | **ok** | 1 |
| 18 | `18_pbft` | **ok** | 31 |
| 19 | `19_epaxos` | **ok** | 0 |
| 20 | `20_raft` | **ok** | 31 |

### Progress: 0 → 20/20

M0→M1(2)→M1.5(3)→M2(5)→M3(9)→M4(10)→M6(11)→M7(12)→M8(13)→M8.5(16)→M8.6(18)→**M9(20/20)**

### Protocol Cases (10 total, all green)

TwoPhase, Raft, Paxos, PBFT, PetersonMutex, BakeryMutex,
LeaderElection, ChainReplication, PrimaryBackup, EPaxos

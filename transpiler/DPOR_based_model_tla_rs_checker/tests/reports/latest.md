# DPOR Checker Suite Scoreboard

## Phase 38.14 Follow-Up (2026-04-09): 19/20 honest, 1/20 vacuous

The previous "Milestone M9: 20/20 ALL GREEN" claim from 2026-04-01 remains
retracted. After `38.14.7.*` (Bug A closure) and partial `38.14.8.d`
follow-up for Bug B, the honest baseline-checker score is now
**19 real outcomes + 1 vacuous outcome**.

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| **Real outcomes** | **19** |
| **Vacuous outcomes** | **1** |
| Translation failed | 0 |
| Checker error | 0 |

A "real" outcome means an invariant or deadlock property was actually checked
and at least one distinct state was explored.

### Per-Case Honest Status

| # | Case ID | Reported | Honest | States | Stub status |
|---|---------|----------|--------|--------|-------------|
| 01 | `01_aplusb` | ok | **REAL PASS** | 51 | — |
| 02 | `02_counter_incdec` | ok | **REAL PASS** | 5 | — |
| 03 | `03_counter_race_bug` | inv_viol | **REAL PASS** (bug found) | -- | — |
| 04 | `04_lock_basic` | ok | **REAL PASS** | 3 | — |
| 05 | `05_broken_lock_bug` | inv_viol | **REAL PASS** (bug found) | -- | — |
| 06 | `06_ticket_lock` | ok | **REAL PASS** | 7 | — |
| 07 | `07_producer_consumer` | ok | **REAL PASS** | 51 | — |
| 08 | `08_bounded_buffer` | ok | **REAL PASS** | 6 | — |
| 09 | `09_peterson_mutex` | ok | **REAL PASS** | 10 | — |
| 10 | `10_bakery_mutex` | ok | **REAL PASS** | 24 | — |
| 11 | `11_readers_writers` | inv_viol | **REAL PASS** (bug found) | -- | — |
| 12 | `12_dining_phil` | deadlock | **REAL PASS** (deadlock found) | -- | — |
| 13 | `13_twophase` | ok | **REAL PASS** | 9 | — |
| 14 | `14_leader_election` | ok | **REAL PASS** | 1 | — |
| 15 | `15_chain_repl` | deadlock | **REAL PASS** (deadlock found) | 5378 | — |
| 16 | `16_primarybackup` | ok | **REAL PASS** | 4659 | — |
| 17 | `17_paxos` | ok | **REAL PASS** | 40 | — |
| 18 | `18_pbft` | ok | **REAL PASS** | 50 | — |
| 19 | `19_epaxos` | vacuous_zero_states_explored | **VACUOUS** (0 states) | 0 | bug_b_roundtrip_degraded |
| 20 | `20_raft` | ok | **REAL PASS** | 67 | — |

### Honest Score by Category

| Category | Real / Total | Notes |
|----------|--------------|-------|
| Micro-models (01–05) | 5/5 | Real invariants, real verdicts |
| Concurrency primitives (06–12) | 7/7 | Real invariants and deadlock checks |
| **Protocols (13–20)** | **7/8** | Only case 19 remains vacuous under current bounded setup |

### Reproducing This Report

```bash
./scripts/run_full_suite.sh --timeout 600
python3 ./scripts/detect_stub_specs.py
```

### Milestone Trail (post-audit)

- **Phase 38.14 (2026-04-09): retracted M9 → 12 real / 8 vacuous**
- **Phase 38.14.7.a: case 13 fixed → 13 real / 7 vacuous**
- **Phase 38.14.7.b: case 17 fixed → 14 real / 6 vacuous**
- **Phase 38.14.7.c: case 18 fixed → 15 real / 5 vacuous**
- **Phase 38.14.7.d: case 20 fixed → 16 real / 4 vacuous**
- **Phase 38.14.7.e: Bug A closure pass complete**
- **Phase 38.14.8.d (partial): cases 15/16 promoted to real outcomes; case 19 still open**

### What Is Next

1. Close Bug B case 19 honestly (avoid zero-state vacuity without fake bounds).
2. Re-run suite + stub detector and keep reports in sync with honest counts.

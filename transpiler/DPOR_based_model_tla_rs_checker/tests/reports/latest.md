# DPOR Checker Suite Scoreboard

## Phase 38.14 Follow-Up (2026-04-09): 16/20 honest, 4/20 vacuous

The previous "Milestone M9: 20/20 ALL GREEN" claim from 2026-04-01 remains
retracted. After `38.14.7.a` (TwoPhase), `38.14.7.b` (Paxos),
`38.14.7.c` (PBFT), and now `38.14.7.d` (Raft), the honest baseline-checker
score is **16 real passes + 4 vacuous passes**.

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| **Real passes** | **16** |
| **Vacuous passes** | **4** |
| Translation failed | 0 |
| Checker error | 0 |

A "real" pass means an invariant or deadlock property was actually checked and
at least one distinct state was explored.

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
| 14 | `14_leader_election` | vacuous_zero_states_explored | **VACUOUS** (0 states) | 0 | bug_b_roundtrip_degraded |
| 15 | `15_chain_repl` | vacuous_zero_states_explored | **VACUOUS** (0 states) | 0 | bug_b_roundtrip_degraded |
| 16 | `16_primarybackup` | vacuous_zero_states_explored | **VACUOUS** (0 states) | 0 | bug_b_roundtrip_degraded |
| 17 | `17_paxos` | ok | **REAL PASS** | 40 | — |
| 18 | `18_pbft` | ok | **REAL PASS** | 50 | — |
| 19 | `19_epaxos` | vacuous_zero_states_explored | **VACUOUS** (0 states) | 0 | bug_b_roundtrip_degraded |
| 20 | `20_raft` | ok | **REAL PASS** | 67 | — |

### Honest Score by Category

| Category | Real / Total | Notes |
|----------|--------------|-------|
| Micro-models (01–05) | 5/5 | Real invariants, real verdicts |
| Concurrency primitives (06–12) | 7/7 | Real invariants and deadlock checks |
| **Protocols (13–20)** | **4/8** | Cases 13, 17, 18, 20 are real; 14/15/16/19 remain Bug B vacuous |

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

### What Is Next

1. **Bug B track** — fix Verus → TLA+ → spec roundtrip degradation for
   cases 14/15/16/19.
2. Re-run suite + stub detector and keep reports in sync with honest counts.

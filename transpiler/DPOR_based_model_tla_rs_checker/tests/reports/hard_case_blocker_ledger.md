# Hard-Case Blocker Ledger (Phase 38.14)

Protocol cases 13-20 honest status after partial `38.14.8.d` follow-up
(2026-04-09).

| # | Case | Reported | Honest verdict | Bug |
|---|------|----------|----------------|-----|
| 13 | TwoPhase | ok, 9 states | **REAL PASS** | Fixed in 38.14.7.a |
| 14 | LeaderElection | ok, 1 state | **REAL PASS** | Fixed in 38.14.8.c |
| 15 | ChainReplication | deadlock_detected, 5378 states | **REAL** (deadlock found) | Bug B translation path repaired; bounded model now non-vacuous |
| 16 | PrimaryBackup | ok, 4659 states | **REAL PASS** | Bug B translation path repaired; invariant checked |
| 17 | Paxos | ok, 40 states | **REAL PASS** | Fixed in 38.14.7.b |
| 18 | PBFT | ok, 50 states | **REAL PASS** | Fixed in 38.14.7.c |
| 19 | EPaxos | vacuous_zero_states_explored, 0 states | **VACUOUS** | **Bug B remaining**: bounded-state construction mismatch (constants constraints + symbolic phase domain) |
| 20 | Raft | ok, 67 states | **REAL PASS** | Fixed in 38.14.7.d |

**Real protocol coverage: 7/8**

## Bug Taxonomy

- **Bug A — hand-written stub TLA+**: fixed for cases 13/17/18/20.
- **Bug B — Verus → TLA+ → spec roundtrip degradation**:
  translator-side collapse is repaired for 14/15/16; one honest blocker remains on case 19.

## Updated: 2026-04-09 — 19 real / 1 vacuous baseline (Bug A closed, Bug B partially closed)

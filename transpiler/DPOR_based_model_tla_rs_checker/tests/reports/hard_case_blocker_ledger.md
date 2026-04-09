# Hard-Case Blocker Ledger (Phase 38.14)

Protocol cases 13-20 honest status after `38.14.7.e` (2026-04-09).

| # | Case | Reported | Honest verdict | Bug |
|---|------|----------|----------------|-----|
| 13 | TwoPhase | ok, 9 states | **REAL PASS** | Fixed in 38.14.7.a |
| 14 | LeaderElection | vacuous_zero_states_explored, 0 states | **VACUOUS** | **Bug B**: roundtrip degradation (`LState`/`LInit` collapse, arbitrary-soup bodies) |
| 15 | ChainReplication | vacuous_zero_states_explored, 0 states | **VACUOUS** | **Bug B** (same fingerprint as case 14) |
| 16 | PrimaryBackup | vacuous_zero_states_explored, 0 states | **VACUOUS** | **Bug B** (same fingerprint as case 14) |
| 17 | Paxos | ok, 40 states | **REAL PASS** | Fixed in 38.14.7.b |
| 18 | PBFT | ok, 50 states | **REAL PASS** | Fixed in 38.14.7.c |
| 19 | EPaxos | vacuous_zero_states_explored, 0 states | **VACUOUS** | **Bug B** (same fingerprint as case 14) |
| 20 | Raft | ok, 67 states | **REAL PASS** | Fixed in 38.14.7.d: multi-server election model, parameterized actions in `Next`, `ElectionSafety` checked |

**Real protocol coverage: 4/8**

## Bug Taxonomy

- **Bug A — hand-written stub TLA+**: fixed for cases 13/17/18/20.
- **Bug B — Verus → TLA+ → spec roundtrip degradation**: still open for cases 14/15/16/19.

## Updated: 2026-04-09 — 16 real / 4 vacuous baseline (Bug A closed, Bug B remaining)

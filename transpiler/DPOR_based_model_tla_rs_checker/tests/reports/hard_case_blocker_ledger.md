# Hard-Case Blocker Ledger (Phase 38.15 follow-up)

Protocol cases 13-20 status snapshot from `tests/reports/latest.json`
(timestamp `2026-04-10T17:42:32Z`).

| # | Case | Result | Honest verdict | Status |
|---|---|---|---|---|
| 13 | TwoPhase | `ok`, 9 states | REAL PASS | Closed in `38.14.7.a` |
| 14 | LeaderElection | `ok`, 1 state | REAL PASS | Closed in `38.14.8.c` |
| 15 | ChainReplication | `deadlock_detected`, 151 states | REAL (deadlock found) | Runtime blocker closed in `38.15.2.d.b` |
| 16 | PrimaryBackup | `ok`, 211 states | REAL PASS | Runtime blocker closed in `38.15.3` |
| 17 | Paxos | `ok`, 40 states | REAL PASS | Closed in `38.14.7.b` |
| 18 | PBFT | `ok`, 50 states | REAL PASS | Closed in `38.14.7.c` |
| 19 | EPaxos | `known_unimplemented`, 0 states | KNOWN_UNIMPLEMENTED | Runtime instability follow-up still open |
| 20 | Raft | `ok`, 67 states | REAL PASS | Closed in `38.14.7.d` |

## Coverage Summary

- Protocol hard-case real coverage: **7/8**
- Protocol hard-case known-unimplemented rows: **1/8** (case 19)
- Remaining runtime blocker tracked here: **case 19 timeout-window instability**

## Bug Taxonomy Status

- Bug A (hand-written stub TLA+ in protocol cases): **closed**.
- Bug B (Verus -> TLA+ -> spec roundtrip degradation on 14/15/16/19):
  **closed for suite-score path**.
- Post-closure runtime follow-up: case 19 remains explicitly
  `known_unimplemented` until timeout-window instability is resolved.

## Residual Follow-Up (non-vacuous accounting)

- Structural stub detector currently flags generated `Types.rs`
  constructor-style `arbitrary::<...>()` usage; this output is tracked
  separately from vacuous-pass scoring.

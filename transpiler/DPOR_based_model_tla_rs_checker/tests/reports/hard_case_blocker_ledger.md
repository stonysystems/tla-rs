# Hard-Case Blocker Ledger (Phase 38.14)

Protocol cases 13-20 honest status after Bug A + Bug B closure work
(snapshot from `tests/reports/latest.json`, timestamp `2026-04-09T15:17:19Z`).

| # | Case | Result | Honest verdict | Status |
|---|---|---|---|---|
| 13 | TwoPhase | `ok`, 9 states | REAL PASS | Closed in `38.14.7.a` |
| 14 | LeaderElection | `ok`, 1 state | REAL PASS | Closed in `38.14.8.c` |
| 15 | ChainReplication | `deadlock_detected`, 5378 states | REAL (deadlock found) | Closed in `38.14.8.d.2` |
| 16 | PrimaryBackup | `ok`, 4659 states | REAL PASS | Closed in `38.14.8.d.3` |
| 17 | Paxos | `ok`, 40 states | REAL PASS | Closed in `38.14.7.b` |
| 18 | PBFT | `ok`, 50 states | REAL PASS | Closed in `38.14.7.c` |
| 19 | EPaxos | `ok`, 11 states | REAL PASS | Closed in `38.14.8.d.4.4` |
| 20 | Raft | `ok`, 67 states | REAL PASS | Closed in `38.14.7.d` |

## Coverage Summary

- Protocol hard-case real coverage: **8/8**
- Remaining vacuous protocol cases: **0**
- Remaining protocol-case blocker in this ledger: **none**

## Bug Taxonomy Status

- Bug A (hand-written stub TLA+ in protocol cases): **closed**.
- Bug B (Verus -> TLA+ -> spec roundtrip degradation on 14/15/16/19): **closed for the suite score path**.

## Residual Follow-Up (non-blocker for this ledger)

- Structural stub detector currently flags `Types.rs` constructor-style
  `arbitrary::<...>()` bodies; those findings do not map to vacuous outcomes in
  the 20-case baseline scoreboard and should be interpreted separately from this
  hard-case execution ledger.

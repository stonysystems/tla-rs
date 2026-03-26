# DPOR Checker Suite Scoreboard

## Milestone M4: Choose + Short-Circuit Eval (2026-03-26)

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| **Passed** | **10** |
| Failed | 0 |
| Translation failed | 0 |
| Known unimplemented | 3 |
| Checker error | 7 |

### Per-Case Status

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
| 10 | `10_bakery_mutex_3p` | inv_viol | checker_error | BLOCKED | Domain expansion (3 Map fields + choose) |
| 11 | `11_readers_writers_small` | inv_viol | **inv_viol (depth 2)** | **PASS** | -- |
| 12 | `12_dining_philosophers_3` | deadlock | checker_error | BLOCKED | Domain expansion (2 Map fields) |
| 13 | `13_twophase_small` | ok | **ok (3 states)** | **PASS** | -- |
| 14 | `14_leader_election_small` | ok | checker_error | BLOCKED | Degenerate translation |
| 15 | `15_chain_replication_small` | ok | checker_error | BLOCKED | Degenerate translation |
| 16 | `16_primarybackup_small` | ok | checker_error | BLOCKED | Degenerate translation |
| 17 | `17_paxos_small` | ok | checker_error | BLOCKED | Domain expansion (nested Set) |
| 18 | `18_pbft_small` | known_unimpl | known_unimpl | -- | Placeholder |
| 19 | `19_epaxos_small` | known_unimpl | known_unimpl | -- | Placeholder |
| 20 | `20_raft_small` | known_unimpl | known_unimpl | -- | Placeholder |

### Blocker Summary

| Blocker Category | Cases | Difficulty |
|-----------------|-------|------------|
| Domain expansion limit | 06, 10, 12, 17 (4) | MEDIUM — needs demand-driven expansion |
| Degenerate translation | 14-16 (3) | HIGH — generated TLA loses variable refs |

### Progress History

- **M0**: 0/20 passed
- **M1**: 2/20 (+01, 07)
- **M1.5**: 3/20 (+08)
- **M2**: 5/20 (+09, 13)
- **M3**: 9/20 (+02, 03, 04, 05) — DotDot, Set::new, multi-var quantifiers
- **M4 (current)**: **10/20** (+11) — choose keyword, short-circuit eval

### Changes in M4

1. **Added `choose` keyword to Verus spec parser**: Added `Expr::Choose` AST variant, `parse_choose_expr()`, and `eval_choose()` that searches the int domain for a satisfying witness. Handles TLA+ CHOOSE translated to `choose |m| predicate`.

2. **Added short-circuit evaluation for `&&` and `||`**: `Expr::Binary(BinOp::And)` now short-circuits: if LHS is `false`, skip RHS. Similarly `||` short-circuits on `true`. Fixes map-key-not-found errors when guard expressions protect out-of-domain accesses.

3. **Updated model configs**: Tuned bounds for cases 10, 11 based on state space analysis. Case 11 passes with NumReaders=1, NumWriters=1 — `LSafety` violated at depth 2.

### Negative Cases (3 total)

| Case | Invariant | Violation Depth | Bug Type |
|------|-----------|----------------|----------|
| 03 CounterRaceBug | LTotalCorrect | 4 | Lost-update race |
| 05 BrokenLockBug | LMutualExclusion | -- | Missing lock check |
| 11 ReadersWritersBug | LSafety | 2 | Writer skips reader check |

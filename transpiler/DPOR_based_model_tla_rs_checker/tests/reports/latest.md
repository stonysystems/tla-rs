# DPOR Checker Suite Scoreboard

## Milestone M3: DotDot + Set::new + Multi-Var Quantifiers (2026-03-26)

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| **Passed** | **9** |
| Failed | 0 |
| Translation failed | 0 |
| Known unimplemented | 3 |
| Checker error | 8 |

### Per-Case Status

| # | Case ID | Expected | Actual | Status | Blocker Category |
|---|---------|----------|--------|--------|------------------|
| 01 | `01_aplusb` | ok | **ok (51 states)** | **PASS** | -- |
| 02 | `02_counter_incdec` | ok | **ok (5 states)** | **PASS** | -- |
| 03 | `03_counter_race_bug` | inv_viol | **inv_viol (13 states, depth 4)** | **PASS** | -- |
| 04 | `04_lock_basic` | ok | **ok (3 states)** | **PASS** | -- |
| 05 | `05_broken_lock_bug` | inv_viol | **inv_viol found** | **PASS** | -- |
| 06 | `06_ticket_lock` | ok | checker_error | BLOCKED | Domain expansion limit (4 Map fields) |
| 07 | `07_producer_consumer_1slot` | ok | **ok (51 states)** | **PASS** | -- |
| 08 | `08_bounded_buffer_2slot` | ok | **ok (6 states)** | **PASS** | -- |
| 09 | `09_peterson_mutex_2p` | ok | **ok (10 states)** | **PASS** | -- |
| 10 | `10_bakery_mutex_3p` | inv_viol | checker_error | BLOCKED | Spec parser: set map comprehension `{expr : x \in S}` |
| 11 | `11_readers_writers_small` | inv_viol | checker_error | BLOCKED | Helper call evaluation (WriterEnter uses Set::new closure) |
| 12 | `12_dining_philosophers_3` | deadlock | checker_error | BLOCKED | Domain expansion limit (Map fields) |
| 13 | `13_twophase_small` | ok | **ok (3 states)** | **PASS** | -- |
| 14 | `14_leader_election_small` | ok | checker_error | BLOCKED | Degenerate translation (arbitrary\<T\>) |
| 15 | `15_chain_replication_small` | ok | checker_error | BLOCKED | Degenerate translation (arbitrary\<T\>) |
| 16 | `16_primarybackup_small` | ok | checker_error | BLOCKED | Degenerate translation (arbitrary\<T\>) |
| 17 | `17_paxos_small` | ok | checker_error | BLOCKED | Domain expansion limit (nested Set\<LRecord\>) |
| 18 | `18_pbft_small` | known_unimpl | known_unimpl | -- | Placeholder |
| 19 | `19_epaxos_small` | known_unimpl | known_unimpl | -- | Placeholder |
| 20 | `20_raft_small` | known_unimpl | known_unimpl | -- | Placeholder |

### Blocker Summary

| Blocker Category | Cases | Difficulty |
|-----------------|-------|------------|
| Domain expansion limit (Map/Set fields) | 06, 12, 17 (3) | MEDIUM — needs demand-driven expansion |
| Degenerate translation (arbitrary\<T\>) | 14-16 (3) | HIGH — generated TLA specs lose variable refs |
| Spec parser: set map comprehension | 10 (1) | LOW — add `{expr : x \in S}` parsing |
| Helper call evaluation (Set::new in helper) | 11 (1) | LOW — extend predicate solver for Set::new |

### Progress History

- **M0**: 0/20 passed
- **M1**: 2/20 passed (01, 07)
- **M1.5**: 3/20 passed (+08)
- **M2**: 5/20 passed (+09, 13) — Seq\<char\> domain, translator recursion fix
- **M3 (current)**: **9/20 passed** (+02, 03, 04, 05) — DotDot, Set::new, multi-var quantifiers

### Changes in M3

1. **Added `..` (DotDot) range operator to TLA+ parser**: Added `TlaBinOp::DotDot` to the additive expression precedence level. This was the single missing parser rule blocking all 8 translation-failed cases (02-06, 10-12). All 20 cases now translate successfully (20/20 translation rate, up from 12/20).

2. **Added `Set::new(|x| predicate)` evaluation**: TLA+ `a..b` translates to `Set::new(|x: int| a <= x && x <= b)`. Added `eval_set_new_with_closure()` in the evaluator that extracts range bounds from the closure predicate and enumerates matching values. Falls back to full int domain when bounds can't be extracted.

3. **Fixed multi-variable quantifier bound sharing**: TLA+ `\A p1, p2 \in S` means BOTH variables are in S, but the parser was only assigning the set to the last variable. Fixed `parse_quant_bounds()` to collect comma-separated identifiers and assign the set to all when `\in` is encountered.

4. **Default untyped quantifier variables to `int`**: When the translator can't infer a type for a quantifier variable, it now defaults to `int` instead of leaving it untyped. This fixes model checker errors on invariants with quantifier variables.

### Negative Cases Passing

Two negative cases now pass correctly:
- **Case 03 (CounterRaceBug)**: Detects lost-update race — `LTotalCorrect` violated at depth 4
- **Case 05 (BrokenLockBug)**: Detects broken mutual exclusion — `LMutualExclusion` violated

# DPOR Checker Suite Scoreboard

## Milestone M1: First Passing Cases (2026-03-25)

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| **Passed** | **2** |
| Failed | 0 |
| Translation failed | 8 |
| Known unimplemented | 3 |
| Checker error | 7 |

### Per-Case Status

| # | Case ID | Expected | Actual | Status | Notes |
|---|---------|----------|--------|--------|-------|
| 01 | `01_aplusb` | ok | **ok (51 states)** | **PASS** | First passing case |
| 02 | `02_counter_incdec` | ok | translation_failed | BLOCKED | CONSTANT/EXCEPT not supported |
| 03 | `03_counter_race_bug` | invariant_violation | translation_failed | BLOCKED | CONSTANT/EXCEPT not supported |
| 04 | `04_lock_basic` | ok | translation_failed | BLOCKED | CONSTANT/EXCEPT not supported |
| 05 | `05_broken_lock_bug` | invariant_violation | translation_failed | BLOCKED | CONSTANT/EXCEPT not supported |
| 06 | `06_ticket_lock` | ok | translation_failed | BLOCKED | CONSTANT/EXCEPT not supported |
| 07 | `07_producer_consumer_1slot` | ok | **ok (51 states)** | **PASS** | Second passing case |
| 08 | `08_bounded_buffer_2slot` | invariant_violation | checker_error | BLOCKED | Parse error: `\|` in translated spec |
| 09 | `09_peterson_mutex_2p` | ok | checker_error | BLOCKED | Parse error: `\|` in translated spec |
| 10 | `10_bakery_mutex_3p` | invariant_violation | translation_failed | BLOCKED | CONSTANT/CHOOSE not supported |
| 11 | `11_readers_writers_small` | invariant_violation | translation_failed | BLOCKED | CONSTANT not supported |
| 12 | `12_dining_philosophers_3` | deadlock | translation_failed | BLOCKED | CONSTANT not supported |
| 13 | `13_twophase_small` | ok | checker_error | BLOCKED | Invariant not in translated spec |
| 14 | `14_leader_election_small` | ok | checker_error | BLOCKED | LNext has 3+ params (incompatible signature) |
| 15 | `15_chain_replication_small` | ok | checker_error | BLOCKED | LNext has 3+ params |
| 16 | `16_primarybackup_small` | ok | checker_error | BLOCKED | LNext has 3+ params |
| 17 | `17_paxos_small` | ok | checker_error | BLOCKED | Invariant not in translated spec |
| 18 | `18_pbft_small` | known_unimplemented | known_unimplemented | -- | Placeholder |
| 19 | `19_epaxos_small` | known_unimplemented | known_unimplemented | -- | Placeholder |
| 20 | `20_raft_small` | known_unimplemented | known_unimplemented | -- | Placeholder |

### Progress vs M0

- **M0 (initial)**: 0 passed, 9 checker_error, 8 translation_failed, 3 known_unimplemented
- **M1 (current)**: 2 passed (+2), 7 checker_error (-2), 8 translation_failed, 3 known_unimplemented

### Remaining Blockers (by category)

1. **TLA+ Translation (8 cases, 02-06/10-12)**: CONSTANT, EXCEPT, CHOOSE, function defs
2. **Spec parse error (2 cases, 08-09)**: Translated Rust uses `|` syntax the spec parser doesn't handle
3. **Signature mismatch (3 cases, 14-16)**: Generated specs have 3+ param LInit/LNext (c_consts + s + c)
4. **Missing invariants (2 cases, 13/17)**: Invariant predicates not translated alongside Init/Next

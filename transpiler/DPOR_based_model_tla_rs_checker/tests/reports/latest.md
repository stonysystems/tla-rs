# DPOR Checker Suite Scoreboard

## Milestone M1: Accurate Blocker Categorization (2026-03-26)

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| **Passed** | **2** |
| Failed | 0 |
| Translation failed | 8 |
| Known unimplemented | 3 |
| Checker error | 7 |

### Per-Case Status

| # | Case ID | Expected | Actual | Status | Blocker Category |
|---|---------|----------|--------|--------|------------------|
| 01 | `01_aplusb` | ok | **ok (51 states)** | **PASS** | — |
| 02 | `02_counter_incdec` | ok | translation_failed | BLOCKED | TLA+ translation: CONSTANT/EXCEPT |
| 03 | `03_counter_race_bug` | inv_viol | translation_failed | BLOCKED | TLA+ translation: CONSTANT/EXCEPT |
| 04 | `04_lock_basic` | ok | translation_failed | BLOCKED | TLA+ translation: CONSTANT/EXCEPT |
| 05 | `05_broken_lock_bug` | inv_viol | translation_failed | BLOCKED | TLA+ translation: CONSTANT/EXCEPT |
| 06 | `06_ticket_lock` | ok | translation_failed | BLOCKED | TLA+ translation: CONSTANT/EXCEPT |
| 07 | `07_producer_consumer_1slot` | ok | **ok (51 states)** | **PASS** | — |
| 08 | `08_bounded_buffer_2slot` | inv_viol | checker_error | BLOCKED | Spec parser: closure/lambda `\|p\|` |
| 09 | `09_peterson_mutex_2p` | ok | checker_error | BLOCKED | Spec parser: closure/lambda `\|p\|` |
| 10 | `10_bakery_mutex_3p` | inv_viol | translation_failed | BLOCKED | TLA+ translation: CONSTANT/CHOOSE |
| 11 | `11_readers_writers_small` | inv_viol | translation_failed | BLOCKED | TLA+ translation: CONSTANT |
| 12 | `12_dining_philosophers_3` | deadlock | translation_failed | BLOCKED | TLA+ translation: CONSTANT |
| 13 | `13_twophase_small` | ok | checker_error | BLOCKED | Missing char domain (Seq\<char\> from TLA+ strings) |
| 14 | `14_leader_election_small` | ok | checker_error | BLOCKED | LNext has 4 params (non-standard generated signature) |
| 15 | `15_chain_replication_small` | ok | checker_error | BLOCKED | LNext has 4 params (non-standard generated signature) |
| 16 | `16_primarybackup_small` | ok | checker_error | BLOCKED | LNext has 4 params (non-standard generated signature) |
| 17 | `17_paxos_small` | ok | checker_error | BLOCKED | Candidate expansion exceeds 10K at int 0..5 |
| 18 | `18_pbft_small` | known_unimpl | known_unimpl | — | Placeholder |
| 19 | `19_epaxos_small` | known_unimpl | known_unimpl | — | Placeholder |
| 20 | `20_raft_small` | known_unimpl | known_unimpl | — | Placeholder |

### Blocker Summary (for 38.8.2.a)

| Blocker Category | Cases | Fix Location | Difficulty |
|-----------------|-------|-------------|------------|
| TLA+ translation: CONSTANT/EXCEPT/CHOOSE | 02-06, 10-12 (8) | `transpiler/src/tla/` translate-tla | HIGH — core TLA+ parser |
| Spec parser: closure/lambda syntax | 08, 09 (2) | `transpiler/src/parser/` | MEDIUM — add closure parsing |
| Missing char domain | 13, 20 (2) | `transpiler/src/modelcheck/domain.rs` | MEDIUM — add char type expansion |
| Non-standard LInit/LNext signatures | 14-16 (3) | `transpiler/src/spec_analyzer/` | MEDIUM — accept 4-param Next |
| Candidate expansion limit | 17 (1) | Model config / bounds tuning | LOW — narrow int domain |

### Progress vs M0

- **M0 (initial)**: 0 passed, 9 checker_error, 8 translation_failed, 3 known_unimplemented
- **M1 (current)**: 2 passed (+2), 7 checker_error (-2), 8 translation_failed, 3 known_unimplemented
- **Blocker analysis added**: 5 distinct categories, each with fix location and difficulty

### Next Steps for 38.8.2.a

Priority order for raising pass count:
1. **Fix candidate expansion (case 17)**: Narrow int domain to 0..2 in per-case model config
2. **Add char domain support (cases 13, 20)**: Map TLA+ strings to finite char domain
3. **Add closure parsing (cases 08, 09)**: Support `|x|` syntax in spec parser
4. **Accept 4-param LNext (cases 14-16)**: Extend signature validation
5. **Add CONSTANT support (cases 02-06, 10-12)**: Biggest win but hardest — core TLA+ parser

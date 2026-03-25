# DPOR Checker Suite Scoreboard

## Milestone M0: Initial Baseline (2026-03-25)

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| Passed | 0 |
| Failed | 0 |
| Translation failed | 8 |
| Known unimplemented | 3 |
| Checker error | 9 |

### Per-Case Status

| # | Case ID | Expected | Actual | Status |
|---|---------|----------|--------|--------|
| 01 | `01_aplusb` | ok | checker_error | Current model checker requires types.rs sibling |
| 02 | `02_counter_incdec` | ok | translation_failed | Transpiler: CONSTANT/EXCEPT not supported |
| 03 | `03_counter_race_bug` | invariant_violation | translation_failed | Transpiler: CONSTANT/EXCEPT not supported |
| 04 | `04_lock_basic` | ok | translation_failed | Transpiler: CONSTANT/EXCEPT not supported |
| 05 | `05_broken_lock_bug` | invariant_violation | translation_failed | Transpiler: CONSTANT/EXCEPT not supported |
| 06 | `06_ticket_lock` | ok | translation_failed | Transpiler: CONSTANT/EXCEPT not supported |
| 07 | `07_producer_consumer_1slot` | ok | checker_error | Requires types.rs |
| 08 | `08_bounded_buffer_2slot` | invariant_violation | checker_error | Requires types.rs |
| 09 | `09_peterson_mutex_2p` | ok | checker_error | Requires types.rs |
| 10 | `10_bakery_mutex_3p` | invariant_violation | translation_failed | Transpiler: CONSTANT/CHOOSE not supported |
| 11 | `11_readers_writers_small` | invariant_violation | translation_failed | Transpiler: CONSTANT not supported |
| 12 | `12_dining_philosophers_3` | deadlock | translation_failed | Transpiler: CONSTANT not supported |
| 13 | `13_twophase_small` | ok | checker_error | Requires types.rs |
| 14 | `14_leader_election_small` | ok | checker_error | Requires types.rs |
| 15 | `15_chain_replication_small` | ok | checker_error | Requires types.rs |
| 16 | `16_primarybackup_small` | ok | checker_error | Requires types.rs |
| 17 | `17_paxos_small` | ok | checker_error | Requires types.rs |
| 18 | `18_pbft_small` | known_unimplemented | known_unimplemented | Placeholder |
| 19 | `19_epaxos_small` | known_unimplemented | known_unimplemented | Placeholder |
| 20 | `20_raft_small` | known_unimplemented | known_unimplemented | Placeholder |

### Blockers

1. **TLA+ Translation (8 cases)**: The TLA+ → Verus transpiler doesn't support
   CONSTANT parameters, EXCEPT notation, or CHOOSE in hand-written specs.
   These features are used in cases 02-06, 10-12.

2. **Model Checker types.rs Requirement (9 cases)**: The existing source-first
   model checker (`verus-transpile model-check`) requires a sibling `types.rs`
   file for each protocol spec. Standalone translated TLA+ specs don't have this.
   This is the primary blocker for Phase 38.6 (baseline oracle).

### Next Steps

- Phase 38.6: Implement a minimal baseline explorer that can check standalone
  translated tla-rs specs WITHOUT requiring a types.rs file.
- Alternatively: extend the translation pipeline to generate types.rs alongside
  the spec, or modify the model checker to infer types from the spec file.

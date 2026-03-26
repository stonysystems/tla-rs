# DPOR Checker Suite Scoreboard

## Milestone M2: Seq\<char\> + Recursion Fixes (2026-03-26)

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| **Passed** | **5** |
| Failed | 0 |
| Translation failed | 8 |
| Known unimplemented | 3 |
| Checker error | 4 |

### Per-Case Status

| # | Case ID | Expected | Actual | Status | Blocker Category |
|---|---------|----------|--------|--------|------------------|
| 01 | `01_aplusb` | ok | **ok (51 states)** | **PASS** | -- |
| 02 | `02_counter_incdec` | ok | translation_failed | BLOCKED | TLA+ translation: CONSTANT/EXCEPT |
| 03 | `03_counter_race_bug` | inv_viol | translation_failed | BLOCKED | TLA+ translation: CONSTANT/EXCEPT |
| 04 | `04_lock_basic` | ok | translation_failed | BLOCKED | TLA+ translation: CONSTANT/EXCEPT |
| 05 | `05_broken_lock_bug` | inv_viol | translation_failed | BLOCKED | TLA+ translation: CONSTANT/EXCEPT |
| 06 | `06_ticket_lock` | ok | translation_failed | BLOCKED | TLA+ translation: CONSTANT/EXCEPT |
| 07 | `07_producer_consumer_1slot` | ok | **ok (51 states)** | **PASS** | -- |
| 08 | `08_bounded_buffer_2slot` | ok | **ok (6 states)** | **PASS** | -- |
| 09 | `09_peterson_mutex_2p` | ok | **ok (10 states)** | **PASS** | -- |
| 10 | `10_bakery_mutex_3p` | inv_viol | translation_failed | BLOCKED | TLA+ translation: CONSTANT/CHOOSE |
| 11 | `11_readers_writers_small` | inv_viol | translation_failed | BLOCKED | TLA+ translation: CONSTANT |
| 12 | `12_dining_philosophers_3` | deadlock | translation_failed | BLOCKED | TLA+ translation: CONSTANT |
| 13 | `13_twophase_small` | ok | **ok (3 states)** | **PASS** | -- |
| 14 | `14_leader_election_small` | ok | checker_error | BLOCKED | Degenerate translation (arbitrary\<T\>, non-LState params) |
| 15 | `15_chain_replication_small` | ok | checker_error | BLOCKED | Degenerate translation (arbitrary\<T\>, non-LState params) |
| 16 | `16_primarybackup_small` | ok | checker_error | BLOCKED | Degenerate translation (arbitrary\<T\>, non-LState params) |
| 17 | `17_paxos_small` | ok | checker_error | BLOCKED | Domain expansion exceeds 100K (nested Set\<LRecord\>) |
| 18 | `18_pbft_small` | known_unimpl | known_unimpl | -- | Placeholder |
| 19 | `19_epaxos_small` | known_unimpl | known_unimpl | -- | Placeholder |
| 20 | `20_raft_small` | known_unimpl | known_unimpl | -- | Placeholder |

### Blocker Summary (for 38.8.2.a)

| Blocker Category | Cases | Fix Location | Difficulty |
|-----------------|-------|-------------|------------|
| TLA+ translation: CONSTANT/EXCEPT/CHOOSE | 02-06, 10-12 (8) | `transpiler/src/tla/` translate-tla | HIGH -- core TLA+ parser |
| Degenerate translation (arbitrary\<T\>) | 14-16 (3) | `transpiler/src/tla/` variable resolution | HIGH -- generated TLA specs lose variable refs |
| Domain expansion limit (nested Set/Map) | 17 (1) | `transpiler/src/modelcheck/domain.rs` | MEDIUM -- lazy/demand-driven expansion |

### Progress vs M1

- **M0 (initial)**: 0 passed, 9 checker_error, 8 translation_failed, 3 known_unimplemented
- **M1**: 2 passed (+2), 7 checker_error, 8 translation_failed, 3 known_unimplemented
- **M1.5**: 3 passed (+1, case 08 via Map::new closure + Map.insert support)
- **M2 (current)**: 5 passed (+2), 4 checker_error (-3), 8 translation_failed, 3 known_unimplemented

### Changes in M2

1. **Fixed TLA+ translator recursion bug** (`expr_refs_action_operators`, `expr_refs_predicate_operators`): These functions didn't recurse into `\E`, `\A`, `IF/THEN/ELSE`, `CASE`, `LET/IN`, `CHOOSE`, set comprehensions, function constructions, etc. Only `Ident`, `BinOp`, `UnaryOp`, and `OpApply` were checked. This caused `Next == \E p \in P : ...` to be misclassified as `ConstantOp` instead of `Action`, generating `LNext()` with 0 params. Now fixed to recurse into all compound TLA+ expression forms.
   - **Impact**: Case 09 (PetersonMutex) now translates correctly and passes.

2. **Added `Seq<char>` domain support**: TLA+ strings translate to `Seq<char>` in Verus. Instead of enumerating all char combinations (combinatorial explosion), added special handling: when `Seq<char>` is encountered, looks for `quantifiers.types.Seq_char` in model config with explicit string constant values.
   - **Impact**: Cases 09 and 13 unblocked. Per-case model configs specify string constants.

3. **Added 4-param LNext infrastructure**: Relaxed `validate_lnext_signature` to accept 2+ params (was exactly 2-3). Added `extra_params` field to `TransitionIr` for params beyond state/state_/constants. Added `expand_extra_params()` in domain.rs. Cross-products extra param assignments with branch existentials in main model-check loop.
   - **Impact**: Infrastructure ready for protocol specs with extra LNext params. Cases 14-16 still blocked on degenerate translation (separate issue).

4. **Relaxed `validate_init_signature`**: Now identifies `LState` params by type, tolerates extra params silently.

### Next Steps for 38.8.2.a

Priority order for raising pass count above 5:
1. **Add CONSTANT/EXCEPT support (cases 02-06, 10-12)**: Biggest win (8 cases) but hardest -- requires core TLA+ parser enhancement
2. **Fix variable resolution in generated TLA specs (cases 14-16)**: The translator loses variable references when translating multi-module generated TLA, producing `arbitrary<T>()` placeholders
3. **Implement demand-driven domain expansion (case 17)**: Instead of pre-enumerating all possible states, expand on demand during search

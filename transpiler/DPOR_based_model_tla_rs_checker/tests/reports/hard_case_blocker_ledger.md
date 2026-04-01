# Hard-Case Blocker Ledger (Phase 38.9.3.a)

Protocol cases 13-20: current result, first concrete blocker, and next code task.

| # | Case | Result | First Blocker | Blocker Surface | Next Task |
|---|------|--------|--------------|-----------------|-----------|
| 13 | TwoPhase | **PASS** (ok, 3 states) | -- | -- | -- |
| 14 | LeaderElection | checker_error | **Degenerate translated corpus**: checked-in `Election.rs` still has `LInit(c_consts: LConstants, s: int, c: int)`, unresolved `arbitrary::<...>()` in `LInit` and action bodies, and symbolic message/state atoms flattened into ints. | `transpiler/src/tla/translator.rs` — `generate_spec_functions`, `generate_operator_function`, `translate_value_context_expr`, `translate_ident`, `generate_record_structs` | Fix generated-D1 protocol translation, regenerate corpus, then rerun suite |
| 15 | ChainReplication | checker_error | **Degenerate translated corpus**: same family as case 14. `Chain.rs` and `Types.rs` still collapse record/set/seq structure into `int` fields and `arbitrary::<Seq<int>>()` placeholders. | Same as case 14 | Same fix |
| 16 | PrimaryBackup | checker_error | **Degenerate translated corpus**: same family as case 14, plus hash-encoded symbolic atoms (`6049598361int`, `1048442360int`) where the source TLA still has named roles/messages. | Same as case 14 | Same fix |
| 17 | Paxos | **PASS** (ok, 1 state) | -- | -- | -- |
| 18 | PBFT | **PASS** (ok, 31 states) | -- | -- | -- |
| 19 | EPaxos | known_unimplemented | **Manifest still masks the real blocker**: checked-in `Epaxos.rs` shows the same degenerate translated-corpus pattern as 14-16, but the suite still short-circuits this case as `known_unimplemented` instead of recording the actual checker failure. | `transpiler/src/tla/translator.rs` plus `tests/manifest.toml` | Fix the shared translation issues first, then remove the manifest mask and record the real result |
| 20 | Raft | **PASS** (ok, 31 states) | -- | -- | -- |

## Blocker Categories

### Degenerate `translate-tla` output (cases 14-16, 19)

- The TLA inputs for these cases are still semantically clean (`Init(s, c)`, symbolic enums like `Primary`/`Backup`/`Ack`, typed record fields, packet constructions like `<<[val |-> ...]>>`).
- The checked-in translated Rust is not: it still emits malformed `LInit`, unresolved `arbitrary()` calls, flat `int` record fields, and hash-encoded symbolic atoms.
- Reproduced directly on 2026-03-31 with case 14: `verus-transpile model-check` fails during initial-state construction with `Failed to evaluate LInit ... helper call arbitrary::<bool>`.
- Concrete patch surfaces:
  - `transpiler/src/tla/translator.rs::generate_spec_functions` / `generate_operator_function` for wrong `Init` state-parameter inference in variable-less generated-protocol modules,
  - `transpiler/src/tla/translator.rs::translate_value_context_expr` / `translate_ident` for `arbitrary()` normalization and symbolic-atom hashing,
  - `transpiler/src/tla/translator.rs::generate_record_structs` plus field-type inference for record/set/bool/seq fields collapsing to `int`.

### Passed But Narrow (cases 17-18)

- `17_paxos_small` and `18_pbft_small` are now green under the checked-in narrow bounds and `[collections]` settings.
- Do not treat them as current pass-count blockers. Reopen them only for intentional bound widening, semantic-parity debugging, or performance work.

## Date

Updated: 2026-03-31 (resynced to checked-in `latest.json`, 16/20 pass)

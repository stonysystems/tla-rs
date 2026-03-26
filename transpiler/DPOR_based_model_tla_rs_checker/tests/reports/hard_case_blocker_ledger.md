# Hard-Case Blocker Ledger (Phase 38.9.3.a)

Protocol cases 13-20: current result, first concrete blocker, and next code task.

| # | Case | Result | First Blocker | Blocker Surface | Next Task |
|---|------|--------|--------------|-----------------|-----------|
| 13 | TwoPhase | **PASS** (ok, 3 states) | -- | -- | -- |
| 14 | LeaderElection | checker_error | **Degenerate translation**: `LInit(c_consts: LConstants, s: int, c: int)` — state param `s` typed as `int` instead of `LState`. TLA+ CONSTANT `State` name collides with state variable inference in `translate-tla --gen-modes`. | `transpiler/src/tla/translator.rs` — mode classification when TLA+ CONSTANTS include `State` | Fix translator to not confuse CONSTANT names with state variable types |
| 15 | ChainReplication | checker_error | **Degenerate translation**: Same as case 14. `LInit(c_consts: LConstants, s: int, c: int)`. TLA+ CONSTANT `State` causes `s` to be typed as `int`. | Same as case 14 | Same fix as case 14 |
| 16 | PrimaryBackup | checker_error | **Degenerate translation**: Same as case 14. `LInit(c_consts: LConstants, s: int, c: int)`. TLA+ CONSTANT `State` causes `s` to be typed as `int`. | Same as case 14 | Same fix as case 14 |
| 17 | Paxos | checker_error | **Domain explosion**: `Set<LRecord>` where LRecord has 4 fields (acc:int, bal:int, type:Seq<char>, val:int). With int 0..1 and 4 strings: 32 possible records. Set expansion with max_set_len=1 should be 33, but nested struct expansion within Set domain exceeds limit. Appears to be a bug in `expand_type_domain` for `Set<NamedStruct>` — the limit is applied to the intermediate LRecord domain, not the final Set. | `transpiler/src/modelcheck/domain.rs` — `expand_type_domain` for Set<NamedStruct> applies expansion_limit to inner type | Fix domain expansion to handle nested struct-in-set correctly, or add demand-driven expansion |
| 18 | PBFT | checker_error | **Domain explosion**: `Set<LRecord>` where LRecord has 5 fields (digest:int, replica:int, seq:int, type:Seq<char>, view:int). Even with int 0..1 and max_set_len=1: 64 records × set size = 65, but actual expansion exceeds 200K — same nested struct expansion issue as case 17. | Same as case 17 | Same fix as case 17 |
| 19 | EPaxos | checker_error | **Degenerate translation**: Same as cases 14-16. `LInit(c_consts: LConstants, s: int, c: int)`. | Same as case 14 | Same fix as case 14 |
| 20 | Raft | **PASS** (ok, 31 states) | -- | -- | -- |

## Blocker Categories

### Degenerate Translation (cases 14-16, 19)

**Root cause**: The `verus2tla` converter produces TLA+ with `CONSTANTS State, <Protocol>Message, Constants`. When the `translate-tla --gen-modes` command processes these TLA+ specs, the CONSTANT name `State` confuses the mode classification system. Instead of recognizing `s` in `Init(s, c)` as the state variable (of type `LState`), it types `s` as `int` and generates `LInit(c_consts: LConstants, s: int, c: int)`.

**Fix location**: `transpiler/src/tla/translator.rs` — the operator classification / parameter type inference in `--gen-modes`.

**Estimated fix**: MEDIUM difficulty. Need to recognize that when a TLA+ CONSTANT is named `State`, it should not override the state variable type inference. All 4 cases share the exact same fix.

### Domain Explosion (cases 17, 18)

**Root cause**: `expand_type_domain` in `domain.rs` applies the `expansion_limit` (from `max_states`) to intermediate type expansions. For `Set<LRecord>`, it first expands all possible `LRecord` values (32-64), then tries to build all possible sets. But the intermediate LRecord expansion itself may trigger the limit before the Set expansion even begins.

**Fix location**: `transpiler/src/modelcheck/domain.rs` — the `expand_type_domain` function for Set/Map types.

**Fix approaches**:
1. **Separate limits**: Use a different (higher) limit for intermediate type expansion vs. final state expansion
2. **Demand-driven**: Don't pre-enumerate all possible states; instead, evaluate `LInit`/`LNext` on demand
3. **Init-template**: Extract initial state directly from `LInit` assignments (baseline already has `derive_fully_pinned_state_template_from_init`)

## Date

Generated: 2026-03-26 (Milestone M8, 13/20 pass)

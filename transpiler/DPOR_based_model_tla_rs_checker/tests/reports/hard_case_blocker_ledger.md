# Hard-Case Blocker Ledger (Phase 38.9.3.a)

Protocol cases 13-20: current result, first concrete blocker, and next code task.

| # | Case | Result | First Blocker | Blocker Surface | Next Task |
|---|------|--------|--------------|-----------------|-----------|
| 13 | TwoPhase | **PASS** (ok, 3 states) | -- | -- | -- |
| 14 | LeaderElection | checker_error | **Existential expansion**: LInit signature fixed (`s: LState`), but LNext has nested existentials with `Seq<int>` domains. With 11 nested `exists` blocks × `Seq<int>` domain: combinatorial explosion exceeds 100K limit. Spec bodies use `arbitrary()` and `s.s.field` deep access patterns. | `transpiler/src/modelcheck/domain.rs` — existential domain expansion for `Seq<int>` | Reduce Seq<int> expansion or fix verus2tla to emit simpler TLA+ |
| 15 | ChainReplication | checker_error | **Existential expansion**: Same as case 14. Nested existentials with `Seq<int>` exceed limit. | Same as case 14 | Same fix |
| 16 | PrimaryBackup | checker_error | **Existential expansion**: Same as case 14. Nested existentials with `Seq<int>` exceed limit. Spec bodies additionally use hash-encoded enum tags (`6049598361int`). | Same as case 14 | Same fix |
| 17 | Paxos | checker_error | **Domain explosion**: `Set<LRecord>` where LRecord has 4 fields. Struct expansion within Set exceeds limit even with max_set_len=1 and int 0..1. | `transpiler/src/modelcheck/domain.rs` — `expand_type_domain` for Set<NamedStruct> | Fix domain expansion or add demand-driven expansion |
| 18 | PBFT | checker_error | **Domain explosion**: `Set<LRecord>` with 5-field records. Same nested struct expansion issue as case 17. | Same as case 17 | Same fix |
| 19 | EPaxos | checker_error | **Existential expansion**: LInit signature fixed (`s: LState`), but same nested existential issue as cases 14-16. | Same as case 14 | Same fix |
| 20 | Raft | **PASS** (ok, 31 states) | -- | -- | -- |

## Blocker Categories

### Existential Expansion (cases 14-16, 19) — UPDATED

**Root cause** (updated after commit `ded3b81`): The LInit signature issue was fixed — `s` is now correctly typed as `LState`. However, LNext uses deeply nested existentials with `Seq<int>` parameters (`sent_packets: Seq<int>`). Each existential over `Seq<int>` expands to all possible sequences, and 7-11 nested existentials create combinatorial explosion beyond 100K.

The spec bodies are also degenerate: they use `arbitrary<T>()` calls, deep field access patterns (`s.s.role.tag`), and hash-encoded enum tag values. Even if existential expansion were solved, the predicate solver would likely fail on these bodies.

**Previous blocker** (before `ded3b81`): Wrong LInit signature — `LInit(c_consts: LConstants, s: int, c: int)` instead of `LInit(s: LState, ...)`. Fixed by inferring state variable from Init's first parameter in variable-less specs.

### Domain Explosion (cases 10, 17, 18)

**Root cause**: `expand_type_domain` in `domain.rs` applies the expansion limit to intermediate type expansions. For `Set<LRecord>` or `Map<int, T>`, the cross-product of record fields or map entries exceeds limits even with minimal domain bounds.

- Case 10 (BakeryMutex): 3 Map fields with bool/int/string values → exceeds 500K guardrail
- Case 17 (Paxos): Set<LRecord> with 4-field records → exceeds limit during struct expansion
- Case 18 (PBFT): Set<LRecord> with 5-field records → same issue

## Date

Updated: 2026-03-26 (after commit `ded3b81`, 13/20 pass)

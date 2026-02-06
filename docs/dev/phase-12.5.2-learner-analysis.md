# Phase 12.5.2: Learner Regeneration Analysis

## Problem

The learner component uses `CLearnerState = HashMap<u64, CLearnerTuple>` with deep key+value type conversion via `abstractify_clearnerstate()`. This makes proofs significantly harder than components with simple fields.

## Reference File Analysis (645 lines, 0 assumes)

### Proof Infrastructure
- 4 proof lemmas for `abstractify_clearnerstate` operations: empty, insert, remove, singleton (~174 LOC)
- 3 external-body helpers: `clone_clearnerstate`, `hashmap_keys_to_vec`, `filter_clearnerstate` (~43 LOC)
- Per-branch proof blocks in `CLearnerProcess2b` (~250 LOC)
- `CLearnerForgetOperationsBefore` filter proof (~60 LOC)

### Key Insight: Proofs Are ~70-80% Templatable

The 4 abstractify lemmas follow identical structure for ANY `HashMap<K, V>`:
1. Domain equivalence via `choose |k: K| m@.contains_key(k) && k as int == ak`
2. Value equivalence via same witness
3. Abstractability propagation
4. Validity propagation (conditional)

The filter proof has a generic 3-conjunct template:
1. Forward: filtered has key → key meets predicate AND original has key
2. Backward: key meets predicate AND original has key → filtered has key
3. Values match between filtered and original

### Protocol-Specific Elements (~20-30% of proof code)
- Ballot comparisons (`BalLt`) for branch navigation in `CLearnerProcess2b`
- EndPoint axioms (`axiom_endpoint_view`, `axiom_endpoint_key_model`) for set membership proofs
- Empty-set-map proof for `Set<EndPoint>` (different from `Set<u64>`)
- Branch navigation assertions (5 branches with specific conditions)

## Design Decision: `map_fields` Config Category

Added a new transpiler config category for HashMap fields with deep abstraction:

```toml
[map_fields]
"unexecuted_learner_state" = ["CLearnerState", "clearnerstate", "CLearnerTuple"]
```

This drives generation of:
- Abstractify proof lemmas (templated)
- External-body clone/filter helpers
- Correct clone dispatch (`clone_{prefix}()` instead of `.clone()`)

## Transpiler Output Issues (Current)

| Issue | Current Output | Correct Output |
|-------|---------------|----------------|
| Struct inline | Generates CLearner | Should import from types_gen.rs |
| Arrow access | `m->opn_2b` in exec | Match destructuring |
| HashSet literal | `HashSet::from(vec![x])` | `HashSet::new()` + `.insert()` |
| Clone dispatch | `clone_hashset(&s.constants)` | `s.constants.clone_up_to_view()` |
| HashMap filter | `for k in iter:` + 3 assumes | `filter_clearnerstate()` + proof |
| Proofs | None | 4 lemmas + per-branch blocks |

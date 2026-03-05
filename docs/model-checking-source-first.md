# Source-First Model Checking Guide

This guide shows how to run model checking directly on tla-rs protocol specs (`LInit`/`LNext`) using `verus-transpile model-check`.

## 1. What This Runs

The source-first workflow checks safety properties from Verus spec source files:

- protocol source: `src/protocol/<Protocol>/<protocol>.rs`
- types source: `src/protocol/<Protocol>/types.rs`
- finite model config: `model.toml`

No TLC wrapper generation is required for this flow.

## 2. Prerequisites

Build the transpiler binary:

```bash
cargo build --manifest-path transpiler/Cargo.toml --bin verus-transpile
```

You can then run either:

- `transpiler/target/debug/verus-transpile`
- `verus-transpile` (if on your `PATH`)

## 3. Prepare `model.toml`

Use finite domains and bounded search so exploration terminates.

Minimal example:

```toml
[quantifiers.int]
min = 0
max = 0

[search]
max_depth = 1
max_states = 200
timeout_ms = 1000

[properties]
check_deadlock = false
successor_semantics = "deadlock"
```

For full schema and domain kinds, see `docs/dev/phase22-model-toml-format.md`.

## 4. Run Model Check

Example (TwoPhase):

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/TwoPhase/twophase.rs \
  --types src/protocol/TwoPhase/types.rs \
  --model path/to/model.toml \
  --search bfs \
  --json-report
```

## 5. Common CLI Overrides

Useful options for bounded runs:

- `--init <name>` (default `LInit`)
- `--next <name>` (default `LNext`)
- `--invariant <name>` (repeatable, overrides `properties.invariants`)
- `--search <bfs|dfs>`
- `--max-depth <N>`
- `--max-states <N>`
- `--timeout <ms>` (alias: `--timeout-ms`)
- `--json-report`

If `--types` is omitted, the tool defaults to sibling `types.rs`.

`model.toml` can also choose state dedup mode under `[search]`:

- `state_dedup = "canonical"` (default, exact)
- `state_dedup = "hash_compaction64"` (lossy hash compaction)
- `symmetry_fields = ["field_a", "field_b"]` (optional top-level `LState` fields to symmetry-normalize before dedup)
- `por_heuristic = "none" | "invisible_branch"` (optional conservative branch-pruning mode; requires `properties.check_deadlock = false`)

## 6. Inspect Results

With `--json-report`, output includes:

- `result` (`ok`, violation, or limit/timeout stop)
- `stop_reason` (for example `FrontierExhausted`, `MaxStatesReached`, `TimeoutReached`)
- `summary.states`
- `summary.transitions`
- `summary.depth`
- `summary.elapsed_ms`
- reduction telemetry (`summary.pruned_by_por`, `summary.symmetry_collapses`, `summary.hash_compaction_collisions`)
- `liveness` summary (when temporal config is present):
  - `obligations`, `checked`, `violation_found`, `skipped_reason`
  - configured fairness labels (`fairness.weak` / `fairness.strong`) and counts
- stop metadata and violation payloads (when present), including `leads_to_violation` counterexample traces

For iterative tuning, adjust search and domain bounds first (`max_depth`, `max_states`, and quantifier/type domains).

## 7. Validate Resolved Config

To validate and inspect the final config after overrides:

```bash
transpiler/target/debug/verus-transpile model-config \
  --model path/to/model.toml \
  --max-depth 2 \
  --max-states 500
```

This prints the resolved, validated configuration to stdout.

## 8. Migration from TLC Wrapper Workflow

If you are migrating from the older wrapper-based workflow, use
`docs/model-checking-migration.md`.

If you still need TLC artifacts (`*_MC.tla`/`.cfg`) for specific runs, use
`docs/model-checking-wrapper-workflow.md`.

## 9. Supported Subset and Current Limitations

This section documents the currently implemented (Phase 22 MVP) execution subset.

### 9.1 Supported Expression Subset (Current)

The runtime evaluator currently supports:

- boolean connectives: conjunction/disjunction, implication, iff, not
- comparisons/equality: `==`, `!=`, `<`, `<=`, `>`, `>=`
- arithmetic: `+`, `-`, `*`, `/`, `%` (with division/modulo-by-zero checks)
- `if`/`else` expressions
- `let` bindings with identifier patterns
- struct/enum literals and field access (`.` / `->`)
- indexing into `Seq`/tuple/map
- sequence/set/map literals, including empty constructors
- helper spec calls reachable from ingested protocol sources
- selected built-in methods:
  - `.len()` on `Seq`/`Set`/`Map`/tuple/string
  - `.contains(...)` on `Set`/`Seq`
  - `.contains_key(...)` on `Map`
  - `.insert(...)` / `.remove(...)` on `Set`
- casts to `int`, `nat`, and `bool`

### 9.2 Supported Type/Domain Subset (Current)

Finite-domain expansion and runtime values currently cover:

- primitive-like values: `unit`, `bool`, `int`, `nat`, `string`
- structured/container values:
  - named structs and enums (including enum payload variants)
  - tuples
  - `Seq<T>`, `Set<T>`, `Map<K, V>`
  - references (`&T`/`&mut T`) via underlying `T`
- `model.toml` domain kinds:
  - `values`
  - `int_range`
  - `nat_range`
  - `enum_subset`

### 9.3 Current Limitations (MVP)

- Temporal scope (current Phase 22 status):
  - Safety-only scope in Phase 22 MVP was the initial baseline; bounded liveness (`leads_to`) support is now available with the caveats below.
  - `properties.leads_to` is executable and reports violations via SCC/cycle analysis.
  - `properties.fairness.{weak,strong}` participates in liveness cycle filtering.
  - `search.timeout_ms` is enforced during exploration; timeout preemption reports `result = timeout_reached` and `stop_reason = TimeoutReached`.
  - Liveness evaluation currently runs only on fully explored graphs (`stop_reason = FrontierExhausted`); otherwise report field `liveness.skipped_reason = "incomplete_exploration"`.
  - Fairness filtering is branch-label based over candidate SCCs and should be treated as a bounded-model diagnostic aid rather than a complete temporal proof procedure.
- Current entrypoint assumptions:
  - model-check execution currently assumes `LInit(s, c)` and `LNext(s, s_, c)` style signatures.
  - constants resolution explores all resolved `LConstants` valuations after applying assignments/domains.
- Supported evaluator additions:
  - finite-domain `forall` / `exists`
  - `match` expressions
  - struct update expressions
- Evaluator unsupported constructs:
  - quantifier bindings that are not identifiers
  - quantifier evaluation without a domain resolver hook
  - struct updates whose base is not a struct/enum value
  - bitwise/shift operators
  - casts beyond `int`/`nat`/`bool`
  - non-identifier `let` patterns
- Quantifier nuance:
  - branch-level existentials in `LNext` are supported via branch/domain expansion.
  - arbitrary quantifier expressions are not generally executable by the evaluator.
- Domain expansion limitations:
  - generic domains are only supported for `Seq<T>`, `Set<T>`, and `Map<K, V>` container forms.
  - expansion is bounded by configured collection/search limits and can fail when domains are too large.
- Hash-compaction caveat:
  - `search.state_dedup = "hash_compaction64"` is intentionally lossy and can merge distinct states on hash collisions.
  - Treat it as a bug-finding acceleration mode, not as a sound proof mode.
- Symmetry-field caveat:
  - `search.symmetry_fields` intentionally merges states by anonymizing selected top-level field identities before dedup.
  - Use only when the selected fields are truly symmetric by protocol design.
- POR heuristic caveat:
  - `search.por_heuristic = "invisible_branch"` prunes branches only when writes are syntactically proven invisible to other branches/invariants.
  - Keep it disabled for deadlock checking (`properties.check_deadlock = true`) and treat it as reduction-for-search, not proof of transition completeness.
- Reduction safety guide:
  - `state_dedup = "canonical"`: safe for exact safety exploration (default).
  - `state_dedup = "hash_compaction64"`: lossy bug-finding mode only; collisions can hide behaviors.
  - `symmetry_fields = [...]`: safe only when those fields are truly permutation-symmetric by protocol design.
  - `por_heuristic = "invisible_branch"`: safe only for safety checks under its conservative syntactic predicate; keep deadlock checking off.
- Helper-call limitations:
  - direct helper-call branch solving is available for simple `LStep(s, s_, c)`-style wrappers when helper branches expose direct next-state equalities.
  - unresolved predicate-only helper branches still use bounded candidate enumeration fallback.
  - helper predicates/functions must resolve unambiguously from ingested sources.
  - recursive helper evaluation has a bounded recursion depth.

## 10. Troubleshooting Common Modeling Errors

### 10.1 Domain Too Large (State Explosion)

Typical symptoms:

- run stops early with `result: max_states_reached`
- config/domain errors containing `exceeded limit`
- very large `summary.states` / `summary.transitions` before timeout

Common causes:

- wide `quantifiers.int` / `quantifiers.nat` ranges
- large `quantifiers.types.<Type>` domains
- large collection bounds (`max_seq_len`, `max_set_len`, `max_map_len`)
- broad enum subsets or unconstrained constants domains

Fixes:

1. Shrink numeric ranges first (`int`, `nat`).
2. Reduce per-type domains and enum subsets to the minimal repro case.
3. Lower collection bounds.
4. Pin constants with `[constants.assignments]` where possible.
5. Iterate with smaller `max_depth` and then scale up.

Useful commands:

```bash
transpiler/target/debug/verus-transpile model-config --model path/to/model.toml
transpiler/target/debug/verus-transpile model-check ... --max-depth 2 --max-states 500
```

### 10.2 Unsupported Constructs

Typical symptoms:

- `Unsupported pattern: Model-check evaluator does not support ...`
- errors mentioning quantifier binding/domain-hook requirements, unsupported bitwise/shift operators,
  unsupported casts, or non-identifier `let` patterns
- helper-call resolution errors (`could not resolve helper call`)

Common causes:

- using expressions outside the current evaluator subset
- relying on helpers that are not ingested or are ambiguously named

Fixes:

1. Rewrite property/helper logic into the supported subset in section 9.
2. Prefer explicit boolean/arithmetic/field constraints over unsupported forms.
3. Ensure helper predicates are in the provided source set and uniquely named.
4. If a construct is required, add evaluator support in `transpiler/src/modelcheck/evaluator.rs`.

### 10.3 Constants Resolution Errors

Typical symptom:

- `zero matching LConstants valuations`

Cause:

- constants assignments/domains leave zero matching constant values.

Fixes:

1. Tighten/adjust `[constants.assignments]` and `[constants.domains]` so at least one valuation remains.
2. Narrow type/quantifier domains used by constants fields.

### 10.4 Signature/Entrypoint Mismatches

Typical symptoms:

- unknown invariant name
- init/next signature errors
- missing/invalid entrypoint function names

Fixes:

1. Confirm entrypoints with `--init` / `--next` if names differ from defaults.
2. Keep invariants list aligned with parsed spec function names.
3. Ensure `LInit`/`LNext` use the expected state/constants parameter conventions for MVP.

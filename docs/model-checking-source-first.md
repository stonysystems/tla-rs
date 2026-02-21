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

## 6. Inspect Results

With `--json-report`, output includes:

- `result` (`ok`, violation, or limit/timeout stop)
- `summary.states`
- `summary.transitions`
- `summary.depth`
- `summary.elapsed_ms`
- stop metadata and violation payloads (when present)

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

- Safety-only scope in Phase 22 MVP:
  - liveness/fairness operators (`[]<>`, `WF`, `SF`, `~>`) are out of scope.
- Current entrypoint assumptions:
  - model-check execution currently assumes `LInit(s, c)` and `LNext(s, s_, c)` style signatures.
  - constants resolution currently requires exactly one concrete `LConstants` valuation after applying assignments/domains.
- Evaluator unsupported constructs:
  - `forall`, `exists`, `match`, struct update expressions
  - bitwise/shift operators
  - casts beyond `int`/`nat`/`bool`
  - non-identifier `let` patterns
- Quantifier nuance:
  - branch-level existentials in `LNext` are supported via branch/domain expansion.
  - arbitrary quantifier expressions are not generally executable by the evaluator.
- Domain expansion limitations:
  - generic domains are only supported for `Seq<T>`, `Set<T>`, and `Map<K, V>` container forms.
  - expansion is bounded by configured collection/search limits and can fail when domains are too large.
- Helper-call limitations:
  - helper predicates/functions must resolve unambiguously from ingested sources.
  - recursive helper evaluation has a bounded recursion depth.

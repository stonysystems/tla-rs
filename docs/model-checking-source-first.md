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


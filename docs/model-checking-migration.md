# Migration Guide: TLC Wrapper Workflow -> Source-First Model Checking

This guide explains how to migrate from the older TLC-wrapper flow to the
Phase 22 source-first flow.

## 1. Old vs New Workflow

Wrapper workflow (old):

- primary artifacts: generated `*_MC.tla` and `*.cfg`
- checker: TLC
- properties selected in `.cfg` (`INVARIANTS`, `CHECK_DEADLOCK`)

Source-first workflow (new):

- primary artifacts: protocol spec (`*.rs`), `types.rs`, `model.toml`
- checker: `verus-transpile model-check`
- properties selected in `model.toml` (`[properties]` section)

## 2. Artifact Mapping

- `*_MC.tla` / `.cfg` pair -> protocol `--input` and `--types` files
- `INVARIANTS` list in `.cfg` -> `properties.invariants` in `model.toml`
- `CHECK_DEADLOCK` in `.cfg` -> `properties.check_deadlock` in `model.toml`
- TLC bound tuning -> `search.max_depth`, `search.max_states`, `search.timeout_ms`

## 3. Migration Steps

1. Choose one protocol and identify:
   - protocol file (`src/protocol/<P>/<p>.rs`)
   - types file (`src/protocol/<P>/types.rs`)
2. Create a bounded `model.toml` with finite domains.
3. Port safety property names from wrapper config into
   `properties.invariants`.
4. Run source-first check:

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/<P>/<p>.rs \
  --types src/protocol/<P>/types.rs \
  --model path/to/model.toml \
  --search bfs \
  --json-report
```

5. Compare qualitative outcome against prior TLC expectations
   (pass/non-violation vs violation) for the same bounded intent.

## 4. Property and Semantics Notes

- Source-first Phase 22 MVP is safety-focused.
- `properties.successor_semantics` accepts:
  - `"deadlock"`: explicit deadlock semantics
  - `"stuttering"`: empty-successor stuttering
- `check_deadlock = true` should be paired with `"deadlock"` semantics.

## 5. Suggested Rollout

1. Migrate one protocol first (small bounded model).
2. Add the protocol `model.toml` to checked-in fixtures.
3. Add integration assertions for non-zero states/transitions and expected
   result category.
4. Repeat per protocol.

This keeps migration incremental and regression-tested.


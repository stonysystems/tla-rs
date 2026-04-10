# DPOR-Based Model Checker Prototype for tla-rs

A standalone prototype exploring Dynamic Partial Order Reduction (DPOR)
for model-checking translated tla-rs specifications. This is an isolated
incubator — it does **not** modify `transpiler/src/modelcheck/`.

## What this prototype checks

Finite-state safety and liveness properties of TLA+-derived Rust/Verus
specs, using DPOR to reduce the explored state space compared to
exhaustive BFS/DFS. The target input is tla-rs specs (Verus `spec fn`
predicates) translated from TLA+ via the repo's transpiler pipeline.

## Corpus layout

- **`tests/tla/`** — Source-of-truth TLA+ corpus (20 cases, `01_` to `20_`).
- **`tests/tla-rs/`** — Generated tla-rs translations (derived, reproducible).
- **`tests/manifest.toml`** — Per-case metadata: expected status, bounds, notes.
- **`tests/reports/`** — Machine-readable suite results (baseline vs DPOR).

## Key commands

Regenerate the translated corpus from TLA+ sources:

```bash
./scripts/regenerate_corpus.sh
```

Run all 20 test cases (baseline exhaustive + DPOR when available):

```bash
./scripts/run_full_suite.sh
```

Run one shadow-mode baseline-vs-DPOR comparison on the same fixture:

```bash
cargo run --manifest-path Cargo.toml --bin dpor-checker -- \
  shadow-compare \
  --spec tests/tla-rs/01_aplusb/APlusB.rs \
  --model /tmp/model.toml \
  --invariant LSumInvariant
```

## Design references

See `design.md` for structured notes on:
- **GenMC** (`https://github.com/MPI-SWS/genmc`) — architecture reference
- **Nidhugg** (`https://github.com/nidhugg/nidhugg`) — DPOR algorithm reference
- **CDSChecker** (`https://github.com/computersforpeace/model-checker`) — smaller algorithmic reference

## Integration policy

This prototype must earn mainline integration by demonstrating:
1. All 20 corpus cases pass the baseline oracle.
2. DPOR results agree with baseline on verdict + reachable-state set.
3. A green regression story exists before any `transpiler/src/modelcheck` changes.

See `design.md` §"Prototype-to-Mainline Integration Gate" for details.

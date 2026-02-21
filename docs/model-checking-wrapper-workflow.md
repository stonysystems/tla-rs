# Relational Wrapper Generation Guide

This guide documents how to generate TLC-friendly wrappers from relational TLA+
modules and how to choose this path versus the source-first
`verus-transpile model-check` workflow.

## 1. When This Applies

Use wrapper generation when you already have relational TLA+ modules (for
example from `verus2tla`) and need TLC-oriented artifacts:

- `<Module>_MC.tla`
- `<Module>_MC.cfg`

The wrapper generator targets modules that expose relational entrypoints:

- `Init(s, c)`
- `Next(s, s_, c)`

## 2. Command Workflow

Build the transpiler binary:

```bash
cargo build --manifest-path transpiler/Cargo.toml --bin verus-transpile
```

Generate wrapper + cfg:

```bash
transpiler/target/debug/verus-transpile generate-mc-wrapper \
  --input transpiler/tla_test_workspace/transpiler_generated_tla/TwoPhase/Twophase.tla \
  --output out/Twophase_MC.tla \
  --invariant Consistency
```

The command writes:

- wrapper module: `out/Twophase_MC.tla`
- cfg file: `out/Twophase_MC.cfg`

## 3. Optional Packet Projection Modes

For protocols where `Next` branches bind explicit packet outputs (for example
`sent_packets`), you can project them into a `msgs` variable in the wrapper:

```bash
transpiler/target/debug/verus-transpile generate-mc-wrapper \
  --input transpiler/tla_test_workspace/transpiler_generated_tla/TwoPhase/Twophase.tla \
  --output out/Twophase_MC_lifted.tla \
  --packet-mode append-seq \
  --packet-var sent_packets
```

Supported modes:

- `--packet-mode none` (default): no packet projection.
- `--packet-mode append-seq`: `msgs' = msgs \o sent_packets`.
- `--packet-mode replace-seq`: `msgs' = sent_packets`.

## 4. Selection Guidance: Wrapper vs Source-First

Use **source-first** (`verus-transpile model-check`) when:

- you want direct checking on `src/protocol/<P>/<p>.rs` and `types.rs`
- you want one bounded model configuration (`model.toml`) tracked in repo
- you want JSON machine-readable reports from the checker

Use **wrapper generation** (`generate-mc-wrapper`) when:

- you need TLC artifacts (`*_MC.tla` + `.cfg`) for existing TLC pipelines
- you are comparing results with historical wrapper-based runs
- you need explicit wrapper-level message-lift modeling for TLC runs

## 5. Recommended Team Workflow

1. Prefer source-first model checks for day-to-day protocol regression.
2. Generate wrappers only when TLC integration or historical parity is needed.
3. Keep generated wrappers deterministic and fixture-tested under
   `transpiler/tests/mc_wrapper_fixtures/`.
4. Keep the migration mapping in `docs/model-checking-migration.md` aligned.


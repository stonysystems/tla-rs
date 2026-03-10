# Worked Walkthrough

## Chosen Shared Example
This walkthrough uses one shared small protocol/model for both engines: `TwoPhase` with the checked-in benchmark model.

- Chosen protocol: `src/protocol/TwoPhase/twophase.rs` with `src/protocol/TwoPhase/types.rs`
- Shared model fixture: `transpiler/tests/model_check_fixtures/benchmarks_1h/twophase_benchmark.model.toml`
- Why this model: `TwoPhase` is smaller than `LeaderElection`/`Paxos`, and the repo already contains checked-in outcomes for both engines on this same model.

## Checked-In Evidence for Both Sides
- Source-first evidence:
  - `reports/benchmarks/source_first/twophase_benchmark.json`
  - `reports/benchmarks/source_first/SUMMARY.md`
- Traditional TLC evidence:
  - `reports/benchmarks/tlc/twophase_benchmark.log`
  - `reports/benchmarks/tlc/SUMMARY.md`
  - TLC wrapper and config for the same model:
    - `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.tla`
    - `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.cfg`
- Cross-engine synthesis:
  - `reports/benchmarks/TLC_VS_SOURCE_FIRST_BENCHMARK_COMPARISON.md`

## Inputs and Setup
This section will trace the chosen `TwoPhase` model only (same fixture, same invariants) so both tracks stay directly comparable.

## Step-by-Step State Transition
This section will show at least one concrete state and one successor transition from the chosen `TwoPhase` model.

## Parallel Track A: Traditional TLC Terms
This section will describe the chosen run in TLC-style terminology using the checked-in TLC wrapper/log artifacts above.

## Parallel Track B: tla-rs Source-First Terms
This section will describe the same chosen run in tla-rs source-first terminology using the checked-in source-first JSON artifacts above.

## Output Interpretation
This section will explain how to read the two checked-in outputs for the same shared model.

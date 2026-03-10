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
- Source-first protocol inputs:
  - `src/protocol/TwoPhase/twophase.rs`
  - `src/protocol/TwoPhase/types.rs`
- Shared model input:
  - `transpiler/tests/model_check_fixtures/benchmarks_1h/twophase_benchmark.model.toml`
- Traditional TLC side for the same model:
  - `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.tla`
  - `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.cfg`
- Shared safety properties used in both runs:
  - no commit-abort overlap
  - committed subset prepared
  - TM committed requires all prepared

## Step-by-Step Trace (Ordered)
1. **Input spec/model selection**
   - Source-first reads the Verus spec entrypoints from `twophase.rs` (`LInit`, `LNext`) plus the finite model from `twophase_benchmark.model.toml`.
   - TLC reads the checked-in wrapper/config pair `TwoPhase_Benchmark_MC.tla` + `TwoPhase_Benchmark_MC.cfg`, which encode the same model intent for the benchmark campaign.
   - Anchor: `src/protocol/TwoPhase/twophase.rs` (`LInit`, `LNext`, `LSafety*`)
   - Anchor: `transpiler/tests/model_check_fixtures/benchmarks_1h/twophase_benchmark.model.toml`
   - Anchor: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.tla`
   - Anchor: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.cfg`

2. **How initial states are obtained**
   - Source-first expands finite domains from `model.toml`, then keeps states that satisfy `LInit`; the checked-in JSON reports one constants valuation for this model.
   - TLC evaluates `StateInit` from the wrapper and logs that it finished computing initial states with one distinct initial state.
   - Anchor: `src/protocol/TwoPhase/twophase.rs` (`LInit`)
   - Anchor: `reports/benchmarks/source_first/twophase_benchmark.json` (`summary.constants_valuations_total`)
   - Anchor: `reports/benchmarks/tlc/twophase_benchmark.log` (`Finished computing initial states: 1 distinct state`)

3. **How one successor step is computed**
   - Start from the initial shape (`tm_state=Init`, all RM sets empty, no messages), then apply `TMSendPrepare` / `LTMSendPrepare`.
   - In source-first terms, this is one `LNext` branch: precondition `tm_state is Init`, next state keeps core fields unchanged, and emitted packet sequence is `Prepare`.
   - In TLC wrapper terms, `TMSendPrepare` keeps `state' = state`, adds `PrepareMsg` into `msgs'`, and leaves constants unchanged.
   - Anchor: `src/protocol/TwoPhase/twophase.rs` (`LTMSendPrepare`, `LNext`)
   - Anchor: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.tla` (`StateInit`, `TMSendPrepare`, `StateNext`)

4. **Where invariant checking happens**
   - Source-first checks the configured/resolved safety invariants during exploration; the checked-in JSON shows `configured_count = 3`, `resolved_count = 3`, and no invariant violation.
   - TLC checks the invariants listed in `.cfg` during model checking; the checked-in log reports no error.
   - Anchor: `reports/benchmarks/source_first/twophase_benchmark.json` (`invariants`, `invariant_violation`)
   - Anchor: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.cfg` (`INVARIANTS`)
   - Anchor: `reports/benchmarks/tlc/twophase_benchmark.log` (`Model checking completed. No error has been found.`)

5. **What output/report the user gets**
   - Source-first output is machine-readable JSON (`result`, stop reason, depth/states/transitions, timing, evidence mode).
   - TLC output is log-style text with generated/distinct states, depth, and wall-clock completion summary.
   - The comparison report aligns these outputs side by side for the same model.
   - Anchor: `reports/benchmarks/source_first/twophase_benchmark.json`
   - Anchor: `reports/benchmarks/tlc/twophase_benchmark.log`
   - Anchor: `reports/benchmarks/TLC_VS_SOURCE_FIRST_BENCHMARK_COMPARISON.md`

## Step-by-Step State Transition
### Concrete Example: `TMSendPrepare` / `LTMSendPrepare`
This walkthrough uses one explicit transition instance so the explanation is not only command-level or pipeline-level prose.

**Pre-state snapshot (before successor step)**
- `tm_state = Init`
- `tm_prepared = {}`
- `rm_prepared = {}`
- `rm_committed = {}`
- `rm_aborted = {}`
- message set / emitted packets are empty at this point (`msgs = {}` on TLC side)
- model constants use two RMs in this benchmark (`RMs == {0, 1}`)

**Transition applied**
- Source-first branch: `LTMSendPrepare` under `LNext`
- TLC wrapper action: `TMSendPrepare` under `StateNext`

**Post-state snapshot (after successor step)**
- Core protocol state remains unchanged (`tm_state`, `tm_prepared`, `rm_*` sets are the same as pre-state)
- Source-first emitted packets: `sent_packets == [Prepare]`
- TLC message channel update: `msgs' = msgs \\cup {PrepareMsg}`

This is intentionally small, but it is a real state transition example with explicit pre-state, transition, and post-state.
- Anchor: `src/protocol/TwoPhase/twophase.rs` (`LTMSendPrepare`, `LNext`)
- Anchor: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.tla` (`TMSendPrepare`, `StateNext`, `RMs`)

## Parallel Track A: Traditional TLC Terms
### How this looks in traditional TLA+/TLC terms
1. **Input/model layer**
   - TLC consumes the wrapper module and config:
     - `TwoPhase_Benchmark_MC.tla`
     - `TwoPhase_Benchmark_MC.cfg`
   - The wrapper defines `VARIABLE state, constants, msgs` and a `Spec == StateInit /\ [][StateNext]_vars`.
   - Anchor: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.tla`
   - Anchor: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.cfg`

2. **Initial-state construction**
   - TLC evaluates `StateInit` in the wrapper and logs one distinct initial state for this benchmark run.
   - Anchor: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.tla` (`StateInit`)
   - Anchor: `reports/benchmarks/tlc/twophase_benchmark.log` (`Finished computing initial states: 1 distinct state`)

3. **One successor step**
   - A concrete successor is `TMSendPrepare`: keep `state' = state`, add `PrepareMsg` to `msgs'`, keep constants unchanged.
   - Anchor: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.tla` (`TMSendPrepare`, `StateNext`)

4. **Invariant checking**
   - TLC checks the invariants listed in `.cfg` across explored states; this checked-in run reports no error.
   - Anchor: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.cfg` (`INVARIANTS`)
   - Anchor: `reports/benchmarks/tlc/twophase_benchmark.log` (`Model checking completed. No error has been found.`)

5. **Output/report surface**
   - TLC result is log-oriented text: generated states, distinct states, depth, and elapsed time.
   - Anchor: `reports/benchmarks/tlc/twophase_benchmark.log`
   - Anchor: `reports/benchmarks/tlc/SUMMARY.md`

## Parallel Track B: tla-rs Source-First Terms
### How this looks in current tla-rs source-first terms
1. **Input/model layer**
   - Source-first consumes the Rust/Verus spec plus type file and the same shared model fixture.
   - Anchor: `src/protocol/TwoPhase/twophase.rs`
   - Anchor: `src/protocol/TwoPhase/types.rs`
   - Anchor: `transpiler/tests/model_check_fixtures/benchmarks_1h/twophase_benchmark.model.toml`

2. **Initial-state construction**
   - Source-first evaluates `LInit` under finite domains and records constants valuation counts in the JSON summary.
   - Anchor: `src/protocol/TwoPhase/twophase.rs` (`LInit`)
   - Anchor: `reports/benchmarks/source_first/twophase_benchmark.json` (`summary.constants_valuations_total`)

3. **One successor step**
   - The corresponding concrete branch is `LTMSendPrepare` under `LNext`: `tm_state is Init`, unchanged state fields, emitted `Prepare`.
   - Anchor: `src/protocol/TwoPhase/twophase.rs` (`LTMSendPrepare`, `LNext`)

4. **Invariant checking**
   - Source-first resolves and checks the 3 configured invariants during exploration; the checked-in run has no invariant violation.
   - Anchor: `reports/benchmarks/source_first/twophase_benchmark.json` (`invariants.configured_count`, `invariants.resolved_count`, `invariant_violation`)

5. **Output/report surface**
   - Source-first result is machine-readable JSON: result, stop reason, states/transitions/depth, elapsed time, evidence mode.
   - Anchor: `reports/benchmarks/source_first/twophase_benchmark.json`
   - Anchor: `reports/benchmarks/source_first/SUMMARY.md`
   - Anchor: `reports/benchmarks/TLC_VS_SOURCE_FIRST_BENCHMARK_COMPARISON.md`

## Output Interpretation
This section will explain how to read the two checked-in outputs for the same shared model.

## TLC Detail Confidence and Inference Marking
- **Inference status for this walkthrough**: No inferred/approximate TLC details are used in this walkthrough.
- Every TLC statement above is grounded in checked-in local artifacts:
  - `reports/benchmarks/tlc/twophase_benchmark.log`
  - `reports/benchmarks/tlc/SUMMARY.md`
  - `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.tla`
  - `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.cfg`
- If a future revision introduces TLC details that are inferred/approximate rather than directly evidenced, it must mark each such claim with `[Inference]` and cite the specific source used.

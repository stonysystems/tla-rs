# tla-rs Source-First Model Checking

## Beginner Context
This chapter explains how the current repository's source-first checker works, based on local code and docs.

## End-to-End Source-First Path
1. Load Rust/Verus input sources and model config.
2. Resolve checker entrypoints (`LInit`, `LNext`, invariants, fairness).
3. Build branch IR and initial states.
4. Expand finite domains and solve branch constraints.
5. Explore states with dedup/reductions and evaluate properties.
6. Produce reports/telemetry artifacts.

## Architecture Anchors
This section will map each stage to concrete modules under `transpiler/src/modelcheck/`.

## Known Limits
This section will summarize current evaluator/solver/coverage limits from checked-in status docs.

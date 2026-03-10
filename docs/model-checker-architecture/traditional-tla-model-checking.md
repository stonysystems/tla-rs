# Traditional TLA+ Model Checking (TLC-Centered)

## Beginner Context
This chapter explains the traditional TLA+ model-checking path with TLC as the primary checker.

## Toolchain Overview
- TLA+ module and model/config inputs.
- Front-end parsing/validation.
- Explicit-state exploration and property checks.

## End-to-End Execution Path
1. Parse module and model configuration.
2. Construct initial states.
3. Generate successors from `Next`.
4. Deduplicate visited states and continue exploration.
5. Check invariants/deadlocks/liveness and emit counterexamples.

## Explicit-State vs Theorem Proving
This section will contrast state exploration with proof-based methods in beginner terms.

## Practical Limits
- Finite-model assumptions.
- State explosion.
- Sensitivity to model/config choices.

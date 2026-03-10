# Glossary

## Core State-Space Terms
- **State**: A complete snapshot of all modeled variables at one point.
- **Transition**: A valid one-step move from one state to another.
- **State Space**: The set of all reachable states under the model.
- **Successor Generation**: Constructing next states from a current state.
- **State Deduplication**: Detecting and skipping already-seen states.

## Property Terms
- **Invariant**: A property that must hold in every reachable state.
- **Safety**: "Nothing bad happens" properties (for example invariant violations).
- **Liveness**: "Something good eventually happens" properties.
- **Deadlock**: A state with no enabled next transition under checker semantics.
- **Fairness**: Constraints that rule out unfair infinite behaviors.
- **Counterexample**: A concrete violating execution trace produced by the checker.

## TLA+ Ecosystem Terms
- **TLA+**: A specification language for concurrent/distributed systems.
- **SANY**: Front-end parser/analyzer used in the TLA+ toolchain.
- **TLC**: Explicit-state model checker for TLA+ specifications.
- **Explicit-State Model Checking**: Enumerating reachable states directly.

## tla-rs Source-First Terms
- **Source-First**: Checking Rust/Verus source-level specs directly.
- **Finite-Domain Expansion**: Enumerating concrete values for symbolic vars.
- **Symmetry Reduction**: Canonicalizing equivalent states under permutations.
- **Partial-Order Reduction (POR)**: Pruning independent interleavings.
- **Hash Compaction**: Memory-saving approximate dedup mode.
- **Telemetry**: Structured run statistics and phase timing/report outputs.

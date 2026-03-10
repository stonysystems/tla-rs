# Glossary

## Core State-Space Terms
- **State**: One full snapshot of all model variables at a single step.
- **Transition**: One valid step from a current state to a next state.
- **State Space**: The set of states reachable by repeatedly applying transitions.
- **Successor Generation**: The checker process that computes next states from one current state.
- **State Deduplication**: Detecting states already seen so exploration does not revisit them forever.

## Property Terms
- **Invariant**: A property that must hold in every reachable state.
- **Safety**: A "nothing bad happens" property, often encoded as invariants.
- **Liveness**: A "something good eventually happens" property.
- **Deadlock**: A state with no enabled transition under the checker's step semantics.
- **Fairness**: Assumptions that disallow unfair infinite schedules when checking liveness.
- **Counterexample**: A concrete violating execution trace that shows why a property fails.

## TLA+ Ecosystem Terms
- **TLA+**: A formal language for writing state-machine specifications.
- **SANY**: The front-end parser/analyzer in the standard TLA+ toolchain.
- **TLC**: The traditional explicit-state checker used for TLA+ model checking.
- **Explicit-State Model Checking**: Exploring concrete states and transitions directly, instead of proving formulas universally as in theorem proving.

## tla-rs Source-First Terms
- **Source-First**: Model checking directly over Rust/Verus spec source instead of translated TLA+ text.
- **Finite-Domain Expansion**: Replacing symbolic variables with bounded concrete value domains during exploration.
- **Symmetry Reduction**: Canonicalizing equivalent states under identity/permutation symmetries to reduce duplicates.
- **Partial-Order Reduction (POR)**: Avoiding exploration of redundant interleavings when actions are independent.
- **Hash Compaction**: A lossy, memory-saving deduplication mode using compact state fingerprints.
- **Telemetry**: Structured run statistics (counts, timings, stop reasons) emitted for diagnostics and reports.

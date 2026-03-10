# Traditional TLA+ Model Checking (TLC-Centered)

## Beginner Toolchain Primer
Traditional TLA+ model checking is a pipeline, not a single tool.

- **TLA+** is the specification language. You write a state-machine style module that declares variables, an initial condition (`Init`), and step relation (`Next`).
- **SANY** is the front-end analyzer in the standard TLA+ toolchain. It parses the module, resolves names/imports, and rejects malformed or inconsistent spec structure before model checking.
- **TLC** is the explicit-state model checker. It takes the analyzed spec plus model settings, generates concrete initial states, repeatedly applies `Next` to generate successors, and checks properties during exploration.
- **Finite model/config** settings make checking executable: they pick concrete constant values and finite domains, choose what to check (invariants, deadlock, liveness), and therefore define the exact state space TLC will explore.

A useful beginner mental model is: **TLA+ defines behavior**, **SANY validates structure**, and **TLC explores a finite instance of that behavior**.

## What The Model/Config Contributes
TLA+ modules are usually symbolic. A model/config file turns them into a concrete run by fixing constants and bounds.

- It binds abstract constants to concrete values or finite sets.
- It can constrain the initial state and action parameters through model values and overrides.
- It selects the property checks to run (for example invariants and deadlock checks).
- It controls whether TLC explores a tiny teaching model or a larger stress model.

Because of this, two different model/config choices for the same TLA+ module can produce very different exploration size, runtime, and bug-finding behavior.

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

# Phase 22 MVP Scope (Source-First Model Checking)

## Objective

Define the Phase 22 minimum viable product as a **source-first safety model checker** for tla-rs protocol specs.

## MVP Definition

The Phase 22 MVP is:

- A model checker that consumes tla-rs Verus spec source directly (not transpiled `.tla` files).
- Input semantics are driven by protocol `LInit` and `LNext` operators.
- The checker focuses on **safety** properties over finite domains for initial implementation.

This means MVP entrypoints are expected from source-level spec modules, with `LInit` and `LNext` as the canonical transition interface.

## Explicit Boundaries

- Source-first only for MVP: `.tla` input is not required for the primary checking path.
- Liveness and fairness (`[]<>`, `WF`, `SF`, `~>`) are outside MVP scope and handled in later phases.

## Deferred Work (Post-MVP)

Liveness/fairness work is explicitly deferred to **Phase 22.10 Follow-Up** and is not required for Phase 22 MVP acceptance.

Deferred items include:

- `[]<>` (eventuality) checks
- fairness constraints (`WF`, `SF`)
- leads-to (`~>`) obligations and cycle/SCC-style algorithms

## Phase 22 MVP Pass Criteria

Phase 22 MVP is considered complete when:

- Exhaustive finite-model safety checks run successfully for small models of:
  - TwoPhase
  - LeaderElection
  - PrimaryBackup
- Bounded/partial exploration mode is available for larger-state protocols (for example Paxos) with explicit limits (`max_depth`, `max_states`, timeout).

## Why This Boundary

This keeps initial implementation complexity bounded while enabling direct verification workflows for existing tla-rs protocol specs without requiring an intermediate TLA+ conversion step.

# Sleep-Set Reduction Table (Phase 38.8.3.c)

## Cases 04-11: Before/After Sleep-Set Comparison

All measurements from DPOR engine with `max_depth=20, max_states=10000`.

| # | Case | States (no sleep) | States (with sleep) | Transitions (no sleep) | Transitions (with sleep) | Reduction | Notes |
|---|------|-------------------|--------------------|-----------------------|-------------------------|-----------|-------|
| 04 | LockBasic | 3 | 3 | 2 | 2 | 0% | Single-process, empty footprints |
| 05 | BrokenLockBug | 7 | 7 | 6 | 6 | 0% | Violation stops early |
| 06 | TicketLock | 7 | 7 | 6 | 6 | 0% | Single-process, empty footprints |
| 07 | ProducerConsumer | 21 | 21 | 20 | 20 | 0% | Single-process, empty footprints |
| 08 | BoundedBuffer | 6 | 6 | 5 | 5 | 0% | Single-process, empty footprints |
| 09 | PetersonMutex | 10 | 10 | 9 | 9 | 0% | Single-process, empty footprints |
| 10 | BakeryMutex | -- | -- | -- | -- | N/A | Blocked: domain expansion |
| 11 | ReadersWriters | 4 | 4 | 3 | 3 | 0% | Violation stops early |

## Analysis

**Zero reduction observed.** This is expected and correct because:

1. **Single-process model**: All translated TLA+ specs currently use `ProcessId(0)` for all transitions. In source-DPOR, same-process transitions are always dependent — independence only applies across different processes.

2. **Empty footprints**: The `TransitionFootprint` on each `EnabledTransition` is default (empty reads/writes). The `compute_child_sleep_set()` function treats empty footprints as dependent with everything (conservative), so no transitions stay asleep during propagation.

3. **Why footprints are empty**: The DPOR engine's `enabled_transitions()` delegates to `full_successors()` which uses a flat candidate-enumeration fallback. This fallback evaluates the full `LNext` predicate without decomposing by branch, so it can't attribute individual successors to specific branches. Since branch footprints can't be mapped to transitions, all footprints remain empty.

## When will reduction appear?

Sleep sets will provide measurable reduction when either:

1. **Multi-process specs**: TLA+ specs with multiple distinct process types (e.g., `\E p \in Procs : Action(p)` with per-process state) where the translator assigns distinct `ProcessId` values.

2. **Per-transition footprints**: The enabled_transitions path successfully decomposes LNext into branches with direct `s_.field == ...` assignments (not predicate-only), allowing branch-level footprints to be assigned to individual transitions.

3. **Both conditions**: Independence requires both that transitions touch disjoint state fields AND belong to different processes. In the current single-process model, all transitions are trivially dependent regardless of footprints.

## Correctness Verification

The `test_sleep_set_parity_all_passing_cases` test (Phase 38.8.3.b) verifies on every commit that sleep sets never lose states across all 7 positive baseline-passing cases. This gate ensures that even when reduction starts appearing, it never causes verdict regressions.

## Date

Generated: 2026-03-26 (Milestone M7, 12/20 pass)

# Bug B Follow-Up: Case 19 Remaining Blocker (2026-04-09)

## Summary

After the translator-side Bug B repairs, case 19 (`19_epaxos_small`) no longer
has the old degraded signatures/bodies issue. The remaining blocker is bounded
model construction, not parser/translation collapse:

- `LInit` now has correct shape (`s: LState, c_consts: LConstants`).
- Symbolic phase tags are now dense (`1..5`) instead of sparse hash-like ints.
- Baseline still reports `initial_states=0` under current tiny bounds (`int 0..1`).

## Why `initial_states=0` Still Happens

Case 19 `LInit` requires:

- `s.phase == 1int`,
- `c_consts.num_replicas >= 3`,
- `c_consts.quorum_size > 0`,
- `c_consts.fast_quorum_size >= c_consts.quorum_size`.

With `int 0..1`, constants constraints are unsatisfiable unless integer domains
are widened for constants. But widening global `int` also widens `LState`
candidate expansion in initial-state construction, which currently performs a
full cartesian product over struct fields and hits tractability limits.

## Quantified Explosion (Current Expansion Model)

For `LState` with 8 int fields, 2 bool fields, and 2 `Set<int>` fields
(`max_set_len=1`), candidate count is approximately:

`n^8 * 4 * (n+1)^2`

where `n = |int domain|`.

Examples:

- `n=2` (`0..1`): `9,216` (tractable) but constants constraints unsat.
- `n=4` (`0..3`): `6,553,600` (already very high).
- `n=5` (`0..4`): `56,250,000` (impractical for current eager expansion).

## Honest Next Options

1. Improve initial-state candidate synthesis/pruning for large struct domains
   so case 19 can run with required integer ranges.
2. Introduce a non-int finite representation for symbolic protocol tags (e.g.,
   enum-like typing for `phase`) so protocol control states do not depend on
   the global int range.

Either option should be landed before claiming Bug B fully closed.

## Follow-Up (2026-04-09, evening pass)

We landed two checker-side improvements in `transpiler/src/main.rs`:

1. The `LInit` pinned-template fallback now recognizes generated binary `&&`
   conjunctions (not just `&&&`).
2. When pinned-template seeding is active, transition solving is no longer
   forcibly filtered to the pinned seed candidate set.

Additionally, helper-call solving now skips unsupported helper sub-branches
instead of discarding the whole helper call path when pinned-fallback mode is
active (while preserving prior fallback behavior for normal expanded runs).

With temporary widened bounds (`int 0..3`, deadlock checking enabled), case 19
now reaches a real initial state:

- `initial_states = 1`
- `distinct_states = 1`
- `result = deadlock_detected`

This is progress over the previous `initial_states=0`, but still not honest
closure. Current branch telemetry shows zero successful successors on every
`LNext` branch, so the remaining blocker moved from pure init seeding to
transition enablement on the degraded EPaxos helper signatures/bodies.

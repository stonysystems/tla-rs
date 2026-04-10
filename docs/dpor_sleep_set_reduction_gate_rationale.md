# DPOR Sleep-Set Reduction Gate Rationale

Date: 2026-04-10

## Context

Phase `38.14.10.d` originally tracked a gate of:

- `>10%` **distinct-state** reduction on at least `3` measured multi-process cases.

At the same time, both parity tests and the measurement harness enforce:

- `conservative ⊆ independence`
- `conservative ⊆ sleep`

This was introduced as a no-lost-state safety invariant for optimized modes.

## Blocker

If `conservative ⊆ sleep`, then `|sleep| >= |conservative|`.
The currently reported distinct-state reduction metric is:

- `(conservative - sleep) / conservative`

Therefore this metric is always `<= 0` under the enforced safety invariant.
A positive distinct-state reduction is mathematically impossible unless that
subset invariant is relaxed or the metric definition changes.

## Practical implication

Current sleep-set tuning can still provide real value through:

- transition reduction (`transitions_fired`), and
- lower exploration work at equivalent safety results.

Observed example on 2026-04-10 measurements: `09_peterson_mutex_2p`
shows `16 -> 12` transitions (`25%` reduction) with no state-loss regression.

## Proposed next leaves for `38.14.10.d.b.c.i`

1. Keep no-lost-state subset parity invariant and define an evidence gate based
   on transition/work reduction instead of distinct-state reduction.
2. If distinct-state reduction remains mandatory, explicitly replace the current
   safety invariant with a weaker, justified projection-level parity contract,
   then document the soundness risk and required witness checks.

## Resolution applied in `38.14.10.d.b.c.i.b`

The evidence gate is now retargeted to a parity-consistent work metric:

- `>10%` transition reduction (`transitions_fired`) on at least `3`
  measured multi-process cases.

Distinct-state reduction remains in the table as diagnostics only, not as a
closure gate, because it is incompatible with the enforced subset safety check.

Current measured status after retargeting (2026-04-10):

- `1 / 3` transition-gate hits (`09_peterson_mutex_2p`), so the gate is
  still **NOT MET**.

## Resolution applied in `38.14.10.d.b.c.i.c`

Decision: do **not** weaken subset parity.

- Distinct-state reduction is not a hard gate anymore.
- Keep `conservative ⊆ independence` and `conservative ⊆ sleep` as-is.
- Do not introduce a weaker projection-level parity contract at this stage.

## Rejected experiment (`38.14.10.d.b.c.j`)

Tried broadening child-sleep seeding to all enabled sibling alternatives
(instead of only deterministic ordered-before candidates).

Result on 2026-04-10:

- Broke parity on `09_peterson_mutex_2p`: sleep-mode distinct states dropped
  from `10` to `7` (lost conservative states).

Decision:

- Reject and revert this widening under the current conservative parity model.
- Keep the focused guardrail test
  `test_sleep_set_parity_peterson_mutex_no_lost_states`.

## Resolution applied in `38.14.10.d.b.c.k`

Implemented a small parity-safe transition reduction in `explore_dpor`:

- In sleep mode, while scanning candidates at one frame, skip a candidate if a
  previously explored sibling in `done` already reaches the same
  `successor_fingerprint`.

Rationale:

- For this checker's current state-based safety contract, re-firing a sibling
  that reaches the exact same successor state is redundant work.
- The step is conservative and frame-local; it does not weaken the existing
  subset parity requirement.

Validation on 2026-04-10:

- Added focused helper tests:
  `test_has_done_successor_fingerprint_true_for_matching_done_transition`,
  `test_has_done_successor_fingerprint_false_without_matching_done_transition`.
- Parity guard tests passed, including
  `test_sleep_set_parity_peterson_mutex_no_lost_states` and
  `test_sleep_set_parity_all_passing_cases`.
- Reduction harness remained unchanged (`1/3` transition-gate hits).

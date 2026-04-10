# DPOR Sleep-Set Reduction Gate Rationale

Date: 2026-04-10

## Context

Phase `38.14.10.d` currently tracks a gate of:

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

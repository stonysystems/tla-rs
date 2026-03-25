# DPOR Checker Test Corpus

## Case Ordering

Test cases are numbered `01_` through `20_`, ordered from easiest to hardest:

- `01_`–`05_`: Micro-models (single variable, few states)
- `06_`–`10_`: Classical concurrency models (mutex, producer-consumer)
- `11_`–`15_`: Small distributed protocol models (two-phase commit, leader election)
- `16_`–`20_`: Full protocol models (Paxos, Raft, PBFT — may need shrunk bounds)

Each case is a directory under `tla/` containing one or more `.tla` files.
The corresponding generated tla-rs output lives under `tla-rs/` with the
same case ID prefix.

## Expected Status Vocabulary

Each case in `manifest.toml` has an `expected_status` field:

| Status | Meaning |
|--------|---------|
| `ok` | Exploration completes, all invariants hold, no deadlock |
| `invariant_violation` | Expected to find an invariant violation (negative case) |
| `deadlock` | Expected to find a deadlock state (negative case) |
| `known_unimplemented` | Case cannot be translated or checked yet; placeholder |
| `timeout` | Case is expected to exceed time budget at current bounds |

## What Counts as a Regression

A **regression** is any of the following compared to the previous milestone:

1. A case that was `ok` now reports `invariant_violation` or `deadlock`.
2. A case that was `invariant_violation` now reports `ok` (lost the bug).
3. A case that was passing (`ok` or expected-negative matched) now fails
   to complete (crash, panic, timeout where it previously finished).
4. The DPOR explorer disagrees with the baseline exhaustive explorer on
   verdict or normalized reachable-state set for any case where both
   previously agreed.

A case moving from `known_unimplemented` to any other status is **not** a
regression — it is progress.

## Corpus Provenance

For protocol-scale cases (cases 11+), the TLA+ source may come from:

- `transpiler/tests/tla_examples/` — existing TLA+ examples in the repo
- `transpiler/tla_test_workspace/transpiler_generated_tla/` — auto-generated TLA+
- `src/protocol/*/` — Verus spec files (used as tla-rs input directly)

The exact source for each case is documented in `manifest.toml` under the
`source` field.

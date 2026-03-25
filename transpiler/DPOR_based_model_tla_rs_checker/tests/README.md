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

| Case | Source | Provenance |
|------|--------|------------|
| 01-12 | Hand-written TLA+ | Original specs in `tests/tla/` |
| 13 (TwoPhase) | `transpiler/tests/tla_examples/TwoPhase.tla` | Copied verbatim |
| 14 (LeaderElection) | `transpiler/tla_test_workspace/transpiler_generated_tla/LeaderElection/` | Copied verbatim |
| 15 (ChainReplication) | `transpiler/tla_test_workspace/transpiler_generated_tla/ChainReplication/` | Copied verbatim |
| 16 (PrimaryBackup) | `transpiler/tla_test_workspace/transpiler_generated_tla/PrimaryBackup/` | Copied verbatim |
| 17 (Paxos) | `transpiler/tests/tla_examples/Paxos.tla` | Copied verbatim |
| 18 (PBFT) | `transpiler/tests/tla_examples/PBFT.tla` | Copied verbatim |
| 19 (EPaxos) | `transpiler/tla_test_workspace/transpiler_generated_tla/EPaxos/` | Copied verbatim |
| 20 (Raft) | `transpiler/tests/tla_examples/Raft.tla` | Copied verbatim |

The `source` field in `manifest.toml` records the exact provenance per case.

## Corpus Generation

Regenerate the tla-rs translations from TLA+ sources:

```bash
cd transpiler/DPOR_based_model_tla_rs_checker
./scripts/regenerate_corpus.sh
```

**Current translation status** (2026-03-25): 12/20 cases translate successfully.
8 cases fail because the transpiler doesn't yet support certain TLA+ features
used in the hand-written specs (CONSTANT params, EXCEPT notation, function
definitions). Failed cases have a `TRANSLATION_FAILED` marker in `tests/tla-rs/`.

The `tla-rs/` directory is a generated artifact — do NOT hand-edit files there.
Run `regenerate_corpus.sh` to reproduce from a clean checkout.

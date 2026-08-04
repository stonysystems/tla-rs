# Clean-Subset TLA+ Corpus (Phase 53)

This corpus is the foundation of the Phase 52 translator (clean-subset global-multi-server
TLA+ → single-process Verus spec). It is a **dev/test/eval** corpus for a deterministic,
rule-based AST translator — *not* a training set.

Plan of record: [`docs/clean_tla_to_verus_translator_plan.md`](../../../docs/clean_tla_to_verus_translator_plan.md).
Work queue: `TODO.md` Phase 53 (dataset) and Phase 52 (translator).

## Layout

```
transpiler/tests/corpus/
  README.md              # this file — the four-tuple convention
  manifest.toml          # the registry: every case, its tier, status, and source
  scripts/
    intake_case.sh       # download a spec from the wild + scaffold a case dir
  tier0/<case_id>/       # micro / classical concurrency
  tier1/<case_id>/       # medium consensus (Paxos, TwoPhase)
  tier2/<case_id>/       # complex but already message-passing (Raft, EPaxos)
  tier3/<case_id>/       # hard (Jetpack)
```

## The four-tuple (per case)

Every case directory holds the same four files. This is the contract; a case that is missing
one of them is not `green`.

| File | What it is | Who writes it |
|---|---|---|
| `original.tla` | The spec as found in the wild, byte-for-byte. Never edited. | `intake_case.sh` (download) |
| `clean.tla` | `original.tla` hand-rewritten into the clean subset (C1–C5). | human, per the rewrite playbook (53.6) |
| `rewrite.md` | What changed and why: history vars removed, which instantaneous cross-node reads were message-ified into which messages, which variable is the network, what was dropped as out-of-subset. | human |
| `golden.rs` | The **expected translator output** — the single-process Verus spec the translator must emit for `clean.tla`. | see "Golden strategy" |

Auxiliary files a case may also carry:

| File | Purpose |
|---|---|
| `original.cfg` / `clean.cfg` | TLC configs for the V2 semantic-fidelity comparison (`clean.tla` vs `original.tla`). |
| `reference.rs` | An *existing hand-written* tla-rs spec for the same protocol (e.g. `src/protocol/Paxos/paxos.rs`). Used for human review and semantic comparison — **not** for byte-diff. |
| `*.tla` (extra) | Auxiliary TLA+ modules the spec `EXTENDS`/`INSTANCE`s. |

### Why `golden.rs` and `reference.rs` are different files

The plan says "reuse the hand-written tla-rs spec as the golden" for Tier-1/2. In practice a
deterministic translator will not emit a byte-identical copy of a hand-written spec (field
order, comments, helper factoring, naming). Byte-diffing against the hand-written spec would
therefore produce a permanently red test, which is worse than no test.

So the corpus splits the role:

- **`golden.rs` — regression oracle (V3).** Byte-compared against translator output by the
  regression test. Frozen after a human reviewed it once.
- **`reference.rs` — review oracle.** The hand-written spec, copied in for side-by-side human
  comparison during bootstrapping. Never byte-compared.

The hand-written spec still does the work the plan intended: it is what a human diffs
`golden.rs` against *before freezing it*. That review is recorded in `rewrite.md`.

## Golden strategy per tier

| Tier | Cases | How the golden is produced | `golden_kind` |
|---|---|---|---|
| 0 | Peterson, Bakery, DiningPhilosophers, BlockingQueue, ReadersWriters | hand-written (small, cheap) | `handwritten` |
| 1 | Paxos (message-passing), TwoPhase | bootstrapped, reviewed against `reference.rs` (the existing tla-rs spec) | `bootstrapped_reviewed` |
| 2 | Raft (ongardie), EPaxos | bootstrapped; TLC strong fidelity backstops correctness | `bootstrapped` |
| 3 | Jetpack | bootstrapped; reviewed against the **partial** Phase 51 hand-written spec (`src/protocol/Jetpack/jetpack.rs`) | `bootstrapped_partial_ref` |

⚠️ Jetpack has **no complete independent golden** — Phase 51 was paused after 7 of ~9 actions
(entry actions 51.9 missing) and the module was never mounted, so it has never been checked by
`verus`. Its translation is validated by TLC fidelity + `verus` pass + review against the
partial spec. Do not present it as a golden-verified case.

## Status vocabulary (`manifest.toml`)

| Status | Meaning |
|---|---|
| `planned` | Listed in the manifest; nothing downloaded yet. |
| `intake` | `original.tla` downloaded and pinned; not yet rewritten. |
| `clean` | `clean.tla` + `rewrite.md` exist and the Phase 52 linter accepts `clean.tla`. |
| `golden` | `golden.rs` exists and has been human-reviewed/frozen. |
| `green` | Translator output byte-matches `golden.rs` (V3) **and** the output passes `verus` (V1) **and** TLC fidelity `clean.tla` ≡ `original.tla` holds (V2). |

A `golden.rs` must itself pass `verus` before it is frozen. A golden that does
not verify would make V1 unreachable no matter what the translator emits.
| `blocked` | Case cannot progress; `notes` must say why. Never delete a case — mark it blocked. |

A case only counts toward a Phase 52 milestone when it is `green`.

## Roles (`role` in `manifest.toml`)

Not every case is on the road to `green`. `role` says what a case is *for*, and
omitting it means the default, `translate`.

| Role | Meaning |
|---|---|
| `translate` (default) | The case is meant to be rewritten, translated, and driven to `green`. |
| `reject-only` | The case exists so the **linter** has something it must reject, with a pinned clean-distance. It is never rewritten, so it never has a `clean.tla`, a `golden.rs`, or a V2 comparison, and its `status` stays at `intake` by design. |

A `reject-only` case is not an unfinished `translate` case. Its `notes` must say
why rewriting it would not produce a rewrite *of that algorithm* — see
`t0_02_bakery` and `t0_04_readers_writers`, where a message-passing version is a
**different algorithm that solves the same problem**, so there would be nothing
for V2 to compare and, for Bakery, the honest counterpart is literally
`t0_05_lamport_mutex`.

## Parse status

`parse_status` in the manifest records whether the tla-rs TLA+ frontend can read
the case's specs. Omitted means "parses" — the normal state. A case that cannot
be parsed is marked `parse_status = "unparseable"` with the reason in `notes`.

`tests/corpus_parse_guard.rs` asserts the manifest and reality agree **in both
directions**: a spec that stops parsing fails the test, and so does a spec that
is still marked unparseable after the frontend learned to read it. Without the
second direction the corpus would quietly accumulate stale "broken" marks.

## Clean-distance

`clean_distance` in the manifest records how far `original.tla` is from the clean subset,
measured by the Phase 52 linter (`52.M0`) as the number of C1–C5 violations:

- `unmeasured` — the linter did not exist yet when the case was taken in.
- an integer — violation count on `original.tla`. Higher = more human rewrite work.

`intake_case.sh` fills this in automatically (the linter landed in Phase 52.M0).

`expected_rules` records which rules the linter reports for the case. Together
with `clean_distance` it is pinned by `tests/corpus_lint_guard.rs`, which asserts
the **exact** count rather than "at least one": a linter that reports more than a
spec actually violates is as broken as one that reports fewer, and the count is
what publishes rewrite effort.

Measured tier-0 distances (2026-08-04):

| Case | Distance | Rules | What the human has to decide |
|---|---:|---|---|
| `t0_01_simple` | 1 | C2 | which message carries the neighbour's `x` |
| `t0_02_bakery` | 3 | C2 | how the doorway reads of `num`/`flag` become messages |
| `t0_03_dining_philosophers` | 6 | C2 | how fork state is exchanged between neighbours |
| `t0_04_readers_writers` | 1 | C5 | it has no per-node state at all — re-model per node first |
| `t0_05_lamport_mutex` | 2 | C1, C4 | `crit` → per-node boolean; flatten the 2-D queue network |

## Adding a case

```bash
transpiler/tests/corpus/scripts/intake_case.sh \
  --tier 0 --id t0_06_coffeecan \
  --url https://raw.githubusercontent.com/tlaplus/Examples/master/specifications/CoffeeCan/CoffeeCan.tla \
  --append-manifest
```

Then: rewrite `clean.tla`, fill `rewrite.md`, produce `golden.rs`, and move the manifest
`status` forward. Every status bump should be a commit.

## Rules

- **Never edit `original.tla`.** It is the fidelity baseline for V2. Pin the upstream commit in
  the manifest so the download is reproducible.
- **Never delete an inconvenient case.** Mark it `blocked` with a reason (mirrors the Phase 38
  corpus discipline that caught the vacuous-pass failure).
- **A green case needs all three of V1/V2/V3.** A translator that emits something that matches
  `golden.rs` but does not verify is not green.
- **Excluded upstream dirs:** `fastpaxos`, `naiad`, `losa_rda` — PDF-only, no machine-readable
  `.tla`.

# Phase 54 — measuring and diffing Verus trigger choices

Status: 54.1 (tooling), 54.2.a (CI trigger capture), 54.2.c (per-module timing)
and 54.9 (CI guard mechanism) complete. The measured baseline — and therefore
the number the guard enforces — lands with 54.2.b, once a `verify` run has
published the artifact; see §5, §6 and §9.

## 1. Why the tool exists before the edits

Verus picks quantifier triggers automatically when we do not write
`#[trigger]`. A full pass over this crate emits 534 such notes, all in our own
code. The choice is an implementation detail of the release: it can change
between versions, and when it does, the proof that verified yesterday fails
today as `rlimit exceeded` — an error that says nothing about the cause. We
have already paid that bill once, in
`lemma_getsent2b_value_matches_candidate` (five months, nine failed structural
fixes, root cause quantifier-instantiation blowup).

Adding `#[trigger]` is not a mechanical edit. Too restrictive and the needed
instantiation never fires; too permissive and the solver explodes; and an
annotation that verifies today may still have doubled the module's solving
time, which is a regression that no pass/fail check catches. So the first
deliverable of Phase 54 is not an annotation — it is the instrument:

* **the inventory** — what Verus chose, per expression, per release;
* **the diff** — what changed between two runs, split into progress,
  regression, and the silent case.

Without it, "534 → 0" is a number nobody can reproduce and a trigger-induced
slowdown is invisible.

## 2. What the diff actually distinguishes

A raw note count hides the failure mode this phase is about. The diff splits
changes three ways:

| category | meaning |
|---|---|
| **removed** | a note that is gone — an explicit trigger replaced it. Progress. |
| **added** | a new note — a regression, usually a new quantifier that nobody annotated. |
| **changed** | the *same expression* is still auto-triggered, but Verus now chooses **different terms**. |

The third category is the point. It moves no counter: the note total is
identical, the file list is identical, and yet the solver is now instantiating
different terms than it did last release. That is exactly the instability the
Verus team flagged when they raised this against tla-rs as a compatibility test
target, and it is invisible to any check that only counts notes.

Entries are keyed on `(file, normalised expression text, ordinal)` rather than
on line numbers, so editing anything above a quantifier does not present as a
removal plus an addition. Identical expressions repeated in one file are
disambiguated by their order of appearance.

## 3. User manual

### Record an inventory

```bash
scripts/collect_trigger_inventory.sh \
    --verus-path /path/to/verus \
    --triggers-mode all-modules \
    --label "0.2026.08.02 full"
```

Writes `reports/triggers/<version>-<mode>.json` (the artifact of record) and a
`.md` summary. The raw log is deleted unless `--keep-log` is passed. Verus
exiting non-zero does not abort the capture: notes are emitted for the modules
that were processed, and the exit status is reported.

`--triggers-mode selective` is the Verus default and reports only ambiguous
choices; `all-modules` reports every automatic choice. **Counts from different
modes are not comparable** — the mode is baked into the file name and label so
a diff cannot silently mix them.

### Parse a log you already have

```bash
scripts/trigger_inventory.py parse run.log \
    --label "0.2026.08.02 full" --root . -o reports/triggers/base.json
scripts/trigger_inventory.py report reports/triggers/base.json -o reports/triggers/base.md
```

`parse` exits 1 if the log contains no trigger notes at all — the common cause
is that Verus prints them only for verified modules, so a run that errored out
early yields an empty inventory that would otherwise look like success. Pass
`--allow-empty` when the emptiness is genuine.

### Compare two runs

```bash
# after a batch of #[trigger] edits
scripts/trigger_inventory.py diff reports/triggers/base.json new.json

# in CI (54.9): fail on new notes or changed choices
scripts/trigger_inventory.py diff base.json new.json --fail-on-regression

# or hold a ceiling
scripts/trigger_inventory.py diff base.json new.json --max-notes 534
```

`--fail-on-regression` exits 1 when notes were **added** or trigger choices
**changed**; removals never fail. `--json` emits the delta as JSON for further
processing.

## 4. Log format the parser depends on

```
note: automatically chose triggers for this expression:
  --> src/protocol/RSL/replica.rs:412:9
   |
412 |     forall|i: int| 0 <= i < n ==> f(i) == g(i)
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

note:   trigger 1 of 2:
  --> src/protocol/RSL/replica.rs:412:35
   |
412 |     forall|i: int| 0 <= i < n ==> f(i) == g(i)
   |                                   ^^^^
```

Trigger terms are recovered by aligning the caret run with the quoted source
line, so a single trigger made of several terms (`^^^^   ^^^^`) is kept as a
list rather than flattened. Multi-line spans (rustc's `/ … |____^` form) are
joined and flagged `multiline`; their trigger notes are still parsed exactly.

Two real Verus logs are checked in at
`scripts/fixtures/trigger_inventory/` and asserted against by
`scripts/test_trigger_inventory.py` (55 tests). If a future Verus release
changes the diagnostic shape, those tests fail loudly instead of the inventory
quietly going empty.

## 5. How the baseline is actually captured (CI)

The pinned verifier does not run on every development box (§9), but it already
runs in CI on `ubuntu-24.04`. So the `verify` job captures the inventory as a
side effect of the verification it was already doing:

```yaml
- name: Verify with Verus
  run: |
    set -o pipefail
    scons --verus-path=$HOME/verus/verus --skip-dotnet \
      --verus-extra-args="--time-expanded" 2>&1 | tee verus-verify.log

- name: Capture trigger inventory
  if: always()
  run: |
    python3 scripts/trigger_inventory.py parse verus-verify.log ... --allow-empty
```

Three properties this is designed to have:

* **It cannot change the verdict.** The capture asserts nothing and passes
  `--allow-empty`; `set -o pipefail` is there so that `tee` cannot swallow a
  real verification failure.
* **It runs on failure too.** `if: always()` — Verus still emits notes for the
  modules it processed, and a failing run's inventory is still evidence.
* **It cannot be silently dropped.** `TestCiWiring` in
  `scripts/test_trigger_inventory.py` asserts the wiring exists. A capture step
  that quietly disappeared would produce exactly the same signal as "we removed
  all the triggers".

The artifact is `trigger-inventory-<version>`, containing the trigger
inventory, the timing inventory (§6) and both Markdown summaries; the summaries
are also written to the GitHub step summary so they are readable without
downloading anything.

The capture parses the whole `scons` log, not a bare verus invocation, so the
parser has to find the notes among the build chatter — `scons_wrapped_notes.log`
in the fixtures pins that case, including rewriting the runner's absolute paths
back to repo-relative ones via `--root`.

## 6. The other half of the baseline: per-module wall-clock

A batch of `#[trigger]` edits can verify and still be a regression. An
over-permissive trigger makes the solver instantiate more terms, so the module
that verified in 8 s now takes 20 s — green, and twice as expensive, and one
more edit away from `rlimit exceeded`. The phase's acceptance criterion is
therefore stated in wall-clock terms:

> no module's verification wall-clock regresses more than 20% against the
> 54.2 baseline

`scripts/verus_timing.py` makes that checkable. Verus prints the breakdown with
`--time-expanded`:

```
verify-crate-time-breakdown
    total verify-time:            157 ms   (3 threads)
      1. alpha                                            54 ms
      2.                                                  53 ms
      3. beta                                             48 ms
```

The unnamed row is the crate root, recorded as `<root>` so it cannot be
confused with a missing module. Per module the tool keeps verify, air, smt-init
and smt-run times plus the rlimit count.

```bash
scripts/verus_timing.py parse verus-verify.log --label "0.2026.08.02 baseline" \
    -o reports/triggers/timing-baseline.json
scripts/verus_timing.py report reports/triggers/timing-baseline.json
scripts/verus_timing.py diff timing-baseline.json new.json \
    --max-regression-pct 20 --fail-on-regression
```

Two things the diff does deliberately:

* **Noise floor.** `--min-ms` (default 500) keeps a 40 ms → 80 ms module from
  being called a 100% regression. Those rows are still printed, under
  *"below the noise floor"*, so the judgement is visible rather than silent.
* **Improvements are separate.** A module that got 50% faster is reported, never
  failed on — but it is worth reading, since a large speedup can mean a trigger
  became too restrictive and the proof now succeeds for a different reason.

Getting the flag to Verus needed one build-system change: `SConstruct` hard-coded
the verifier command line, so it now accepts
`--verus-extra-args`, which CI uses as
`scons ... --verus-extra-args="--time-expanded"`. The flag changes no verifier
behaviour, only what is printed.

## 7. The guard (54.9)

Progress has to be defended, or the auto-chosen triggers simply regrow. The
`Guard trigger inventory` CI step does that:

```bash
scripts/trigger_inventory.py guard trigger-inventory.json \
    --ceiling reports/triggers/ceiling.json \
    --capture-mode selective \
    [--baseline reports/triggers/baseline.json]
```

| exit | meaning |
|---:|---|
| 0 | at or under the ceiling (or the ceiling is not set yet) |
| 1 | over the ceiling, or notes were added / trigger choices changed |
| 2 | the comparison itself is invalid — the inventory and the ceiling come from different `--triggers-mode` settings |

Deliberate choices:

* **The ceiling is data, not YAML.** `reports/triggers/ceiling.json` carries
  `max_notes`, the mode it was agreed in, and a `rationale`. Raising it is a
  reviewable diff that has to say why — not a quiet edit to a workflow file.
* **It ships unset.** `enforce: false, max_notes: null`. The guard prints the
  measured count and passes. Asserting a number nobody has measured on the
  pinned release would be vacuous at best and would turn CI red for the wrong
  reason at worst; 54.2.b sets it from the real artifact.
* **Changed choices fail too**, once a baseline exists. A count-only ceiling
  cannot see the case where Verus keeps the same number of notes and picks
  different terms — the exact instability this phase was raised about.
* **An empty capture is never judged.** If verification died early, Verus
  printed no notes; "0 notes" is missing data, not success.
* **`set -o pipefail` in the step.** The guards pipe into `tee` for the job
  summary, and without it a failing guard would exit 0 and silently stop
  guarding — the failure mode most likely to go unnoticed for months.

The timing half of the gate reuses `verus_timing.py diff
--max-regression-pct 20 --fail-on-regression` and is skipped with an explicit
message until `reports/triggers/timing-baseline.json` is committed.

## 8. The work-list: which sites Phase 54 has to touch

`scripts/trigger_inventory.py` answers "what is Verus guessing at?" but needs a
verification log. `scripts/trigger_sites.py` answers "where are the quantifiers?"
from the source alone, so the annotation batches (54.3 onwards) can be planned
and split per file without waiting for CI:

```bash
scripts/trigger_sites.py src                       # Markdown, checked in as reports/triggers/sites.md
scripts/trigger_sites.py src --json -o sites.json  # machine-readable
```

Each `forall|`/`exists|` is classified:

| class | meaning |
|---|---|
| `annotated` | a `#[trigger]` / `#![trigger(...)]` governs it |
| `auto` | `#![auto]` — automatic selection was asked for deliberately |
| `ambiguous` | an annotation is in scope but only after a nested quantifier, so it may belong to the inner one |
| `unannotated` | nothing in scope |

**These are not note counts.** Verus's default `selective` mode reports only the
choices it finds ambiguous, so an unannotated quantifier need not produce a
note. Read the site count as the upper bound on the work and the inventory as
what is actually being guessed at. The `ambiguous` bucket exists because the
scanner is a heuristic, not a Rust parser: rather than credit a site with an
annotation that may belong to a nested quantifier, it says so and leaves it for
a human. It sits at ~2.5% of sites, and a test fails if it grows past 10% —
that would mean the scope heuristic needs revisiting, not quiet acceptance.

One bug this caught during development, worth recording because it is the kind
that produces confident wrong numbers: a comma between binders
(`forall |x1: X, x2: X|`) ended the scope scan, so a `#![trigger ...]` written
after a multi-binder list was invisible and the site was reported as
unannotated. The aggregate totals looked entirely plausible either way.

## 9. Known constraint: the pinned verifier does not run everywhere

The baseline must come from the pinned verifier,
`release/0.2026.08.02.b677dd5`. That binary requires **glibc ≥ 2.39**; the
development box this was written on has 2.35, so it aborts before running:

```
verus: /lib/x86_64-linux-gnu/libc.so.6: version `GLIBC_2.39' not found
```

`docker` is installed there but the daemon refuses the user
(`permission denied while trying to connect to ... docker.sock`), and `bwrap`
alone would need a full newer-glibc rootfs to be useful.

Older releases in the local cache do run, and were used to capture the parser
fixtures — but they cannot stand in for the pinned one. Measured 2026-08-04:
`0.2026.01.02.6f52890` with `--no-verify` over `src/lib.rs` aborts with **72
errors** (`IMap` undeclared, `lemma_set_disjoint_iff_empty_intersection`
renamed, and so on) because the tree targets 0.2026.08 vstd. It cannot compile
the crate, let alone verify it. So trigger edits (54.3 onwards) cannot be
validated on such a box at all, and committing unverified proof edits is not an
option — the whole point of the phase is that adding `#[trigger]` changes
solver behaviour in ways only verification can reveal.

Hence §5: CI is the capture host. On a machine that does have a new enough
glibc, the same inventory can be produced locally in one command:

```bash
scripts/collect_trigger_inventory.sh --verus-path <verus> --triggers-mode all-modules
```

Do not substitute an older release's inventory for the baseline. A diff across
two different Verus versions is precisely the measurement Phase 54 wants to
make *deliberately*, and mislabelling one as "the baseline" would poison every
later comparison.

## 10. Where this fits

* Plan: `TODO.md` Phase 54; this covers **54.1**, **54.2.a**, **54.2.c** and
  the **54.9** mechanism. What remains is **54.2.b** — commit the published
  artifacts as the baseline and set `max_notes` / `enforce` in the ceiling —
  after which 54.3 onwards can start editing triggers with a measurement to
  answer to.
* Artifacts: `reports/triggers/` (see the README there).

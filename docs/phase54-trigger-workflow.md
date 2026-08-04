# Phase 54 — measuring and diffing Verus trigger choices

Status: 54.1 (tooling) complete. 54.2 (baseline) blocked on toolchain, see §5.

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
`scripts/test_trigger_inventory.py` (27 tests). If a future Verus release
changes the diagnostic shape, those tests fail loudly instead of the inventory
quietly going empty.

## 5. Known constraint: capturing the 54.2 baseline

The baseline must come from the pinned verifier,
`release/0.2026.08.02.b677dd5`. That binary requires **glibc ≥ 2.39**; this
development box has 2.35, so it aborts before running:

```
verus: /lib/x86_64-linux-gnu/libc.so.6: version `GLIBC_2.39' not found
```

Older releases in the local cache (e.g. `0.2026.01.02.6f52890`) do run here and
were used to capture the fixtures, but their trigger choices are not the
baseline we need: the whole point is to pin what *the pinned release* decides.
So 54.2 needs either a host with a newer glibc or a container image, and the
tooling is ready for it — one command, no further code.

Do not substitute an older release's inventory for the baseline. A diff across
two different Verus versions is precisely the measurement Phase 54 wants to
make *deliberately*, and mislabelling one as "the baseline" would poison every
later comparison.

## 6. Where this fits

* Plan: `TODO.md` Phase 54; this covers **54.1**, and unblocks **54.2**
  (baseline) and **54.9** (CI guard, which is `diff --fail-on-regression` or
  `--max-notes` wired into `.github/workflows/ci.yml`).
* Artifacts: `reports/triggers/` (see the README there).

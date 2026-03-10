# Model Checker Architecture Tutorial

## Audience
This tutorial targets readers with zero prior model-checking background.

## Scope
This folder explains:
- traditional TLA+ model checking, where "traditional" means the TLC path in this phase unless another engine is explicitly labeled as side context;
- the current tla-rs source-first checker in this repository; and
- an evidence-based comparison between them.

This phase is documentation-only.

## Reading Order
1. `glossary.md`
2. `traditional-tla-model-checking.md`
3. `tlars-source-first-model-checking.md`
4. `walkthrough.md`
5. `comparison.md`
6. `tlars-only-optimizations.md`
7. `sources-and-evidence.md`

## What You Will Understand After Reading
- Core explicit-state model-checking concepts in beginner terms.
- How TLC-style checking works from model/config to counterexample output.
- How tla-rs source-first checking is currently implemented in this repository.
- Which differences are architectural, semantic, or reporting-oriented.
- Which tla-rs optimization claims are confirmed vs uncertain.

## Deliverables In This Folder
- Tutorial chapters for traditional TLC and tla-rs source-first flows.
- A dual-track worked example.
- A side-by-side comparison and crosswalk artifact.
- A disciplined source/evidence log.

## Anti-Corner-Cutting Structure (Phase 35.8.1)
This deliverable is intentionally split across multiple files; it must not be collapsed into one shallow markdown summary.

Required separation of concerns:
- `traditional-tla-model-checking.md`: beginner-oriented TLC/traditional path tutorial.
- `tlars-source-first-model-checking.md`: beginner-oriented current tla-rs source-first path tutorial.
- `walkthrough.md`: one shared worked example traced through both paths.
- `comparison.md`: explicit side-by-side same/similar/different analysis and consequences.
- `tlars-only-optimizations.md`: optimization/reduction audit with confirmed vs uncertain classification.
- `sources-and-evidence.md`: source ledger and confidence policy for substantive claims.
- `artifacts/engine-crosswalk.csv`: machine-checkable row schema for the comparison matrix.

## Source Inputs vs Finished Tutorial (Phase 35.8.2)
`docs/model_checker_status.md` and `docs/model-checking-source-first.md` are source inputs, not the finished tutorial deliverable for this phase.
This folder must not merely paraphrase those inputs.

What this folder adds beyond source-input restatement:
- beginner-first structure and terminology path (`glossary` + ordered chapters),
- a dual-track worked example (`walkthrough.md`),
- an explicit side-by-side comparison with consequence analysis (`comparison.md`),
- a disciplined optimization audit with confidence labels (`tlars-only-optimizations.md`),
- and an explicit source/claim-evidence ledger (`sources-and-evidence.md`).

## Jargon First-Use + Readability Rule (Phase 35.8.3)
Every chapter in this folder must define jargon on first use and stay readable for a newcomer.

Required writing discipline:
- Expand acronyms the first time they appear in each chapter (for example, "intermediate representation (IR)").
- Add a short plain-language gloss the first time a technical term appears in a section; do not assume prior model-checking knowledge.
- Keep `glossary.md` as the canonical fallback for terms that need a longer definition, and point readers to it early.

Readability guardrails:
- Prefer short sentences and one main idea per bullet.
- Use concrete "input -> processing -> output" wording before introducing implementation details.
- Avoid unexplained shorthand such as `IR`, `POR`, `SCC`, `AST`, `BFS`, or `DFS`.

## Minimum Artifact Counts (Phase 35.8.4)
This deliverable must include at least:
- `2` architecture diagrams,
- `1` worked example,
- `1` side-by-side comparison table,
- `1` optimization audit table.

Current artifact mapping for this phase:
- architecture diagram A: `traditional-tla-model-checking.md` (`Traditional TLC Pipeline Diagram` mermaid block),
- architecture diagram B: `tlars-source-first-model-checking.md` (`Current tla-rs Source-First Architecture Diagram` mermaid block),
- worked example: `walkthrough.md` (`Step-by-Step State Transition` with pre-state/transition/post-state),
- side-by-side comparison table: `comparison.md` (`Side-by-Side Matrix`),
- optimization audit table: `tlars-only-optimizations.md` (optimization/reduction audit tables).

## Category Separation Rule (Phase 35.8.5)
Do not blur `optimization`, `feature`, `limitation`, and `reporting surface` into one category.

Category definitions:
- `optimization`: a mechanism that primarily reduces exploration/runtime/memory cost.
- `feature`: a capability difference that changes what workflows or checks are available.
- `limitation`: a known blocker or unsupported surface where behavior is currently constrained.
- `reporting surface`: how results/evidence are exposed (logs, JSON fields, telemetry labels), which is not itself a runtime optimization.

Per-file ownership in this tutorial set:
- optimization audit claims belong in `tlars-only-optimizations.md`,
- feature differences and consequence analysis belong in `comparison.md`,
- limitation/blocker tracking belongs in `tlars-source-first-model-checking.md` (`Main Known Limits`) and `docs/model_checker_status.md`,
- reporting-surface differences belong in `walkthrough.md` and `comparison.md` output/reporting sections.

Guardrail:
- If one statement mixes more than one category, split it into separate statements with separate evidence anchors.

## Comparison Baseline Rule (Phase 35.8.6)
Do not compare tla-rs to an idealized notion of "TLA+".

Comparison baseline for this phase:
- compare against the reviewed traditional model-checking path inspected in this tutorial, primarily the TLC path (`TLA+` module + model/config + `SANY`/`TLC` execution flow);
- keep language-level TLA+ semantics separate from checker-implementation claims.

When other tools are mentioned:
- label them explicitly as side context, not as the main comparison baseline;
- do not merge side-context tool claims into the TLC-baseline rows in `comparison.md`.

## Citation or Inference Rule (Phase 35.8.7)
Every substantive non-local claim in this folder needs either a source citation or an explicit `[Inference]` label.

Allowed evidence forms:
- local citation via concrete anchor path/function (for example `Anchor: transpiler/src/main.rs`),
- source-ID citation from `sources-and-evidence.md` (for example `T*`, `R*`, `C*`),
- explicit `[Inference]` wording plus the source IDs it is inferred from.

Guardrail:
- Do not leave substantive non-local claims unlabeled; if a claim is not directly evidenced, mark it as `[Inference]` instead of writing it as a fact.

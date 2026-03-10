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

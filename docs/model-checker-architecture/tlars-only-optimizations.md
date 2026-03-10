# tla-rs-Only Optimizations and Reductions Audit

## Scope and Evidence Standard
This document audits optimization/reduction claims for the current tla-rs source-first checker
against the reviewed traditional TLC path.

Classification rules:
- `optimization/reduction`: a mechanism that primarily targets search/runtime/memory cost.
- `feature/reporting difference`: capability/UX/observability difference that is not itself a cost-reduction mechanism.
- `confirmed tla-rs-only`: requires direct local tla-rs evidence plus reviewed TLC evidence for the comparison scope.
- `possibly different but not yet confirmed`: evidence is incomplete, so claims stay explicitly uncertain.

## Confirmed tla-rs-only in reviewed comparison
Only fully confirmed items belong in this section.
As of 2026-03-10, no item is fully confirmed yet under the current evidence bar.
Per-item required fields for this section are fixed by Phase 35.7.2.

| Optimization / Reduction Name | Cost Reduced | Preserves Exactness? | tla-rs Code/Doc Anchor | TLC "not found / not used" Evidence | Confidence Level | Short Effect Example (artifact-backed when available) |
| --- | --- | --- | --- | --- | --- | --- |
| none confirmed yet (2026-03-10) | - | - | - | - | `uncertain / not confirmed` | No confirmed item to illustrate yet; keep field for future artifact-backed examples. |

## Possibly different but not yet confirmed
Use this section when there is a plausible difference but the TLC-side comparison is not fully confirmed.

| Candidate | Audit Decision (35.7.3) | Current Classification | tla-rs Evidence Anchor | Reviewed TLC Evidence | Why This Decision / Remaining Gap | Current Confidence |
| --- | --- | --- | --- | --- | --- | --- |
| Run-scoped successor memoization used during liveness graph indexing | Reject for confirmed-now; include in this uncertain bucket | plausible optimization difference; not confirmed tla-rs-only | `transpiler/src/main.rs` (`successor_cache` in `execute_model_check`), `docs/model_checker_status.md` (3.15 + telemetry keys) | `docs/model-checker-architecture/sources-and-evidence.md` IDs `T3`, `T4`, `T5` | Local mechanism is clear and artifact-backed, but reviewed TLC-side evidence has not yet established mechanism-level equivalence or absence for this exact cache pattern. | `uncertain / not confirmed` |
| Direct helper-branch solving vs enumeration fallback split | Reject for confirmed-now; include in this uncertain bucket | plausible optimization difference; not confirmed tla-rs-only | `transpiler/src/modelcheck/solver.rs` (`solve_branch_successors_with_candidates_and_telemetry`), `docs/model_checker_status.md` (3.13/3.14) | `docs/model-checker-architecture/sources-and-evidence.md` IDs `T3`, `T4`, `T5` | Source-first direct-solver/fallback split is explicit and tested, but TLC-side implementation mapping for this exact split is not yet pinned to a reviewed anchor. | `uncertain / not confirmed` |
| Static-guard pruning before candidate enumeration | Reject for confirmed-now; include in this uncertain bucket | plausible optimization difference; not confirmed tla-rs-only | `transpiler/src/modelcheck/solver.rs` (`guard_pruned_candidate_evaluations`), `docs/model_checker_status.md` (3.14 telemetry guard test) | `docs/model-checker-architecture/sources-and-evidence.md` IDs `T3`, `T4`, `T5` | We can show local pruning and telemetry, but we have not yet established whether reviewed TLC internals do or do not apply an equivalent pruning stage in comparable paths. | `uncertain / not confirmed` |
| `por_heuristic = "invisible_branch"` | Reject for confirmed-now; include in this uncertain bucket | plausible optimization difference; not confirmed tla-rs-only | `transpiler/src/modelcheck/por.rs` (`infer_invisible_branch_pruning`), `docs/model-checking-source-first.md` (POR option + safety caveat) | `docs/model-checker-architecture/sources-and-evidence.md` IDs `T3`, `T4`, `T5` | The local heuristic is explicit and conservative, but this audit has not yet produced reviewed TLC-source evidence strong enough to claim unique absence/presence at mechanism level. | `uncertain / not confirmed` |
| `symmetry_fields` normalization | Reject for confirmed-now; include in this uncertain bucket | plausible optimization difference; not confirmed tla-rs-only | `transpiler/src/modelcheck/explorer.rs` (`canonical_dedup_key` with symmetry-field normalization), `transpiler/src/modelcheck/config.rs` (`symmetry_fields`) | `docs/model-checker-architecture/sources-and-evidence.md` IDs `T3`, `T4`, `T5` | Local normalization is clear, but cross-engine comparison depth is still insufficient to classify this mechanism as definitely unique or definitely shared. | `uncertain / not confirmed` |
| `hash_compaction64` exactness/lossiness labeling | Reject from optimization-confirmed set; split classification | split: optimization candidate (`hash_compaction64` dedup) + reporting-surface difference (exactness/lossiness labeling) | `transpiler/src/modelcheck/config.rs` (`StateDedupMode::HashCompaction64`), `transpiler/src/main.rs` (`classify_search_evidence_mode`) | `docs/model-checker-architecture/sources-and-evidence.md` IDs `T3`, `T4`, `T5` | The dedup mode is a reduction candidate, but the labeling surface itself is reporting UX and belongs in the non-optimization table until cross-engine equivalence claims are directly evidenced. | `uncertain / not confirmed` |

## Not an optimization; only a feature/reporting difference
Use this section for differences that are not cost-reduction mechanisms.

| Difference | Why It Is Not an Optimization | Anchor |
| --- | --- | --- |
| Exactness/lossiness evidence-mode labeling (including `hash_compaction64` run labeling) | Labels explain result trust level; they do not themselves reduce search/runtime/memory cost. | `transpiler/src/main.rs` (`classify_search_evidence_mode`), `docs/model-checker-architecture/comparison.md`, `docs/model-checking-source-first.md` |

## Candidate audit closure (Phase 35.7.3)
All six required candidate items were explicitly audited in the table above.
None is promoted to "confirmed tla-rs-only" yet; each remains confidence-labeled until mechanism-level TLC-side evidence is stronger.

## Anti-force classification rule (Phase 35.7.4)
This audit does not force every candidate into `confirmed tla-rs-only`.
Current result after candidate-by-candidate review:
- `0/6` candidates are in the confirmed section.
- `5/6` remain plausible optimization differences but not yet confirmed.
- `1/6` (`hash_compaction64` exactness/lossiness labeling) is explicitly split so the labeling surface is treated as reporting/UX rather than an optimization claim.

## Plain zero-confirmed outcome (Phase 35.7.5)
Current comparison outcome: **zero fully confirmed tla-rs-only optimizations**.
This report keeps that result explicit instead of stretching uncertain evidence into confirmed claims.

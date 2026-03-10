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

| Status | Optimization / Reduction | Cost Reduced | Exactness Impact | tla-rs Anchor | TLC Comparison Evidence | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| none yet | - | - | - | - | - | Keep empty until an item is directly evidenced as confirmed tla-rs-only. |

## Possibly different but not yet confirmed
Use this section when there is a plausible difference but the TLC-side comparison is not fully confirmed.

| Candidate | Why Not Yet Confirmed | Evidence Needed To Promote | Current Confidence |
| --- | --- | --- | --- |
| pending audit | Cross-engine evidence is still being collected. | Direct reviewed TLC source/docs evidence for the exact mechanism and behavior match/mismatch. | `uncertain / not confirmed` |

## Not an optimization; only a feature/reporting difference
Use this section for differences that are not cost-reduction mechanisms.

| Difference | Why It Is Not an Optimization | Anchor |
| --- | --- | --- |
| pending classification | Reserve this section for UX/reporting/feature differences that should not be counted as optimizations. | `docs/model-checker-architecture/comparison.md` |

## Candidate items to audit
- Run-scoped successor memoization.
- Direct solving vs enumeration fallback split.
- Static guard pruning before enumeration.
- Invisible-branch POR heuristic.
- Symmetry-field normalization.
- Hash compaction exactness labeling.

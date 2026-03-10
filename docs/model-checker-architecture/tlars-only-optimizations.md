# tla-rs-Only Optimizations and Reductions Audit

## Scope and Evidence Standard
This document audits optimization claims and separates confirmed, uncertain, and non-optimization differences.

## Confirmed tla-rs-Only (In Reviewed Comparison)
Rows will include mechanism, reduced cost, exactness impact, and evidence anchors.

## Possibly Different but Not Yet Confirmed
Rows will include why evidence is incomplete and what remains to inspect.

## Not an Optimization (Feature or Reporting Difference)
Rows will separate semantic/perf mechanisms from UX/reporting-only differences.

## Candidate Items to Audit
- Run-scoped successor memoization.
- Direct solving vs enumeration fallback split.
- Static guard pruning before enumeration.
- Invisible-branch POR heuristic.
- Symmetry-field normalization.
- Hash compaction exactness labeling.

# Phase 36.3.1: Source-First Performance Profile

Release-mode profiling of the source-first model checker on the shared
benchmark configs (`benchmarks_1h/*`). All runs on the same machine.

## Summary Table

| Protocol | States | Depth | Elapsed | Solver ms | Init ms | Dedup ms | Candidate/branch | Exist assigns/branch | Status |
|----------|--------|-------|---------|-----------|---------|----------|------------------|---------------------|--------|
| TwoPhase | 79 | 3 | 1.6s | 1,426 | 4 | 164 | N/A (direct) | N/A (direct) | Exhausted* |
| PrimaryBackup | 60 | 7 | 2.3s | 1,955 | 10 | 293 | N/A (direct) | N/A (direct) | Exhausted |
| LeaderElection | 105 | 3 | 60s | 59,900 | 112 | 59 | 13,824 | 2,460–7,380 | Timeout |
| Paxos | 5 | 1 | 93s | 44,214 | 22,196 | 13 | 1,679,616 | 3–27 | Timeout |

\* TwoPhase hits invariant violation at depth 3 (expected — no message channel)

## Detailed Findings

### TwoPhase (1.6s, 79 states — GOOD)

- All 8 branches use direct solver (0 enum fallback)
- 288 total direct solves across 36 invocations per branch
- Solver: 1.4s, dedup: 0.16s — reasonable
- No performance issue

### PrimaryBackup (2.3s, 60 states — GOOD)

- All 8 branches use direct solver
- 480 direct solves, 0 enum fallback
- Solver: 2.0s, dedup: 0.3s — reasonable
- No performance issue

### LeaderElection (60s timeout, 105 states — BOTTLENECK)

**Root cause: Existential assignment explosion**

- 7 branches, each invoked 14-15 times
- **2,460–7,380 existential assignments per branch invocation**
- **13,824 candidate states per branch** — full cartesian product
- Solver dominates: 59.9s of 60.3s total
- Each branch invocation: 300–1000ms

The existential variables in LeaderElection branches produce thousands
of assignment combinations (product of int/bool/set domains for all
existential vars). The direct solver iterates all of these, checking
13,824 candidate states for each.

**Optimization targets:**
1. Reduce existential assignment count by constraint-propagation
   (derive concrete values from equalities before enumerating)
2. Reduce candidate state count by eliminating impossible field
   combinations earlier
3. Cache and reuse solver results for shared assignment prefixes

### Paxos (93s timeout, 5 states — CRITICAL BOTTLENECK)

**Root cause: Candidate state explosion (1.7M per branch)**

- 4 branches, each invoked once
- **1,679,616 candidate states per branch** — catastrophic
- Only 3–27 existential assignments (reasonable)
- Initial state construction: 22s (building 1.7M candidates)
- Solver: 44s, candidate evaluation: 27s

The Paxos state type is a TLC function (Map<int, Record>) with 11
fields per record and 3 nodes. The candidate space is the full cartesian
product of all possible values for each field of each node.

**Optimization targets:**
1. **Critical**: Replace cartesian candidate construction with
   constraint-driven field assignment. Most next-state fields are
   directly constrained by equalities (e.g., `s_.field == s.field` for
   frame conditions). Only unconstrained fields need enumeration.
2. **High**: For map/function-typed state, only the modified entry
   needs enumeration; unchanged entries should be copied from pre-state.
3. **Medium**: Lazy candidate evaluation — don't materialize the full
   product, evaluate constraints as fields are assigned.

## Branch-Level Detail

### LeaderElection Branches

| Branch | Invocations | Exist assigns | Candidates | Successors | Solve ms |
|--------|-------------|--------------|------------|------------|----------|
| branch_0 | 15 | 2,460 | 13,824 | 0 | 4,724 |
| branch_1 | 15 | 2,460 | 13,824 | 42 | 4,611 |
| branch_2 | 15 | 7,380 | 13,824 | 28 | 14,550 |
| branch_3 | 14 | 7,380 | 13,824 | 5 | 14,184 |
| branch_4 | 14 | 2,460 | 13,824 | 5 | 4,315 |
| branch_5 | 14 | 7,380 | 13,824 | 69 | 12,888 |
| branch_6 | 14 | 2,460 | 13,824 | 39 | 4,628 |

### Paxos Branches

| Branch | Invocations | Exist assigns | Candidates | Successors | Solve ms |
|--------|-------------|--------------|------------|------------|----------|
| branch_0 | 1 | 3 | 1,679,616 | 2 | 11,036 |
| branch_1 | 1 | 3 | 1,679,616 | 3 | 11,145 |
| branch_2 | 1 | 27 | 1,679,616 | 0 | 11,159 |
| branch_3 | 1 | 3 | 1,679,616 | 0 | 10,874 |

## Comparison with TLC

| Protocol | SF states | SF time | TLC states | TLC time | SF/TLC speed ratio |
|----------|-----------|---------|------------|----------|--------------------|
| TwoPhase | 79* | 1.6s | 64 | 1s | 1.6x slower |
| PrimaryBackup | 60 | 2.3s | 54 | 1s | 2.3x slower |
| LeaderElection | 105/60s | timeout | 9,337 | 2s | >30x slower |
| Paxos | 5/93s | timeout | 3,005,604 | 375s | >1000x slower |

\* Different state counts due to message-channel modeling difference

## Recommendations

1. **Phase 36.3.3 (audit)**: Confirm the solver IS materializing full
   cartesian candidates before applying constraints (the 1.7M number
   for Paxos proves this)
2. **Phase 36.3.4 (optimization)**: Implement constraint-driven field
   assignment: for each branch, extract `s_.field == expr` equalities
   and compute those fields first, only enumerating truly unconstrained
   fields
3. **High impact for Paxos**: For function/map-typed state, copy
   unmodified entries from pre-state rather than enumerating all
   possible values

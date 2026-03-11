# TLC vs Source-first Benchmark Comparison

Generated: 2026-03-11 03:14:06 UTC
Git rev: d93c9ab

Source-first run: Generated: 2026-03-11 02:53:32 UTC
TLC run: Generated: 2026-03-08 16:25:00 UTC

## Source-first Build/Environment Parity (Phase 33.4.4.a)

- Canonical source-first performance view: **release build** (`reports/benchmarks/source_first_release`).
- Continuity baseline retained: **debug build** (`reports/benchmarks/source_first`).

- Release run context:
  - Build profile: release
  - Threading mode: single-thread (workers=1)
  - Timeout override (ms): 240000
  - Machine: Linux 6.17.4-2-pve x86_64 GNU/Linux
  - Host: zoo-005
- Debug run context:
  - Build profile: debug
  - Threading mode: single-thread (workers=1)
  - Timeout override (ms): 240000
  - Machine: Linux 6.17.4-2-pve x86_64 GNU/Linux
  - Host: zoo-005

| Protocol | Release result | Release wall (s) | Release stop reason | Debug result | Debug wall (s) | Debug stop reason | Debug/Release wall ratio |
|----------|----------------|------------------|---------------------|--------------|----------------|-------------------|--------------------------|
| TwoPhase | ok(FrontierExhausted) | 1 | FrontierExhausted | ok(FrontierExhausted) | 1 | FrontierExhausted | 1.00x |
| PrimaryBackup | ok(FrontierExhausted) | 2 | FrontierExhausted | ok(FrontierExhausted) | 8 | FrontierExhausted | 4.00x |
| LeaderElection | timeout_reached(TimeoutReached) | 241 | TimeoutReached | timeout_reached(TimeoutReached) | 243 | TimeoutReached | 1.01x |
| Paxos | timeout_reached(TimeoutReached) | 274 | TimeoutReached | timeout_reached(TimeoutReached) | 304 | TimeoutReached | 1.11x |

## Phase-Attributed Source-First Timing Breakdown (ms)

Canonical source-first timing values come from `reports/benchmarks/source_first_release` JSON artifacts.

| Protocol | Source ingest | Model/config | Init construction | Successor solving | Candidate gen/eval | Dedup/hash/normalize | Invariant eval | Report serialize/output |
|----------|---------------|--------------|-------------------|-------------------|--------------------|----------------------|----------------|--------------------------|
| TwoPhase | 0 | 0 | 4 | 168 | 5 | 35 | 0 | 0 |
| PrimaryBackup | 0 | 0 | 10 | 2008 | 12 | 294 | 0 | 0 |
| LeaderElection | 0 | 0 | 108 | 239698 | 288 | 242 | 0 | 0 |
| Paxos | 0 | 0 | 21369 | 222492 | 25805 | 37 | 0 | 0 |

## Small-Model Wall-Time Gap Diagnosis (Phase 33.4.4.c)

This section is restricted to the two shared small-model protocols that currently finish in exact mode (TwoPhase, PrimaryBackup).
The diagnosis is computed from release canonical telemetry plus debug-vs-release elapsed-ms ratios.

| Protocol | Release wall (ms) | Candidate gen/eval (ms) | Candidate share | Fixed startup+parsing share | Dedup/hash share | Invariant share | Debug/Release (elapsed-ms) | Dominant release phase | Fixed-overhead dominates? | Dedup meaningful? | Release materially changes wall time? |
|----------|-------------------|--------------------------|-----------------|-----------------------------|------------------|-----------------|-----------------------------|------------------------|---------------------------|-------------------|----------------------------------------|
| TwoPhase | 212 | 5 | 2.36% | 1.89% (4 ms) | 16.51% (35 ms) | 0.00% (0 ms) | 4.06x | successor_solving | no | yes | yes |
| PrimaryBackup | 2324 | 12 | 0.52% | 0.43% (10 ms) | 12.65% (294 ms) | 0.00% (0 ms) | 3.36x | successor_solving | no | yes | yes |

- TwoPhase: dominant release cost is `successor_solving` (candidate=2.36%, fixed=1.89%, dedup=16.51%, invariant=0.00%). Fixed-overhead dominates: **no**. Dedup meaningful: **yes**. Release materially changes wall time: **yes** (debug/release=4.06x).
- PrimaryBackup: dominant release cost is `successor_solving` (candidate=0.52%, fixed=0.43%, dedup=12.65%, invariant=0.00%). Fixed-overhead dominates: **no**. Dedup meaningful: **yes**. Release materially changes wall time: **yes** (debug/release=3.36x).

- Cross-protocol conclusion: neither small model is currently fixed-overhead dominated; both are dominated by successor solving on current release telemetry. Dedup/hash is now non-negligible on both runs, while invariant checking remains negligible. Release build materially reduces wall time on both protocols without changing the dominant phase.

## Branch-Level Blocker Telemetry (Phase 33.4.4.d)

Branch rows come from release canonical source-first artifacts (reports/benchmarks/source_first_release), sorted by cumulative branch solve time.
Tables focus on exact-mode blocker protocols (LeaderElection, Paxos) and keep only top branch families for compact auditability.

### LeaderElection

| Branch label | Existential assignments | Candidate states | Direct solver hits | Enumeration fallback hits | Guard-pruned evals | Successful successors | Cumulative solve ms |
|--------------|-------------------------|------------------|--------------------|---------------------------|--------------------|-----------------------|---------------------|
| branch_3 | 7380 | 13824 | 56 | 0 | 0 | 39 | 58830 |
| branch_2 | 7380 | 13824 | 57 | 0 | 0 | 105 | 55305 |
| branch_5 | 7380 | 13824 | 56 | 0 | 0 | 312 | 52436 |
| branch_6 | 2460 | 13824 | 56 | 0 | 0 | 158 | 18874 |

### Paxos

| Branch label | Existential assignments | Candidate states | Direct solver hits | Enumeration fallback hits | Guard-pruned evals | Successful successors | Cumulative solve ms |
|--------------|-------------------------|------------------|--------------------|---------------------------|--------------------|-----------------------|---------------------|
| branch_5 | 3 | 1679616 | 3 | 0 | 0 | 0 | 33802 |
| branch_1 | 3 | 1679616 | 3 | 0 | 0 | 9 | 33513 |
| branch_0 | 3 | 1679616 | 3 | 0 | 0 | 2 | 33432 |
| branch_3 | 3 | 1679616 | 3 | 0 | 0 | 0 | 33405 |
| branch_2 | 27 | 1679616 | 3 | 0 | 0 | 42 | 33318 |
| branch_4 | 9 | 1679616 | 3 | 0 | 0 | 27 | 33274 |
| branch_6 | 1 | 1679616 | 2 | 0 | 0 | 0 | 21748 |

- Phase 33.4.4.f (Paxos blocker reduction): release telemetry now shows direct helper-branch solving with `enumeration_fallback_hits=0` and `enumeration_eval=0`; prior blocker rows `branch_0` and `branch_2` no longer fall back to candidate enumeration.

- Interpretation rule for blocker narratives: prioritize branch families with highest cumulative solve ms and enumeration fallback hits; use existential/candidate counts plus guard-pruned/successor outcomes to distinguish domain blow-up from guard-filtered dead-ends.

## Explicit Root-Cause Answers (Phase 33.4.4.g)

- **Why is source-first currently slower on the protocols that finish?**
  - **Answer:** release telemetry shows the dominant phase is solver work (`successor_solving` for TwoPhase and `successor_solving` for PrimaryBackup), not fixed startup overhead.
  - TwoPhase evidence: wall=212ms, candidate share=2.36%, fixed share=1.89% (4ms, dominates=no), dedup share=16.51% (35ms, meaningful=yes), invariant share=0.00%, debug/release=4.06x.
  - PrimaryBackup evidence: wall=2324ms, candidate share=0.52%, fixed share=0.43% (10ms, dominates=no), dedup share=12.65% (294ms, meaningful=yes), invariant share=0.00%, debug/release=3.36x.
  - Conclusion: release build materially helps, but the remaining wall-time gap is primarily successor-solving overhead rather than startup or invariant checking.

- **Why do LeaderElection and Paxos still block under matched benchmarks?**
  - **LeaderElection:** stop_reason=TimeoutReached with timeout at 240336ms (states=280, transitions=804). Blocked mainly by large-domain direct solving, not enumeration fallback (enum_eval=0, enum_fallback_branch_solves=0, direct_solves=395, top_branch=branch_3 direct_hits=56, max_existentials=7380, max_candidates=13824, top_branch_solve_ms=58830).
  - **Paxos:** stop_reason=TimeoutReached with timeout at 269703ms (states=75, transitions=80). Blocked mainly by large-domain direct solving, not enumeration fallback (enum_eval=0, enum_fallback_branch_solves=0, direct_solves=20, top_branch=branch_5 direct_hits=3, max_existentials=27, max_candidates=1679616, top_branch_solve_ms=33802).
  - Conclusion: the current blocker is timeout under high branch-domain solve cost; further wins require reducing existential/candidate-domain solve pressure in hot branches.

## Column Meanings

- `States (gen)`: total states generated before deduplication. For TLC this includes revisits.
- `Distinct`: unique states after the engine's deduplication/fingerprinting step.
- `Depth`: maximum search depth reached in the run.
- `Wall (s)`: wall-clock elapsed time in seconds.
- For source-first, `States (gen)` is currently reported as `—` because the checked-in benchmark summaries expose deduplicated explored states, not a separate generated-state counter.

## Side-by-side Results

| Protocol | Engine | Result | States (gen) | Distinct | Depth | Wall (s) |
|----------|--------|--------|--------------|----------|-------|----------|
| twophase | source-first | ok(FrontierExhausted) | — | 8 | 3 | 1 |
| | TLC | pass | 150 | 64 | 9 | 1 |
| primarybackup | source-first | ok(FrontierExhausted) | — | 60 | 7 | 2 |
| | TLC | pass | 86 | 54 | 10 | 1 |
| leaderelection | source-first | timeout_reached(TimeoutReached) | — | 280 | 3 | 241 |
| | TLC | pass | 100636 | 9337 | 13 | 2 |
| paxos | source-first | timeout_reached(TimeoutReached) | — | 75 | 2 | 274 |
| | TLC | pass | 25288515 | 3005604 | 37 | 375 |

## Notes

- **State-count semantics differ**: Source-first counts states on the
  centralized Verus `LState` directly. TLC counts states on the TLA+
  wrapper which may include additional message-channel variables.
- LeaderElection source-first status: `timeout_reached(TimeoutReached)` (stop_reason=TimeoutReached, enumeration_eval=0).
- Paxos source-first status: `timeout_reached(TimeoutReached)` (stop_reason=TimeoutReached, enumeration_eval=0).
  See branch-level blocker telemetry above for per-branch evidence.
- Configs: `transpiler/tests/model_check_fixtures/benchmarks_1h/`
- TLC wrappers: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/`

## Same-Model Provenance

- Generated base TLA+ (from `verus-transpile verus2-tla --batch`):
  - `transpiler/tla_test_workspace/transpiler_generated_tla/TwoPhase/Twophase.tla`
  - `transpiler/tla_test_workspace/transpiler_generated_tla/PrimaryBackup/Primarybackup.tla`
  - `transpiler/tla_test_workspace/transpiler_generated_tla/LeaderElection/Election.tla`
  - `transpiler/tla_test_workspace/transpiler_generated_tla/Paxos/Paxos.tla`
- TLC wrapper/property glue used for model checking:
  - `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.tla` + `.cfg`
  - `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/PrimaryBackup_Benchmark_MC.tla` + `.cfg`
  - `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/LeaderElection_Benchmark_MC.tla` + `.cfg`
  - `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/Paxos_Benchmark_MC.tla` + `.cfg`
- The benchmark comparison uses generated base modules plus checked-in wrapper/property glue; it does not compare against scratch-written standalone TLA+ specs.

## Matched-Cutoff Progress (Shared 120s Budget)

This section is generated from dedicated time-bounded raw artifacts (not inferred from full-run totals).

- Source-first cutoff artifacts: `reports/benchmarks/source_first_cutoff_120s`
- TLC cutoff artifacts: `reports/benchmarks/tlc_cutoff_120s`

| Protocol | Engine | Result | States (gen) | Distinct | Depth | Wall (s) | Transitions | Elapsed (ms) | Notes |
|----------|--------|--------|--------------|----------|-------|----------|-------------|--------------|-------|
| TwoPhase | source-first | ok(FrontierExhausted) | — | 8 | 3 | 74 | 24 | 73495 | bounded progress |
| | TLC | pass | 150 | 64 | 9 | 1 | n/a | n/a | exhausted before cutoff |
| PrimaryBackup | source-first | timeout_reached(TimeoutReached) | — | 52 | 5 | 120 | 128 | 120033 | time-bounded blocked progress; stop_reason=TimeoutReached; enum_eval=1855808 |
| | TLC | pass | 86 | 54 | 10 | 1 | n/a | n/a | exhausted before cutoff |
| LeaderElection | source-first | timeout_reached(TimeoutReached) | — | 1 | 0 | 120 | 0 | 120548 | time-bounded blocked progress; stop_reason=TimeoutReached; enum_eval=1437838 |
| | TLC | pass | 100636 | 9337 | 13 | 2 | n/a | n/a | exhausted before cutoff |
| Paxos | source-first | timeout_reached(TimeoutReached) | — | 1 | 0 | 182 | 0 | 174345 | time-bounded blocked progress; stop_reason=TimeoutReached; enum_eval=712532 |
| | TLC | timeout | 5312208 | 876750 | ? | 120 | n/a | n/a | time-bounded progress at cutoff |

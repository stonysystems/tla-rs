# TLC vs Source-first Benchmark Comparison

Generated: 2026-03-11 02:03:39 UTC
Git rev: 875a221

Source-first run: Generated: 2026-03-11 01:53:44 UTC
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
| TwoPhase | ok(FrontierExhausted) | 5 | FrontierExhausted | ok(FrontierExhausted) | 21 | FrontierExhausted | 4.20x |
| PrimaryBackup | ok(FrontierExhausted) | 12 | FrontierExhausted | ok(FrontierExhausted) | 40 | FrontierExhausted | 3.33x |
| LeaderElection | timeout_reached(TimeoutReached) | 240 | TimeoutReached | timeout_reached(TimeoutReached) | 242 | TimeoutReached | 1.01x |
| Paxos | timeout_reached(TimeoutReached) | 270 | TimeoutReached | timeout_reached(TimeoutReached) | 308 | TimeoutReached | 1.14x |

## Phase-Attributed Source-First Timing Breakdown (ms)

Canonical source-first timing values come from `reports/benchmarks/source_first_release` JSON artifacts.

| Protocol | Source ingest | Model/config | Init construction | Successor solving | Candidate gen/eval | Dedup/hash/normalize | Invariant eval | Report serialize/output |
|----------|---------------|--------------|-------------------|-------------------|--------------------|----------------------|----------------|--------------------------|
| TwoPhase | 0 | 0 | 4 | 162 | 4818 | 40 | 0 | 0 |
| PrimaryBackup | 0 | 0 | 13 | 2128 | 9117 | 268 | 0 | 0 |
| LeaderElection | 0 | 0 | 110 | 239910 | 273 | 241 | 0 | 0 |
| Paxos | 0 | 0 | 21855 | 33144 | 211375 | 10 | 0 | 0 |

## Small-Model Wall-Time Gap Diagnosis (Phase 33.4.4.c)

This section is restricted to the two shared small-model protocols that currently finish in exact mode (TwoPhase, PrimaryBackup).
The diagnosis is computed from release canonical telemetry plus debug-vs-release elapsed-ms ratios.

| Protocol | Release wall (ms) | Candidate gen/eval (ms) | Candidate share | Fixed startup+parsing share | Dedup/hash share | Invariant share | Debug/Release (elapsed-ms) | Dominant release phase | Fixed-overhead dominates? | Dedup meaningful? | Release materially changes wall time? |
|----------|-------------------|--------------------------|-----------------|-----------------------------|------------------|-----------------|-----------------------------|------------------------|---------------------------|-------------------|----------------------------------------|
| TwoPhase | 5024 | 4818 | 95.90% | 0.08% (4 ms) | 0.80% (40 ms) | 0.00% (0 ms) | 4.05x | candidate_enumeration | no | no | yes |
| PrimaryBackup | 11526 | 9117 | 79.10% | 0.11% (13 ms) | 2.33% (268 ms) | 0.00% (0 ms) | 3.48x | candidate_enumeration | no | no | yes |

- TwoPhase: dominant release cost is `candidate_enumeration` (candidate=95.90%, fixed=0.08%, dedup=0.80%, invariant=0.00%). Fixed-overhead dominates: **no**. Dedup meaningful: **no**. Release materially changes wall time: **yes** (debug/release=4.05x).
- PrimaryBackup: dominant release cost is `candidate_enumeration` (candidate=79.10%, fixed=0.11%, dedup=2.33%, invariant=0.00%). Fixed-overhead dominates: **no**. Dedup meaningful: **no**. Release materially changes wall time: **yes** (debug/release=3.48x).

- Cross-protocol conclusion: neither small model is currently fixed-overhead dominated; both are dominated by candidate generation/evaluation, with dedup/hash and invariant checking negligible. Release build materially reduces wall time on both protocols but does not change the dominant cost center.

## Branch-Level Blocker Telemetry (Phase 33.4.4.d)

Branch rows come from release canonical source-first artifacts (reports/benchmarks/source_first_release), sorted by cumulative branch solve time.
Tables focus on exact-mode blocker protocols (LeaderElection, Paxos) and keep only top branch families for compact auditability.

### LeaderElection

| Branch label | Existential assignments | Candidate states | Direct solver hits | Enumeration fallback hits | Guard-pruned evals | Successful successors | Cumulative solve ms |
|--------------|-------------------------|------------------|--------------------|---------------------------|--------------------|-----------------------|---------------------|
| branch_3 | 7380 | 13824 | 56 | 0 | 0 | 39 | 59363 |
| branch_2 | 7380 | 13824 | 56 | 0 | 0 | 104 | 54845 |
| branch_5 | 7380 | 13824 | 56 | 0 | 0 | 312 | 52795 |
| branch_6 | 2460 | 13824 | 55 | 0 | 0 | 156 | 18730 |

### Paxos

| Branch label | Existential assignments | Candidate states | Direct solver hits | Enumeration fallback hits | Guard-pruned evals | Successful successors | Cumulative solve ms |
|--------------|-------------------------|------------------|--------------------|---------------------------|--------------------|-----------------------|---------------------|
| branch_0 | 3 | 1679616 | 0 | 1 | 0 | 2 | 138882 |
| branch_2 | 27 | 1679616 | 0 | 1 | 0 | 0 | 68521 |
| branch_1 | 3 | 1679616 | 1 | 0 | 0 | 3 | 11269 |

- Interpretation rule for blocker narratives: prioritize branch families with highest cumulative solve ms and enumeration fallback hits; use existential/candidate counts plus guard-pruned/successor outcomes to distinguish domain blow-up from guard-filtered dead-ends.

## Column Meanings

- `States (gen)`: total states generated before deduplication. For TLC this includes revisits.
- `Distinct`: unique states after the engine's deduplication/fingerprinting step.
- `Depth`: maximum search depth reached in the run.
- `Wall (s)`: wall-clock elapsed time in seconds.
- For source-first, `States (gen)` is currently reported as `—` because the checked-in benchmark summaries expose deduplicated explored states, not a separate generated-state counter.

## Side-by-side Results

| Protocol | Engine | Result | States (gen) | Distinct | Depth | Wall (s) |
|----------|--------|--------|--------------|----------|-------|----------|
| twophase | source-first | ok(FrontierExhausted) | — | 8 | 3 | 5 |
| | TLC | pass | 150 | 64 | 9 | 1 |
| primarybackup | source-first | ok(FrontierExhausted) | — | 60 | 7 | 12 |
| | TLC | pass | 86 | 54 | 10 | 1 |
| leaderelection | source-first | timeout_reached(TimeoutReached) | — | 276 | 2 | 240 |
| | TLC | pass | 100636 | 9337 | 13 | 2 |
| paxos | source-first | timeout_reached(TimeoutReached) | — | 5 | 1 | 270 |
| | TLC | pass | 25288515 | 3005604 | 37 | 375 |

## Notes

- **State-count semantics differ**: Source-first counts states on the
  centralized Verus `LState` directly. TLC counts states on the TLA+
  wrapper which may include additional message-channel variables.
- LeaderElection source-first status: `timeout_reached(TimeoutReached)` (stop_reason=TimeoutReached, enumeration_eval=0).
- Paxos source-first status: `timeout_reached(TimeoutReached)` (stop_reason=TimeoutReached, enumeration_eval=7397877).
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

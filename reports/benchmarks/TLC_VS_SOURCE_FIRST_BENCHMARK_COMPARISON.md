# TLC vs Source-first Benchmark Comparison

Generated: 2026-03-11 00:52:47 UTC
Git rev: fd77b1c

Source-first run: Generated: 2026-03-11 00:42:45 UTC
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
| TwoPhase | ok(FrontierExhausted) | 18 | FrontierExhausted | ok(FrontierExhausted) | 74 | FrontierExhausted | 4.11x |
| PrimaryBackup | ok(FrontierExhausted) | 50 | FrontierExhausted | ok(FrontierExhausted) | 176 | FrontierExhausted | 3.52x |
| LeaderElection | timeout_reached(TimeoutReached) | 240 | TimeoutReached | timeout_reached(TimeoutReached) | 240 | TimeoutReached | 1.00x |
| Paxos | timeout_reached(TimeoutReached) | 270 | TimeoutReached | timeout_reached(TimeoutReached) | 303 | TimeoutReached | 1.12x |

## Phase-Attributed Source-First Timing Breakdown (ms)

Canonical source-first timing values come from `reports/benchmarks/source_first_release` JSON artifacts.

| Protocol | Source ingest | Model/config | Init construction | Successor solving | Candidate gen/eval | Dedup/hash/normalize | Invariant eval | Report serialize/output |
|----------|---------------|--------------|-------------------|-------------------|--------------------|----------------------|----------------|--------------------------|
| TwoPhase | 0 | 0 | 4 | 0 | 17573 | 34 | 0 | 0 |
| PrimaryBackup | 0 | 0 | 11 | 4 | 49727 | 255 | 0 | 0 |
| LeaderElection | 0 | 0 | 106 | 20 | 240149 | 6 | 0 | 0 |
| Paxos | 0 | 0 | 21577 | 0 | 243996 | 5 | 0 | 0 |

## Small-Model Wall-Time Gap Diagnosis (Phase 33.4.4.c)

This section is restricted to the two shared small-model protocols that currently finish in exact mode (TwoPhase, PrimaryBackup).
The diagnosis is computed from release canonical telemetry plus debug-vs-release elapsed-ms ratios.

| Protocol | Release wall (ms) | Candidate gen/eval (ms) | Candidate share | Fixed startup+parsing share | Dedup/hash share | Invariant share | Debug/Release (elapsed-ms) | Dominant release phase | Fixed-overhead dominates? | Dedup meaningful? | Release materially changes wall time? |
|----------|-------------------|--------------------------|-----------------|-----------------------------|------------------|-----------------|-----------------------------|------------------------|---------------------------|-------------------|----------------------------------------|
| TwoPhase | 17611 | 17573 | 99.78% | 0.02% (4 ms) | 0.19% (34 ms) | 0.00% (0 ms) | 4.16x | candidate_enumeration | no | no | yes |
| PrimaryBackup | 49997 | 49727 | 99.46% | 0.02% (11 ms) | 0.51% (255 ms) | 0.00% (0 ms) | 3.52x | candidate_enumeration | no | no | yes |

- TwoPhase: dominant release cost is `candidate_enumeration` (candidate=99.78%, fixed=0.02%, dedup=0.19%, invariant=0.00%). Fixed-overhead dominates: **no**. Dedup meaningful: **no**. Release materially changes wall time: **yes** (debug/release=4.16x).
- PrimaryBackup: dominant release cost is `candidate_enumeration` (candidate=99.46%, fixed=0.02%, dedup=0.51%, invariant=0.00%). Fixed-overhead dominates: **no**. Dedup meaningful: **no**. Release materially changes wall time: **yes** (debug/release=3.52x).

- Cross-protocol conclusion: neither small model is currently fixed-overhead dominated; both are dominated by candidate generation/evaluation, with dedup/hash and invariant checking negligible. Release build materially reduces wall time on both protocols but does not change the dominant cost center.

## Branch-Level Blocker Telemetry (Phase 33.4.4.d)

Branch rows come from release canonical source-first artifacts (reports/benchmarks/source_first_release), sorted by cumulative branch solve time.
Tables focus on exact-mode blocker protocols (LeaderElection, Paxos) and keep only top branch families for compact auditability.

### LeaderElection

| Branch label | Existential assignments | Candidate states | Direct solver hits | Enumeration fallback hits | Guard-pruned evals | Successful successors | Cumulative solve ms |
|--------------|-------------------------|------------------|--------------------|---------------------------|--------------------|-----------------------|---------------------|
| branch_0 | 2460 | 13824 | 0 | 1 | 0 | 0 | 239903 |

### Paxos

| Branch label | Existential assignments | Candidate states | Direct solver hits | Enumeration fallback hits | Guard-pruned evals | Successful successors | Cumulative solve ms |
|--------------|-------------------------|------------------|--------------------|---------------------------|--------------------|-----------------------|---------------------|
| branch_0 | 3 | 1679616 | 0 | 1 | 0 | 2 | 120964 |
| branch_1 | 3 | 1679616 | 0 | 1 | 0 | 2 | 97455 |

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
| twophase | source-first | ok(FrontierExhausted) | — | 8 | 3 | 18 |
| | TLC | pass | 150 | 64 | 9 | 1 |
| primarybackup | source-first | ok(FrontierExhausted) | — | 60 | 7 | 50 |
| | TLC | pass | 86 | 54 | 10 | 1 |
| leaderelection | source-first | timeout_reached(TimeoutReached) | — | 1 | 0 | 240 |
| | TLC | pass | 100636 | 9337 | 13 | 2 |
| paxos | source-first | timeout_reached(TimeoutReached) | — | 4 | 1 | 270 |
| | TLC | pass | 25288515 | 3005604 | 37 | 375 |

## Notes

- **State-count semantics differ**: Source-first counts states on the
  centralized Verus `LState` directly. TLC counts states on the TLA+
  wrapper which may include additional message-channel variables.
- **Paxos and LeaderElection** source-first runs are BLOCKED on
  candidate enumeration scalability (see benchmark configs for details).
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

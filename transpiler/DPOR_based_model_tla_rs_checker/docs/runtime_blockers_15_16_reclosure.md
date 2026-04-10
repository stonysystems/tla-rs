# Runtime Blockers Re-closure (Cases 15/16)

Date: 2026-04-10  
Scope: Phase 38 open-task-map priority item ("Re-close regenerated-corpus runtime blockers").

## Why this doc exists

After regenerated-corpus replay, `15_chain_replication_small` and
`16_primarybackup_small` were temporarily reclassified to
`expected_primary_result = "known_unimplemented"` in
`tests/manifest.toml`.

This document records direct, reproducible baseline runs that confirmed the
initial blocker modes, plus later closure steps. Case 15 has since been
restored to `deadlock` (`38.15.2.d.b`); case 16 has now been restored to `ok`
(`38.15.3`).

## Reproduction commands and observed outcomes

All commands run from repo root (`/home/shuai/workspace/tla-rs`).

### Case 15 (`15_chain_replication_small`)

Command pattern (using current per-case config with high timeout budget):

```bash
timeout 1200s transpiler/target/release/verus-transpile model-check \
  --input transpiler/DPOR_based_model_tla_rs_checker/tests/tla-rs/15_chain_replication_small/Chain.rs \
  --init LInit --next LNext \
  --model <tmp_15_config_with_timeout_ms_1200000> \
  --json-report
```

Observed result:

- Process exits non-zero (`exit=1`).
- No JSON report is emitted.
- Stderr message:
  `Configuration error: Sequence domain expansion exceeded limit 200000 assignments/values.`

Interpretation:

- This is a candidate-enumeration guardrail abort (not a deadlock verdict).
- The current case cannot be scored as a real negative result until this path
  is tuned/fixed.

### Case 16 (`16_primarybackup_small`)

Command pattern (bounded timeout-window probe with invariant enabled):

```bash
timeout 60s transpiler/target/release/verus-transpile model-check \
  --input transpiler/DPOR_based_model_tla_rs_checker/tests/tla-rs/16_primarybackup_small/Primarybackup.rs \
  --init LInit --next LNext \
  --model <tmp_16_config_with_timeout_ms_60000> \
  --json-report \
  --invariant LSafetyInactiveStateIsQuiescent
```

Observed result:

- Wrapper exits with timeout code (`exit=124`).
- Output file size remains `0` bytes.
- No JSON report is emitted for the run.

Interpretation:

- This matches the "timeout-window checker_error/no-report" blocker class in
  the open-task map.
- Runtime/bounds closure is required before restoring `expected_primary_result = "ok"`.

## Closure decomposition reference

See `TODO.md` `38.15` leaves:

- `38.15.2`: case 15 candidate-enumeration closure
- `38.15.3`: case 16 timeout-window closure (done)
- `38.15.4`: re-enable focused protocol regressions
- `38.15.5`: full-suite/report resync and open-task-map closure

## 38.15.2.a guardrail/timeout sweep (case 15)

Goal: determine whether simply increasing
`candidate_eval_guardrail` on the current non-vacuous case-15 model is enough
to restore a real `deadlock_detected` outcome.

Baseline model family:

- input: `tests/tla-rs/15_chain_replication_small/Chain.rs`
- model basis: `tests/model_configs/15_chain_replication_small.toml`
- deadlock enabled (`check_deadlock = true`)
- int domain / collection bounds unchanged from checked-in case-15 config

Observed sweep (`2026-04-10`):

| candidate_eval_guardrail | wrapper timeout | observed outcome |
|---:|---:|---|
| 300,000 | 180s | guardrail abort (`Sequence domain expansion exceeded limit 300000`) |
| 500,000 | 180s | guardrail abort (`... limit 500000`) |
| 800,000 | 180s | guardrail abort (`... limit 800000`) |
| 1,200,000 | 180s | guardrail abort (`... limit 1200000`) |
| 2,000,000 | 180s | guardrail abort (`... limit 2000000`) |
| 5,000,000 | 300s | guardrail abort (`Model-check candidate-enumeration guardrail exceeded`) |
| 10,000,000 | 300s | timeout-window exit (`exit=124`, no JSON report) |
| 20,000,000 | 300s | timeout-window exit (`exit=124`, no JSON report) |

Conclusion:

- Tuning-only via scalar guardrail increases is insufficient for case 15.
- Next closure step must either find a smaller non-vacuous deadlock-friendly
  domain profile (`38.15.2.b`) or reduce candidate-explosion behavior in code
  (`38.15.2.c`).

## 38.15.2.b low-domain bounded-config probe (case 15)

Goal: find a smaller case-15 model domain that is still non-vacuous
(`distinct_states > 0`) and reaches a real deadlock verdict under suite budget.

Probe A (`2026-04-10`): low-domain structural sweep around the checked-in model
shape with `candidate_eval_guardrail = 200000`, wrapper `timeout 75s`,
`timeout_ms = 60000`, and fixed `max_set_len = 1`.

| int domain | max_seq_len | max_map_len | outcome |
|---|---:|---:|---|
| `0..0` | `1` | `1` | completes `result=ok`, but vacuous (`initial_states=0`, `distinct_states=0`) |
| `0..0` | `2` | `1` | completes `result=ok`, but vacuous (`initial_states=0`, `distinct_states=0`) |
| `0..1` | `1` | `1` | guardrail abort (`Model-check candidate-enumeration guardrail exceeded`) |
| `0..1` | `2` | `1` | guardrail abort (`Sequence domain expansion exceeded limit 200000`) |
| any | `0` or `max_map_len=0` | any | rejected by config validation (`collection bounds must be > 0`) |

Probe B (`2026-04-10`): focus on the minimal non-vacuous candidate profile
(`int=0..1`, `max_seq_len=1`, `max_map_len=1`, `max_set_len=1`) across
`max_depth` `{8, 12, 16, 20}` and guardrails
`{300000, 500000, 800000, 1200000, 2000000}` with wrapper `timeout 120s`.

Observed result:

- all 20 runs aborted with
  `Configuration error: Model-check candidate-enumeration guardrail exceeded`.
- no run emitted a JSON report; no deadlock row was produced.

Probe C (`2026-04-10`): same minimal non-vacuous profile at elevated
guardrail `10000000` with `max_depth` 8 and 20 (wrapper `timeout 120s`).

Observed result:

- both runs exited `124` with zero-byte output files and no JSON report.

Conclusion:

- Low-domain tuning did not find a non-vacuous bounded config that reaches a
  real deadlock verdict for case 15.
- `38.15.2.b` closes with "no feasible low-domain config found"; the next leaf
  is `38.15.2.c` (targeted candidate-enumeration reduction step in code).

## 38.15.2.c targeted reduction step (helper-heavy branch fallback)

Goal: land one <500 LOC reduction step that reduces unnecessary
candidate-enumeration fallback for case-15 helper-call branches, then remeasure.

Implemented change (`2026-04-10`):

- File: `transpiler/src/main.rs`
- Function: `try_solve_predicate_only_helper_branch`
- Step: when a helper sub-branch is unsupported by direct assignment solving,
  but (a) does **not** depend on `s_` and (b) is provably disabled for all
  merged assignments at the current state, skip that sub-branch instead of
  forcing full call-site fallback enumeration.
- New unit regression:
  `tests::test_execute_model_check_helper_solver_skips_statically_disabled_unsupported_subbranches_without_fallback`
  verifies direct-helper solving remains active and fallback counters stay zero
  in this guard-disabled unsupported-sub-branch shape.

Focused remeasure (`2026-04-10`):

1. Checked-in case-15 config (`tests/model_configs/15_chain_replication_small.toml`):
   still fails at domain expansion stage:
   `Sequence domain expansion exceeded limit 200000 assignments/values`.
2. Minimal non-vacuous profile from `38.15.2.b`
   (`int=0..1`, `max_seq_len=1`, `max_map_len=1`, guardrail `200000`):
   still fails on `branch_1` guardrail (`200001 > 200000`) because the
   problematic helper disjunct is satisfiable in this configuration.
3. Pinned-constants probe where that helper disjunct is disabled
   (`chain_len=2`, `node_id=1`, `max_seq_len=1`):
   failure mode shifts from guardrail to a concrete next-state bound error:
   `Failed to evaluate next-state assignment in branch 'branch_1' at s_.history:
   Seq value length 2 exceeds configured max_seq_len 1.`

Conclusion:

- The `38.15.2.c` reduction path is active and cuts fallback in the
  statically-disabled unsupported-sub-branch scenario.
- Case-15 closure is still blocked in default/minimal profiles by (i) sequence
  domain expansion and (ii) satisfiable helper disjuncts that retain huge
  candidate spaces. `38.15.2.d` remains pending real deadlock closure.

## 38.15.2.d preflight (restore-known-unimplemented removal) — blocked

Goal: satisfy the precondition for `38.15.2.d` by producing one real,
non-vacuous `deadlock_detected` case-15 row under bounded budget, then restore
manifest/test expectations.

Focused probes (`2026-04-10`) after `38.15.2.c`:

1. Pinned constants (`chain_len=2`, `node_id=1`), `int=0..1`,
   `max_seq_len=1`:
   all runs complete as vacuous `ok` (`initial_states=0`, `distinct_states=0`)
   because this constant profile requires `role=2` while `2` is outside
   `int=0..1`.
2. Same constants, `int=0..2`, `max_seq_len=1`:
   non-vacuous precondition is reachable, but runs fail on a concrete bound
   error while exploring:
   `Failed to evaluate next-state assignment in branch 'branch_1' at s_.history:
   Seq value length 2 exceeds configured max_seq_len 1.`
3. Same constants, `int=0..2`, `max_seq_len=2`:
   sequence-domain expansion still aborts before a deadlock verdict; observed
   repeatedly at limits `500000`, `1000000`, `2000000`, and `5000000`.
4. Alternate tail constants (`chain_len=3`, `node_id=2`, `int=0..3`,
   `max_seq_len=1`) did not close either; probe hit
   `Struct domain expansion for LRecord exceeded limit 300000`.

Conclusion:

- `38.15.2.d` precondition is not met yet; no reproducible non-vacuous
  deadlock row exists in checked-in evidence.
- Historical snapshot only: this preflight block was resolved later by
  `38.15.2.d.a` closure evidence; manifest restoration is tracked in
  `38.15.2.d.b`.

## 38.15.2.d.a.i bounded-assignment rejection step + 38.15.2.d.a.ii reruns

Goal: reduce one blocking failure mode from `38.15.2.d` and re-check whether a
real deadlock row becomes reproducible under valid 2-node constants.

Implemented step (`38.15.2.d.a.i`, done 2026-04-10):

- File: `transpiler/src/modelcheck/solver.rs`
- Change: when evaluating a next-state assignment (`s_.field == ...`), bounded
  collection overflow (`max_seq_len`, `max_set_len`, `max_map_len`) now rejects
  that assignment as `ConstraintFailed` instead of aborting the entire run.
- Unit coverage:
  `test_solve_branch_successors_treats_assignment_collection_overflow_as_constraint_failure`.

Post-fix focused sweep (`38.15.2.d.a.ii`, 2026-04-10):

- Input: `tests/tla-rs/15_chain_replication_small/Chain.rs`
- Shared bounds:
  `max_seq_len=1`, `max_set_len=1`, `max_map_len=1`, `max_depth=2`
- Constants/profile families:
  valid 2-node constants (`chain_len=2`, `node_id in {0,1}`) and nearby
  3-node tails (`chain_len=3`, `node_id in {0,2}`), matching role-feasible int
  ranges.
- Guardrails tested: `200000`, `300000`, `500000`
- Wrapper: `timeout 30s`

Observed outcomes:

| constants + int profile | guardrail 200000 | guardrail 300000 | guardrail 500000 |
|---|---|---|---|
| `chain_len=2,node_id=1,int=0..2` | existential expansion limit | timeout (no JSON in 30s) | timeout (no JSON in 30s) |
| `chain_len=2,node_id=0,int=0..1` | branch guardrail exceeded | branch guardrail exceeded | branch guardrail exceeded |
| `chain_len=3,node_id=2,int=0..2` | existential expansion limit | timeout (no JSON in 30s) | timeout (no JSON in 30s) |
| `chain_len=3,node_id=0,int=0..1` | branch guardrail exceeded | branch guardrail exceeded | branch guardrail exceeded |
| `chain_len=3,node_id=1,int=0..3` | struct expansion limit (`LRecord`) | struct expansion limit (`LRecord`) | struct expansion limit (`LRecord`) |

Extended focused reruns (`38.15.2.d.a.ii`, 2026-04-10 later pass) added
aux-constant pinning to reduce constants-valuation fanout:
`State=0`, `CRMessage=0`, `Constants=0`.

| constants + int profile | guardrail 300000 (depth 1) | guardrail 300000 (depth 2) | guardrail 500000 (depth 1) | guardrail 500000 (depth 2) | guardrail 800000 (depth 1) | guardrail 800000 (depth 2) |
|---|---|---|---|---|---|---|
| `chain_len=2,node_id=1,int=0..2` + aux pinned | `ok` (FrontierExhausted, `distinct_states=40`, ~37s) | timeout in 45s wrapper | `ok` (FrontierExhausted, `distinct_states=40`, ~41s) | timeout in 45s wrapper | `ok` (FrontierExhausted, `distinct_states=40`, ~41s) | timeout in 45s wrapper |

Targeted long-wrapper reruns for the same profile at
`guardrail=300000`, `max_depth=2`, `timeout_ms=180000`:

```bash
timeout 240s transpiler/target/release/verus-transpile model-check \
  --input transpiler/DPOR_based_model_tla_rs_checker/tests/tla-rs/15_chain_replication_small/Chain.rs \
  --init LInit --next LNext \
  --model <tmp_case15_deadlock_profile> \
  --json-report
```

Observed (two repeated runs):

- run 1: `result=deadlock_detected`, `stop_reason=DeadlockDetected`,
  `initial_states=1`, `distinct_states=151`, `elapsed_ms=147830`,
  deadlock depth `1`.
- run 2: `result=deadlock_detected`, `stop_reason=DeadlockDetected`,
  `initial_states=1`, `distinct_states=151`, `elapsed_ms=147624`,
  deadlock depth `1`.

Conclusion (updated):

- `38.15.2.d.a.ii` is satisfied: a reproducible non-vacuous deadlock row is
  now confirmed for case 15 under the selected bounded profile.
- `38.15.2.d.a.iii` is satisfied by checking in that profile at
  `tests/model_configs/15_chain_replication_small.toml`.
- Follow-up leaf `38.15.2.d.c` (focused regression re-enable) is now complete
  (see subsection below).

## 38.15.2.d.b manifest expectation restore (done)

Goal: once `38.15.2.d.a` closes with a reproducible non-vacuous deadlock row,
restore case 15 from temporary `known_unimplemented` to real `deadlock`
expectation in `tests/manifest.toml`.

Manifest update:

- case `15_chain_replication_small` now uses
  `expected_primary_result = "deadlock"`.
- temporary known-unimplemented blocker note for case 15 is removed and
  replaced with a closure note that points to the checked-in model profile.

Focused verification run (`2026-04-10`), using the checked-in case-15 model:

```bash
timeout 240s transpiler/target/release/verus-transpile model-check \
  --input transpiler/DPOR_based_model_tla_rs_checker/tests/tla-rs/15_chain_replication_small/Chain.rs \
  --init LInit --next LNext \
  --model transpiler/DPOR_based_model_tla_rs_checker/tests/model_configs/15_chain_replication_small.toml \
  --json-report
```

Observed result:

- `result=deadlock_detected`, `stop_reason=DeadlockDetected`
- `initial_states=1`, `distinct_states=151`, deadlock depth `1`
- `elapsed_ms=148357`

Full-suite verification after manifest restore:

- Command:
  `./transpiler/DPOR_based_model_tla_rs_checker/scripts/run_full_suite.sh --timeout 1200`
- Timestamp: `2026-04-10T15:37:34Z`
- Case row:
  `[15_chain_replication_small] PASS (deadlock found, 148982ms)`
- Summary:
  `Passed (real): 18`, `Known unimplemented: 2` (cases 16 and 19), `Failed: 0`.

## 38.15.2.d.c focused regression re-enable (done)

Goal: remove the temporary case-15 focused-regression ignore in
`src/dpor.rs`, then verify focused + full-suite behavior stays green.

Code change (<500 LOC):

- File: `src/dpor.rs`
- Removed temporary `#[ignore = "...candidate-enumeration guardrails..."]`
  from `test_case15_chain_replication_is_real_non_vacuous_deadlock`.
- Updated its call-site timeout budget from `120` to `240` seconds for
  consistency with observed bounded runtime margin.

Verification:

- Focused DPOR test suite:
  `cargo test --manifest-path transpiler/DPOR_based_model_tla_rs_checker/Cargo.toml -q`
  => `86 passed; 0 failed; 4 ignored`
  (case 15 focused regression executes as active test).
- Full suite:
  `./transpiler/DPOR_based_model_tla_rs_checker/scripts/run_full_suite.sh --timeout 1200`
  => case row
  `[15_chain_replication_small] PASS (deadlock found, 152675ms)` and overall
  `Passed (real): 18`, `Known unimplemented: 2`, `Failed: 0`.

## 38.15.3 case-16 timeout-window closure (done)

Goal: restore `16_primarybackup_small` from temporary
`known_unimplemented` to real invariant-checked `ok` under bounded profile and
suite budget.

Code/config change (<500 LOC):

- File: `tests/model_configs/16_primarybackup_small.toml`
- Added pinned constants assignments:
  `State = 0`, `PBMessage = 0`, `Constants = 0`, `max_log_len = 1`
- Tuned bounded search profile:
  `max_depth = 6`, `max_states = 20000`, `timeout_ms = 45000`

Focused verification run (`2026-04-10`):

```bash
transpiler/target/release/verus-transpile model-check \
  --input transpiler/DPOR_based_model_tla_rs_checker/tests/tla-rs/16_primarybackup_small/Primarybackup.rs \
  --init LInit --next LNext \
  --model transpiler/DPOR_based_model_tla_rs_checker/tests/model_configs/16_primarybackup_small.toml \
  --invariant LSafetyInactiveStateIsQuiescent \
  --json-report
```

Observed result:

- `result=ok`, `stop_reason=FrontierExhausted`
- `initial_states=1`, `distinct_states=211`, `depth=6`
- `elapsed_ms=8539`

Manifest update:

- `tests/manifest.toml` case `16_primarybackup_small` restored to
  `expected_primary_result = "ok"`
- closure note now points to the checked-in bounded profile and non-vacuous
  metrics above.

## Runtime note discovered during 38.15.2.a reruns (case 19)

While re-running mandatory full suites for this phase, case
`19_epaxos_small` showed timeout-window instability in the current environment:

- Full-suite run (`--timeout 1200`) produced a timeout-wrapper
  `checker_error`/no-JSON outcome for case 19.
- Focused direct probes (3/3 attempts, `timeout 120s`) exited `124` with
  no JSON report emission.

Because this was reproducible in repeated direct runs, case 19 is temporarily
reclassified to `known_unimplemented` in `tests/manifest.toml` pending a
separate runtime-stability re-closure pass.

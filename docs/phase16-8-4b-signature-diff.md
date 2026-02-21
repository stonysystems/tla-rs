# Phase 16.8.4b Signature Diff Snapshot

Date: 2026-02-21

## Goal
Regenerate `transpiler/tla_test_workspace/transpiler_generated_verus_spec/` from
`transpiler/tla_test_workspace/transpiler_generated_tla/` after the `16.8.4a`
translator fix (reserved parameter dedup), and capture pre/post signature deltas.

## Execution Notes
- Regeneration ran in a clean detached worktree at commit `588fef1` to avoid
  contamination from unrelated dirty files in the main workspace.
- Command shape used for each input `.tla` file:
  - `target/release/verus-transpile translate-tla --input <file.tla> --output <file.rs> --gen-modes`

## Counts
- Input `.tla` files translated: `33`
- Pre-regeneration signature lines: `267`
- Post-regeneration signature lines: `267`
- Signature diff length (`diff -u` lines): `466`
- Regenerated spec files changed: `30`
- Net file diff stats: `197` insertions, `197` deletions (`394` changed LOC)

## Representative Signature Changes
These examples show the intended removal of duplicated auto-injected reserved
params (`s`, `s_`, `c`) from D1-generated signatures.

```text
ChainReplication/Chain.rs
- pub open spec fn LInit(s: LState, c: LConstants, s: int, c: int) -> bool {
+ pub open spec fn LInit(s: LState, c: LConstants) -> bool {
- pub open spec fn LNext(s: LState, c: LConstants, s: int, s_: int, c: int) -> bool {
+ pub open spec fn LNext(s: LState, c: LConstants, s_: int) -> bool {

Paxos/Paxos.rs
- pub open spec fn LInit(s: LState, c: LConstants, s: int, c: int) -> bool {
+ pub open spec fn LInit(s: LState, c: LConstants) -> bool {
- pub open spec fn LNext(s: LState, c: LConstants, s: int, s_: int, c: int) -> bool {
+ pub open spec fn LNext(s: LState, c: LConstants, s_: int) -> bool {

Raft/Raft.rs
- pub open spec fn LInit(s: LState, c: LConstants, s: int, c: int) -> bool {
+ pub open spec fn LInit(s: LState, c: LConstants) -> bool {
- pub open spec fn LNext(s: LState, c: LConstants, s: int, s_: int, c: int) -> bool {
+ pub open spec fn LNext(s: LState, c: LConstants, s_: int) -> bool {

RSL/Acceptor.rs
- pub open spec fn LAcceptorInit(s: LState, c: LConstants, a: int, c: int) -> bool {
+ pub open spec fn LAcceptorInit(s: LState, c: LConstants, a: int) -> bool {
```

## Changed File Set (30)
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/ChainReplication/Chain.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/ChainReplication/Types.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/EPaxos/Epaxos.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/EPaxos/Types.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/LeaderElection/Election.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/LeaderElection/Types.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/PBFT/Pbft.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/PBFT/Types.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/Paxos/Paxos.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/Paxos/Types.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/PrimaryBackup/Primarybackup.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/PrimaryBackup/Types.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/RSL/Acceptor.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/RSL/Broadcast.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/RSL/Configuration.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/RSL/Constants.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/RSL/Distributed_system.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/RSL/Election.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/RSL/Executor.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/RSL/Learner.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/RSL/Parameters.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/RSL/Proposer.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/RSL/Replica.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/RSL/Types.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/Raft/Raft.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/Raft/Types.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/TwoPhase/Twophase.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/TwoPhase/Types.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/VerticalPaxos/Types.rs`
- `transpiler/tla_test_workspace/transpiler_generated_verus_spec/VerticalPaxos/Vpaxos.rs`

## Observation
Besides reserved-param dedup improvements in function signatures, regeneration
also reordered some record-field layouts in generated type-return signatures.
That churn is syntactic and expected from full regeneration; `16.8.4c` will
re-run D2 and refresh category counts against this updated baseline.

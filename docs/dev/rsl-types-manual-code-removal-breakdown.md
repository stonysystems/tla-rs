# RSL Types Manual-Code Removal Breakdown (Phase 21.7.5.1)

## Goal
Remove `output.manual_code = "types_manual_helpers.rs"` from `src/protocol/RSL/types_transpile.toml` without regressing:
- transpiler generation parity,
- generated module public API,
- Verus verification,
- existing integration test expectations.

## Current State
`types_manual_helpers.rs` still injects major type infrastructure into `src/generated/RSL/types_gen.rs`.
Recent leaves already re-homed helper methods/functions:
- `StaticParams` -> `implementation/RSL/cparameters.rs`
- quorum/index helpers (`CMinQuorumSize`, `CGetReplicaIndex`, `CFindIndexInSeq`) -> `implementation/RSL/cconfiguration.rs`
- replica-constants helpers (`CReplicaConstantsValid`, `InitReplicaConstants`) -> `implementation/RSL/cconstants.rs`

Remaining injected surface is mostly struct/enum definitions plus `valid`/`View`/`clone_up_to_view` impl blocks for RSL concrete types.

## Remaining Manual Blocks

### Foundational blocks
- `CConfiguration` (type + validity/view/clone + structural predicates)
- `CConstants` (type + validity/view/clone)
- `CReplicaConstants` (type + validity/view/clone)

### Component block A
- `CAcceptor`
- `CLearner`
- `CElectionState`
- `COutstandingOperation`

### Component block B
- `CExecutor`
- `CIncompleteBatchTimer`
- `CProposer`
- `CReplica`
- `CScheduler`

## Why 21.7.5 Is Too Large As One Leaf
Migrating all remaining blocks at once requires coordinated changes across:
- `types_manual_helpers.rs`
- `types_transpile.toml` (`skip_types`, `re_exports`, maybe `skip_validity_types`/`skip_view_types`)
- implementation boundary modules under `src/implementation/RSL/`
- generated output (`types_gen.rs`)
- integration tests that assert symbol placement/public API text

This exceeds a safe single-leaf change budget and increases risk of cross-module breakage.

## Migration Strategy (Ordered)

1. `21.7.5.2`: Foundational blocks first
- These underpin all other component types.
- Success criterion: foundational symbols no longer injected by manual_code.

2. `21.7.5.3`: Component block A
- Intermediate complexity, fewer transitive dependencies than proposer/replica scheduler stack.

3. `21.7.5.4`: Component block B
- Highest coupling and largest surface.

4. `21.7.5.5`: Remove `output.manual_code`
- After all required symbols are sourced from generated/re-exported implementation modules.

## Verification Gate Per Leaf
Each leaf must pass:
- `cd transpiler && cargo test --all-features`
- `scons --verus-path=/home/shuai/tools/verus-x86-linux/verus -c liblib.so`
- `scons --verus-path=/home/shuai/tools/verus-x86-linux/verus liblib.so`

## Notes
- Keep compatibility aliases/re-exports stable to avoid consumer churn.
- Prefer moving code into `src/implementation/RSL/*` modules over re-creating logic.
- Keep integration assertions updated to enforce the new symbol ownership boundaries.

# RSL Executor Manual-Code Audit (2026-02-22)

## Scope

Audit `src/protocol/RSL/executor_manual.rs` before executor final-mile migration to:

1. lock the current manual footprint with regression checks;
2. define a small-leaf execution order for `21.11.3`.

## Current Footprint

`executor_manual.rs` is 706 LOC and currently exports 10 `pub exec fn` functions:

1. `CExecutorInit`
2. `CExecutorGetDecision`
3. `CClientsInReplies`
4. `CUpdateNewCache`
5. `CGetPacketsFromReplies`
6. `CExecutorExecute`
7. `CExecutorProcessAppStateSupply`
8. `CExecutorProcessAppStateRequest`
9. `CExecutorProcessStartingPhase2`
10. `CExecutorProcessRequest`

`#[verifier(external_body)]` boundaries in this file are currently six total:

- four proof lemmas
- `CClientsInReplies`
- `CUpdateNewCache`

`executor_manual.rs` contains no direct `assume(...)` statements (proof-oriented boundary, unlike replica IO wrappers).

## Migration Order (Leaf Plan)

1. Re-home pure cache helpers (`CClientsInReplies`, `CUpdateNewCache`).
2. Migrate recursive packet helper (`CGetPacketsFromReplies`).
3. Migrate packet-processing action functions.
4. Migrate remaining state-only action functions.
5. Resolve `CExecutorExecute` end-state and remove `output.manual_code`.

This order intentionally removes low-risk helper code first, then progressively tackles higher proof-complexity action paths.

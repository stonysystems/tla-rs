# Phase 47.1.c: RSL Hot-Loop Exec Function Inventory

## Summary

~35-40 exec functions execute per-request in the RSL hot loop, across 6 components.
Two dispatch layers exist:

1. **Sushant's `ReplicaImpl.rs`** (hand-written) - already `&mut self` on `CReplica`
2. **Generated `replica_gen.rs`** (optimized_rsl copy) - functional wrappers that rebuild `CReplica`

Converting sub-component functions to `&mut self` eliminates layer-2 struct rebuilds.

## Hot-Path Functions by Component

### Proposer (`optimized_rsl/RSL/proposer_gen.rs`)

| Function | Signature | Hot? | Notes |
|----------|-----------|------|-------|
| `CProposerProcessRequest` | `&mut self, &CPacket` | YES | Phase 47.1.a done |
| `CProposerMaybeEnterNewViewAndSend1a` | `&CProposer -> (CProposer, Vec<CPacket>)` | YES | |
| `CProposerProcess1b` | `&CProposer, &CPacket -> CProposer` | YES | |
| `CProposerMaybeEnterPhase2` | `&CProposer, &u64 -> (CProposer, Vec<CPacket>)` | YES | |
| `CProposerNominateNewValueAndSend2a` | `&CProposer, &u64, &u64 -> (CProposer, Vec<CPacket>)` | YES | clone_up_to_view |
| `CProposerNominateOldValueAndSend2a` | `&CProposer, &u64 -> (CProposer, Vec<CPacket>)` | YES | existential search |
| `CProposerMaybeNominateValueAndSend2a` | `&CProposer, &u64, &u64 -> (CProposer, Vec<CPacket>)` | YES | 5-branch dispatch |
| `CProposerProcessHeartbeat` | `&CProposer, &CPacket, &u64 -> CProposer` | YES | |
| `CProposerResetViewTimerDueToExecution` | `&CProposer, &CRequestBatch -> CProposer` | YES | |
| `CProposerCheckForViewTimeout` | `&CProposer, &u64 -> CProposer` | cold | |
| `CProposerCheckForQuorumOfViewSuspicions` | `&CProposer, &u64 -> CProposer` | cold | |

### Acceptor (`optimized_rsl/RSL/acceptor_gen.rs`)

| Function | Signature | Hot? |
|----------|-----------|------|
| `CAcceptorProcess1a` | `&CAcceptor, &CPacket -> (CAcceptor, Vec<CPacket>)` | YES |
| `CAcceptorProcess2a` | `&CAcceptor, &CPacket -> (CAcceptor, Vec<CPacket>)` | YES |
| `CAcceptorProcessHeartbeat` | `&CAcceptor, &CPacket -> CAcceptor` | YES |
| `CAcceptorTruncateLog` | `&CAcceptor, &u64 -> CAcceptor` | YES |

### Learner (`optimized_rsl/RSL/learner_gen.rs`)

| Function | Signature | Hot? |
|----------|-----------|------|
| `CLearnerProcess2b` | `&CLearner, &CPacket -> CLearner` | YES |
| `CLearnerForgetDecision` | `&CLearner, &u64 -> CLearner` | YES |
| `CLearnerForgetOperationsBefore` | `&CLearner, &u64 -> CLearner` | YES |

### Executor (`optimized_rsl/RSL/executor_gen.rs`)

| Function | Signature | Hot? |
|----------|-----------|------|
| `CExecutorProcessRequest` | `&CExecutor, &CPacket -> Vec<CPacket>` | YES |
| `CExecutorGetDecision` | `&CExecutor, &CBallot, &u64, &CRequestBatch -> CExecutor` | YES |
| `CExecutorExecute` | `&CExecutor -> (CExecutor, Vec<CPacket>)` | YES |
| `CExecutorProcessStartingPhase2` | `&CExecutor, &CPacket -> (CExecutor, Vec<CPacket>)` | YES |

### Election (`optimized_rsl/RSL/election_gen.rs`)

| Function | Signature | Hot? |
|----------|-----------|------|
| `CElectionStateProcessHeartbeat` | `&CElectionState, &CPacket, &u64 -> CElectionState` | YES |
| `CElectionStateReflectReceivedRequest` | `&CElectionState, &CRequest -> CElectionState` | YES |
| `CElectionStateReflectExecutedRequestBatch` | `&CElectionState, &CRequestBatch -> CElectionState` | YES |
| `CRemoveAllSatisfiedRequestsInSequence` | `&Vec<CRequest>, &CRequest -> Vec<CRequest>` | YES |
| `CRemoveExecutedRequestBatch` | `&Vec<CRequest>, &CRequestBatch -> Vec<CRequest>` | YES |
| `CBoundRequestSequence` | `&Vec<CRequest>, u64 -> Vec<CRequest>` | YES |

### Replica Wrappers (`optimized_rsl/RSL/replica_gen.rs`)

~15 hot-path functional wrappers: `CReplicaNextProcessRequest`, `CReplicaNextProcess1a`, `CReplicaNextProcess1b`, `CReplicaNextProcessStartingPhase2`, `CReplicaNextProcess2a`, `CReplicaNextProcess2b`, `CReplicaNextProcessHeartbeat`, `CReplicaNextSpontaneous*` (5 functions), `CReplicaNextReadClockMaybeNominate*`.

All use `(&CReplica, ...) -> (CReplica, Vec<CPacket>)` pattern, rebuilding `CReplica` each call.

### Broadcast + Helpers

- `CBroadcastToEveryone` — per-message (N replicas loop)
- `CClientsInReplies`, `CUpdateNewCache`, `CGetPacketsFromReplies` — per-reply
- `Packet1bHasUniqueSrc` — per-1b uniqueness check

## Conversion Strategy for Phase 47.3

Priority order (most allocation-heavy first):
1. **Proposer** (8 remaining functional) — largest struct, most Arc fields
2. **Acceptor** (4 functions) — CVotes HashMap operations
3. **Learner** (3 functions) — HashMap-heavy
4. **Executor** (4 functions) — reply cache operations
5. **Election** (6 functions) — request queue filtering
6. **Replica wrappers** (15 functions) — depends on all above being `&mut self`

Total conversion: ~35 functions from `(&CXxx) -> CXxx` to `(&mut self)`.

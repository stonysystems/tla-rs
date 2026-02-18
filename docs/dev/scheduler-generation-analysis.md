# Scheduler Generation Analysis (Phase 17.4)

## Problem Statement

Each protocol's `LNext` spec function is a disjunction of all possible state transitions.
At runtime, the host needs a scheduler that dispatches incoming messages and timer events
to the appropriate transpiler-generated `C*` function. Currently this is hand-written
(~500 LOC per protocol, ~4500 LOC total across 9 protocols).

## LNext Structure Analysis

All 9 non-RSL protocols follow the same LNext pattern:

```rust
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| LAction1(s, s_, c)                           // direct call
    ||| (exists |param: int| LAction2(s, s_, c, param))  // quantified
    ...
}
```

### Branch Count by Protocol

| Protocol | Total | Direct | Quantified |
|----------|-------|--------|------------|
| TwoPhase | 8 | 3 | 5 |
| Paxos | 7 | 2 | 5 |
| LeaderElection | 7 | 0 | 7 |
| PrimaryBackup | 8 | 7 | 1 |
| ChainReplication | 8 | 4 | 4 |
| Raft | 11 | 2 | 9 |
| PBFT | 9 | 3 | 6 |
| VerticalPaxos | 10 | 4 | 6 |
| EPaxos | 11 | 4 | 7 |
| **Total** | **79** | **29** | **50** |

### Existential Parameter Patterns

Existential parameters typically represent:
- **Node IDs**: `|rm: int|`, `|node: int|`, `|sender: int|`, `|follower: int|`
  - At runtime, extracted from the incoming message's source endpoint
- **Values**: `|value: int|`, `|val: int|`, `|entry_value: int|`
  - At runtime, extracted from message fields or client input
- **Protocol state**: `|ballot: int|`, `|new_term: int|`, `|new_commit_index: int|`
  - At runtime, computed from current state or message fields

## Host.rs Dispatch Patterns

Hand-written host.rs files use three main patterns:

1. **Message-first dispatch** (6 protocols): Paxos, LeaderElection, Raft, PBFT, VerticalPaxos, EPaxos
   - Match on incoming message variant -> call corresponding C* function
   - Fallback to round-robin timer actions on timeout

2. **Role-based dispatch** (3 protocols): TwoPhase, ChainReplication, PrimaryBackup
   - Check node's role (TM/RM, Head/Middle/Tail, Primary/Backup)
   - Dispatch message handling and timer actions based on role

3. **Common timer pattern**: Round-robin via `action_index % N`
   - N ranges from 2 (PrimaryBackup backup) to 7 (EPaxos)

## Implementation Approach

### Phase 17.4.1: Parse LNext (DONE)
- `analyze-lnext` CLI subcommand extracts disjunction structure
- Outputs `[scheduler]` TOML config section
- 10 unit tests + 10 integration tests (all 9 protocols)

### Phase 17.4.2: Generate TOML config (next)
- Auto-populate `[scheduler]` sections from analyze-lnext output
- Add action-to-message mapping hints

### Phase 17.4.3: Generate scheduler scaffold
- Generate ProtocolHost trait implementation from `[scheduler]` config
- Message dispatch based on variant-to-action mapping
- Round-robin timer dispatch

### Phase 17.4.4: Protocol-specific refinements (deferred)
- Role-based dispatch for TwoPhase/ChainReplication/PrimaryBackup
- Message flag simulation for shared-state bridging
- Guard checks from spec preconditions

## CLI Usage

```bash
# Analyze a protocol's LNext function
verus-transpile analyze-lnext -i src/protocol/Paxos/paxos.rs

# Custom function name and prefix
verus-transpile analyze-lnext -i spec.rs --next-fn LNext --spec-prefix L --exec-prefix C

# Output to file
verus-transpile analyze-lnext -i spec.rs -o scheduler.toml
```

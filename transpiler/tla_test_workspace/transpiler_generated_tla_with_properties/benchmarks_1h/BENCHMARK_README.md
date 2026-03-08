# TLC Benchmark Wrappers

TLC model-checking wrappers for the 4 benchmark protocols, with model sizes
matching the source-first benchmark configs in `transpiler/tests/model_check_fixtures/benchmarks_1h/`.

## Invariant Mapping (Source-first → TLC)

All 12 invariant pairs are **exact semantic equivalents**. The Verus source
predicates operate on `(s: LState, c: LConstants)` (single centralized state).
TLC wrappers use `state` (single-state protocols) or `state[n]` (multi-node
Paxos). Quantifier domains match: Verus `forall |rm: int|` covers all integers
but only RMs are ever inserted; TLC `\A rm \in RMs` restricts to the finite set.

### TwoPhase
| Source-first (Verus) | TLC wrapper | Equivalence |
|---------------------|-------------|-------------|
| `LSafetyNoCommitAbortOverlap` | `NoCommitAbortOverlap` | Exact |
| `LSafetyCommittedSubsetPrepared` | `CommittedSubsetPrepared` | Exact |
| `LSafetyTmCommittedRequiresAllPrepared` | `TmCommittedRequiresAllPrepared` | Exact |

### PrimaryBackup
| Source-first (Verus) | TLC wrapper | Equivalence |
|---------------------|-------------|-------------|
| `LSafetyNoPendingImpliesClearedValue` | `NoPendingImpliesClearedValue` | Exact |
| `LSafetyUnackedImpliesPending` | `UnackedImpliesPending` | Exact |
| `LSafetyInactiveStateIsQuiescent` | `InactiveStateIsQuiescent` | Exact |

### LeaderElection
| Source-first (Verus) | TLC wrapper | Equivalence |
|---------------------|-------------|-------------|
| `LSafetyElectingSubsetAlive` | `ElectingSubsetAlive` | Exact |
| `LSafetyWaitingNodeAliveWhenWaiting` | `WaitingNodeAliveWhenWaiting` | Exact |
| `LSafetyNoWaitingImpliesClearedWaitingNode` | `NoWaitingImpliesClearedWaitingNode` | Exact |

### Paxos
| Source-first (Verus) | TLC wrapper | Equivalence |
|---------------------|-------------|-------------|
| `LSafetyAcceptedBallotBoundedByPromise` | `AcceptedBallotBoundedByPromise` | Exact |
| `LSafetyDecidedRequiresQuorum` | `DecidedRequiresQuorum` | Exact |
| `LSafetyDecidedMatchesProposedValue` | `DecidedMatchesProposedValue` | Exact |

Note: Paxos is multi-node in TLC (per-node state array `state[n]`), while the
Verus source uses a single centralized `LState`. The TLC invariants quantify
`\A n \in Nodes` to check each node's state independently, matching the
source-first model checker which evaluates the predicate on the centralized state.

## Model Size Matching

| Protocol | Model constant | Source-first | TLC |
|----------|---------------|-------------|-----|
| TwoPhase | RMs | `{0, 1}` (2 RMs) | `{0, 1}` (2 RMs) |
| PrimaryBackup | MaxLogLen, Values | 1, `{0,1}` | 1, `{0,1}` |
| LeaderElection | Nodes | `{0, 1, 2}` (3) | `{0, 1, 2}` (3) |
| Paxos | Nodes, QuorumSize | `{0,1,2}`, 2 | `{0,1,2}`, 2 |

## Running TLC

```bash
# Requires Java 11+ and tla2tools.jar
JAVA=java
TLA2TOOLS=/path/to/tla2tools.jar

# Example: TwoPhase benchmark with 1-hour timeout
cd transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/
timeout 3600 $JAVA -XX:+UseParallelGC -cp $TLA2TOOLS tlc2.TLC \
    -workers auto -config TwoPhase_Benchmark_MC.cfg TwoPhase_Benchmark_MC.tla
```

## Base TLA+ Generation

The core TLA+ modules are generated from Verus source:
```bash
verus-transpile verus2-tla --batch \
    --input src/protocol/<Protocol> \
    --output transpiler/tla_test_workspace/transpiler_generated_tla/<Protocol> \
    --spec-prefix L
```

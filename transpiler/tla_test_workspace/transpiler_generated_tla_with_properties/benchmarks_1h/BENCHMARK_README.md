# TLC Benchmark Wrappers

TLC model-checking wrappers for the 4 benchmark protocols, with model sizes
matching the source-first benchmark configs in `transpiler/tests/model_check_fixtures/benchmarks_1h/`.

## Invariant Mapping (Source-first → TLC)

### TwoPhase
| Source-first (Verus) | TLC wrapper |
|---------------------|-------------|
| `LSafetyNoCommitAbortOverlap` | `NoCommitAbortOverlap` |
| `LSafetyCommittedSubsetPrepared` | `CommittedSubsetPrepared` |
| `LSafetyTmCommittedRequiresAllPrepared` | `TmCommittedRequiresAllPrepared` |

### PrimaryBackup
| Source-first (Verus) | TLC wrapper |
|---------------------|-------------|
| `LSafetyNoPendingImpliesClearedValue` | `NoPendingImpliesClearedValue` |
| `LSafetyUnackedImpliesPending` | `UnackedImpliesPending` |
| `LSafetyInactiveStateIsQuiescent` | `InactiveStateIsQuiescent` |

### LeaderElection
| Source-first (Verus) | TLC wrapper |
|---------------------|-------------|
| `LSafetyElectingSubsetAlive` | `ElectingSubsetAlive` |
| `LSafetyWaitingNodeAliveWhenWaiting` | `WaitingNodeAliveWhenWaiting` |
| `LSafetyNoWaitingImpliesClearedWaitingNode` | `NoWaitingImpliesClearedWaitingNode` |

### Paxos
| Source-first (Verus) | TLC wrapper |
|---------------------|-------------|
| `LSafetyAcceptedBallotBoundedByPromise` | `AcceptedBallotBoundedByPromise` |
| `LSafetyDecidedRequiresQuorum` | `DecidedRequiresQuorum` |
| `LSafetyDecidedMatchesProposedValue` | `DecidedMatchesProposedValue` |

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

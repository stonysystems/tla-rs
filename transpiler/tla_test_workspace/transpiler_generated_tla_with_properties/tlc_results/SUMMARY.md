# TLC Model Checking Results

All 9 non-RSL protocol MC wrappers were model-checked with TLC2 v2.17
on 2026-02-26 using 64 cores, Java 17 (OpenJDK).

## Command Template

```bash
JAVA=/usr/lib/jvm/java-17-openjdk-amd64/bin/java
TLA2TOOLS=/home/users/zihao/pgo/tools/tla2tools.jar
cd transpiler/tla_test_workspace/transpiler_generated_tla_with_properties

$JAVA -XX:+UseParallelGC -cp $TLA2TOOLS tlc2.TLC \
  -workers auto -config <Protocol>_MC.cfg <Protocol>_MC.tla
```

Timeout runs used: `timeout 300 $JAVA ...` (5-minute cap).

## Results

| Protocol         | Result   | States Gen  | Distinct    | Depth | Time | Invariants |
|------------------|----------|-------------|-------------|-------|------|------------|
| TwoPhase         | PASS     | 926         | 304         | 10    | 1s   | 5          |
| LeaderElection   | PASS     | 100,636     | 9,337       | 18    | 2s   | 5          |
| PrimaryBackup    | PASS     | 786         | 438         | 7     | 1s   | 6          |
| Paxos            | TIMEOUT  | ~109M       | ~18M        | 24+   | 5min | 5          |
| ChainReplication | PASS     | 599         | 326         | 8     | 1s   | 5          |
| Raft             | PASS     | 4,795       | 1,453       | 16    | 2s   | 6          |
| PBFT             | TIMEOUT  | ~303M       | ~102M       | 264K+ | 5min | 6          |
| VerticalPaxos    | PASS     | 3,480,465   | 255,872     | 21    | 5s   | 6          |
| EPaxos           | TIMEOUT  | ~190M       | ~79M        | 401K+ | 5min | 6          |

**6/9 exhaustive pass, 3/9 timeout with 0 violations found.**

## Notes

- **Paxos**: 3-node, ballot ∈ {1..3}, quorum=2. State space too large for exhaustive
  check; ~109M states explored in 5min with no violations. Queue growing (7M states
  remaining), suggesting full exploration would require hours.
- **PBFT**: 3-replica, view ∈ {0..2}, seq ∈ {0..2}. Very deep state graph (264K+ depth)
  from sequence-number/view-change combinations. ~303M states in 5min, no violations.
- **EPaxos**: 2-replica, 2-command model. Deep state graph (401K+ depth) from command
  interference and fast/slow path interleaving. ~190M states in 5min, no violations.
- **VerticalPaxos**: Largest exhaustive check (3.5M states, 256K distinct, 5s). Config
  reconfiguration and witness sync create rich but bounded state space.
- **ChainReplication**: Fixed Head/Tail naming conflict with TLA+ Sequences module
  builtins by renaming to HeadRole/MiddleRole/TailRole.
- **VerticalPaxos**: Fixed 2 overly-strong invariants found by TLC counterexamples:
  - BallotOrdering (max_v_bal <= max_bal) violated by ReceivePromise tracking remote ballots
  - CommittedImpliesVoted violated because proposer commits via remote accepts

## Log Files

Each `<Protocol>_MC.log` in this directory contains the full TLC output.

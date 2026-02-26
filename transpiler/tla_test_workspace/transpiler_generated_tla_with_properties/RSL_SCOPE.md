# RSL TLC Model-Checking Scope Decision

## Decision: RSL is OUT OF SCOPE for TLC property bundles in Phase 16.8

## Rationale

RSL (Replicated State Library) is a multi-module protocol decomposed into 15 TLA+
files (Acceptor, Broadcast, Configuration, Constants, Distributed_system, Election,
Environment, Executor, Learner, Message, Parameters, Proposer, Replica,
State_machine, Types). Unlike the other 8 protocols which each have a single
self-contained spec file with relational (s, s_, c, sent_packets) actions, RSL's
TLA+ output mirrors its Verus source structure with cross-module dependencies.

Creating a meaningful MC wrapper for RSL would require:

1. **Module composition**: Combining 15 interdependent modules into a single
   model-checkable state machine, resolving all cross-references.

2. **Multi-node state**: RSL inherently requires modeling interactions between
   proposer, acceptor, learner, executor, and election modules — each with their
   own state — across multiple replicas.

3. **Massive state space**: Even with aggressive bounds, RSL's state (ballots,
   votes, quorums, operation logs, elections) produces an intractable state space
   for TLC.

4. **Existing verification**: RSL is already formally verified via Verus with
   624 verified conditions and 0 errors. The verification covers refinement
   proofs that are strictly stronger than TLC model checking.

## Coverage Summary

| Protocol          | MC Bundle | Invariants |
|-------------------|-----------|------------|
| TwoPhase          | Yes       | 5          |
| PrimaryBackup     | Yes       | (existing) |
| LeaderElection    | Yes       | 5          |
| Paxos             | Yes       | (existing) |
| ChainReplication  | Yes       | 5          |
| Raft              | Yes       | 6          |
| PBFT              | Yes       | 6          |
| VerticalPaxos     | Yes       | 6          |
| EPaxos            | Yes       | 6          |
| RSL               | No        | N/A — Verus-verified |

All 9 non-RSL protocols have property bundles. RSL is excluded due to structural
complexity and the availability of stronger formal verification.

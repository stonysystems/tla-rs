# Non-BFT consensus research ledger

The requested scope is papers introducing or changing consensus protocols in
OSDI, SOSP, NSDI, SIGMOD and VLDB, from September 26, 1996 through September 26,
2026. The [catalog](catalog.md) currently contains 52 included records, comprising
51 papers and one published correction, plus 10 unresolved candidates. It is
not yet exhaustive. Modeling and proving all included protocols remains open.

Only properties formally proved with Verus count toward progress. Proof reports
must state the theorem, its assumptions and remaining obligations. TLC runs,
state counts and mutation checks do not count as proved properties. The active
proof workflow uses Verus only; prior model-checking records are historical.

The catalog includes protocol changes to crash/omission-fault agreement, SMR,
elections, recovery, reconfiguration and linearizable reads within consensus
systems. A system's use of Paxos or Raft is insufficient for inclusion. Pure
read/write-register protocols, weak consistency, BFT, tutorials and demos are
outside this scope. Full industry papers count, including SIGMOD industry
papers published in companion proceedings. Conference edition years determine
the main date column; publication-date differences appear in each record.

Four formalization packages have been added:

| Work | Result | Remaining boundary |
|---|---|---|
| [Chain Replication, OSDI 2004](chain-replication.md) | Verus proves history safety for arbitrary finite executions | Atomic reconfiguration abstraction; distributed master handshake, client linearizability and liveness remain open |
| [Mencius, OSDI 2008](mencius.md) | Verus proves agreement and coordinator origin for the single-instance core | Atomic prepare-quorum collection; multi-instance scheduling, skip optimizations and liveness remain open |
| [PAC/G-PAC, VLDB 2019 and 2021 correction](gpac-recovery.md) | No Verus-proved properties yet | Historical replay evidence only; formal protocol proofs remain open |
| [Jetpack, OSDI 2026](jetpack.md) | Verus proves recovery safety, fast/base ordering agreement, execution consistency and client linearizability for an abstract host composition | Explicit host ordering, fenced prefix recovery and execution contracts; host/implementation refinement, membership changes and liveness remain open |

Existing repository evidence for EPaxos and Tiga is linked in the
catalog. Those results have not been reverified or promoted to proofs of the
conference versions. The EPaxos and Tiga audits contain counterexamples to
specified models. A repaired variant must keep a separate identity from its
source protocol.

## Reading and reproducing the work

- [Catalog and per-paper obligations](catalog.md)
- [Machine-readable ledger](catalog.json)
- [Coverage and exclusions](coverage.md)
- [Retrieved source URLs and SHA-256 digests](sources.json)
- [Verification evidence](verification.json)

Run from the repository root with an installed Verus release:

```bash
python3 scripts/consensus_catalog.py --check
VERUS_PATH=/path/to/verus \
  scripts/verify_consensus_chain.sh
VERUS_PATH=/path/to/verus \
  scripts/verify_consensus_mencius.sh
VERUS_PATH=/path/to/verus \
  bash scripts/verify_consensus_jetpack.sh
```

The checked Verus release was `0.2026.08.02.b677dd5`. Tool and source digests are
recorded in the verification ledger. These checks do not run the entire
repository suite. No files under `src/generated/` were changed.

## What counts as finishing a paper

Each paper needs a pinned version, fault and timing assumptions, an action-by-action
mapping from the paper to its model, and a separately stated theorem. Safety,
liveness and implementation refinement are separate obligations. An invariant
check over a finite configuration does not establish an unbounded theorem.
Fairness and timing assumptions belong in the model, not in unstated prose.

A failed claim requires a reachable trace and a source comparison. Preserve the
original model before trying a repair. Never add the desired safety property as
an action guard to make a proof pass. Record trusted components and any omitted
recovery paths. A generic Paxos proof does not discharge a paper-specific
recovery or fast-path obligation.

Next work is to finish proceedings coverage and resolve the ten pending scope
decisions. Extend Mencius with multi-instance ordering, skip aggregation and
liveness. Chain Replication still needs refinement of its atomic membership
steps before receiving a paper-level completion status. No remaining model or
proof has been marked complete merely because its obligation appears here.

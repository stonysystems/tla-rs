# Community TLA+ Specifications - Sources and Attribution

These TLA+ specifications were collected from publicly available repositories
for testing the tla-rs transpiler's TLA+ parser compatibility. Only specs with
permissive open-source licenses are included.

## Included Specifications

### 1. TwoPhase_community.tla — Two-Phase Commit

- **Source:** [tlaplus/Examples](https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla)
- **Authors:** Jim Gray and Leslie Lamport
- **Paper:** "Consensus on Transaction Commit" (2006)
- **License:** MIT License
- **Downloaded:** 2026-02-19

### 2. Paxos_community.tla — Paxos Consensus

- **Source:** [tlaplus/Examples](https://github.com/tlaplus/Examples/tree/master/specifications/Paxos)
- **Author:** Leslie Lamport (proof work by Jean-Baptiste Tristan)
- **Papers:** "The Part-Time Parliament" (1998), "Paxos Made Simple" (2001)
- **License:** MIT License
- **Downloaded:** 2026-02-19

### 3. Raft_community.tla — Raft Consensus

- **Source:** [ongardie/raft.tla](https://github.com/ongardie/raft.tla)
- **Author:** Diego Ongaro
- **Paper:** "In Search of an Understandable Consensus Algorithm" (USENIX ATC 2014)
- **License:** Creative Commons Attribution 4.0 International (CC BY 4.0)
- **Downloaded:** 2026-02-19

### 4. EPaxos_community.tla — Egalitarian Paxos

- **Source:** [efficient/epaxos](https://github.com/efficient/epaxos/blob/master/tla%2B/EgalitarianPaxos.tla)
- **Authors:** Iulian Moraru, David G. Andersen, Michael Kaminsky (CMU / Intel Labs)
- **Paper:** "There Is More Consensus in Egalitarian Parliaments" (SOSP 2013)
- **License:** Apache License 2.0
- **Downloaded:** 2026-02-19

## Excluded Specifications (License Issues)

The following protocols have community TLA+ specs available but were excluded
due to missing or restrictive licenses:

- **PBFT** — [pkj415/PBFT-TLA](https://github.com/pkj415/PBFT-TLA) — No license
- **Chain Replication** — [cosmoviola/Chain-Replication-Spec](https://github.com/cosmoviola/Chain-Replication-Spec) — No license, incomplete

## Protocols Without Known TLA+ Specifications

No publicly available canonical TLA+ specifications were found for:

- **Leader Election (Bully Algorithm)** — Garcia-Molina (1982)
- **Primary-Backup Replication** — Budhiraja et al. (1993)
- **Vertical Paxos** — Lamport, Malkhi, Zhou (2009)

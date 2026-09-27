# Non-BFT consensus paper catalog

Generated from [catalog.json](catalog.json) by `python3 scripts/consensus_catalog.py`.

As of 2026-09-26: 52 included records, 10 unresolved candidates. This is a provisional catalog, not an exhaustive census or a claim that the listed protocols have been proved.

Conference editions in the interval 1996-09-26 through 2026-09-26. Include full research and industry papers, SIGMOD research in PACMMOD, VLDB research/industry in PVLDB, and separately marked protocol corrections. Exclude workshops, demos, tutorials and unrelated journals.

Papers introducing or changing crash/omission-fault consensus or state-machine replication protocols, including protocol-level reads, recovery, election and reconfiguration. Exclude ordinary applications, unchanged implementations, weak consistency and BFT. Borderline cases remain pending.

Only properties formally proved with Verus count toward proof progress. Historical model-checking results do not discharge proof obligations.

Counts: NSDI 15; OSDI 10; SIGMOD 5; SOSP 7; VLDB 15.

The 2021 PAC/G-PAC erratum is a separate correction record. The year column uses conference editions, which can differ from PVLDB/PACMMOD publication dates.

| Year | Venue | Paper | Protocol change | Local verification status |
|---|---|---|---|---|
| 2004 | NSDI | [Consistent and Automatic Replica Regeneration](https://www.usenix.org/legacy/events/nsdi04/tech/full_papers/yu/yu_html/index.html) | Witness-based membership agreement and one-round graceful reconfiguration | not-started |
| 2004 | OSDI | [Chain Replication for Supporting High Throughput and Availability](https://www.usenix.org/conference/osdi-04/chain-replication-supporting-high-throughput-and-availability) | Ordered chain propagation and fail-stop reconfiguration; external master | abstract-history-safety-proved-in-verus; full-paper-open |
| 2008 | OSDI | [Mencius: Building Efficient Replicated State Machines for WANs](https://www.usenix.org/legacy/event/osdi08/tech/full_papers/mao/mao_html/) | Rotating slot coordinators with suggest, skip and revoke | abstract-instance-safety-proved-in-verus; full-paper-open |
| 2011 | NSDI | [Paxos Replicated State Machines as the Basis of a High-Performance Data Store](https://www.usenix.org/legacy/events/nsdi11/tech/full_papers/Bolosky.pdf) | New read-only view-check protocol without logging or clock synchronization | not-started |
| 2012 | NSDI | [CORFU: A Shared Log Design for Flash Clusters](https://www.usenix.org/conference/nsdi12/technical-sessions/presentation/balakrishnan) | Shared-log append, hole filling and epoch sealing | not-started |
| 2013 | SOSP | [There Is More Consensus in Egalitarian Parliaments](https://www.cs.cmu.edu/~dga/papers/epaxos-sosp2013.pdf) | Leaderless agreement on commands and dependencies | existing-variant-proof-and-counterexample |
| 2013 | VLDB | [Low-Latency Multi-Datacenter Databases using Replicated Commit](https://www.vldb.org/pvldb/vol6/p661-mahmoud.pdf) | Commit-decision replication with reduced Paxos coordination | not-started |
| 2015 | NSDI | [Designing Distributed Systems Using Approximate Synchrony in Data Center Networks](https://www.usenix.org/conference/nsdi15/technical-sessions/presentation/ports) | Speculative agreement using mostly ordered multicast | not-started |
| 2015 | SOSP | [Building Consistent Transactions with Inconsistent Replication](https://irenezhang.net/papers/tapir-sosp15.pdf) | Inconsistent replication with consensus operations and recovery reconciliation | not-started |
| 2016 | OSDI | [Consolidating Concurrency Control and Consensus for Commits under Conflicts](https://www.usenix.org/conference/osdi16/technical-sessions/presentation/mu) | Unified consensus and concurrency control over dependencies | not-started |
| 2016 | OSDI | [Just Say NO to Paxos Overhead: Replacing Consensus with Network Ordering](https://www.usenix.org/conference/osdi16/technical-sessions/presentation/li) | Consensus using ordered unreliable multicast | not-started |
| 2017 | SOSP | [Eris: Coordination-Free Consistent Transactions Using In-Network Concurrency Control](https://danports.net/papers/eris-sosp17.pdf) | Network multi-sequencing with a new replicated transaction and recovery protocol | not-started |
| 2018 | NSDI | [NetChain: Scale-Free Sub-RTT Coordination](https://www.usenix.org/conference/nsdi18/presentation/jin) | Switch-based chain replication with tailored failure handling | not-started |
| 2018 | OSDI | [Fault-Tolerance, Fast and Slow: Exploiting Failure Asynchrony in Distributed Systems](https://www.usenix.org/conference/osdi18/presentation/alagappan) | Replication switches between volatile and persistent durability modes | not-started |
| 2018 | SIGMOD | [DPaxos: Managing Data Closer to Users for Low-Latency and Mobile Applications](https://www.nawab.me/Uploads/Nawab_DPaxos_SIGMOD2018.pdf) | Zone-centric quorums and consensus near mobile clients | not-started |
| 2018 | VLDB | [PolarFS: An Ultra-low Latency and Failure Resilient Distributed File System for Shared Storage Cloud Database](https://www.vldb.org/pvldb/vol11/p1849-cao.pdf) | Raft with out-of-order acknowledgement, commit and apply | not-started |
| 2019 | NSDI | [Exploiting Commutativity For Practical Fast Replication](https://www.usenix.org/conference/nsdi19/presentation/park) | Witness durability before ordering for commuting operations | not-started |
| 2019 | VLDB | [Unifying Consensus and Atomic Commitment for Effective Cloud Data Management](https://www.vldb.org/pvldb/vol12/p611-maiyya.pdf) | Consensus and atomic commitment combined in one protocol family | no-verus-proof |
| 2020 | NSDI | [FLAIR: Accelerating Reads with Consistency-Aware Network Routing](https://www.usenix.org/conference/nsdi20/presentation/takruri) | Switch tracks consistency and directs linearizable Raft reads to followers | not-started |
| 2020 | NSDI | [Gryff: Unifying Consensus and Shared Registers](https://www.usenix.org/conference/nsdi20/presentation/burke) | Carstamps join shared-register operations with EPaxos | not-started |
| 2020 | NSDI | [Near-Optimal Latency Versus Cost Tradeoffs in Geo-Distributed Storage](https://www.usenix.org/system/files/nsdi20-paper-uluyol.pdf) | Consensus for conditional updates with erasure coding and delegated second phase | not-started |
| 2020 | NSDI | [Scalog: Seamless Reconfiguration and Total Order in a Scalable Shared Log](https://www.usenix.org/conference/nsdi20/presentation/ding) | Durable local logs and globally agreed cuts with reconfiguration | not-started |
| 2020 | OSDI | [Tolerating Slowdowns in Replicated State Machines using Copilots](https://www.usenix.org/conference/osdi20/presentation/ngo) | Two pilots with dependency ordering and fast takeovers | not-started |
| 2020 | OSDI | [Virtual Consensus in Delos](https://www.usenix.org/conference/osdi20/presentation/balakrishnan) | Reconfiguration separated from replaceable ordering protocols | not-started |
| 2020 | OSDI | [Microsecond Consensus for Microsecond Applications](https://www.usenix.org/conference/osdi20/presentation/aguilera) | RDMA permissions provide a new consensus replication path | not-started |
| 2020 | VLDB | [Harmonia: Near-Linear Scalability for Replicated Storage with In-Network Conflict Detection](https://drkp.net/papers/harmonia-vldb20.pdf) | Read protocol extension with switch conflict tracking | not-started |
| 2021 | NSDI | [Fault-Tolerant Replication with Pull-Based Consensus in MongoDB](https://www.usenix.org/conference/nsdi21/presentation/zhou) | Raft-derived consensus with arbitrary replica-to-replica pulls | not-started |
| 2021 | NSDI | [EPaxos Revisited](https://www.usenix.org/conference/nsdi21/presentation/tollman) | Clock-based delay policy changes EPaxos message processing | not-started |
| 2021 | SIGMOD | [PigPaxos: Devouring the Communication Bottlenecks in Distributed Consensus](https://2021.sigmod.org/sigmod_research_list.shtml) | Random relay groups and aggregated Paxos responses | not-started |
| 2021 | SOSP | [Rabia: Simplifying State-Machine Replication Through Randomization](https://arxiv.org/abs/2109.12616) | Randomized consensus avoids a separate leader failover path | not-started |
| 2021 | SOSP | [Exploiting Nil-Externality for Fast Replicated Storage](https://pages.cs.wisc.edu/~ra/nilext.pdf) | Defer order and execution until effects become externally visible | not-started |
| 2021 | VLDB | [Scaling Replicated State Machines with Compartmentalization](https://www.vldb.org/pvldb/vol14/p2203-whittaker.pdf) | Protocol roles split into independently scalable components | not-started |
| 2021 | VLDB | [Errata for "Unifying Consensus and Atomic Commitment for Effective Cloud Data Management"](https://www.vldb.org/pvldb/vol14/p1166-maiyya.pdf) | Replaces commit-biased recovery with highest-accepted-ballot selection | no-verus-proof |
| 2022 | VLDB | [In-Network Leaderless Replication for Distributed Data Stores](https://www.vldb.org/pvldb/vol15/p1337-lee.pdf) | Switch coordinates writes and membership changes for linearizable replication | not-started |
| 2023 | NSDI | [Hydra: Serialization-Free Network Ordering for Strongly Consistent Distributed Applications](https://www.usenix.org/conference/nsdi23/presentation/choi) | SMR co-designed with multiple network sequencers | not-started |
| 2023 | SOSP | [QuePaxa: Escaping the Tyranny of Timeouts in Consensus](https://discovery.ucl.ac.uk/id/eprint/10181480/1/quepaxa.pdf) | Randomized asynchronous consensus with a fast common case | not-started |
| 2023 | VLDB | [Nezha: Deployable and High-Performance Consensus Using Synchronized Clocks](https://www.vldb.org/pvldb/vol16/p629-geng.pdf) | Deadline-ordered multicast with fast and slow commit paths | not-started |
| 2024 | NSDI | [SwiftPaxos: Fast Geo-Replicated State Machines](https://www.usenix.org/conference/nsdi24/presentation/ryabinin) | Replicas vote for their own order and then the leader's order | not-started |
| 2024 | VLDB | [Caerus: Low-Latency Distributed Transactions for Geo-Replicated Systems](https://www.vldb.org/pvldb/vol17/p469-hildred.pdf) | Partial sequence replication, deterministic merge and region recovery | not-started |
| 2024 | VLDB | [PALF: Replicated Write-Ahead Logging for Distributed Databases](https://www.vldb.org/pvldb/vol17/p3745-xu.pdf) | Election/log-reconfirmation separation and pending-follower role | not-started |
| 2025 | NSDI | [Pineapple: Unifying Multi-Paxos and Atomic Shared Registers](https://www.usenix.org/conference/nsdi25/presentation/bantikyan) | Logical timestamps integrate registers and Multi-Paxos | not-started |
| 2025 | SOSP | [Tiga: Accelerating Geo-Distributed Transactions with Synchronized Clocks](https://mpaxos.com/pub/tiga-sosp25.pdf) | Clock-based unified consensus and concurrency control | existing-counterexample |
| 2025 | VLDB | [Cabinet: Dynamically Weighted Consensus Made Fast](https://www.vldb.org/pvldb/vol18/p1439-zhang.pdf) | Dynamic weighted consensus responds to node speed | not-started |
| 2025 | VLDB | [FLEET: High-Performance Durable Replicated State Machines using Scattered and Coordinated Log Entries](https://www.vldb.org/pvldb/vol18/p1522-fan.pdf) | Combines synchronous scattered-entry persistence and asynchronous ordered logging | not-started |
| 2025 | VLDB | [HoliPaxos: Towards More Predictable Performance in State Machine Replication](https://www.vldb.org/pvldb/vol18/p2505-charapko.pdf) | Changes SMR failure detection, leadership transfer and log reclamation around MultiPaxos | not-started |
| 2025 | VLDB | [The LAW theorem: Local Reads and Linearizable Asynchronous Replication](https://www.vldb.org/pvldb/vol18/p2831-giortamis.pdf) | Eager and lazy read protocols, including changes to Raft and ZAB | not-started |
| 2026 | OSDI | [Bodega: Localized Linearizable Reads at Anywhere Anytime via Roster Leases](https://www.usenix.org/conference/osdi26/presentation/hu-guanzhou) | Roster leases permit local linearizable reads across responders | not-started |
| 2026 | OSDI | [Jetpack: Consensus Made Generally Fast](https://www.usenix.org/conference/osdi26/presentation/tang) | Composable one-RTT fast path across host protocols | conditional-agreement-execution-consistency-linearizability-proved; host-refinement-open |
| 2026 | SIGMOD | [Scalable Leader Leases For Multi Consensus Groups in CockroachDB](https://assets.ctfassets.net/00voh0j35590/2EHUM3hbvPrvrYle4IAB5c/f5ad2be3b27726d04715e40785dd086c/leader-leases-paper-2.pdf) | Raft leader fortification with cluster-wide failure detection | not-started |
| 2026 | SIGMOD | [LeaseGuard: Raft Leases Done Right](https://arxiv.org/abs/2512.15659) | Raft log entries establish leases and improve failover | not-started |
| 2026 | SIGMOD | [RIOT: Replicated Independently-Ordered Transactions](https://jimwebber.org/publication/2026-sigmod/) | Generalized consensus over independently ordered DAG entries | not-started |
| 2026 | VLDB | [Orca: Flexible Quorums Meet Dynamic Quorums](https://www.vldb.org/pvldb/vol19/p3565-dharmawan.pdf) | Raft-style replication with flexible and dynamic quorums | not-started |

## Proof obligations and evidence

These are targets for formalization. An obligation listed here is not a proved theorem. Existing repository evidence has not been rerun unless its report explicitly says so.

### om-2004

Om. Conditional quorum intersection; probabilistic safety boundary; lease graph; concurrent reconfiguration.

Model status: `not-started`. Source review: `abstract-and-selected-protocol-sections`.

The witness configuration deliberately permits a small probability of inconsistency. Unconditional agreement is not claimed by the authors; model the witness assumption or analyze probability of violation.

### chain-2004

Chain Replication. FIFO delivery; head/internal/tail failure; transfer; master refinement.

Model status: `abstract-model`. Source review: `section-3.1`.

Local files: [src/protocol/ChainReplication/paper_model.rs](../../src/protocol/ChainReplication/paper_model.rs), [models/non_bft/chain_replication/ChainReplication.tla](../../models/non_bft/chain_replication/ChainReplication.tla), [docs/non-bft-consensus/chain-replication.md](../../docs/non-bft-consensus/chain-replication.md).

### mencius-2008

Mencius. Coordinated Paxos; skip acceleration; recovery; prefix execution.

Model status: `abstract-single-instance-model`. Source review: `section-4.2`.

Local files: [src/protocol/Mencius/instance.rs](../../src/protocol/Mencius/instance.rs), [models/non_bft/mencius/CoordinatedPaxos.tla](../../models/non_bft/mencius/CoordinatedPaxos.tla), [docs/non-bft-consensus/mencius.md](../../docs/non-bft-consensus/mencius.md).

### gaios-2011

Gaios / SMARTER reads. Read freshness across elections; execution barrier; recovery; membership change.

Model status: `not-started`. Source review: `abstract-and-selected-protocol-sections`.

Include the new benign-fault read protocol. The paper also detects selected hardware corruptions and converts them to stopping failures; no arbitrary-Byzantine tolerance theorem is included.

### corfu-2012

CORFU. Per-position agreement; sealing; concurrent reconfiguration.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### epaxos-2013

EPaxos. Fast/slow/recovery agreement; dependency coverage; execution order.

Model status: `existing-models-need-version-audit`. Source review: `abstract-or-protocol-description`.

Local files: [src/protocol/EPaxos/epaxos.rs](../../src/protocol/EPaxos/epaxos.rs), [src/protocol/EPaxos/star/model.rs](../../src/protocol/EPaxos/star/model.rs), [docs/epaxos-safety-audit.md](../../docs/epaxos-safety-audit.md), [docs/epaxos-star-proof.md](../../docs/epaxos-star-proof.md).

### replicated-commit-2013

Replicated Commit. Phase-one elision assumptions; commit agreement; recovery.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### specpaxos-2015

Speculative Paxos. Speculation validation; rollback; view changes; multicast disorder.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### tapir-2015

IR / TAPIR. IR consensus result agreement; merge; recovery; transaction refinement.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### janus-2016

Janus. Dependency agreement; recovery; deterministic graph execution.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### nopaxos-2016

NOPaxos. Gap agreement; view/session change; execution prefix.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### eris-2017

Eris. Drop/undrop promises; per-shard prefix; cross-shard agreement; view and epoch changes.

Model status: `not-started`. Source review: `abstract-and-selected-protocol-sections`.

### netchain-2018

NetChain. Sequence/version checks; switch failures; master configurations.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### saucr-2018

SAUCR. Failure-asynchrony assumption; mode transition; recovery durability.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### dpaxos-2018

DPaxos. Quorum intersection; object migration; leader changes.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### parallelraft-2018

ParallelRaft. Dependency look-back; holes; election and recovery.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### curp-2019

CURP. Witness recovery; noncommuting requests; primary failover.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### gpac-2019

PAC / G-PAC. Cross-group decision agreement; validity; failure recovery.

Model status: `recovery-witness-model`. Source review: `algorithm-3-and-2021-erratum`.

Local files: [models/non_bft/gpac/PACRecovery.tla](../../models/non_bft/gpac/PACRecovery.tla), [models/non_bft/gpac/PACOriginal.cfg](../../models/non_bft/gpac/PACOriginal.cfg), [docs/non-bft-consensus/gpac-recovery.md](../../docs/non-bft-consensus/gpac-recovery.md).

### flair-2020

FLAIR. Read barrier; overlapping writes; switch failure; leader changes.

Model status: `not-started`. Source review: `abstract-and-selected-protocol-sections`.

### gryff-2020

Gryff. Register/consensus interaction; read-modify-write linearizability.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### pando-2020

PANDO. Read/write quorum intersection; recoverability; concurrent conditional writes; incomplete writes.

Model status: `not-started`. Source review: `abstract-and-selected-protocol-sections`.

### scalog-2020

Scalog. Cut agreement; durability before ordering; shard reconfiguration.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### copilot-2020

Copilot. Agreement under concurrent pilots; takeover; dependency execution.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### delos-2020

VirtualLog / Loglets. Sealing; loglet transitions; composed log prefix.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### mu-2020

Mu. Permission fencing; overlapping leaders; log recovery and reclamation.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### harmonia-2020

Harmonia. Read linearizability; in-flight writes; switch and leader failure.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

PVLDB 13 publication in 2019; listed under its VLDB 2020 conference edition.

### mongo-2021

MongoDB pull-based Raft. Election freshness; rollback; chained pulls; commit preservation.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### toq-epaxos-2021

TOQ-EPaxos. Ordering policy refinement; skew; recovery interaction.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### pigpaxos-2021

PigPaxos. Origin-preserving aggregation; distinct voter counting; relay failure.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

Final title and venue verified against the official SIGMOD 2021 accepted list. arXiv:2003.07760v2 is titled Scaling Strongly Consistent Replication; reconcile versions before modeling.

### rabia-2021

Rabia. Version/errata audit; weak multivalued consensus; probabilistic progress.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### skyros-2021

Skyros. Durability before order; read barriers; failover; client-visible safety.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### compartmentalized-2021

Compartmentalized MultiPaxos. Ballot/slot identity across proxies; batching; independent role failure.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### gpac-errata-2021

PAC / G-PAC corrected. PAC and sharded G-PAC agreement across recovery; original counterexample regression.

Model status: `recovery-witness-model`. Source review: `complete-erratum`.

Local files: [models/non_bft/gpac/PACRecovery.tla](../../models/non_bft/gpac/PACRecovery.tla), [models/non_bft/gpac/PACCorrectedReplay.cfg](../../models/non_bft/gpac/PACCorrectedReplay.cfg), [docs/non-bft-consensus/gpac-recovery.md](../../docs/non-bft-consensus/gpac-recovery.md).

### netlr-2022

NetLR. Network ordering; membership fencing; incomplete writes; switch fault assumptions.

Model status: `not-started`. Source review: `abstract-and-selected-protocol-sections`.

### hydra-2023

Hydra SMR. Timestamp order; drop detection; idle sequencers; failover.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### quepaxa-2023

QuePaxa. Races; rounds; fast/fallback agreement; randomized liveness.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### nezha-2023

Nezha. Deadline misses; fast/slow quorum agreement; view recovery.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

PVLDB 16(4), published December 2022; presented at VLDB 2023. Conference year used for grouping.

### swiftpaxos-2024

SwiftPaxos. Two-vote consistency; conflict order; recovery.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### caerus-2024

Caerus. Merge agreement; quorum recovery; preserved committed positions; serializability.

Model status: `not-started`. Source review: `abstract-and-selected-protocol-sections`.

PVLDB 17(3), 2023 publication; listed under VLDB 2024.

### palf-2024

PALF. Reconfirmation; explicit replication results; mirrored groups.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### pineapple-2025

Pineapple. Operation-type ordering; register writeback; nonblocking execution.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### tiga-2025

Tiga. Cross-shard recovery; completed-result preservation; serializability.

Model status: `existing-paper-model`. Source review: `abstract-or-protocol-description`.

Local files: [src/protocol/Tiga/normal.rs](../../src/protocol/Tiga/normal.rs), [src/protocol/Tiga/recovery.rs](../../src/protocol/Tiga/recovery.rs), [docs/tiga-safety-audit.md](../../docs/tiga-safety-audit.md).

### cabinet-2025

Cabinet. Intersection across weight changes; election; reconfiguration.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### fleet-2025

FLEET. Durable agreement; all-node crash recovery; log reconstruction; pre-apply correctness.

Model status: `not-started`. Source review: `abstract-and-selected-protocol-sections`.

### holipaxos-2025

HoliPaxos. Election progress under partial partitions; safe pruning and snapshot recovery.

Model status: `not-started`. Source review: `abstract-and-selected-protocol-sections`.

The underlying Paxos agreement core is unchanged. Included for protocol-level election and log-recovery changes; this classification would change under a restriction to new voting rules only.

### law-2025

Almost-local reads. Read batching boundaries; synchronization barriers; real-time ordering; protocol-specific refinement.

Model status: `not-started`. Source review: `abstract-and-selected-protocol-sections`.

### bodega-2026

Bodega. Clock assumptions; roster intersection; interfering writes; roster change.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

### jetpack-2026

Jetpack. Recovery safety; fast/base ordering agreement; execution consistency and linearizability; host-contract refinement.

Model status: `recovery-and-client-history-with-explicit-host-contracts`. Source review: `full-paper-sections-3.3-4.3-B.2-B.3-and-pinned-artifact`.

Verus proves recovery safety, conflicting-command order agreement, matching execution results and a real-time-respecting sequential completion for every finite client history. The composition assumes a common durable executed base prefix, proposer ordering, fenced prefix-preserving host recovery and correct fast-execution state. Independent commands must preserve state and outputs; reads/exchanges on registers instantiate this contract. Logical removal of executed fast commands is modeled. Host/implementation refinement, physical garbage collection, membership changes, retry/deduplication and liveness remain open.

Local files: [src/protocol/Jetpack/recovery.rs](../../src/protocol/Jetpack/recovery.rs), [src/protocol/Jetpack/view_change.rs](../../src/protocol/Jetpack/view_change.rs), [src/protocol/Jetpack/application.rs](../../src/protocol/Jetpack/application.rs), [src/protocol/Jetpack/ordering.rs](../../src/protocol/Jetpack/ordering.rs), [src/protocol/Jetpack/execution.rs](../../src/protocol/Jetpack/execution.rs), [src/protocol/Jetpack/registers.rs](../../src/protocol/Jetpack/registers.rs), [src/protocol/Jetpack/execution_witness.rs](../../src/protocol/Jetpack/execution_witness.rs), [docs/non-bft-consensus/jetpack.md](../../docs/non-bft-consensus/jetpack.md), [docs/non-bft-consensus/evidence/jetpack-verification.log](../../docs/non-bft-consensus/evidence/jetpack-verification.log), [docs/non-bft-consensus/evidence/jetpack-integrated.log](../../docs/non-bft-consensus/evidence/jetpack-integrated.log).

### fortification-2026

Leader leases / fortification. Support withdrawal; leadership fencing; lease transfer.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

Full industry paper in SIGMOD Companion 2026, not a workshop or demo.

### leaseguard-2026

LeaseGuard. Election completeness; clock bounds; read/write failover optimizations.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

PACMMOD 4(1), article 49, April 2026; SIGMOD 2026. The linked December 2025 preprint records this journal reference. Pin final version before modeling.

### riot-2026

RIOT. DAG agreement; conflict order; one/two-phase recovery.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

SIGMOD Companion 2026, full industry paper, pp. 464-476.

### orca-2026

Orca. Temporal failure bound; voting-set changes; election intersection.

Model status: `not-started`. Source review: `abstract-or-protocol-description`.

## Unresolved candidates

| Paper | Venue/year | Reason |
|---|---|---|
| [Consensus in a Box: Inexpensive Coordination in Hardware](https://www.usenix.org/conference/nsdi16/technical-sessions/presentation/istvan) | NSDI 2016 | Separate protocol changes from hardware implementation of ZAB. |
| [Fine-Grained Replicated State Machines for a Cluster Storage System](https://www.usenix.org/system/files/nsdi20spring_liu-ming_prepub_0.pdf) | NSDI 2020 | Authors distinguish their storage co-design contribution from consensus novelty; audit whether recovery modifications meet the protocol-change criterion. |
| [Using Paxos to Build a Scalable, Consistent, and Highly Available Datastore](https://www.vldb.org/pvldb/vol4/p243-rao.pdf) | VLDB 2011 | Audit whether elastic-group changes are new agreement/reconfiguration rules or use established Paxos. |
| [Amazon Aurora: On Avoiding Distributed Consensus for I/Os, Commits, and Membership Changes](https://doi.org/10.1145/3183713.3196937) | SIGMOD 2018 | Distinguish novel membership and quorum protocol from a storage design using an existing metadata consensus service. |
| [Building a Replicated Logging System with Apache Kafka](https://www.vldb.org/pvldb/vol8/p1654-wang.pdf) | VLDB 2015 | Audit in-sync replica membership, acknowledgment and leader-election changes; separate consistency modes. |
| [Tunable Consistency in MongoDB](https://www.vldb.org/pvldb/vol12/p2071-schultz.pdf) | VLDB 2019 | Determine whether it introduces protocol rules beyond the NSDI 2021 protocol account. |
| [Ocean Vista: Gossip-Based Visibility Control for Speedy Geo-Distributed Transactions](https://www.vldb.org/pvldb/vol12/p1471-fan.pdf) | VLDB 2019 | Check whether failure recovery changes consensus or only transaction visibility above it. |
| [Dandelion: Smaller Clusters, Bigger Speeds—Distributed Transactions Redefined](https://www.vldb.org/pvldb/vol18/p1264-katsarakis.pdf) | VLDB 2025 | Protocol novelty needs full-paper screening for consensus versus transaction concurrency control. |
| [Waverunner: An Elegant Approach to Hardware Acceleration of State Machine Replication](https://www.usenix.org/conference/nsdi23/presentation/alimadadi) | NSDI 2023 | Separate hardware implementation from a changed consensus protocol. |
| [No compromises: distributed transactions with consistency, availability, and performance](https://www.microsoft.com/en-us/research/publication/no-compromises-distributed-transactions-with-consistency-availability-and-performance/) | SOSP 2015 | Audit RDMA replication/reconfiguration changes against consensus-use exclusion. |

## Screened exclusions

| Paper | Venue/year | Reason |
|---|---|---|
| [Scalable Consistency in Scatter](https://homes.cs.washington.edu/~tom/pubs/scatter.pdf) | SOSP 2011 | Section 4 composes 2PC with Paxos and describes standard Paxos extensions. No distinct new consensus protocol identified under the requested narrow scope. |
| [PolyBase: Adapting to Data Affinity Changes in Geo-Replicated Database via Row-Level Consensus-Group Affiliation Re-Assignment](https://www.vldb.org/pvldb/vol18/p702-ruan.pdf) | VLDB 2025 | The abstract explicitly runs row reassignment over unchanged Paxos; database placement is outside scope. |
| [LEGOStore: A Linearizable Geo-Distributed Store Combining Replication and Erasure Coding](https://www.vldb.org/pvldb/vol15/p2201-zare.pdf) | VLDB 2022 | New read/write-register reconfiguration, based on ABD and coded atomic storage; no new consensus or general SMR protocol identified. Linearizable registers alone do not implement consensus. |
| [XLL: Cross-Layer Logging for Data Deduplication in Consensus-Based Storage](https://www.usenix.org/conference/nsdi26/presentation/shawger) | NSDI 2026 | Abstract describes local logging and crash recovery beneath TiKV, not changed consensus agreement/election rules; provisional abstract-level exclusion. |

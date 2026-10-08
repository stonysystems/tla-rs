# Handwritten TLAPS-Bench ports

This batch rewrites all nine current TLAPS-Bench models as handwritten tla-rs
state machines. All nine models have proved benchmark goals: thirty-eight invariants and
nine liveness properties. Low-level ZooKeeper has both leadership goals proved.
The complete current collection has
47 invariants and nine liveness goals. FLASH has all 15 of its benchmark goals
proved, seven safety invariants and eight liveness properties. The TLB model
also has both its safety and liveness goals proved. OpenAddressing has all five
safety goals proved. All eight etcd targets are resolved: six invariants are
proved and two have checked reachable counterexamples in the pinned source.
HashiCorp Raft has all six safety goals proved. Zab has all nine safety goals
proved. Cahill SSI has its serializability theorem proved. MongoDB has its
snapshot-isolation theorem proved. Low-level ZooKeeper has four reachable
violations and three remaining goals whose original source expressions fail to
evaluate on a reachable invalid history index. Evaluation errors count as
neither proofs nor Boolean invariant violations.

The [coverage report](../reports/tlaps_bench_manual/README.md) lists all nine
models. Its [JSON file](../reports/tlaps_bench_manual/results.json) records every
goal, source hashes, proof hashes, the Verus version, and the verification command.
Published command metadata uses `verus` in place of the machine-specific
executable path. Proof files and verifier output retain their original hashes.
The source is pinned to TLAPS-Bench
[`ffa3e31da28f960b70d8c5d44f2735e75d6edcac`](https://github.com/specula-org/TLAPS-Bench/tree/ffa3e31da28f960b70d8c5d44f2735e75d6edcac).
Only `benchmark/problem-sets.json`'s `current` collection contributes to the score.

| Model | Proved benchmark goals | Verus theorem |
|---|---|---|
| Low-level ZooKeeper | `Leadership1`, `Leadership2` | `zookeeper_leadership::benchmark_leadership1`, `benchmark_leadership2` |
| OpenAddressing | `CompleteAsSafety`, `Sorted` | `open_addressing_proof::benchmark_safety` |
| OpenAddressing | `Contains`, `Consistent`, `Duplicates` | `open_addressing_safety::benchmark_safety` |
| FLASH | `TypeCorrect` | `flash_proof::type_correct_always` |
| FLASH | `Lemma_1_Correct`, `MemDataCorrect` | `flash_coherence::benchmark_coherence` |
| FLASH | `Lemma_2_Correct`, `Lemma_3_Correct`, `Lemma_4_Correct` | `flash_control::benchmark_control` |
| FLASH | `CacheDataCorrect` | `flash_shared::cache_data_correct` |
| FLASH | `RpProgressCorrect`, `WbProgressCorrect`, `ShWbProgressCorrect`, `NakcProgressCorrect` | `flash_liveness::benchmark_progress` |
| FLASH | `InvProgressCorrect` | `flash_invalidation::inv_progress_correct` |
| FLASH | `ReqProgressCorrect`, `UniProgressCorrect` | `flash_requests::request_progress_correct` |
| FLASH | `DirProgressCorrect` | `flash_directory::dir_progress_correct` |
| Ivy TLB | `Safety`, namely `[]NoError` | `tlb_proof::safety` |
| Ivy TLB | `Liveness`, namely `NonStarvation` | `tlb_progress::liveness` |
| etcd Raft | `MoreThanOneLeader` | `etcd_election::more_than_one_leader_correct` |
| etcd Raft | `ElectionSafety` | `etcd_origins::election_safety_correct` |
| etcd Raft | `LogMatching` | `etcd_logs::log_matching_correct` |
| etcd Raft | `CommittedIsDurable` | `etcd_durability::committed_is_durable_correct` |
| etcd Raft | `LogInv`, `QuorumLog` | `etcd_safety::benchmark_safety` |
| Zab | `Leadership1`, `Leadership2` | `zab_elections::benchmark_leadership` |
| Zab | `PrefixConsistency`, `Agreement`, `TotalOrder`, `GlobalPrimaryOrder` | `zab_commit_safety::benchmark_safety` |
| Zab | `PrimaryIntegrity` | `zab_primary_barrier::benchmark_primary_integrity` |
| Zab | `Integrity` | `zab_integrity::benchmark_integrity` |
| Zab | `LocalPrimaryOrder` | `zab_proposal_order::benchmark_local_order` |
| HashiCorp Raft | `ConfigurationSafetyCorrect` | `hashicorp_config::configuration_safety_correct` |
| HashiCorp Raft | `LeaderCompletenessCorrect`, `StateMachineSafetyCorrect`, `CommittedEntriesPreservedCorrect`, `LogMatchingCorrect`, `ElectionSafetyCorrect` | `hashicorp_safety::benchmark_safety` |
| Cahill SSI | `CahillSerializableCorrect` | `cahill_cycle_search::benchmark_serializable` |
| MongoDB | `SnapshotIsolationCorrect` | `mongodb_snapshot_isolation::benchmark_snapshot_isolation` |

The modules live in [src/protocol/TLAPSBench](../src/protocol/TLAPSBench/mod.rs).
They use the project's spec/proof state-machine conventions, logical records,
Verus collections, and the existing `common/logic/temporal_s.rs` behavior type.
They are mathematical protocol models, with no executable implementation or
networking changes. No transpiler participates, and `src/generated/` is untouched.

The standalone [TLAPS-Bench workflow](../.github/workflows/tlaps-bench.yml)
runs every Sunday at 04:17 UTC against both pinned and latest rolling Verus.
It can also be started manually from GitHub Actions, or with
`gh workflow run tlaps-bench.yml --repo stonysystems/tla-rs`.
Each job checks `--no-cheating`, uses the default resource limit, rejects
automatically chosen triggers, and uploads its verification log.
The benchmark stays outside the main crate and does not run in PR/push CI,
the daily latest-Verus workflow, or the Verita entry point. This avoids adding
roughly 15 minutes of benchmark verification to routine checks.

Every successful safety theorem has an initialization proof, a preservation proof
for every modeled transition, and induction at an arbitrary nonnegative index of
an infinite behavior. Stuttering is allowed. There is no configured bound on
execution length, integer values, log length, or the number of participants.
Source finiteness assumptions determine whether a domain uses `Set` or `ISet`.
The initialization witnesses also establish nonempty parameter choices and
enabled protocol actions.

All imported handwritten proofs pass one standalone Verus invocation with
`--no-cheating`. The recorded function count and verifier output are in the coverage report.
Opaque spec functions retain checked definitions; they control unfolding rather
than replacing a proof with an assumption. The usual Verus/vstd and SMT trust
boundary remains. The correspondence between the original TLA+ and handwritten
models has been reviewed, but it is not a machine-checked language-refinement
theorem. Abstract identifiers use integers, and string labels use Rust enums.

OpenAddressing retains every writer and eviction action, the wait counter,
probe/hash arithmetic, history, and the subroutine stack. `Cell::Empty` represents
the noninteger empty sentinel. Table positions remain one-based; sequence and
stack positions become zero-based. External sequences contain integers because
the source only appends nonempty table values. The constant procedure tag on
stack frames is omitted. The sorting proof establishes pairwise strict order,
which implies the source's adjacent-element order. The completion proof tracks
valid fingerprints and stack return locations. Writer fairness can be dropped
for all five safety goals.

The remaining OpenAddressing proofs split on the source's integer hash scale.
A positive scale gives distinct fingerprints distinct home slots. A zero scale
gives every fingerprint the same home slot. This dichotomy follows from the
source assumptions and covers every permitted fingerprint set and table size.
The zero-probe-length case is handled separately. No configuration bound or
extra hash assumption is added to the final theorem.

In the shared-home case, the wait counter proves exclusive access during
eviction. Probe certificates track each thread's scanned prefix, reusable
position, and absence from external storage. The occupied table positions form
a prefix of the probe sequence. During eviction, the proof excludes the current
hole from the abstract table and includes the value in the eviction temporary.
Shifting moves a value into the hole and makes its previous position the new
hole. This preserves membership and uniqueness. External merging retains every
old entry and every newly marked value. Positive table entries remain absent
from external storage until marked. These strengthenings are initialized and
preserved by every source action, including concurrent insertions and stuttering.

FLASH retains every rule in `FlashWithMutexModel.Next`. Related rules share an
action variant and a boolean or destination parameter. For example,
`LocalForward` covers `PI_Local_Get_Get` and `PI_Local_GetX_GetX`, while
`LocalGrant` covers `NI_Local_Get_Put` and the three branches of
`NI_Local_GetX_PutX`. `ReceivePut` and `ReceivePutX` retain the separate home and
remote updates. Undefined is `-1`, excluded from the node and data domains;
these domains remain disjoint. The type proof strengthens `TypeOK` with valid
data in occupied caches and data-carrying messages.

FLASH safety uses several inductive strengthenings. Exclusive ownership moves
between a cache and an in-flight grant, writeback, shared writeback, or home
read reply. The owner carries the latest stored data. Directory serialization
permits at most one forwarded request, terminal reply, negative acknowledgment,
or invalidation round. Shared caches and unconsumed read replies are registered
in the directory or covered by an invalidation. Their data equals the current
value outside an invalidation round and the saved previous value during one.
Each strengthening has initialization and preservation proofs for every action.

The temporal model retains the six kinds of action groups in
`FlashWithMutexDefs.Fairness`. All eight progress proofs use exactly their weak
fairness, over infinite behaviors. Invalidations decrease a rank through
`Inv`, `Ack`, and `None`. Unicast requests decrease a rank through directory
handling, forwarding, replies, and consumption; replacement progress releases
the guard on read handling. Processor request completion follows from the
request/message correspondence. Directory progress follows terminal replies
and uses the decreasing cardinality of the finite invalidation set. No
fairness is added for individual actions within a source action group.

The TLB port retains all 27 processor actions and the source's `SafetySpec`.
Its inductive invariant connects page-map ownership, action-lock ownership,
sent invalidation requests, quiesced processors, and stale-cache states. The
responder acquisition action retains the source's page-map-lock guard and its
assertion that the action lock was free. `Processor`, `PMap`, and `PageEntry`
may be infinite. No finite-domain assumption was added. The liveness proof
establishes that only finitely many processors have booted at each finite index
of an infinite behavior, so each shootdown has a finite work set. Action-lock
owners eventually release their locks. A waiting initiator owns the target's
page map, preventing competing acquisition while it waits for its action lock.
The sending loop decreases its work-set size and control-state rank. Relevant
processors eventually remain inactive while the page map is locked, allowing
the quiescence loop to finish. Every page-map owner then releases its lock.
The proof uses exactly the source's weak fairness for each processor and strong
fairness for boot, page-map acquisition, and responder acquisition. It proves
`Spec => NonStarvation` at every behavior index.

The etcd port retains pending and delivered message bags, their multiplicities,
`Ready`, persistent state, restart rollback, all receive branches, heartbeats,
snapshots, duplication, and loss. The source initializes its configuration to
`<<InitServer, {}>>`, has no configuration-changing action in `Next`, and keeps
learners, `pendingConfChangeIndex`, and `reconfigCount` constant. The port stores
these static choices in `Constants` or omits their redundant fields. Every
source client request is `ValueEntry(0)`, so log entries need only the term;
the other entry fields reconstruct uniquely. A passive `votes` history records
positive responses released by `Ready`. No action guard reads this history.
Persistence and vote consistency prove uniqueness of a leader in a term.
The source names this goal `MoreThanOneLeader`. Its separate `ElectionSafety`
goal is now proved by tracking elected origins of entries in live logs, disk
logs, pending messages, and delivered messages. Persisted vote certificates
identify each origin. While its leader remains in that term, every copied
current-term entry is still present at the same index in that leader's log.
A proof-only history of leader-created logs now proves `LogMatching`. Every live
log and disk log is a prefix of a history entry; every append message is a
segment of one. Canonical logs agree wherever their entry terms agree. The
history adds no protocol action or guard.

The continued etcd proof effort checks append-message persistence in
`etcd_sent.rs`, commit-counter persistence in `etcd_persistence.rs`, and delayed
acknowledgments in `etcd_acknowledgments.rs`. Released append requests retain a
segment of their sender's persisted log while its durable term stays unchanged.
Persisted commit counters never decrease. An acknowledgment at the receiving
leader's term is bounded either by that leader's persisted log or by the
responding server's persisted commit counter. This follows the source's special
response rule for a request below a follower's existing commit index.

These facts are initialized, preserved, and lifted to every behavior index.
They imply that any commit advancement beyond a leader's persisted log would
require a quorum that already persisted commit counters at least as high.
`etcd_commit_history.rs` records the actual term, log prefix, and acknowledging
quorum for each direct leader decision. Every nonzero live or persisted commit
counter, and every commit index advertised in an append request, traces to one
of those decisions at an equal or lower term. `etcd_ack_history.rs` carries that
provenance through acknowledgments and leader match indices. It proves that
advancing beyond a leader's persisted log would require an earlier recorded
decision at an equal or lower term with at least as long a prefix.

`etcd_decision_owners.rs` strengthens that result to a strictly lower term:
a leader cannot forget its own decisions while remaining leader in their term.
`etcd_prefixes.rs` proves that historical logs are closed under prefixes and
that histories ending in the same term agree up to the shorter length.
`etcd_candidates.rs` proves that a campaign advertises only entries from earlier
terms and retains that advertised log while it remains a candidate in the term.

The trace proofs in `etcd_transmissions.rs` recover actual message-creation and
`Ready` steps. An older message was created before a subsequently released
higher-term vote was granted, even when message release occurred after the
grant. `etcd_vote_witness.rs` recovers the actual log comparison behind every
released vote counted by a candidate. `etcd_match_witness.rs` recovers creation,
release, and reception of the acknowledgment behind a current-term match index;
the match cannot come solely from the value initialized at leader election.

`etcd_retention.rs` checks prefix retention across conflict truncation, append,
crash, and persistence under a compatibility premise for applicable append
requests. It covers both acknowledgment-release orders relative to a later
vote grant. `etcd_history_trace.rs` constructs one canonical passive history
along a behavior and recovers the source step for every direct decision and
created log. `etcd_leader_trace.rs` proves that two observations of a leader in
the same term belong to one continuous leadership interval.

`etcd_ack_prefixes.rs` connects successful acknowledgments to the exact log
prefixes they certify. The source's special response below an existing commit
index instead traces to an earlier decision in a strictly lower term.
`etcd_election_prefixes.rs` establishes compatible append histories between
acknowledgment creation and a later vote, using completeness of earlier-term
leaders. Same-term packets are comparable by their unique leader's log history.
Packets from the election term cannot precede that candidate's election.

`etcd_completeness.rs` discharges the earlier-term premise by induction on
election terms. Intersecting a decision quorum and an election quorum supplies
a voter that acknowledged the decided prefix before granting its later vote.
The voter retains that prefix, and the voting log comparison transfers it to
the candidate. The argument covers decisions before or after the later
leader's election within any finite behavior prefix. It adds no timing bound
or protocol assumption. This historical completeness theorem uses the term of
the direct commit decision. It does not replace the benchmark's different
`LeaderCompleteness` target.

`etcd_durability.rs` applies historical completeness to prove the benchmark's
`CommittedIsDurable` at every behavior index. An advancing leader cannot rely
on an older decision to commit past its persisted log, since that decision
contains only older-term entries. Election and persistence steps preserve the
bound as well. The earlier conditional lemmas' premises are now discharged in
this proof; the completed benchmark goal contributes one invariant to the count.
No protocol action or guard reads either history.

`etcd_stable_prefixes.rs` proves that every acknowledging member of a direct
decision's quorum retains the decided prefix in both its live and disk logs.
The proof uses historical completeness to establish compatibility of future
append messages, including same-term messages created before the decision.
It covers arbitrary subsequent restarts and term changes.

`etcd_heartbeat.rs` connects a heartbeat's advertised commit index to the
recipient's earlier successful acknowledgment. A normal acknowledgment
certifies a log prefix that remains protected. The source's commit-counter
fallback instead certifies a persisted counter that cannot decrease. This
distinction handles delayed acknowledgments and prevents a heartbeat from
advancing the recipient's commit index beyond its retained log.

`etcd_committed_prefixes.rs` proves that every live and persisted commit prefix
is a prefix of an actual direct decision, and that commit indices stay within
their respective logs. It covers ordinary append replies, heartbeats,
conflict truncation, leader decisions, persistence, and restart. The final
`etcd_safety::benchmark_safety` theorem proves `LogInv` because all direct
decisions are prefix-compatible. It proves `QuorumLog` by intersecting any
quorum with the retained quorum for the decision covering a node's commit
prefix. Both properties hold at every index of an arbitrary behavior.

The `LeaderCompleteness` target
is false as stated in the pinned benchmark. The source compares a current
leader's term with an entry's creation term even when the entry is committed
later. In a checked 47-transition execution, server 1 creates an uncommitted
term-1 entry; server 2 becomes a term-2 leader and creates a conflicting entry;
then server 1 wins term 3, replicates its term-1 entry plus a term-3 entry to
server 3, and commits both. Server 2 remains an isolated term-2 leader with
its conflicting entry, violating the target.

The [source counterexample](../reports/tlaps_bench_manual/etcd_counterexample/counterexample.log)
uses byte-identical copies of the pinned model and definitions. The
[replay](../reports/tlaps_bench_manual/etcd_counterexample/replay.log) checks all
48 scheduled states, the final witness, the original `Spec`, and eventual
arrival at the final state under the schedule's own fairness. That schedule
fairness selects a valid source behavior; the source protocol is unchanged.
The Verus certificate checks all 47 adjacent state pairs and constructs an
infinite source-model behavior by stuttering after the final state. It proves
the negation of the target at index 47 with `--no-cheating`. Its ground states
come from `scripts/build_tlaps_bench_etcd_counterexample.py`; every generated
edge is checked against the handwritten transition relation, so the generator
is not trusted.
Hashes and reproduction commands are in
[the counterexample record](../reports/tlaps_bench_manual/etcd_counterexample/results.json).
A corrected historical theorem would record the term when a prefix becomes
committed and require later elections to retain it, as the benchmark already
does for its separate HashiCorp model. Such a correction would change the
benchmark target, so it is not substituted or counted as a proof here.

The separate `MoreUpToDate` target is also false. Its comparison uses only the
last entry term and log length, without the term when an earlier entry becomes
committed. In a checked five-server execution, server 1 creates `[1]` in term 1,
and server 2 later creates the conflicting log `[2]` in term 2. Server 1 wins
term 3 with votes from servers 4 and 5, replicates `[1, 3]` to both, and commits
through index 2. It then sends a snapshot containing only the committed prefix
`[1]` to server 3. Server 2 remains isolated with `[2]`. Its last term is higher
than server 3's last term, but its log lacks server 3's committed prefix.

`etcd_uptodate_counterexample::counterexample` checks all 72 transitions and
constructs an infinite behavior by stuttering after state 72. TLC independently
replays the schedule against byte-identical pinned TLA+ source, checks the
original `Spec`, and confirms the final violation. Both certificates and their
hashes are recorded in the [up-to-date log counterexample evidence](../reports/tlaps_bench_manual/etcd_uptodate_counterexample/results.json).
The ground-state generator is `scripts/build_tlaps_bench_etcd_uptodate_counterexample.py`;
Verus checks its output against the handwritten model. Neither refutation counts
as a proved invariant. Both concern the stated property rather than disagreement
between committed logs.

HashiCorp Raft has all six safety goals proved. The port retains the runtime
model's single-server membership changes, split vote persistence, heartbeat and
replication behavior, leases, disk blocking, crashes, and passive election/commit
histories. Last and penultimate configuration indices are computed by recursion
over the log, equivalent to the source's maxima over configuration positions.
The configuration invariant bounds the committed configuration index between
the penultimate and latest indices, proving the benchmark's bound of one pending
configuration entry.

The five other goals share `hashicorp_safety::benchmark_safety`. Its only
premise is the protocol safety behavior specification. The proof establishes
leader uniqueness and direct-decision completeness together by induction over
terms, with an inner induction over election order in each term. A direct
decision is an actual leader commit advance backed by an acknowledgment quorum.
The induction includes decisions made later in the execution than an election;
it does not assume that lower-term decisions happen first.

Vote persistence and consistency hold through crashes, including a heartbeat
advancing the term while a vote write is pending. A passive history records self
votes and released responses. Each election has a majority certificate in the
configuration from its elected log. `hashicorp_election_trace` reconstructs the
actual voter comparison before response release. For deferred votes, the voter's
log stays unchanged until release even if its term advances. Protocol actions
do not read these proof histories.

`hashicorp_candidates` proves that a successful log comparison transfers a
decided prefix to the candidate, using uniqueness and completeness in earlier
terms. `hashicorp_eligibility` retains that prefix from the shared quorum
member's receipt to its vote check. For append traffic in the candidate's own
term, it uses completeness of leaders elected earlier in that term. This is why
the proof needs the inner election-order induction. An elected log is called
eligible when it contains lower-term decisions from configurations equal or
adjacent to its own, where adjacency means one single-server membership change.

`hashicorp_config_commit` and `hashicorp_config_barriers` trace each configuration
proposal to a direct commit by its creator in the same term and parent
configuration. That committed prefix includes every earlier configuration entry.
`hashicorp_config_adjacency` uses these prefixes to compare configuration
histories. After their common committed prefix, a competing branch or a second
intervening change would require a decision under a configuration adjacent to
the eligible candidate's, with an entry absent from that candidate. Eligibility
rules this out. The resulting adjacency is proved, not an additional restriction
on allowed election configurations.

`hashicorp_eligible_safety` then intersects the election quorums to prove
uniqueness. It also proves that an eligible elected log contains every lower-term
direct decision. Depending on the relative configuration terms, either a
configuration's creating leader already contains the decision by the outer
induction, or the configuration-history argument establishes the adjacency
needed by eligibility. The inner induction extends completeness through the
current term; the outer induction extends both uniqueness and completeness.

Supporting lemmas trace log entries to actual leader appends, prove ordered
positive log terms and continuous leadership within a term, connect every
acknowledgment to a receipt, and connect follower commits to direct decisions.
`hashicorp_safety_reduction` derives the benchmark's five state predicates from
these facts, including its passive commit/election histories. A finite bound
covering terms at any chosen behavior index is constructed from the finite
server set; there is no configured execution or term limit. Temporal induction
then establishes all five targets at every nonnegative behavior index.

The first-mismatch search in `merge` uses zero-based quantification for stable
SMT instantiation. `hashicorp_types::merge_correspondence` proves equality with
the original one-based search at every valid merge boundary. This changes
neither the append guards nor the transition relation.

Zab retains all 16 source actions, FIFO channels, quorum receipt records with
connected/disconnected status, restarts, proposal history, and epoch-leader
history. Source disjunctions that accept both a check and its negation remain
unconditional. In particular, the port does not add a validity guard to
`FollowerProcessCOMMITLD`. Epoch-history updates outside `1..MAXEPOCH` preserve
the map domain, matching TLA+ `EXCEPT`. The request value is one fixed arbitrary
parameter, as in the source's `CHOOSE`, rather than a fresh choice per request.
Both Zab leadership goals are proved by `zab_elections::benchmark_leadership`.
`Leadership1` excludes simultaneous synchronized or broadcasting leaders in the
same epoch. `Leadership2` excludes different leaders recorded in the history
for the same epoch, even when their leadership intervals do not overlap.

The proof uses the source's leader oracle: only its selected leader can accept
new connections. `zab_sessions` identifies each continuous leadership interval.
After a later interval starts at a different server, the earlier leader cannot
regain oracle selection while remaining leader, so its learner set only shrinks.

`zab_ce_trace` reconstructs the accepted-epoch snapshot behind each CE receipt,
including disconnected receipts. It also finds the original quorum used to
choose a proposed epoch, whose received values are all strictly below that
epoch. `zab_ae_trace` reconstructs each acknowledgment quorum member's accepted
epoch and membership in that leader's learner set. For two completed elections,
intersect the earlier interval's acknowledgment quorum with the later interval's
original CE quorum. The shared server's earlier acknowledgment must precede its
later CE snapshot: the reverse order would place it in both leaders' learner
sets after the older set could only shrink. Accepted-epoch monotonicity then
makes the later elected epoch strictly greater. No leadership uniqueness premise
is assumed.

`zab_connections` proves connection and channel structure through shutdowns,
timeouts, and reconnects. `zab_epochs`, `zab_phases`, and `zab_receipts` establish
epoch bounds, phase ordering, sender/receiver epoch agreement, and receipt
uniqueness. The phase proof includes the one-server case, which remains in
discovery. `zab_quorum_support` proves that after a CE quorum forms, a quorum
remains among the leader's learners and servers whose accepted epochs have
advanced beyond its own. These facts retain disconnected records rather than
replacing historical quorums with the current learner set.

`zab_sync` proves that a queued proposal either targets a follower already in
the sender's current epoch or follows a matching `NEWLEADER` message in the
FIFO queue. Connected epoch acknowledgments have the same guarantee. The proof
accounts for disconnecting receipt records, consuming synchronization messages,
and broadcasting the first new-leader history to a quorum.

`zab_log_math` and `zab_logs` prove that logs start with the bootstrap entry,
have increasing transaction identifiers, and are bounded by their server's
current epoch. Acknowledgment metadata updates preserve log contents. Broadcast
lookup returns the actual entry for the next counter, so it cannot depend on
an out-of-range sequence lookup.

`zab_epoch_origins` traces each nonzero current epoch to an active leader and
proves that repeated observations of one active leader in the same epoch belong
to one uninterrupted leadership interval. `zab_leader_logs` proves that the
leader only extends its history during that interval, using entries from its
current epoch. It also proves that a newly activated epoch has never been any
server's current epoch at an earlier time.

`zab_proposal_logs` connects queued `NEWLEADER` and `PROPOSAL` contents to the
sender's history. `zab_current_logs` proves that a server's nonzero-current-epoch
history is a synchronized prefix of its epoch leader's history, with any missing
suffix confined to that epoch. This is enough to show that an accepted proposal
appends at the same index as in the leader's history.

`zab_entry_origins` traces each non-bootstrap entry and its preceding prefix to
an active leader of the entry's epoch. The argument covers acknowledgment
snapshots, selected histories, synchronization messages, and metadata updates.
`zab_log_matching::historical_matching` then proves that two server histories,
even from different times, place equal transaction identifiers at the same index
and agree on the prefix through that index.

`zab_sync_prefixes` proves that queued synchronization histories include the
proposals and synchronization histories ahead of them in the FIFO queue. When
the receiver already has the message's epoch, the queued history extends the
receiver's current log. `zab_epoch_retention::between` uses this fact to prove
that a server retains its log prefix between any two observations with the same
current epoch, including across restarts and repeated synchronization.

`zab_history_trace` reconstructs the actual current epoch and complete history
behind each acknowledgment record, including disconnected records.
`zab_activation_logs::earlier_history` combines those snapshots with epoch
freshness to prove that a newly activated leader's selected history contains
only transactions from earlier epochs. The receipt-selection comparison and
the acknowledgment-prefix calculation are checked separately in
`zab_collections::selected_maximal` and `zab_log_math::ack_prefix`.

`zab_ack_epochs` proves epoch agreement for proposal and acknowledgment traffic.
`zab_ack_messages::stored_prefix` traces queued `ACK` and `ACKLD` messages to
actual sender histories. At that observation, the sender has accepted the
leader's epoch and stored the matching prefix. `zab_ack_certificates` extends
those witnesses to every acknowledgment recorded in an active leader's log.
`zab_sync_acks` proves that synchronization acknowledgments cover the entire
selected history. `zab_commit_certificates::new_commit` then proves that every
new leader commitment names an existing entry backed by a quorum of those
storage witnesses. This theorem concerns commitment transitions, not inherited
commit indices after history replacement.

`zab_discovery_logs::report_witness` places each election history report at an
actual observation after the voter accepted the new epoch. This also covers the
leader's own report: its history stays unchanged during discovery, so its report
can be observed after the new accepted epoch is chosen.

`zab_certified_retention::higher_epoch` proves that a prefix certified by an
earlier quorum appears in every server history whose current epoch is greater.
The proof intersects the acknowledgment quorum with the election's history
reports. Accepted-epoch monotonicity places the old acknowledgment before the
new report. Retention within an epoch handles an equal-epoch report; induction
over current epochs handles a later-epoch report. The source's maximal-history
selection preserves the prefix in both cases. A second induction over execution
steps propagates it through synchronization messages and receiver histories.
The earlier-epoch premise used inside the selection lemma is discharged by
this outer induction.

`zab_certified_safety::quorum_safety` proves that any two quorum-certified
prefixes agree wherever both are defined. This applies across historical times
and epochs. These are supporting theorems used in the completed benchmark proofs.

`zab_queue_math` defines logical replay of queued log updates. The replay is
proof machinery and adds no protocol transitions. `zab_queue_prefix` proves
that this replay is a prefix of the sender's log, missing only current-epoch
entries. `zab_queue_coverage` proves that it covers every counter already
broadcast to a connected follower. `zab_receipt_links` connects the source's
synchronization receipts to these live channels. `zab_broadcast_commits` bounds
advertised commits by either an earlier epoch or the broadcast counter.
Together, `zab_future_commits` and `zab_commit_delivery` prove that a queued
`CommitLd` names an entry that exists when the follower processes it. This
justifies the source's unchecked lookup without changing its guard.

`zab_committed_prefixes` proves that every committed range fits in the server's
history and agrees with its committed identifier. Every range beyond the
bootstrap entry has a quorum certificate. A received commit carries a
certificate from a historical leader log; historical log matching transfers
it to the receiving log. Same-epoch retention and certified retention across
epochs preserve inherited commitments when `NewLeader` replaces a history.
The source's retained commit index therefore remains valid.

`zab_commit_safety` discharges `PrefixConsistency`, `Agreement`, `TotalOrder`,
and `GlobalPrimaryOrder` from those bounds, certificates, and historical log
matching. `zab_primary_barrier` proves that entering broadcast commits all
inherited entries, and that a broadcasting leader's commit index never goes
backwards. This establishes `PrimaryIntegrity` for connected followers.

`zab_proposal_records` proves that an entry missing from the passive proposal
history must be a local request of that server's own current epoch. A quorum
certificate includes a different server. Election uniqueness excludes such a
private request at that server, so its stored prefix was actually proposed.
`zab_integrity` uses this fact to prove `Integrity`. Finally,
`zab_proposal_order` traces each positive-epoch proposal record to the issuing
leader's actual log. Two records from the same leader and epoch have a common
ordered history. Historical log matching carries their order into any
committed recipient prefix, proving `LocalPrimaryOrder`.

All nine Zab benchmark safety goals are proved from the initial state and the
unchanged transition relation. The proofs cover arbitrary finite server sets,
unbounded executions, restarts, and log replacement. The one-server case
remains in discovery as specified by the source.

Low-level ZooKeeper has a separate `FastLeaderElection` state machine, including
notification queues, vote versions, rank-based tie breaking, and election
rounds. The protocol port retains all 23 top-level action alternatives,
partitions, crashes/restarts, DIFF/TRUNC/SNAP synchronization, buffered proposals
and commits, snapshots, and the two passive verification histories. Its goals
reuse Zab's equal predicates through a projection of the state; `Leadership1`
compares accepted epochs as required by this model. All nine initial predicates
verify. The source's disconnected-follower crash calls `CleanInputBuffer({i})`,
although that helper compares each receiver directly with its argument. With
the port's integer server identifiers, this clears no protocol channels. The
port preserves that behavior and does not repair the source call.
`zookeeper_channels::disconnected_empty` now proves that a disconnected follower
already has empty protocol channels in both directions, for the port's integer
identifiers. The scalar-versus-set comparison still needs revisiting before
generalizing correspondence to TLA+ identifiers that are themselves sets.
Both low-level ZooKeeper leadership invariants are proved. Four other
benchmark invariants have reachable counterexamples; the remaining three hit
out-of-domain history accesses in the original source.

`zk_election_types` proves that selected leaders and notification sources are
configured servers, that a leader's vote names itself, and that receipt maps
retain their domains. Election steps preserve current epochs and log contents.
`zookeeper_support` extends the map and reference invariants to the protocol,
including shutdown, crash, partition, recovery, and synchronization actions.
`zookeeper_connections` proves the role/phase and leader/follower link relations.

`zookeeper_epochs` proves that accepted and current epochs never decrease.
A fresh leader starts its proposed epoch above its accepted epoch.
`zookeeper_channels` proves that queued protocol messages connect an actual
leader and follower, and forwarding destinations remain learners.
`zookeeper_receipt_sets` and `zookeeper_receipts` prove unique receipt identities
and retention of the leader's own receipt. `zookeeper_leader_frame` proves that
a continuing leader retains receipt identities and fixes its proposed epoch
after a quorum has formed.

`zookeeper_epoch_votes` defines vote evidence through actual `FollowerInfo` or
`LeaderInfo` steps that strictly increase a server's accepted epoch. It proves
that one server cannot cast these votes for different leaders at the same
epoch. Quorum intersection then proves uniqueness for leaders with such vote
certificates.

`zookeeper_message_frames` and `zookeeper_epoch_messages` connect queued
discovery messages to their send steps and to the leader's fixed proposed
epoch. `zookeeper_ack_votes` proves that a positive acknowledgment records an
actual strict epoch increase. `zookeeper_self_votes` proves that a leader's own
receipt also corresponds to a strict epoch increase when a connection quorum
first forms. The proof handles configurations with at most one server
separately; the final theorems add no server-count assumption.

`zookeeper_quorum_receipts` proves that positive election receipts persist
during continuous leadership. `zookeeper_receipt_votes` uses those receipts
to certify every completed discovery election. `zookeeper_completion` traces
`NewLeader` and `AckLd` messages and proves that a leader in synchronization or
broadcast has completed that election. This closes the previously conditional
connection between the actual protocol and its quorum-vote certificates.

`zookeeper_leadership::benchmark_leadership1` proves uniqueness of concurrent
leaders with the same accepted epoch. `benchmark_leadership2` proves uniqueness
of all leaders recorded for each historical epoch, by finding the actual
completed discovery step that recorded each leader. Both apply to every state
of every behavior admitted by the handwritten initial state and transition
relation. They use neither the abstract Zab election oracle nor a monotonicity
assumption about FastLeaderElection's logical clock.

`zookeeper_session_frames` proves that a continuing follower keeps its leader,
accepted epoch, and phase progress. `zookeeper_leader_logs` proves that a
continuing leader preserves all earlier transaction contents. Its history may
grow and acknowledgment metadata may change. `zookeeper_ready` connects
protocol traffic, forwarding destinations, and synchronization receipts to
followers that accepted the connected leader's fixed epoch. Disconnecting a
learner clears the receipt fields that would authorize another synchronization.

`zookeeper_single_sync` counts queued epoch acknowledgments, ready receipts,
and active forwarding streams. Their sum is at most one for each leader/peer
pair. A new synchronization therefore starts before forwarding is active and
cannot reuse the same receipt. `zookeeper_forwarding` proves that data and
activation traffic follow a synchronization batch. `zookeeper_buffer_origin`
proves that the follower's buffers are empty when that batch starts.

`zookeeper_mode_fifo` proves that DIFF/TRUNC/SNAP precedes data in the batch and
is processed with empty pending and commit buffers. `zookeeper_pending_mode`
shows that a forwarding follower cannot receive a proposal or commit before
processing its mode header. `zookeeper_initial_log` tracks the retained history
before that header. `zookeeper_sync_buffers` then proves that TRUNC/SNAP commit
processing removes an existing pending transaction, excluding an empty-buffer
read or tail operation in that branch. `zookeeper_online` rules out restarting
a server that is still an active follower or leader.

`zookeeper_proposal_records` proves that each transmitted proposal appears in
the benchmark's passive proposal history, whether created by a new request or
sent in a synchronization batch. That history never shrinks.

`zookeeper_leader_bounds` proves that a broadcasting leader's committed and
snapshot indices stay within its retained history. `zookeeper_log_records`
uses this bound for SNAP payloads and proves proposal provenance for every
stored transaction, pending transaction, and transmitted snapshot entry.
It checks election changes, acknowledgment updates, buffer draining, and
history replacement.

`zookeeper_active_epoch` proves that completed discovery installs the accepted
epoch as the leader's current epoch. `zookeeper_log_math` handles increasing
transaction sequences, including empty histories. `zookeeper_log_order` proves
that retained histories and active synchronization buffers contain strictly
increasing transaction identifiers, with epochs bounded by the server's
accepted epoch. It also proves nonnegative committed, snapshot, and processed
indices. Proposal and SNAP message bounds connect each append or replacement
to that invariant. `zookeeper_small_cluster` handles the zero- and one-server
cases, so the final log-order theorem adds no server-count assumption.
These supporting invariants do not add benchmark goals to the proof count.

A guided source check found reachable violations of `PrimaryIntegrity`,
`PrefixConsistency`, `Agreement`, and `TotalOrder`. The exact 167-transition
replay uses byte-identical source modules, three servers, and the allowed fixed
request value 0. Verus checks every enabled action and resulting state, then
extends the execution forever by stuttering. The source audit compares every
state against the certificate input. See the
[counterexample evidence](../reports/tlaps_bench_manual/zookeeper_counterexample/README.md).

The failure combines partial synchronization with truncation refusal. A
follower installs and commits a snapshot before processing NEWLEADER. Another
server wins a later election with a shorter log. The follower rejects a
truncation below its committed index but still completes the later handshake
and enters broadcast. The new leader lacks the follower's committed entry.
Later appends and another follower's snapshot expose the other three failures.
Unconditional preservation of committed prefixes is therefore false for this
source model and cannot serve as an inductive strengthening.

`Integrity` and `GlobalPrimaryOrder` initially appeared approachable through
proved local facts. Stored and pending transactions have proposal records,
and each retained history has increasing transaction identifiers. The missing
step was bounding the committed index after history replacement and restart.
That range claim is false in the source. A longer trace reaches snapshot index
4 after the corresponding history has been replaced by a three-entry snapshot.
Restart restores committed index 4, and the server later follows its leader
again without restoring a fourth entry.

Exact source replays of `Integrity`, `GlobalPrimaryOrder`, and
`LocalPrimaryOrder` each fail when evaluating history entry 4. These are source
evaluation errors, not solver timeouts or proofs of negated benchmark goals.
The [invalid-index evidence](../reports/tlaps_bench_manual/zookeeper_bad_index/README.md)
records the 197-transition trace and all state comparisons. Its separate Verus
certificate checks reachability of the invalid committed index. Assigning an arbitrary value to the
missing entry or adding a transition guard would change the benchmark problem.

A separate [conditional diagnostic](../reports/tlaps_bench_manual/zookeeper_index_probe/README.md)
checks the dependency on that missing entry. Three lemmas pass Verus with
`--no-cheating`. At the certified states, `Integrity` requires its value to be
0, and `GlobalPrimaryOrder` requires its epoch to be at least 4. If the missing
entry instead denotes transaction `(1, 2)` with value 0, `LocalPrimaryOrder`
fails because the required earlier transaction `(1, 1)` is absent. These are
conditional facts about an unspecified out-of-range value. They do not supply
that value, prove the three goals, or refute them. They are excluded from the
benchmark score and the complete proof-suite function count.

A repair would need to keep installed history and saved snapshot metadata
consistent, and to prevent the synchronization handshake from completing after
an unsafe truncation is rejected. These are repair candidates, not verified
fixes. The source models and handwritten transition definitions remain unchanged.

Cahill SSI retains begin/read/write/commit/abort, blocked writes, first-committer
wins, X locks, SIREAD locks, conflict flags, abort reasons, and event history.
Transaction and key domains may be infinite. The goal uses the source's three
kinds of committed-transaction dependency edges. A finite closed path expresses
a graph cycle. The full committed-dependency-cycle theorem is proved. The source's
weak fairness is unnecessary for this safety argument.

`cahill_support` proves that every lock holder and waiter belongs to the finite
active history. Consequently the source's first-committer-wins loser set is
finite, and its `ISet` to `Set` conversion preserves every member. This closes
the finite-abort-set obligation without restricting the transaction-ID domain.
`cahill_history` checks the effect of every abort in the atomic commit batch.
`cahill_lifecycle` proves that events either begin a fresh transaction or belong
to an active transaction. Begin events are unique and the source's chosen start
position is an actual, unique history index. `cahill_locks` proves exclusive
ownership and validates the lock owner selected by deadlock detection.

`cahill_deadlocks` proves that the reachable wait graph is acyclic. Acquiring a
lock can add wait edges only toward a transaction that is no longer waiting.
A new wait edge either leaves the graph acyclic or creates a cycle through the
requesting transaction. The selected abort victim lies on that cycle and
breaks it. The functional-graph lemmas show that two simple cycles sharing a
transaction have the same members.

`cahill_wait_search::correspondence` closes the deadlock-search obligation. It
proves that the successor walk terminates after visiting at most the number of
active transactions. It either reaches a transaction that is not waiting or
returns to the requester. The unique returned cycle is exactly the simple
path used by the handwritten victim-selection predicate. The proof's finite
search guard is shown unreachable before either source stopping condition.
The connection of these checked definitions to the TLA+ operators is still
part of the documented manual source review, rather than a language-refinement
theorem.

`cahill_records` connects X locks and SIREAD locks to the recorded writes and
reads. `cahill_unique` proves each transaction accesses a key at most once for
each operation kind. `cahill_history_order` proves unique transaction endpoints,
disjoint commit/abort outcomes, and stable event positions as histories grow.
`cahill_positions` proves that filtering to committed transactions preserves
the relative order of retained events.

`cahill_first_committer` proves that a transaction holding or awaiting an X lock
has no writer to that key committed since its begin event. A committing writer
aborts every waiter on its locks. Exclusive ownership excludes other active
writers to the same key. This covers `FinishBlockedWrite`, which does not repeat
the initial first-committer check. `cahill_writer_intervals` consequently proves
that committed transactions writing the same key have disjoint lifetimes.

`cahill_conflicts` proves that a committed transaction never has both conflict
flags, including changes made by other transactions after it commits.
`cahill_versions` connects the snapshot's selected version and later committed
writers to the source's newer-version set. `cahill_overlap_safety` proves that
every overlapping read/write pair whose transactions have not aborted has the
reader's outgoing flag and the writer's incoming flag. Both access orders,
blocked writes, commit batches, and deadlock aborts are covered.

`cahill_serializable` assigns each committed transaction its begin-event index
when `outConflict` is true, and its commit-event index otherwise. Every source
dependency strictly increases this rank. A write/write dependency places the
first commit before the second begin; the source's write/read dependency has
that order directly. A read/write dependency either has the same order or
uses the overlap flags. In the latter case, the writer's incoming flag excludes
its outgoing flag, so the reader's begin index is less than the writer's commit
index. Strict increase excludes every finite closed dependency path.

`cahill_cycle_search` also checks the recursive cycle detector used in the
benchmark. The dependency graph is finite because committed transactions come
from a finite history, even when the identifier and key domains are infinite.
The search terminates by decreasing the set of unvisited graph nodes.
`source_equation` checks its recurrence with the source's visited-set argument.
The rank proof makes every search result empty. The final theorem establishes
both the closed-path predicate and the empty cycle-node set at every behavior
index. The connection to the original TLA+ text remains a manual source review,
as for the other handwritten models.

MongoDB retains the benchmark's snapshot settings, router requests, participant
tracking, shard operations, prepare/vote/commit message sets, storage snapshots,
prepare blocking, write conflicts, and timestamps. The model keeps the source's
read and write success/failure behavior. Static catalog copies share one
catalog; always-zero commit/stable/oldest indices and the unused abort-message
set are omitted. The durable timestamp field remains explicit. `NoValue` is
excluded from transaction IDs but may equal a timestamp, as allowed by the
source. The goal asks for a permutation of committed transactions with a
snapshot cut, complete reads, and no intervening write conflict. The induction
probe requires `SingleWritePerKey` before and after each transition, matching
the theorem's explicit temporal premise. That initial probe has now been
superseded by a full proof of the benchmark theorem.

The MongoDB proof starts with storage and read-snapshot invariants.
`mongodb_support` connects active snapshot flags to the finite active set.
`mongodb_maximum` proves that the timestamp maxima used by prepare and commit
exist, even with an infinite transaction-ID domain. `mongodb_router_time` and
`mongodb_read_time` establish one immutable router read timestamp per transaction
and the same read timestamp at every started shard. The source's allowance for
`NoValue` to equal a timestamp is preserved; such a router selection cannot
issue operations until a different timestamp is selected.

`mongodb_storage_lifecycle` connects prepare and commit records to transaction
flags, proves their uniqueness, and puts each record after its transaction's
read timestamp. Completed shard snapshots and operations stay fixed.
`mongodb_storage_contents` and `mongodb_log_contents` connect local operations,
write sets, key ownership, and stored write identifiers. `mongodb_observed`
proves that the observed transaction set is finite and its operations are
well-formed. `mongodb_projection` proves that filtering an observed transaction's
operations by shard yields exactly that shard's committed operations.

`mongodb_write_conflicts` proves exclusive active writers and excludes a
committed write from an active writer's snapshot interval. `mongodb_write_order`
orders successive committed writes of a key before the next writer's read
timestamp. `mongodb_snapshot_values` checks the selected last eligible log
entry. `mongodb_snapshot_view` accounts for prepared transactions that commit
after a reader creates its snapshot, including the source's refreshed reads.

`mongodb_prepare_barrier` proves that every active prepared writer to an already
read key has a prepare timestamp after that reader's snapshot. This remains
true when the reader commits, because its commit record protects the timestamp
bound. `mongodb_read_stability` then excludes later eligible commits to the
already read key. `mongodb_local_reads::complete_local` proves that every
committed shard transaction satisfies `Complete` against its timestamped local
snapshot, including its preceding local writes. These are inductive proofs over
all model actions, without finite parameter bounds or added assumptions.

`mongodb_participants` proves that a selected router's participant list freezes
when commit begins. `mongodb_issued` relates every requested and executed
operation to that list. `mongodb_coordination` and `mongodb_votes` certify the
prepare messages and votes against the frozen participants and immutable
prepare timestamps. `mongodb_commit_time` covers two-phase commit, direct
single-shard commit, and direct read-only commit. If the two-phase timestamp
aliases `NoValue`, the storage guard prevents it from being used as an
unprepared commit. No extra sentinel restriction is imposed.

`mongodb_transaction_time` proves that every observed writer has one commit
timestamp across its shards, strictly after its common read timestamp.
`mongodb_global_reads` composes local read correctness through the shard
projection, including the exact prefix before each read. It does not assume
that equal operation records have distinct contents or collapse their positions.

`mongodb_order` constructs a permutation of the finite observed transaction
set. Writers sort at twice their commit timestamp; read-only transactions sort
at twice their read timestamp plus one. A transaction's snapshot cut includes
exactly the prefix at or below twice its read timestamp. `mongodb_execution`
proves that executing this prefix yields the same values as the storage
snapshots: both choose the last eligible writer of each key. The write-order
invariant excludes conflicting writes between the cut and the transaction.
This follows the timestamp-ordering route described in the
[protocol paper, section 3.2.1](https://www.vldb.org/pvldb/vol18/p5045-schultz.pdf#page=4).

`mongodb_snapshot_isolation::benchmark_snapshot_isolation` proves the source's
identity-based, position-based `SnapshotIsolation` predicate at every behavior
index. The final theorem retains the benchmark's explicit temporal
`SingleWritePerKey` premise; the supporting argument also works without using
it. The model and its transition guards are unchanged. Transaction, key,
router, shard, and timestamp domains have no added finiteness assumption.
The order contains only transactions whose committed shard operations are
observed at that state, so the proof also covers partial multi-shard commits.

The [direct-induction probes](../reports/tlaps_bench_manual/probes/results.json)
record the initial attempts on the 41 safety goals that were open before the
FLASH strengthening proofs. For the first five ports they use the
already proved strengthening together with the target predicate. The four new
ports start with the target itself. Initialization proofs are supplied where
needed. These attempts do not establish a counterexample or impossibility of a
proof when they fail. Thirty-eight attempts did not close and three reached the solver resource
limit. The six FLASH failures, three OpenAddressing failures, and the etcd
`ElectionSafety`, `LogMatching`, `CommittedIsDurable`, `LogInv`, and `QuorumLog`
failures, together with all five HashiCorp attempts and all nine Zab attempts,
and the Cahill serializability, MongoDB snapshot-isolation, and low-level
ZooKeeper leadership attempts have since been superseded by full proofs.
Six safety goals have reachable counterexamples: two etcd goals and four
low-level ZooKeeper goals. Three low-level ZooKeeper goals encounter source
evaluation errors on a reachable invalid index. Probe files and logs are
separate from the passing verification suite. Initialization-only results and
evaluation errors do not count as proved benchmark invariants.

Sixty-three fault controls modify temporary copies of the models and require an
assertion or contract failure, rather than treating a timeout or compile failure
as success. They introduce early OpenAddressing completion, a reversed flush
value, undefined FLASH writeback data, an uncleared negative acknowledgment,
an unchecked TLB page-map lock, released etcd votes without persistence, and
overlapping HashiCorp configuration changes. The seven new FLASH controls
duplicate exclusive ownership, write back stale data, leave forwarding unlocked,
acknowledge without invalidating, suppress an invalidation acknowledgment,
leave a reply unconsumed, and retain the directory lock after its last
acknowledgment. The etcd origin control invents a future-term entry during append reception.
The etcd log control removes the previous-term check from append reception.
The TLB progress controls retain quiescence work and fail to release a page-map
lock. Three further OpenAddressing controls overwrite a positive entry, advance
past a matching fingerprint, and flush a value without marking its table copy.
The etcd persistence control releases append messages while retaining the old
disk log. The decision-history control commits without an acknowledgment quorum.
The election controls skip the voting log comparison and truncate two entries
instead of one on an append conflict. The heartbeat control removes the cap
on advertised commit indices imposed by the recipient's acknowledged match index.
Two HashiCorp controls release a vote without persisting it and allow votes for
different candidates in one term. Three further HashiCorp controls skip the
append previous-term check, acknowledge an extra unstored entry, and grant votes
without comparing logs. Two commit controls allow configuration proposals without
a current-term commit and mark a configuration committed before its index.
Three Zab controls retain channel messages during shutdown, accept a stale
epoch, and let an older leader reconnect after the oracle moves to another
leader. They break the connection, epoch, and leadership-interval proofs.
Two more Zab controls send proposals to followers before synchronization and
change a received transaction's value. They break the FIFO synchronization and
follower-prefix proofs. Two acknowledgment controls send an acknowledgment
without storing its transaction and omit the acknowledgment-prefix update.
They break the storage-witness and acknowledgment-update proofs. Two commitment
controls advertise a missing entry and skip the final inherited commitment.
Two proposal controls omit a broadcast's passive record and record the wrong
issuing epoch. Three Cahill controls retain a waiter after aborting it, keep
a newly formed deadlock cycle, and acquire a lock already held by another
transaction. They break the support, wait-graph, and exclusive-lock proofs.
Four further Cahill controls commit with both conflict flags, omit the newer
writer's incoming flag, omit the reader's outgoing flag, and ignore a previously
committed writer. They break the conflict, overlap, and first-committer proofs.
Three MongoDB controls change a request's read timestamp, allow a read despite
a prepare conflict, and ignore a write conflict. They break the read-timestamp,
prepare-barrier, and exclusive-writer proofs. Two more allow participant changes
after commit begins and alter the timestamp in a prepare vote. They break the
frozen-participant and vote-certificate proofs. Two low-level ZooKeeper controls
forge an election notification's sender and store an epoch receipt under a
different server identity. They break the notification and receipt-identity
proofs. Together with the later controls below, all sixty-three controls are
rejected by assertion or contract failures. The first
five logs are under [controls](../reports/tlaps_bench_manual/controls/results.json);
the Raft logs are under [raft_controls](../reports/tlaps_bench_manual/raft_controls/results.json).
The new FLASH logs are under
[coherence_controls](../reports/tlaps_bench_manual/coherence_controls/results.json)
and [progress_controls](../reports/tlaps_bench_manual/progress_controls/results.json).
The etcd origin control is under
[origin_controls](../reports/tlaps_bench_manual/origin_controls/results.json);
the log control is under [log_controls](../reports/tlaps_bench_manual/log_controls/results.json).
The TLB progress controls are under [tlb_controls](../reports/tlaps_bench_manual/tlb_controls/results.json).
The OpenAddressing controls are under [open_addressing_controls](../reports/tlaps_bench_manual/open_addressing_controls/results.json).
The etcd persistence control is under [persistence_controls](../reports/tlaps_bench_manual/persistence_controls/results.json).
The etcd election controls are under [election_controls](../reports/tlaps_bench_manual/election_controls/results.json).
The heartbeat control is under [heartbeat_controls](../reports/tlaps_bench_manual/heartbeat_controls/results.json).
Two leadership controls record the wrong leader identity and erase an earlier
positive election receipt. They must fail the historical-leader and
receipt-retention proofs respectively.
Two synchronization controls omit a DIFF header and alter a transaction value
while updating acknowledgment metadata. They must fail the pending-header and
leader-history preservation proofs respectively.
A transaction-counter control reuses the last counter when appending a request.
It fails the transaction-order proof. Two attempted provenance mutations
exhausted solver resources and are excluded from the control count.

The HashiCorp vote controls are under [hashicorp_vote_controls](../reports/tlaps_bench_manual/hashicorp_vote_controls/results.json).
The HashiCorp log controls are under [hashicorp_log_controls](../reports/tlaps_bench_manual/hashicorp_log_controls/results.json).
The HashiCorp commit controls are under [hashicorp_commit_controls](../reports/tlaps_bench_manual/hashicorp_commit_controls/results.json).
The Zab controls are under [zab_controls](../reports/tlaps_bench_manual/zab_controls/results.json),
[zab_epoch_controls](../reports/tlaps_bench_manual/zab_epoch_controls/results.json),
[zab_election_controls](../reports/tlaps_bench_manual/zab_election_controls/results.json),
[zab_log_controls](../reports/tlaps_bench_manual/zab_log_controls/results.json),
[zab_ack_controls](../reports/tlaps_bench_manual/zab_ack_controls/results.json),
[zab_commit_controls](../reports/tlaps_bench_manual/zab_commit_controls/results.json),
[zab_proposal_controls](../reports/tlaps_bench_manual/zab_proposal_controls/results.json),
[cahill_controls](../reports/tlaps_bench_manual/cahill_controls/results.json),
[cahill_safety_controls](../reports/tlaps_bench_manual/cahill_safety_controls/results.json),
[mongodb_storage_controls](../reports/tlaps_bench_manual/mongodb_storage_controls/results.json),
[mongodb_commit_controls](../reports/tlaps_bench_manual/mongodb_commit_controls/results.json),
[zookeeper_foundation_controls](../reports/tlaps_bench_manual/zookeeper_foundation_controls/results.json),
[zookeeper_leadership_controls](../reports/tlaps_bench_manual/zookeeper_leadership_controls/results.json),
[zookeeper_sync_controls](../reports/tlaps_bench_manual/zookeeper_sync_controls/results.json),
and [zookeeper_log_controls](../reports/tlaps_bench_manual/zookeeper_log_controls/results.json).

The three remaining unproved goals are listed below. Their range-preservation
obligation failed because the original model permits the bad state, not because
the SMT solver lacked an induction hint.

| Model | Unproved safety goals | Current evidence |
|---|---|---|
| Low-level ZooKeeper | `Integrity`, `GlobalPrimaryOrder`, `LocalPrimaryOrder` | A source execution restores committed index 4 over a three-entry history. Exact replays of each original goal report an out-of-domain access. Verus checks reachability of that invalid index. |

All nine benchmark liveness goals are proved. Six other safety goals have
checked reachable counterexamples and are not included in the proved count.
The two etcd counterexamples concern defects in the stated properties and do
not establish a violation of committed-log agreement. The low-level ZooKeeper
counterexamples also prevent the proposed unconditional prefix argument.

The continued proof effort has also established etcd log-term ordering and the
relationship between a current leader's live and persisted logs in
`etcd_order.rs`. These supporting properties do not count as benchmark goals.

OpenAddressing content provenance in `open_addressing_contents.rs` proves that
a membership result cannot invent an uninserted fingerprint. It forms part of
the completed `Contains` proof. Finite TLC checks of the pinned OpenAddressing
source also passed for the original two-fingerprint
configuration and a three-fingerprint configuration forcing collisions and
eviction. Those finite checks do not contribute to the unbounded proof count.

The recorded toolchain is Verus `0.2026.08.30.b432e82` with Rust `1.97.1`.
From this worktree, set `VERUS_PATH` to the verifier executable and put its Rust
toolchain on `PATH`:

```bash
scripts/verify_tlaps_bench_manual.sh
python3 scripts/report_tlaps_bench_manual.py --bench /var/tmp/TLAPS-Bench
python3 scripts/test_tlaps_bench_manual_controls.py
python3 scripts/probe_tlaps_bench_manual.py
```

The report command checks the pinned benchmark revision and rejects modified
tracked benchmark sources. The baseline and controls should succeed. Probe
results are diagnostic and cannot promote a goal into the score automatically.
No TLAPS installation, .NET build, or generated Rust is needed for these checks.

Source attribution and license texts are preserved under
[docs/licenses/tlaps-bench](licenses/tlaps-bench/upstream-NOTICE.txt).
Earlier automatic-translation experiments do not contribute to this batch.
